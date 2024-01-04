/* This file is part of DarkFi (https://dark.fi)
 *
 * Copyright (C) 2020-2023 Dyne.org foundation
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Affero General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Affero General Public License for more details.
 *
 * You should have received a copy of the GNU Affero General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Region, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct IsZeroChip<F: FieldExt> {
    // internal signal
    x_inv: Column<Advice>,
    // selector
    s: Selector,
    // expression
    _expr: Expression<F>,
}

impl<F: FieldExt> IsZeroChip<F> {
    // Output expression
    pub fn expr(&self) -> Expression<F> {
        self._expr.clone()
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let mut _expr = Expression::Constant(F::zero());
        let x_inv = meta.advice_column();
        let s = meta.selector();

        meta.create_gate("is_zero", |meta| {
            //
            // valid | x |  x_inv |  1 - x * x_inv | x * (1 - x* x_inv)
            // ------+-------+------------+------------------------+-------------------------------
            //  yes  |   x   |    1/x     |         0              |  0
            //  no   |   x   |    0       |         1              |  x
            //  yes  |   0   |    0       |         1              |  0
            //  yes  |   0   |    y       |         1              |  0
            //
            let x: Expression<F> = x(meta);
            let s = meta.query_selector(s);
            let x_inv = meta.query_advice(x_inv, Rotation::cur());

            _expr = Expression::Constant(F::one()) - x.clone() * x_inv;
            vec![s * x * _expr.clone()]
        });

        IsZeroChip { x_inv, s, _expr }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        x: Value<F>,
    ) -> Result<Value<F>, Error> {
        let x_inv = x.map(|x| x.invert().unwrap_or(F::zero()));
        self.s.enable(region, offset)?;
        region.name_column(|| "inv", self.x_inv);
        region.assign_advice(|| "inv", self.x_inv, offset, || x_inv)?;

        Ok(x.map(|x| if x == F::zero() { F::one() } else { F::zero() }))
    }
}

#[derive(Clone, Debug)]
pub struct AssertNonZeroChip<F: FieldExt> {
    inv: Column<Advice>,
    s: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AssertNonZeroChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let inv = meta.advice_column();
        let s = meta.selector();
        meta.create_gate("assert_nonzero", |meta| {
            let x = x(meta);
            let s = meta.query_selector(s);
            let inv = meta.query_advice(inv, Rotation::cur());
            vec![s * (Expression::Constant(F::one()) - x * inv)]
        });

        AssertNonZeroChip { inv, s, _marker: PhantomData }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        x: Value<F>,
    ) -> Result<(), Error> {
        self.s.enable(region, offset)?;
        region.name_column(|| "inv", self.inv);
        region.assign_advice(
            || "inv",
            self.inv,
            offset,
            || x.map(|x| x.invert().unwrap_or(F::zero())),
        )?;
        Ok(())
    }
}

#[derive(Clone, Debug)]
pub struct AssertZeroChip<F: FieldExt> {
    s: Selector,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> AssertZeroChip<F> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let s = meta.selector();
        meta.create_gate("assert_nonzero", |meta| {
            let x = x(meta);
            let s = meta.query_selector(s);
            vec![s * x]
        });

        AssertZeroChip { s, _marker: PhantomData }
    }

    pub fn assign(&self, region: &mut Region<'_, F>, offset: usize) -> Result<(), Error> {
        self.s.enable(region, offset)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {

    mod test_is_zero {

        use crate::gadgets::is_zero::IsZeroChip;
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
            poly::Rotation,
        };

        #[derive(Clone)]
        struct IsZTestConfig {
            izc: IsZeroChip<Fp>,
            inp: Column<Advice>,
            is_zero: Column<Advice>,
            instance: Column<Instance>,
            s: Selector,
        }

        #[derive(Default)]
        struct IsZTestCircuit {
            a: Value<Fp>,
        }

        impl Circuit<Fp> for IsZTestCircuit {
            type Config = IsZTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let [inp, is_zero] = [(); 2].map(|_| meta.advice_column());
                [inp, is_zero].map(|col| meta.enable_equality(col));

                let instance = meta.instance_column();
                meta.enable_equality(instance);

                let s = meta.selector();

                let izc =
                    IsZeroChip::configure(meta, |meta| meta.query_advice(inp, Rotation::cur()));

                meta.create_gate("is_zero", |meta| {
                    let is_zero = meta.query_advice(is_zero, Rotation::cur());
                    let s = meta.query_selector(s);
                    vec![s * (is_zero - izc.expr())]
                });

                IsZTestConfig { izc, inp, s, is_zero, instance }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                let is_zero = layouter.assign_region(
                    || "",
                    |mut region| {
                        config.s.enable(&mut region, 0)?;
                        let inp =
                            region.assign_advice(|| "load input", config.inp, 0, || self.a)?;
                        let is_zero_val =
                            config.izc.assign(&mut region, 0, inp.value().copied())?;
                        let is_zero = region.assign_advice(
                            || "is_zero",
                            config.is_zero,
                            0,
                            || is_zero_val,
                        )?;
                        Ok(is_zero)
                    },
                )?;
                layouter.constrain_instance(is_zero.cell(), config.instance, 0)?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let a = Fp::from(0);
            let o = Fp::from(1);
            let p_circuit = IsZTestCircuit { a: Value::known(a) };
            let public_inputs = vec![o];
            let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        fn test_ok2() {
            let a = Fp::from(69);
            let o = Fp::from(0);
            let p_circuit = IsZTestCircuit { a: Value::known(a) };
            let public_inputs = vec![o];
            let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic1() {
            let a = Fp::from(0);
            let o = Fp::from(0);
            let p_circuit = IsZTestCircuit { a: Value::known(a) };
            let public_inputs = vec![o];
            let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic2() {
            let a = Fp::from(69);
            let o = Fp::from(1);
            let p_circuit = IsZTestCircuit { a: Value::known(a) };
            let public_inputs = vec![o];
            let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
            prover.assert_satisfied();
        }
    }

    mod test_assert_nonzero {

        use crate::gadgets::is_zero::AssertNonZeroChip;
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
            poly::Rotation,
        };

        #[derive(Clone)]
        struct ANZTestConfig {
            anz: AssertNonZeroChip<Fp>,
            inp: Column<Advice>,
        }

        #[derive(Default)]
        struct ANZTestCircuit {
            a: Value<Fp>,
        }

        impl Circuit<Fp> for ANZTestCircuit {
            type Config = ANZTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let inp = meta.advice_column();
                meta.enable_equality(inp);

                let anz = AssertNonZeroChip::configure(meta, |meta| {
                    meta.query_advice(inp, Rotation::cur())
                });

                ANZTestConfig { anz, inp }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "",
                    |mut region| {
                        let inp =
                            region.assign_advice(|| "load input", config.inp, 0, || self.a)?;
                        config.anz.assign(&mut region, 0, inp.value().copied())?;
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let a = Fp::from(69);
            let p_circuit = ANZTestCircuit { a: Value::known(a) };
            let prover = MockProver::run(3, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic1() {
            let a = Fp::from(0);
            let p_circuit = ANZTestCircuit { a: Value::known(a) };
            let prover = MockProver::run(3, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }

    mod test_assert_zero {

        use crate::gadgets::is_zero::AssertZeroChip;
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
            poly::Rotation,
        };

        #[derive(Clone)]
        struct AZTestConfig {
            az: AssertZeroChip<Fp>,
            inp: Column<Advice>,
        }

        #[derive(Default)]
        struct AZTestCircuit {
            a: Value<Fp>,
        }

        impl Circuit<Fp> for AZTestCircuit {
            type Config = AZTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let inp = meta.advice_column();
                meta.enable_equality(inp);

                let az =
                    AssertZeroChip::configure(meta, |meta| meta.query_advice(inp, Rotation::cur()));

                AZTestConfig { az, inp }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "",
                    |mut region| {
                        region.assign_advice(|| "load input", config.inp, 0, || self.a)?;
                        config.az.assign(&mut region, 0)?;
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let a = Fp::from(0);
            let p_circuit = AZTestCircuit { a: Value::known(a) };
            let prover = MockProver::run(3, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic1() {
            let a = Fp::from(69);
            let p_circuit = AZTestCircuit { a: Value::known(a) };
            let prover = MockProver::run(3, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
