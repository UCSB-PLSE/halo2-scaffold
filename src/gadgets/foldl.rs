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
    circuit::{AssignedCell, Region, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct Foldl<F> {
    expr: fn(Expression<F>, Expression<F>) -> Expression<F>,
    wg: fn(F, F) -> F,
    init: Value<F>,
    annotation: &'static str,
}

impl<F: FieldExt> Foldl<F> {
    fn add() -> Self {
        Self {
            expr: |acc, x| acc + x,
            wg: F::add,
            init: Value::known(F::zero()),
            annotation: "add",
        }
    }

    fn mul() -> Self {
        Self { expr: |acc, x| acc * x, wg: F::mul, init: Value::known(F::one()), annotation: "mul" }
    }

    fn sub() -> Self {
        Self {
            expr: |acc, x| acc - x,
            wg: F::sub,
            init: Value::known(F::zero()),
            annotation: "sub",
        }
    }
}

#[derive(Clone, Debug)]
pub struct FoldlChip<F: FieldExt> {
    xs: Column<Advice>,
    acc: Column<Advice>,
    s: Selector,
    op: Foldl<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> FoldlChip<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>, g: Foldl<F>) -> Self {
        let xs = meta.advice_column();
        let acc = meta.advice_column();
        let s = meta.selector();
        meta.create_gate(g.annotation, |meta| {
            let x = meta.query_advice(xs, Rotation::cur());
            let acc_curr = meta.query_advice(acc, Rotation::cur());
            let acc_next = meta.query_advice(acc, Rotation::next());
            let s = meta.query_selector(s);
            vec![s * (acc_next - (g.expr)(acc_curr, x))]
        });
        meta.enable_equality(acc);
        FoldlChip { xs, acc, s, op: g, _marker: PhantomData }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        xs: Vec<Value<F>>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.name_column(|| "acc", self.acc);
        region.name_column(|| "xs", self.xs);
        let mut acc = region.assign_advice(|| "acc/init", self.acc, 0, || self.op.init)?;
        for (i, x) in xs.into_iter().enumerate() {
            self.s.enable(region, i)?;
            region.assign_advice(|| "x", self.xs, i, || x)?;
            let acc_val = acc.value().copied().zip(x).map(|(acc, x)| (self.op.wg)(acc, x));
            acc = region.assign_advice(|| "acc", self.acc, i + 1, || acc_val)?;
        }
        Ok(acc)
    }
}

#[cfg(test)]
mod tests {

    mod test_assert_nonzero {

        use crate::gadgets::foldl::{Foldl, FoldlChip};
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Circuit, Column, ConstraintSystem, Error, Fixed},
        };

        #[derive(Clone)]
        struct FoldlTestConfig {
            fc: FoldlChip<Fp>,
            #[allow(dead_code)]
            constant: Column<Fixed>,
        }

        #[derive(Default)]
        struct FoldlTestCircuit {
            xs: Vec<Value<Fp>>,
            out: Fp,
        }

        impl Circuit<Fp> for FoldlTestCircuit {
            type Config = FoldlTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let s = meta.selector();

                let fc = FoldlChip::configure(meta, Foldl::add());

                let constant = meta.fixed_column();
                meta.enable_constant(constant);

                FoldlTestConfig { fc, constant }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "foldl add",
                    |mut region| {
                        let out = config.fc.assign(&mut region, self.xs.clone())?;
                        region.constrain_constant(out.cell(), self.out)
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let xs = vec![0, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = FoldlTestCircuit { xs: xs, out: Fp::from(3) };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[derive(Default)]
        struct FoldlTestCircuit2 {
            xs: Vec<Value<Fp>>,
            out: Fp,
        }

        impl Circuit<Fp> for FoldlTestCircuit2 {
            type Config = FoldlTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let s = meta.selector();

                let fc = FoldlChip::configure(meta, Foldl::mul());

                let constant = meta.fixed_column();
                meta.enable_constant(constant);

                FoldlTestConfig { fc, constant }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "foldl add",
                    |mut region| {
                        let out = config.fc.assign(&mut region, self.xs.clone())?;
                        region.constrain_constant(out.cell(), self.out)
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok2() {
            let xs = vec![1, 2, 3, 4].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = FoldlTestCircuit2 { xs: xs, out: Fp::from(24) };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        // #[test]
        // #[should_panic]
        // fn test_panic1() {
        //     let a = Fp::from(0);
        //     let p_circuit = FoldlTestCircuit { a: Value::known(a) };
        //     let prover = MockProver::run(3, &p_circuit, vec![]).unwrap();
        //     prover.assert_satisfied();
        // }
    }
}
