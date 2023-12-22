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

use halo2_proofs::{
    circuit::{Region, Value},
    halo2curves::FieldExt,
    plonk::{ConstraintSystem, Error, Expression, VirtualCells},
};

use super::is_zero::IsZeroChip;

#[derive(Clone, Debug)]
pub struct IsEqualChip<F: FieldExt> {
    is_zero_chip: IsZeroChip<F>,
}

impl<F: FieldExt> IsEqualChip<F> {
    // Output expression
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_chip.expr()
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        y: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let is_zero_chip = IsZeroChip::configure(meta, |meta| x(meta) - y(meta));

        IsEqualChip { is_zero_chip }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        x: Value<F>,
        y: Value<F>,
    ) -> Result<Value<F>, Error> {
        let diff = x.zip(y).map(|(a, b)| a - b);
        self.is_zero_chip.assign(region, offset, diff)
    }
}

#[derive(Clone, Debug)]
pub struct IsNotEqualChip<F: FieldExt> {
    is_equal: IsEqualChip<F>,
}

impl<F: FieldExt> IsNotEqualChip<F> {
    // Output expression
    pub fn expr(&self) -> Expression<F> {
        Expression::Constant(F::one()) - self.is_equal.expr()
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        y: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let is_equal = IsEqualChip::configure(meta, x, y);

        IsNotEqualChip { is_equal }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        x: Value<F>,
        y: Value<F>,
    ) -> Result<Value<F>, Error> {
        let o = self.is_equal.assign(region, offset, x, y)?;
        Ok(o.map(|o| F::one() - o))
    }
}

#[cfg(test)]
mod tests {

    use super::{IsEqualChip, IsNotEqualChip};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::pasta::Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
        poly::Rotation,
    };

    #[derive(Clone)]
    struct MyConfig {
        is_equal: IsEqualChip<Fp>,
        is_not_equal: IsNotEqualChip<Fp>,
        inp_x: Column<Advice>,
        inp_y: Column<Advice>,
        eq: Column<Advice>,
        neq: Column<Advice>,
        instance: Column<Instance>,
        selector: Selector,
    }

    #[derive(Default)]
    struct MyCircuit {
        a: Value<Fp>,
        b: Value<Fp>,
    }

    impl Circuit<Fp> for MyCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        // type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let [inp_x, inp_y, eq, neq] = [(); 4].map(|_| meta.advice_column());
            [inp_x, inp_y, eq, neq].map(|col| meta.enable_equality(col));

            let instance = meta.instance_column();
            meta.enable_equality(instance);

            let selector = meta.selector();

            let is_equal = IsEqualChip::configure(
                meta,
                |meta| meta.query_advice(inp_x, Rotation::cur()),
                |meta| meta.query_advice(inp_y, Rotation::cur()),
            );

            let is_not_equal = IsNotEqualChip::configure(
                meta,
                |meta| meta.query_advice(inp_x, Rotation::cur()),
                |meta| meta.query_advice(inp_y, Rotation::cur()),
            );

            meta.create_gate("is_equal", |meta| {
                let eq = meta.query_advice(eq, Rotation::cur());
                let s = meta.query_selector(selector);
                vec![s * (eq - is_equal.expr())]
            });

            meta.create_gate("is_not_equal", |meta| {
                let neq = meta.query_advice(neq, Rotation::cur());
                let s = meta.query_selector(selector);
                vec![s * (neq - is_not_equal.expr())]
            });

            MyConfig { is_equal, is_not_equal, inp_x, inp_y, eq, neq, instance, selector }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let (eq, neq) = layouter.assign_region(
                || "is_equal",
                |mut region| {
                    region.name_column(|| "eq", config.eq);
                    region.name_column(|| "neq", config.neq);
                    region.name_column(|| "inp_x", config.inp_x);
                    region.name_column(|| "inp_y", config.inp_y);

                    config.selector.enable(&mut region, 0)?;
                    let inp_x = region.assign_advice(|| "load x", config.inp_x, 0, || self.a)?;
                    let inp_y = region.assign_advice(|| "load y", config.inp_y, 0, || self.b)?;
                    let eq_val = config.is_equal.assign(
                        &mut region,
                        0,
                        inp_x.value().copied(),
                        inp_y.value().copied(),
                    )?;
                    let eq = region.assign_advice(|| "eq", config.eq, 0, || eq_val)?;
                    let neq_val = config.is_not_equal.assign(
                        &mut region,
                        0,
                        inp_x.value().copied(),
                        inp_y.value().copied(),
                    )?;
                    let neq = region.assign_advice(|| "neq", config.neq, 0, || neq_val)?;
                    Ok((eq, neq))
                },
            )?;
            layouter.constrain_instance(eq.cell(), config.instance, 0)?;
            layouter.constrain_instance(neq.cell(), config.instance, 1)?;
            Ok(())
        }
    }

    #[test]
    fn test() {
        let a = Fp::from(3);
        let b = Fp::from(2);
        let o1 = Fp::from(0);
        let o2 = Fp::from(1);
        let p_circuit = MyCircuit { a: Value::known(a), b: Value::known(b) };
        let public_inputs = vec![o1, o2];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();

        let a = Fp::from(69);
        let b = Fp::from(69);
        let o1 = Fp::from(1);
        let o2 = Fp::from(0);
        let p_circuit = MyCircuit { a: Value::known(a), b: Value::known(b) };
        let public_inputs = vec![o1, o2];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
}
