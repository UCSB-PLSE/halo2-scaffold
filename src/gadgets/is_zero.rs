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
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, VirtualCells},
    poly::Rotation,
};

#[derive(Clone, Debug)]
pub struct IsZeroChip<F: FieldExt> {
    // internal signal
    pub value_inv: Column<Advice>,
    // expression
    pub is_zero_expr: Expression<F>,
}

impl<F: FieldExt> IsZeroChip<F> {
    // Output expression
    pub fn expr(&self) -> Expression<F> {
        self.is_zero_expr.clone()
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        value: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let mut is_zero_expr = Expression::Constant(F::zero());
        let value_inv = meta.advice_column();

        meta.create_gate("is_zero", |meta| {
            //
            // valid | value |  value_inv |  1 - value * value_inv | value * (1 - value* value_inv)
            // ------+-------+------------+------------------------+-------------------------------
            //  yes  |   x   |    1/x     |         0              |  0
            //  no   |   x   |    0       |         1              |  x
            //  yes  |   0   |    0       |         1              |  0
            //  yes  |   0   |    y       |         1              |  0
            //
            let value = value(meta);
            let q_enable = q_enable(meta);
            let value_inv = meta.query_advice(value_inv, Rotation::cur());

            is_zero_expr = Expression::Constant(F::one()) - value.clone() * value_inv;
            vec![q_enable * value * is_zero_expr.clone()]
        });

        IsZeroChip { value_inv, is_zero_expr }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        value: Value<F>,
    ) -> Result<Value<F>, Error> {
        let value_inv = value.map(|value| value.invert().unwrap_or(F::zero()));
        region.assign_advice(|| "value inv", self.value_inv, offset, || value_inv)?;

        Ok(value.map(|value| if value == F::zero() { F::one() } else { F::zero() }))
    }
}

#[cfg(test)]
mod tests {

    use super::IsZeroChip;
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::MockProver,
        halo2curves::pasta::Fp,
        plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Instance, Selector},
        poly::Rotation,
    };

    #[derive(Clone)]
    struct MyConfig {
        izc: IsZeroChip<Fp>,
        inp: Column<Advice>,
        out: Column<Advice>,
        instance: Column<Instance>,
        selector: Selector,
    }

    #[derive(Default)]
    struct MyCircuit {
        a: Value<Fp>,
    }

    impl Circuit<Fp> for MyCircuit {
        type Config = MyConfig;
        type FloorPlanner = SimpleFloorPlanner;
        // type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
            let [inp, out] = [(); 2].map(|_| meta.advice_column());
            [inp, out].map(|col| meta.enable_equality(col));

            let instance = meta.instance_column();
            meta.enable_equality(instance);

            let selector = meta.selector();

            let izc = IsZeroChip::configure(
                meta,
                |meta| meta.query_selector(selector),
                |meta| meta.query_advice(inp, Rotation::cur()),
            );

            meta.create_gate("is_zero", |meta| {
                let out = meta.query_advice(out, Rotation::cur());
                let s = meta.query_selector(selector);
                vec![s * (out - izc.expr())]
            });

            MyConfig { izc, inp, out, instance, selector }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<Fp>,
        ) -> Result<(), Error> {
            let out = layouter.assign_region(
                || "",
                |mut region| {
                    config.selector.enable(&mut region, 0)?;
                    let inp = region.assign_advice(|| "load input", config.inp, 0, || self.a)?;
                    let out_val = config.izc.assign(&mut region, 0, inp.value().copied())?;
                    let out = region.assign_advice(|| "out", config.out, 0, || out_val)?;
                    Ok(out)
                },
            )?;
            layouter.constrain_instance(out.cell(), config.instance, 0)?;
            Ok(())
        }
    }

    #[test]
    fn zero() {
        let a = Fp::from(0);
        let o = Fp::from(1);
        let p_circuit = MyCircuit { a: Value::known(a) };
        let public_inputs = vec![o];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();

        let a = Fp::from(69);
        let o = Fp::from(0);
        let p_circuit = MyCircuit { a: Value::known(a) };
        let public_inputs = vec![o];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
}
