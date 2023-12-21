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
        q_enable: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        x: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
        y: impl FnOnce(&mut VirtualCells<'_, F>) -> Expression<F>,
    ) -> Self {
        let is_zero_chip = IsZeroChip::configure(meta, q_enable, |meta| x(meta) - y(meta));

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

#[cfg(test)]
mod tests {

    use super::IsEqualChip;
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
        inp_x: Column<Advice>,
        inp_y: Column<Advice>,
        out: Column<Advice>,
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
            let [inp_x, inp_y, out] = [(); 3].map(|_| meta.advice_column());
            [inp_x, inp_y, out].map(|col| meta.enable_equality(col));

            let instance = meta.instance_column();
            meta.enable_equality(instance);

            let selector = meta.selector();

            let is_equal = IsEqualChip::configure(
                meta,
                |meta| meta.query_selector(selector),
                |meta| meta.query_advice(inp_x, Rotation::cur()),
                |meta| meta.query_advice(inp_y, Rotation::cur()),
            );

            meta.create_gate("is_equal", |meta| {
                let out = meta.query_advice(out, Rotation::cur());
                let s = meta.query_selector(selector);
                vec![s * (out - is_equal.expr())]
            });

            MyConfig { is_equal, inp_x, inp_y, out, instance, selector }
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
                    let inp_x =
                        region.assign_advice(|| "load input a", config.inp_x, 0, || self.a)?;
                    let inp_y =
                        region.assign_advice(|| "load input b", config.inp_y, 0, || self.b)?;
                    let out_val = config.is_equal.assign(
                        &mut region,
                        0,
                        inp_x.value().copied(),
                        inp_y.value().copied(),
                    )?;
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
        let a = Fp::from(3);
        let b = Fp::from(2);
        let o = Fp::from(0);
        let p_circuit = MyCircuit { a: Value::known(a), b: Value::known(b) };
        let public_inputs = vec![o];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();

        let a = Fp::from(69);
        let b = Fp::from(69);
        let o = Fp::from(1);
        let p_circuit = MyCircuit { a: Value::known(a), b: Value::known(b) };
        let public_inputs = vec![o];
        let prover = MockProver::run(3, &p_circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
}
