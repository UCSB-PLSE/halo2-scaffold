/* Gadgets for set operations
 */

use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression},
    poly::Rotation,
};

use super::{
    is_zero::AssertZeroChip,
    mfoldl::{FoldlChip, Op},
};

#[derive(Clone, Debug)]
struct CG {}
impl<F: FieldExt> Op<F, 2> for CG {
    fn expr(acc: Expression<F>, xs: [Expression<F>; 2]) -> Expression<F> {
        let [x, y] = xs;
        acc * (x - y)
    }

    fn wg(acc: Value<F>, xs: [Value<F>; 2]) -> Value<F> {
        let [x, y] = xs;
        acc * (x - y)
    }

    fn init() -> Value<F> {
        Value::known(F::one())
    }

    const ANNOTATION: &'static str = "cg";
}

#[derive(Clone, Debug)]
pub struct ContainsChip<F: FieldExt> {
    x: Column<Advice>,
    ys: Column<Advice>,
    cg: FoldlChip<F, 2, CG>,
    assert_zero: AssertZeroChip<F>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> ContainsChip<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let x = meta.advice_column();
        let ys = meta.advice_column();
        let acc = meta.advice_column();
        meta.enable_equality(x);
        meta.enable_equality(ys);
        meta.enable_equality(acc);
        let cg = FoldlChip::<F, 2, CG>::configure(
            meta,
            |m| [x, ys].map(|c| m.query_advice(c, Rotation::cur())),
            Some(acc),
        );
        let assert_zero = AssertZeroChip::configure(meta, |m| m.query_advice(acc, Rotation::cur()));
        ContainsChip { x, ys, cg, assert_zero, _marker: PhantomData }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        x_ac: AssignedCell<F, F>,
        ys_ac: Vec<AssignedCell<F, F>>,
    ) -> Result<(), Error> {
        region.name_column(|| " x ", self.x);
        region.name_column(|| " ys ", self.ys);

        let n = ys_ac.len();

        let mut ws = vec![];
        for i in 0..n {
            let x = x_ac.copy_advice(|| "x", region, self.x, i)?;
            let y = ys_ac[i].copy_advice(|| "ys", region, self.ys, i)?;
            let x_val = x.value().copied();
            let y_val = y.value().copied();
            ws.push([x_val, y_val]);
        }
        self.cg.assign(region, ws)?;
        self.assert_zero.assign(region, n)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    mod test_contains {

        use crate::gadgets::set_ops::ContainsChip;
        use halo2_proofs::{
            circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
        };

        #[derive(Clone)]
        struct ContainsTestConfig {
            contains: ContainsChip<Fp>,
            #[allow(dead_code)]
            x_adv: Column<Advice>,
            ys_adv: Column<Advice>,
        }

        #[derive(Default)]
        struct ContainsTestCircuit {
            x: Value<Fp>,
            ys: Vec<Value<Fp>>,
        }

        impl Circuit<Fp> for ContainsTestCircuit {
            type Config = ContainsTestConfig;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let contains = ContainsChip::configure(meta);

                let [x_adv, ys_adv] = [(); 2].map(|_| meta.advice_column());
                meta.enable_equality(x_adv);
                meta.enable_equality(ys_adv);

                ContainsTestConfig { contains, x_adv, ys_adv }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                // copy from instance to advice
                layouter.assign_region(
                    || "foldl add",
                    |mut region| {
                        // copy from instance to advice
                        let ys_ac: Vec<AssignedCell<Fp, Fp>> = self
                            .ys
                            .iter()
                            .enumerate()
                            .map(|(i, y)| {
                                let y_ac = region
                                    .assign_advice(|| "ys", config.ys_adv, i, || y.clone())
                                    .unwrap();
                                y_ac
                            })
                            .collect();
                        let x_ac = region.assign_advice(|| "x", config.x_adv, 0, || self.x)?;
                        config.contains.assign(&mut region, x_ac, ys_ac)
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let ys: Vec<Value<Fp>> =
                vec![0, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            for &x in ys.iter() {
                let p_circuit = ContainsTestCircuit { x, ys: ys.clone() };
                let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
                prover.assert_satisfied();
            }
        }

        #[test]
        #[should_panic]
        fn test_panic1() {
            let x = Value::known(Fp::from(3));
            let ys = vec![0, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = ContainsTestCircuit { x, ys };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
