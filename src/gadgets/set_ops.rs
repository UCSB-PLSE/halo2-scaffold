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
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        // x_opt: Option<Column<Advice>>,
        // ys_opt: Option<Column<Advice>>,
    ) -> Self {
        // let x = x_opt.unwrap_or_else(|| meta.advice_column());
        // let ys = ys_opt.unwrap_or_else(|| meta.advice_column());
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
        // offset_opt: Option<usize>,
    ) -> Result<(), Error> {
        region.name_column(|| " x ", self.x);
        region.name_column(|| " ys ", self.ys);

        let n = ys_ac.len();

        let mut ws = vec![];
        // let offset = offset_opt.unwrap_or(0);
        let offset = 0;
        for i in offset..offset + n {
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

#[derive(Clone, Debug)]
pub struct SubsetChip<F: FieldExt, const N: usize> {
    contains: [ContainsChip<F>; N],
    // xs: Column<Advice>,
    // ys: Column<Advice>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const N: usize> SubsetChip<F, N> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        // xs_opt: Option<Column<Advice>>,
        // ys_opt: Option<Column<Advice>>,
    ) -> Self {
        // let xs = xs_opt.unwrap_or_else(|| meta.advice_column());
        // let ys = ys_opt.unwrap_or_else(|| meta.advice_column());
        // let contains = ContainsChip::configure(meta, Some(xs), Some(ys));
        let contains = [(); N].map(|_| ContainsChip::configure(meta));
        SubsetChip { contains, _marker: PhantomData }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        xs_ac: Vec<AssignedCell<F, F>>,
        ys_ac: Vec<AssignedCell<F, F>>,
    ) -> Result<(), Error> {
        assert_eq!(xs_ac.len(), N);
        for (x_ac, contains) in xs_ac.clone().into_iter().zip(self.contains.clone().into_iter()) {
            contains.assign(region, x_ac, ys_ac.clone())?;
        }

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
            let ys = vec![4, 5, 6].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = ContainsTestCircuit { x, ys };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }

    mod test_subset {

        use std::marker::PhantomData;

        use crate::gadgets::set_ops::SubsetChip;
        use halo2_proofs::{
            circuit::{AssignedCell, Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error},
        };

        #[derive(Clone)]
        struct SubsetTestConfig<const N: usize> {
            subset: SubsetChip<Fp, N>,
            #[allow(dead_code)]
            xs_adv: Column<Advice>,
            ys_adv: Column<Advice>,
        }

        #[derive(Default)]
        struct SubsetTestCircuit<const N: usize> {
            xs: Vec<Value<Fp>>,
            ys: Vec<Value<Fp>>,
        }

        impl<const N: usize> Circuit<Fp> for SubsetTestCircuit<N> {
            type Config = SubsetTestConfig<N>;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let subset = SubsetChip::configure(meta);
                let [xs_adv, ys_adv] = [(); 2].map(|_| meta.advice_column());
                meta.enable_equality(xs_adv);
                meta.enable_equality(ys_adv);
                SubsetTestConfig { subset, xs_adv, ys_adv }
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
                        let xs_ac: Vec<AssignedCell<Fp, Fp>> = self
                            .xs
                            .iter()
                            .enumerate()
                            .map(|(i, x)| {
                                let x_ac = region
                                    .assign_advice(|| "xs", config.xs_adv, i, || x.clone())
                                    .unwrap();
                                x_ac
                            })
                            .collect();
                        for (x_ac, contains) in xs_ac
                            .clone()
                            .into_iter()
                            .zip(config.subset.contains.clone().into_iter())
                        {
                            contains.assign(&mut region, x_ac, ys_ac.clone())?;
                        }
                        Ok(())
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let xs = vec![1].into_iter().map(Fp::from).map(Value::known).collect();
            let ys: Vec<Value<Fp>> =
                vec![0, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = SubsetTestCircuit::<1> { xs, ys: ys.clone() };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        fn test_ok2() {
            let xs = vec![2, 0, 2, 0, 2, 1].into_iter().map(Fp::from).map(Value::known).collect();
            let ys: Vec<Value<Fp>> =
                vec![0, 1, 0, 1, 1, 0, 0, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = SubsetTestCircuit::<6> { xs, ys: ys.clone() };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic1() {
            let xs = vec![3].into_iter().map(Fp::from).map(Value::known).collect();
            let ys = vec![2, 0, 1, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = SubsetTestCircuit::<1> { xs, ys };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic2() {
            let xs = vec![0, 1, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let ys: Vec<Value<Fp>> =
                vec![1, 0, 3].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit = SubsetTestCircuit::<4> { xs, ys: ys.clone() };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        #[should_panic]
        fn test_panic3() {
            let xs = vec![1, 2, 1, 3].into_iter().map(Fp::from).map(Value::known).collect();
            let ys: Vec<Value<Fp>> = vec![2, 1, 1, 1, 2, 2, 2, 2, 0]
                .into_iter()
                .map(Fp::from)
                .map(Value::known)
                .collect();
            let p_circuit = SubsetTestCircuit::<4> { xs, ys: ys.clone() };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }
    }
}
