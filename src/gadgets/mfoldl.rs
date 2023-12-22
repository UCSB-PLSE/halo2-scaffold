/*
 * Generic foldl gadget
 */

use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{AssignedCell, Region, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, VirtualCells},
    poly::Rotation,
};

pub trait Op<F, const N: usize> {
    fn expr(acc: Expression<F>, xs: [Expression<F>; N]) -> Expression<F>;
    fn wg(acc: Value<F>, values: [Value<F>; N]) -> Value<F>;
    fn init() -> Value<F>;
    const ANNOTATION: &'static str;
}

#[derive(Clone, Debug, Default)]
pub struct Add {}

#[derive(Clone, Debug, Default)]
pub struct Mul {}

impl<F: FieldExt, const N: usize> Op<F, N> for Add {
    fn expr(acc: Expression<F>, xs: [Expression<F>; N]) -> Expression<F> {
        xs.into_iter().fold(acc, |acc, x| acc + x)
    }

    fn wg(acc: Value<F>, xs: [Value<F>; N]) -> Value<F> {
        xs.into_iter().fold(acc, |acc, x| acc + x)
    }

    fn init() -> Value<F> {
        Value::known(F::zero())
    }

    const ANNOTATION: &'static str = "add";
}

impl<F: FieldExt, const N: usize> Op<F, N> for Mul {
    fn expr(acc: Expression<F>, xs: [Expression<F>; N]) -> Expression<F> {
        xs.into_iter().fold(acc, |acc, x| acc * x)
    }

    fn wg(acc: Value<F>, xs: [Value<F>; N]) -> Value<F> {
        xs.iter().fold(acc, |acc, &x| acc * x)
    }

    fn init() -> Value<F> {
        Value::known(F::one())
    }

    const ANNOTATION: &'static str = "mul";
}

#[derive(Clone, Debug)]
pub struct FoldlChip<F: FieldExt, const N: usize, OP: Op<F, N>> {
    // xss: [Column<Advice>; N],
    pub acc: Column<Advice>,
    s: Selector,
    _marker: PhantomData<F>,
    _marker2: PhantomData<OP>,
}

impl<F: FieldExt, const N: usize, OP: Op<F, N>> FoldlChip<F, N, OP> {
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        xss: impl FnOnce(&mut VirtualCells<'_, F>) -> [Expression<F>; N],
        acc: Option<Column<Advice>>,
    ) -> Self {
        let acc = acc.unwrap_or(meta.advice_column());
        let s = meta.selector();
        meta.create_gate(OP::ANNOTATION, |meta| {
            let acc_curr = meta.query_advice(acc, Rotation::cur());
            let acc_next = meta.query_advice(acc, Rotation::next());
            let s = meta.query_selector(s);
            vec![s * (acc_next - (OP::expr)(acc_curr, xss(meta)))]
        });
        meta.enable_equality(acc);
        FoldlChip { acc, s, _marker: PhantomData, _marker2: PhantomData }
    }

    pub fn assign(
        &self,
        region: &mut Region<'_, F>,
        xss: Vec<[Value<F>; N]>,
    ) -> Result<AssignedCell<F, F>, Error> {
        region.name_column(|| "acc", self.acc);
        // self.xss.into_iter().enumerate().for_each(|(i, xs)| {
        //     region.name_column(|| format!("x{}", i), xs);
        // });

        let mut acc = region.assign_advice(|| "acc/init", self.acc, 0, || OP::init())?;
        xss.into_iter().enumerate().for_each(|(i, xs)| {
            // xs.into_iter().zip(self.xss.iter()).enumerate().for_each(|(j, (x, &c))| {
            //     region.assign_advice(|| format!("x{}", j), c, i, || x).unwrap();
            // });
            // Consume the iterator using for_each
            self.s.enable(region, i).unwrap();
            let acc_val = OP::wg(acc.value().copied(), xs);
            acc = region.assign_advice(|| "acc", self.acc, i + 1, || acc_val).unwrap();
            ()
        });

        Ok(acc)
    }
}

#[cfg(test)]
mod tests {

    mod test_assert_nonzero {

        use std::marker::PhantomData;

        use crate::gadgets::mfoldl::{Add, FoldlChip, Mul, Op};
        use halo2_proofs::{
            circuit::{Layouter, SimpleFloorPlanner, Value},
            dev::MockProver,
            halo2curves::pasta::Fp,
            plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed},
            poly::Rotation,
        };

        #[derive(Clone)]
        struct FoldlTestConfig<OP>
        where
            OP: Op<Fp, 1> + Clone,
        {
            fc: FoldlChip<Fp, 1, OP>,
            #[allow(dead_code)]
            constant: Column<Fixed>,
            xs: Column<Advice>,
        }

        #[derive(Default)]
        struct FoldlTestCircuit<OP>
        where
            OP: Op<Fp, 1>,
        {
            xs: Vec<Value<Fp>>,
            out: Fp,
            _marker: PhantomData<OP>,
        }

        impl<OP> Circuit<Fp> for FoldlTestCircuit<OP>
        where
            OP: Op<Fp, 1> + Clone + Default,
        {
            type Config = FoldlTestConfig<OP>;
            type FloorPlanner = SimpleFloorPlanner;
            // type Params = ();

            fn without_witnesses(&self) -> Self {
                Self::default()
            }

            fn configure(meta: &mut ConstraintSystem<Fp>) -> Self::Config {
                let xs = meta.advice_column();

                let fc =
                    FoldlChip::configure(meta, |m| [m.query_advice(xs, Rotation::cur())], None);

                let constant = meta.fixed_column();
                meta.enable_constant(constant);

                FoldlTestConfig { fc, xs, constant }
            }

            fn synthesize(
                &self,
                config: Self::Config,
                mut layouter: impl Layouter<Fp>,
            ) -> Result<(), Error> {
                layouter.assign_region(
                    || "foldl add",
                    |mut region| {
                        for (i, &x) in self.xs.iter().enumerate() {
                            region.assign_advice(|| format!("x{}", i), config.xs, i, || x)?;
                        }
                        let xss = self.xs.iter().map(|x| [x.clone()]).collect();
                        let out = config.fc.assign(&mut region, xss)?;
                        region.constrain_constant(out.cell(), self.out)
                    },
                )?;
                Ok(())
            }
        }

        #[test]
        fn test_ok1() {
            let xs = vec![0, 1, 2].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit =
                FoldlTestCircuit::<Add> { xs: xs, out: Fp::from(3), _marker: PhantomData };
            let prover = MockProver::run(10, &p_circuit, vec![]).unwrap();
            prover.assert_satisfied();
        }

        #[test]
        fn test_ok2() {
            let xs = vec![1, 2, 3, 4].into_iter().map(Fp::from).map(Value::known).collect();
            let p_circuit =
                FoldlTestCircuit::<Mul> { xs: xs, out: Fp::from(24), _marker: PhantomData };
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
