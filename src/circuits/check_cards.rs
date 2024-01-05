use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

use crate::gadgets::is_zero::AssertNonZeroChip;

#[derive(Clone)]
pub struct CheckCardsConfig<F: FieldExt> {
    _marker: PhantomData<F>,
    x: Column<Advice>,
    y: Column<Advice>,
    z: Column<Advice>,
    s_contains: Selector,
    s_prod: Selector,
    s_add: Selector,
    s_z: Selector,
    s_nz: Selector,
    constant: Column<Fixed>,
}

impl<F: FieldExt> CheckCardsConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let x = meta.advice_column();
        let y = meta.advice_column();
        let z = meta.advice_column();
        let s_contains = meta.selector();
        let s_prod = meta.selector();
        let s_add = meta.selector();
        let s_z = meta.selector();
        let s_nz = meta.selector();
        let constant = meta.fixed_column();

        let [s_p, s_nz] = [(); 2].map(|_| meta.selector());

        // specify the columns that you may want to impose equality constraints on cells for (this may include fixed columns)
        meta.enable_equality(x);
        meta.enable_equality(y);
        meta.enable_equality(z);
        meta.enable_constant(constant);

        meta.create_gate("contains", |meta| {
            let x = meta.query_advice(x, Rotation::cur());
            let y = meta.query_advice(y, Rotation::cur());
            let z_curr = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());
            let s_contains = meta.query_selector(s_contains);
            vec![s_contains * (z_next - z_curr * (y - x))]
        });

        meta.create_gate("z", |meta| {
            let z = meta.query_advice(z, Rotation::cur());
            let s_z = meta.query_selector(s_z);
            vec![s_z * z]
        });

        meta.create_gate("prod", |meta| {
            let x = meta.query_advice(x, Rotation::cur());
            let z_curr = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());
            let s_prod = meta.query_selector(s_prod);
            vec![s_prod * (z_next - z_curr * x)]
        });

        meta.create_gate("add", |meta| {
            let x = meta.query_advice(x, Rotation::cur());
            let z_curr = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());
            let s_add = meta.query_selector(s_add);
            vec![s_add * (z_next - (z_curr + x))]
        });

        meta.create_gate("nz", |meta| {
            let y = meta.query_advice(y, Rotation::cur());
            let z = meta.query_advice(z, Rotation::cur());
            let s_nz = meta.query_selector(s_nz);
            vec![s_nz * (y * z - Expression::Constant(F::one()))]
        });

        CheckCardsConfig {
            x,
            y,
            z,
            s_contains,
            s_prod,
            s_add,
            s_z,
            s_nz,
            constant,
            _marker: PhantomData,
        }
    }

    // Config is essentially synonymous with Chip, so we want to build some functionality into this Chip if we want
}

// we use the config to make a circuit:
#[derive(Clone, Default)]
pub struct CheckCardsCircuit<F: FieldExt> {
    a: Vec<u64>,
    k: Vec<u64>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for CheckCardsCircuit<F> {
    type Config = CheckCardsConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        CheckCardsConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // let mut p = None;

        layouter.assign_region(
            || "",
            |mut region| {
                let mut offset = 0;
                region.name_column(|| " x ", config.x);
                region.name_column(|| " y ", config.y);
                region.name_column(|| " z ", config.z);

                // copy k into y
                println!("copy k into y");
                let mut ks_ac = vec![];
                for (i, k) in self.k.iter().enumerate() {
                    let k_val = Value::known(F::from(*k));
                    let k_assigned =
                        region.assign_advice(|| "k", config.y, offset + i, || k_val)?;
                    ks_ac.push(k_assigned);
                }
                offset += self.k.len();

                // check product of as is non-zero
                println!("check product of as is non-zero");
                let mut as_ac = vec![];
                let mut p =
                    region.assign_advice(|| "p", config.z, offset, || Value::known(F::one()))?;

                for (i, a) in self.a.iter().enumerate() {
                    config.s_prod.enable(&mut region, offset + i)?;
                    let a_val = Value::known(F::from(*a));
                    let a_assigned =
                        region.assign_advice(|| "a", config.x, offset + i, || a_val)?;
                    let p_val = p.value().copied().zip(a_val).map(|(p, a)| p * a);
                    p = region.assign_advice(|| "p", config.z, offset + i + 1, || p_val)?;
                    // a_assigned.value().
                    as_ac.push(a_assigned);
                    p_val.map(|p_val| {
                        println!("[{}] a: {}, p: {}", i + offset, a, p_val.get_lower_32());
                    });
                }
                offset += self.a.len();

                // check product is non-zero
                println!("check product is non-zero");
                config.s_nz.enable(&mut region, offset)?;
                let inv_val = p.value().copied().map(|p| p.invert().unwrap());
                inv_val.map(|inv_val| println!("inv_val: {}", inv_val.get_lower_32()));
                region.assign_advice(|| "p_inv", config.y, offset, || inv_val)?;
                offset += 1;

                // for each k, compute the product of (k - a) for each a into ps_ac
                println!("for each k, compute the product of k - a for each a");
                let mut ps_ac = vec![];
                for (i, k) in ks_ac.iter().enumerate() {
                    let mut p = region.assign_advice(
                        || "p",
                        config.z,
                        offset,
                        || Value::known(F::one()),
                    )?;
                    for (j, a) in as_ac.iter().enumerate() {
                        k.value().copied().zip(a.value().copied()).zip(p.value().copied()).map(
                            |((k, a), p)| {
                                println!(
                                    "[{}: ({},{})] k: {}, a: {}, p: {}",
                                    offset,
                                    i,
                                    j,
                                    k.get_lower_32(),
                                    a.get_lower_32(),
                                    p.get_lower_32()
                                );
                            },
                        );
                        config.s_contains.enable(&mut region, offset)?;
                        // println!("[{}] enable contains", offset);
                        a.copy_advice(|| "a", &mut region, config.x, offset)?;
                        k.copy_advice(|| "k", &mut region, config.y, offset)?;
                        offset += 1;
                        let p_val = k
                            .value()
                            .copied()
                            .zip(a.value().copied())
                            .zip(p.value().copied())
                            .map(|((k, a), p)| p * (k - a));
                        p = region.assign_advice(|| "prod", config.z, offset, || p_val)?;
                    }
                    ps_ac.push(p);
                    offset += 1;
                }

                // check sum of products is zero
                println!("check sum of products is zero");
                let mut s =
                    region.assign_advice(|| "s", config.z, offset, || Value::known(F::zero()))?;
                for (i, p) in ps_ac.iter().enumerate() {
                    s.value().copied().zip(p.value().copied()).map(|(s, p)| {
                        println!(
                            "[{}] s: {}, p: {}",
                            offset + i,
                            s.get_lower_32(),
                            p.get_lower_32()
                        );
                    });
                    config.s_add.enable(&mut region, offset + i)?;
                    p.copy_advice(|| "p", &mut region, config.x, offset + i)?;
                    s = region.assign_advice(
                        || "s",
                        config.z,
                        offset + i + 1,
                        || s.value().copied().zip(p.value().copied()).map(|(s, p)| s + p),
                    )?;
                }
                offset += ps_ac.len();

                config.s_z.enable(&mut region, offset)?;
                Ok(())
            },
        )?;
        // layouter.assign_region(|| "product != 0", |mut region|
        Ok(())
    }
}

pub fn generate_circuit<F: FieldExt>(l: u64, ub: u64) -> CheckCardsCircuit<F> {
    // let mut a = vec![];
    // // for _ in 0..ub {
    // for i in 0..l {
    //     let n = i % ub + 1;
    //     a.push(n);
    // }
    // println!("a: {:?}", a);
    // let circuit = CheckCardsCircuit { a, _marker: PhantomData };
    let circuit = CheckCardsCircuit { a: vec![1, 2, 3], k: vec![1, 2, 4], _marker: PhantomData };
    circuit
}

#[cfg(test)]
mod test {
    use halo2_proofs::{
        // arithmetic::Field,
        // circuit::Value,
        dev::MockProver,
        halo2curves::pasta::Fp,
    };
    // use rand::rngs::OsRng;

    use super::generate_circuit;

    #[test]
    fn test() {
        let k = 10;
        let n = 3;
        let ub = 2;
        let circuit = generate_circuit::<Fp>(n, ub);
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}
