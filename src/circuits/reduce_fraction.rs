use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value, Chip},
    halo2curves::FieldExt,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector, Expression},
    poly::Rotation,
};

use crate::gadgets::less_than::{LtChip, LtInstruction};
use crate::gadgets::is_zero::IsZeroChip;

#[derive(Clone)]
pub struct ReduceFractionCircuitConfig<F: FieldExt> {
    _marker: PhantomData<F>,
    a: Column<Advice>, // f.num
    b: Column<Advice>, // f.den
    min: Column<Advice>,
    j: Column<Advice>,
    amj: Column<Advice>, // a mod j
    bmj: Column<Advice>, // b mod j
    gcd: Column<Advice>,
    sign: Column<Advice>, // f.sign
    fr_sign: Column<Advice>,
    fr_num: Column<Advice>,
    fr_den: Column<Advice>,
    less_than_ba: LtChip<F, 64>,
    less_than_mj: LtChip<F, 64>,
    is_zero_amj: IsZeroChip<F>,
    is_zero_bmj: IsZeroChip<F>,
    s: Selector,
    #[allow(dead_code)]
    constant: Column<Fixed>,
}

impl<F: FieldExt> ReduceFractionCircuitConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let [a, b, min, 
             j, amj, bmj, 
             gcd, sign, fr_sign, fr_num, fr_den
            ] = [(); 11].map(|_| meta.advice_column());

        let s = meta.selector();

        let less_than_ba_config = LtChip::<F, 64>::configure(
            meta,
            |meta| meta.query_selector(s),
            |meta| meta.query_advice(b, Rotation::cur()),
            |meta| meta.query_advice(a, Rotation::cur()),
        );
        let less_than_ba = LtChip::<F, 64>::construct(less_than_ba_config);

        let less_than_mj_config = LtChip::<F, 64>::configure(
            meta,
            |meta| meta.query_selector(s),
            |meta| meta.query_advice(min, Rotation::cur()),
            |meta| meta.query_advice(j, Rotation::cur()),
        );
        let less_than_mj = LtChip::<F, 64>::construct(less_than_mj_config);

        let is_zero_amj = IsZeroChip::configure(
            meta,
            |meta| meta.query_advice(amj, Rotation::cur()),
        );

        let is_zero_bmj = IsZeroChip::configure(
            meta,
            |meta| meta.query_advice(bmj, Rotation::cur()),
        );

        let constant = meta.fixed_column();

        // enable equality constraints
        [amj, bmj].map(|column| meta.enable_equality(column));

        // enable constant
        meta.enable_constant(constant);

        meta.create_gate("gcd", |meta|{
            let gcd_curr = meta.query_advice(gcd, Rotation::cur());
            let gcd_prev = meta.query_advice(gcd, Rotation::prev());

            let amj_curr = meta.query_advice(amj, Rotation::cur());
            let bmj_curr = meta.query_advice(bmj, Rotation::cur());

            let j_curr = meta.query_advice(j, Rotation::cur());

            let s = meta.query_selector(s);

            // gcd@curr = cond * j + (1-cond) * gcd@prev
            // cond = (j<=min) && (amj == 0) && (bmj == 0)
            let cond = (Expression::Constant(F::from(1))-less_than_mj.config().is_lt(meta, Some(Rotation::cur()))) * is_zero_amj.expr() * is_zero_bmj.expr();
            vec![
                s.clone() * ( cond.clone() * j_curr + (Expression::Constant(F::from(1))-cond.clone()) * gcd_prev ),
            ]
        });

        ReduceFractionCircuitConfig { 
            a, b, min, j, amj, bmj, gcd, sign, fr_sign, fr_num, fr_den,
            less_than_ba, less_than_mj, is_zero_amj, is_zero_bmj, s, constant, _marker: PhantomData
        }
    }
}

#[derive(Clone, Default)]
pub struct ReduceFractionCircuit<F: FieldExt> {
    pub sign: bool,
    pub num: u64,
    pub den: u64,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for ReduceFractionCircuit<F> {
    type Config = ReduceFractionCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ReduceFractionCircuitConfig::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                region.name_column(|| "a", config.a);
                region.name_column(|| "b", config.b);
                region.name_column(|| "min", config.min);
                region.name_column(|| "j", config.j);
                region.name_column(|| "amj", config.amj);
                region.name_column(|| "bmj", config.bmj);
                region.name_column(|| "gcd", config.gcd);
                region.name_column(|| "sign", config.sign);
                region.name_column(|| "fr_sign", config.fr_sign);
                region.name_column(|| "fr_num", config.fr_num);
                region.name_column(|| "fr_den", config.fr_den);

                // pre-assign gcd
                let mut gcd_prev = region.assign_advice(
                    || "gcd", config.gcd, 0,
                    || Value::known(F::from(1))
                )?;

                // for i in 2..100
                // special: row = 0 and row = 99, addressed separately
                for row in 0..100 {
                    // i is the divisor, subtract 1 to get to row
                    // row = 0 or i = 1 is for initialization
                    let i = row + 1;

                    // enable selectors
                    config.s.enable(&mut region, row)?;

                    // a is always equal to f.num
                    let mut a = region.assign_advice(
                        || "a", config.a, row, 
                        || Value::known(F::from(self.num)),
                    )?;

                    // b is always equal to f.den
                    let mut b = region.assign_advice(
                        || "b", config.b, row,
                        || Value::known(F::from(self.den)),
                    )?;

                    // min is always equal to min(a,b)
                    let mut min = region.assign_advice(
                        || "min", config.min, row,
                        || if self.num > self.den { Value::known(F::from(self.den)) } else { Value::known(F::from(self.num)) },
                    )?;
                    
                    // when row = 0, j = 1
                    // when row > 0, j = i as u32
                    let mut j = region.assign_advice(
                        || "j", config.j, row,
                        || if row == 0 { Value::known(F::from(1)) } else { Value::known(F::from(i as u64)) },
                    )?;

                    // when row = 0, amj = 0 (inferred)
                    // when row > 0, amj = a % j
                    let tmp0 = a.value().copied()
                                         .zip(j.value().copied())
                                         .map(|(a, b)| F::from_u128( a.get_lower_128() % b.get_lower_128() ));
                    let mut amj = region.assign_advice(
                        || "amj", config.amj, row,
                        || if row == 0 { Value::known(F::from(0)) } else { tmp0 },
                    )?;

                    // when row = 0, bmj = 0 (inferred)
                    // when row > 0, bmj = b % j
                    let tmp1 = b.value().copied()
                                         .zip(j.value().copied())
                                         .map(|(a, b)| F::from_u128( a.get_lower_128() & b.get_lower_128() ));
                    let mut bmj = region.assign_advice(
                        || "bmj", config.bmj, row,
                        || if row == 0 { Value::known(F::from(0)) } else { tmp1 },
                    )?;

                    let less_than_mj = config.less_than_mj.assign(&mut region, row, min.value().copied(), j.value().copied())?;
                    let is_zero_amj = config.is_zero_amj.assign(&mut region, row, amj.value().copied())?;
                    let is_zero_bmj = config.is_zero_bmj.assign(&mut region, row, bmj.value().copied())?;
                    // let cond = (1-less_than_mj.config.is_lt(meta,None)) * is_zero_amj * is_zero_bmj;
                    let sub_cond = min.value().copied().zip(j.value().copied()).map(|(a, b)| if a.get_lower_128() < b.get_lower_128() {F::one()} else {F::zero()});
                    let cond = (Value::known(F::from(1)) - sub_cond) * is_zero_amj * is_zero_bmj;

                    // when row = 0, gcd = 1, but we skip this in the loop
                    // when row > 0
                    //   if (j<=min) && (a%j==0) && (b%j==0), gcd = j
                    //   else gcd = gcd@prev
                    if row > 0 {
                        let mut gcd = region.assign_advice(
                            || "gcd", config.gcd, row,
                            || cond * j.value().copied() + (Value::known(F::from(1)) - cond) * gcd_prev.value().copied()
                        )?;
                        // store current for use of next
                        gcd_prev = gcd;
                    }

                    // sign is always equal to f.sign
                    let mut sign = region.assign_advice(
                        || "sign", config.sign, row,
                        || Value::known(F::from(self.sign)),
                    )?;

                    // fr_sign is always equal to f.sign
                    let mut fr_sign = region.assign_advice(
                        || "fr_sign", config.fr_sign, row,
                        || Value::known(F::from(self.sign)),
                    )?;

                    // when row = 0..99, fr_num = 0 (inferred)
                    // when row = 99, fr_num = f.num / gcd_prev (outside of gcd's loop)
                    let tmp2 = Value::known(F::from(self.num))
                                         .zip(gcd_prev.value().copied())
                                         .map(|(a,b)| F::from_u128( a.get_lower_128() / b.get_lower_128() ) );
                    let mut fr_num = region.assign_advice(
                        || "fr_num", config.fr_num, row,
                        // || if row < 99 { Value::known(F::from(0)) } else { Value::known(F::from(self.num)) / gcd_prev.value().copied() },
                        || if row < 99 { Value::known(F::from(0)) } 
                               else { tmp2 },
                    )?;
                    
                    // when row = 0..99, fr_den = 0 (inferred)
                    // when row = 99, fr_den = f.den / gcd_prev (outside of gcd's loop)
                    let tmp3 = Value::known(F::from(self.den))
                                              .zip(gcd_prev.value().copied())
                                              .map(|(a, b)| F::from_u128( a.get_lower_128() / b.get_lower_128() ));
                    let mut fr_den = region.assign_advice(
                        || "fr_den", config.fr_den, row,
                        // || if row < 99 { Value::known(F::from(0)) } else { Value::known(F::from(self.den)) / gcd_prev.value().copied() },
                        || if row < 99 { Value::known(F::from(0)) } else { tmp3 },
                    )?;

                }
                Ok(())
            },
        )
    }
}

pub fn generate_circuit<F: FieldExt>(sign: bool, num: u64, den: u64) -> ReduceFractionCircuit<F> {
    let circuit = ReduceFractionCircuit { sign: sign, num: num, den: den, _marker: PhantomData };
    circuit
}

#[cfg(test)]
mod test {
    use halo2_proofs::{
        // arithmetic::Field,
        // circuit::Value,
        dev::{MockProver, SimpleCircuitCost},
        halo2curves::pasta::{Eq, Fp},
    };
    // use rand::rngs::OsRng;

    use super::{generate_circuit, ReduceFractionCircuit};

    #[test]
    fn test_reduce_fraction() {
        let k = 14;
        let sign = false;
        let num = 96;
        let den = 16;
        let circuit = generate_circuit::<Fp>(sign, num, den);
        let x = SimpleCircuitCost::<Eq, ReduceFractionCircuit<Fp>>::measure(k, &circuit.clone());
        //     /// Power-of-2 bound on the number of rows in the circuit.
        // pub k: u32,
        // /// Maximum degree of the circuit.
        // pub max_deg: usize,
        // /// Number of advice columns.
        // pub advice_columns: usize,
        // /// Number of direct queries for instance columns.
        // pub instance_queries: usize,
        // /// Number of direct queries for advice columns.
        // pub advice_queries: usize,
        // /// Number of direct queries for fixed columns.
        // pub fixed_queries: usize,
        // /// Number of lookup arguments.
        // pub lookups: usize,
        // /// Number of columns in the global permutation.
        // pub permutation_cols: usize,
        // /// Number of distinct sets of points in the multiopening argument.
        // pub point_sets: usize,
        // /// Maximum rows used over all columns
        // pub max_rows: usize,
        // /// Maximum rows used over all advice columns
        // pub max_advice_rows: usize,
        // /// Maximum rows used over all fixed columns
        // pub max_fixed_rows: usize,
        // /// Number of fixed columns
        // pub num_fixed_columns: usize,
        // /// Number of advice columns
        // pub num_advice_columns: usize,
        // /// Number of instance columns
        // pub num_instance_columns: usize,
        // /// Total number of columns
        // pub num_total_columns: usize,
        // println!("k: {:?}", x.k);
        // println!("max_deg: {:?}", x.max_deg);
        // println!("advice_columns: {:?}", x.advice_columns);
        // println!("instance_queries: {:?}", x.instance_queries);
        // println!("advice_queries: {:?}", x.advice_queries);
        // println!("fixed_queries: {:?}", x.fixed_queries);
        // println!("lookups: {:?}", x.lookups);
        // println!("permutation_cols: {:?}", x.permutation_cols);
        // println!("point_sets: {:?}", x.point_sets);
        // println!("max_rows: {:?}", x.max_rows);
        println!("max_advice_rows: {:?}", x.max_advice_rows);
        println!("max_fixed_rows: {:?}", x.max_fixed_rows);
        println!("num_fixed_columns: {:?}", x.num_fixed_columns);
        println!("num_advice_columns: {:?}", x.num_advice_columns);
        // println!("num_instance_columns: {:?}", x.num_instance_columns);
        // println!("num_total_columns: {:?}", x.num_total_columns);
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}
