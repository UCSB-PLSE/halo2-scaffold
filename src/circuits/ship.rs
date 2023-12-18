use std::marker::PhantomData;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Selector},
    poly::Rotation,
};

// pub struct IsEqualConfig<F: FieldExt> {
//     _marker: PhantomData<F>,
//     a: Column<Advice>,
//     b: Column<Advice>,
//     eq: Column<Advice>,
//     eq_inv: Column<Advice>,
//     eq_sel: Selector,
//     constant: Column<Fixed>,
// }

#[derive(Clone, Copy)]
// it is standard practice to define everything where numbers are in a generic prime field `F` (`FieldExt` are the traits of a prime field)
pub struct ShipCircuitConfig<F: FieldExt> {
    _marker: PhantomData<F>,
    ship: Column<Advice>,
    coords: Column<Advice>,
    eq: Column<Advice>,
    eq_inv: Column<Advice>,
    count: Column<Advice>,
    eq_sel: Selector,
    rolling_sum_sel: Selector,
    // #[allow(dead_code)]
    constant: Column<Fixed>,
}

impl<F: FieldExt> ShipCircuitConfig<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> Self {
        let [ship, coords, eq, eq_inv, count] = [(); 5].map(|_| meta.advice_column());

        let constant = meta.fixed_column();

        let [eq_sel, rolling_sum_sel] = [(); 2].map(|_| meta.selector());

        // specify the columns that you may want to impose equality constraints on cells for (this may include fixed columns)
        [ship, coords, eq, eq_inv, count].map(|column| meta.enable_equality(column));
        meta.enable_constant(constant);

        meta.create_gate("eq", |meta| {
            let [ship, coords, eq, eq_inv] =
                [ship, coords, eq, eq_inv].map(|column| meta.query_advice(column, Rotation::cur()));
            let eq_sel = meta.query_selector(eq_sel);

            vec![
                eq_sel.clone() * ((coords.clone() - ship.clone()) * eq_inv.clone()),
                eq_sel.clone()
                    * ((coords.clone() - ship.clone() * eq_inv.clone()) + eq
                        - Expression::Constant(F::from(1))),
            ]
        });

        meta.create_gate("rolling_sum", |meta| {
            let [eq, count_curr] =
                [eq, count].map(|column| meta.query_advice(column, Rotation::cur()));

            let [count_next] = [count].map(|column| meta.query_advice(column, Rotation::next()));

            let rolling_sum_sel = meta.query_selector(rolling_sum_sel);

            // count_next = count + (1 - eq)
            vec![
                // count_next = count_curr + eq
                rolling_sum_sel.clone() * (count_curr.clone() + (eq.clone()) - count_next.clone()),
            ]
        });

        ShipCircuitConfig {
            ship,
            coords,
            eq,
            eq_inv,
            count,
            eq_sel,
            rolling_sum_sel,
            constant,
            _marker: PhantomData,
        }
    }

    // Config is essentially synonymous with Chip, so we want to build some functionality into this Chip if we want
}

// we use the config to make a circuit:
#[derive(Clone, Default)]
pub struct ShipCircuit<F: FieldExt> {
    pub length: usize,
    pub ship: u64,
    pub coords: Vec<u64>,
    pub count: u64,
    _marker: PhantomData<F>,
}

impl<F: FieldExt> Circuit<F> for ShipCircuit<F> {
    type Config = ShipCircuitConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ShipCircuitConfig::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "",
            |mut region| {
                // initialize count to 0
                let mut count = self.count;

                let count_init = region.assign_advice(
                    || "count",
                    config.count,
                    0,
                    || Value::known(F::from(count)),
                )?;
                // let zero: halo2_proofs::circuit::AssignedCell<F, F> = region.assign_fixed(
                //     || "zero",
                //     config.constant,
                //     0,
                //     || Value::known(F::from(0)),
                // )?;
                // constrain the initial value of count to be 0
                // region.constrain_equal(count_init.cell(), zero.cell())?;
                region.constrain_constant(count_init.cell(), F::from(0))?;

                for row in 0..self.length {
                    // enable selectors
                    config.eq_sel.enable(&mut region, row)?;
                    config.rolling_sum_sel.enable(&mut region, row)?;

                    // ship coordinate
                    let s = self.ship;

                    // coordinate being compared against
                    let c = self.coords.get(row).unwrap().clone();

                    // assign s to every row in the ship column
                    region.assign_advice(
                        || "ship coordinate",
                        config.ship,
                        row,
                        || Value::known(F::from(s)),
                    )?;

                    // assign c to the current row in the coords column
                    region.assign_advice(
                        || "compared coordinate",
                        config.coords,
                        row,
                        || Value::known(F::from(c)),
                    )?;

                    // difference between ship coord and compared coord
                    let diff = c - s;

                    if s != c {
                        region.assign_advice(
                            || "eq",
                            config.eq,
                            row,
                            || Value::known(F::zero()),
                        )?;
                        region.assign_advice(
                            || "eq_inv",
                            config.eq_inv,
                            row,
                            || Value::known(F::from(diff).invert().unwrap()),
                        )?;
                    } else {
                        count += 1;
                        region.assign_advice(|| "eq", config.eq, row, || Value::known(F::one()))?;
                        // println!("The inverse of {:?} is {:?}", diff, diff.invert().unwrap());
                        region.assign_advice(
                            || "eq_inv",
                            config.eq_inv,
                            row,
                            || Value::known(F::zero()),
                        )?;
                    }
                    region.assign_advice(
                        || "count",
                        config.count,
                        row + 1,
                        || Value::known(F::from(count)),
                    )?;
                }
                Ok(())
            },
        )
    }
}

pub fn generate_circuit<F: FieldExt>(n: u32) -> ShipCircuit<F> {
    let ship = 0;
    let mut coords = Vec::new();
    for _ in 0..n {
        coords.push(0);
    }
    let count = 0;
    let circuit =
        ShipCircuit { length: n as usize, ship: ship, coords, count, _marker: PhantomData };
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

    use super::{generate_circuit, ShipCircuit};

    #[test]
    fn test_ship() {
        let K = 14;
        let n = 10000;
        let circuit = generate_circuit::<Fp>(n);
        let x = SimpleCircuitCost::<Eq, ShipCircuit<Fp>>::measure(K, &circuit.clone());
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
        let prover = MockProver::run(K, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}
