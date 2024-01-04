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

use halo2_proofs::arithmetic::FieldExt;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::halo2curves::group::ff::FieldBits;
use halo2_proofs::{
    circuit::{AssignedCell, Chip, Layouter, Region, Value},
    plonk,
    plonk::{Advice, Column, ConstraintSystem, Constraints, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

#[derive(Clone, Debug)]
pub struct NativeRangeCheckConfig<
    const WINDOW_SIZE: usize,
    const NUM_BITS: usize,
    const NUM_WINDOWS: usize,
> {
    pub z: Column<Advice>,
    pub s_rc: Selector,
    pub s_short: Selector,
    pub k_values_table: TableColumn,
}

#[derive(Clone, Debug)]
pub struct NativeRangeCheckChip<
    F,
    const WINDOW_SIZE: usize,
    const NUM_BITS: usize,
    const NUM_WINDOWS: usize,
> {
    config: NativeRangeCheckConfig<WINDOW_SIZE, NUM_BITS, NUM_WINDOWS>,
    _marker: PhantomData<F>,
}

impl<F: FieldExt, const WINDOW_SIZE: usize, const NUM_BITS: usize, const NUM_WINDOWS: usize> Chip<F>
    for NativeRangeCheckChip<F, WINDOW_SIZE, NUM_BITS, NUM_WINDOWS>
{
    type Config = NativeRangeCheckConfig<WINDOW_SIZE, NUM_BITS, NUM_WINDOWS>;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: FieldExt, const WINDOW_SIZE: usize, const NUM_BITS: usize, const NUM_WINDOWS: usize>
    NativeRangeCheckChip<F, WINDOW_SIZE, NUM_BITS, NUM_WINDOWS>
{
    pub fn construct(config: NativeRangeCheckConfig<WINDOW_SIZE, NUM_BITS, NUM_WINDOWS>) -> Self {
        Self { config, _marker: Default::default() }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        z: Column<Advice>,
        k_values_table: TableColumn,
    ) -> NativeRangeCheckConfig<WINDOW_SIZE, NUM_BITS, NUM_WINDOWS> {
        // Enable permutation on z column
        meta.enable_equality(z);

        let s_rc = meta.complex_selector();
        let s_short = meta.complex_selector();

        // Running sum decomposition
        meta.lookup("running sum decomposition", |meta| {
            let s_rc = meta.query_selector(s_rc);
            let z_curr = meta.query_advice(z, Rotation::cur());
            let z_next = meta.query_advice(z, Rotation::next());

            //    z_next = (z_curr - k_i) / 2^K
            // => k_i = z_curr - (z_next * 2^K)
            vec![(s_rc * (z_curr - z_next * F::from(1 << WINDOW_SIZE)), k_values_table)]
        });

        // Checks that are enabled if the last chunk is an `s`-bit value
        // where `s < WINDOW_SIZE`:
        //
        //  |s_rc | s_short |                z                |
        //  ---------------------------------------------------
        //  |  1  |    0    |            last_chunk           |
        //  |  0  |    1    |                0                |
        //  |  0  |    0    | last_chunk << (WINDOW_SIZE - s) |

        // Check that `shifted_last_chunk` is `WINDOW_SIZE` bits,
        // where shifted_last_chunk = last_chunk << (WINDOW_SIZE - s)
        //                          = last_chunk * 2^(WINDOW_SIZE - s)
        meta.lookup("last_chunk s bits", |meta| {
            let s_short = meta.query_selector(s_short);
            let shifted_last_chunk = meta.query_advice(z, Rotation::next());
            vec![(s_short * shifted_last_chunk, k_values_table)]
        });

        // Check that `shifted_last_chunk = last_chunk << (WINDOW_SIZE - s)`
        meta.create_gate("Short lookup bitshift", |meta| {
            let two_pow_window_size = F::from(1 << WINDOW_SIZE);
            let s_short = meta.query_selector(s_short);
            let last_chunk = meta.query_advice(z, Rotation::prev());
            // Rotation::cur() is copy-constrained to be zero elsewhere in this gadget.
            let shifted_last_chunk = meta.query_advice(z, Rotation::next());
            // inv_two_pow_s = 1 >> s = 2^{-s}
            let inv_two_pow_s = {
                let s = NUM_BITS % WINDOW_SIZE;
                F::from(1 << s).invert().unwrap()
            };

            // shifted_last_chunk = last_chunk << (WINDOW_SIZE - s)
            //                    = last_chunk * 2^WINDOW_SIZE * 2^{-s}
            Constraints::with_selector(
                s_short,
                Some(last_chunk * two_pow_window_size * inv_two_pow_s - shifted_last_chunk),
            )
        });

        NativeRangeCheckConfig { z, s_rc, s_short, k_values_table }
    }

    /// `k_values_table` should be reused across different chips
    /// which is why we don't limit it to a specific instance.
    pub fn load_k_table(
        layouter: &mut impl Layouter<F>,
        k_values_table: TableColumn,
    ) -> Result<(), plonk::Error> {
        layouter.assign_table(
            || format!("{} window table", WINDOW_SIZE),
            |mut table| {
                for index in 0..(1 << WINDOW_SIZE) {
                    table.assign_cell(
                        || format!("{} window assign", WINDOW_SIZE),
                        k_values_table,
                        index,
                        || Value::known(F::from(index as u64)),
                    )?;
                }
                Ok(())
            },
        )
    }

    fn decompose_value(value: &F) -> Vec<[bool; WINDOW_SIZE]> {
        // TODO this is BN256 specific
        let repr: [u8; 32] = value.to_repr().as_ref().try_into().unwrap();
        let bits: Vec<_> =
            FieldBits::new(repr).into_iter().take(WINDOW_SIZE * NUM_WINDOWS).collect();

        bits.chunks_exact(WINDOW_SIZE)
            .map(|x| {
                let mut chunks = [false; WINDOW_SIZE];
                chunks.copy_from_slice(x);
                chunks
            })
            .collect()
    }

    pub fn decompose(
        &self,
        region: &mut Region<'_, F>,
        z_0: AssignedCell<F, F>,
        offset: usize,
    ) -> Result<(), plonk::Error> {
        assert!(WINDOW_SIZE * NUM_WINDOWS < NUM_BITS + WINDOW_SIZE);

        // The number of bits in the last chunk.
        let last_chunk_length = NUM_BITS - (WINDOW_SIZE * (NUM_WINDOWS - 1));
        assert!(last_chunk_length > 0);

        // Enable selectors for running sum decomposition
        for index in 0..NUM_WINDOWS {
            self.config.s_rc.enable(region, index + offset)?;
        }

        let mut z_values: Vec<AssignedCell<F, F>> = vec![z_0.clone()];
        let mut z = z_0;
        let decomposed_chunks = z.value().map(Self::decompose_value).transpose_vec(NUM_WINDOWS);

        let two_pow_k = F::from(1 << WINDOW_SIZE as u64);
        let two_pow_k_inverse = Value::known(two_pow_k.invert().unwrap());

        for (i, chunk) in decomposed_chunks.iter().enumerate() {
            let z_next = {
                let z_curr = z.value().copied();
                let chunk_value =
                    chunk.map(|c| F::from(c.iter().rev().fold(0, |acc, c| (acc << 1) + *c as u64)));
                // z_next = (z_curr - k_i) / 2^K
                let z_next = (z_curr - chunk_value) * two_pow_k_inverse;
                region.assign_advice(
                    || format!("z_{}", i + offset + 1),
                    self.config.z,
                    i + offset + 1,
                    || z_next,
                )?
            };
            z_values.push(z_next.clone());
            z = z_next.clone();
        }

        assert!(z_values.len() == NUM_WINDOWS + 1);

        // Constrain the remaining bits to be zero
        region.constrain_constant(z_values.last().unwrap().cell(), F::zero())?;

        // If the last chunk is `s` bits where `s < WINDOW_SIZE`,
        // perform short range check
        //
        //  |s_rc | s_short |                z                |
        //  ---------------------------------------------------
        //  |  1  |    0    |            last_chunk           |
        //  |  0  |    1    |                0                |
        //  |  0  |    0    | last_chunk << (WINDOW_SIZE - s) |
        //  |  0  |    0    |             1 >> s              |

        if last_chunk_length < WINDOW_SIZE {
            let s_short_offset = NUM_WINDOWS + offset;
            self.config.s_short.enable(region, s_short_offset)?;

            // 1 >> s = 2^{-s}
            let inv_two_pow_s = F::from(1 << last_chunk_length).invert().unwrap();
            region.assign_advice_from_constant(
                || "inv_two_pow_s",
                self.config.z,
                s_short_offset + 2,
                inv_two_pow_s,
            )?;

            // shifted_last_chunk = last_chunk * 2^{WINDOW_SIZE-s}
            //                    = last_chunk * 2^WINDOW_SIZE * inv_two_pow_s
            let last_chunk = {
                let chunk = decomposed_chunks.last().unwrap();
                chunk.map(|c| F::from(c.iter().rev().fold(0, |acc, c| (acc << 1) + *c as u64)))
            };
            let shifted_last_chunk =
                last_chunk * Value::known(two_pow_k) * Value::known(inv_two_pow_s);
            region.assign_advice(
                || "shifted_last_chunk",
                self.config.z,
                s_short_offset + 1,
                || shifted_last_chunk,
            )?;
        }

        Ok(())
    }

    pub fn witness_range_check(
        &self,
        mut layouter: impl Layouter<F>,
        value: Value<F>,
    ) -> Result<(), plonk::Error> {
        layouter.assign_region(
            || format!("witness {}-bit native range check", NUM_BITS),
            |mut region: Region<'_, F>| {
                let z_0 = region.assign_advice(|| "z_0", self.config.z, 0, || value)?;
                self.decompose(&mut region, z_0, 0)?;
                Ok(())
            },
        )
    }

    pub fn copy_range_check(
        &self,
        mut layouter: impl Layouter<F>,
        value: AssignedCell<F, F>,
    ) -> Result<(), plonk::Error> {
        layouter.assign_region(
            || format!("copy {}-bit native range check", NUM_BITS),
            |mut region: Region<'_, F>| {
                let z_0 = value.copy_advice(|| "z_0", &mut region, self.config.z, 0)?;
                self.decompose(&mut region, z_0, 0)?;
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::arithmetic::Field;
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::halo2curves::group::ff::PrimeField;
    use halo2_proofs::plonk::Assigned;
    use halo2_proofs::{circuit::floor_planner, dev::MockProver, plonk::Circuit};

    pub fn assign_free_advice<F: Field, V: Copy>(
        mut layouter: impl Layouter<F>,
        column: Column<Advice>,
        value: Value<V>,
    ) -> Result<AssignedCell<V, F>, plonk::Error>
    where
        for<'v> Assigned<F>: From<&'v V>,
    {
        layouter.assign_region(
            || "load private",
            |mut region| region.assign_advice(|| "load private", column, 0, || value),
        )
    }

    macro_rules! test_circuit {
        ($k: expr, $window_size:expr, $num_bits: expr, $num_windows:expr, $valid_values:expr, $invalid_values:expr) => {
            #[derive(Default)]
            struct RangeCheckCircuit<F> {
                a: Value<F>,
            }

            impl<F: FieldExt> Circuit<F> for RangeCheckCircuit<F> {
                type Config =
                    (NativeRangeCheckConfig<$window_size, $num_bits, $num_windows>, Column<Advice>);
                type FloorPlanner = floor_planner::V1;

                fn without_witnesses(&self) -> Self {
                    Self::default()
                }

                fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
                    let w = meta.advice_column();
                    meta.enable_equality(w);
                    let z = meta.advice_column();
                    let table_column = meta.lookup_table_column();

                    let constants = meta.fixed_column();
                    meta.enable_constant(constants);
                    (
                        NativeRangeCheckChip::<F, $window_size, $num_bits, $num_windows>::configure(
                            meta,
                            z,
                            table_column,
                        ),
                        w,
                    )
                }

                fn synthesize(
                    &self,
                    config: Self::Config,
                    mut layouter: impl Layouter<F>,
                ) -> Result<(), plonk::Error> {
                    let rangecheck_chip = NativeRangeCheckChip::<
                        F,
                        $window_size,
                        $num_bits,
                        $num_windows,
                    >::construct(config.0.clone());
                    NativeRangeCheckChip::<F, $window_size, $num_bits, $num_windows>::load_k_table(
                        &mut layouter,
                        config.0.k_values_table,
                    )?;

                    let a = assign_free_advice(layouter.namespace(|| "load a"), config.1, self.a)?;
                    rangecheck_chip
                        .copy_range_check(layouter.namespace(|| "copy a and range check"), a)?;

                    rangecheck_chip.witness_range_check(
                        layouter.namespace(|| "witness a and range check"),
                        self.a,
                    )?;

                    Ok(())
                }
            }

            let circuit = RangeCheckCircuit { a: Value::known(Fr::one()) };

            for i in $valid_values {
                println!("{:?}-bit (valid) range check for {:?}", $num_bits, i);
                let circuit = RangeCheckCircuit { a: Value::known(i) };
                let prover = MockProver::run($k, &circuit, vec![]).unwrap();
                prover.assert_satisfied();
                println!("Constraints satisfied");
            }

            for i in $invalid_values {
                println!("{:?}-bit (invalid) range check for {:?}", $num_bits, i);
                let circuit = RangeCheckCircuit { a: Value::known(i) };
                let prover = MockProver::run($k, &circuit, vec![]).unwrap();
                assert!(prover.verify().is_err());
            }
        };
    }

    // cargo test --release --all-features --lib native_range_check -- --nocapture
    #[test]
    fn native_range_check_2() {
        let k = 6;
        const WINDOW_SIZE: usize = 5;
        const NUM_BITS: usize = 2;
        const NUM_WINDOWS: usize = 1;

        // [0, 1, 2, 3]
        let valid_values: Vec<_> = (0..(1 << NUM_BITS)).map(Fr::from).collect();
        // [4, 5, 6, ..., 32]
        let invalid_values: Vec<_> = ((1 << NUM_BITS)..=(1 << WINDOW_SIZE)).map(Fr::from).collect();
        test_circuit!(k, WINDOW_SIZE, NUM_BITS, NUM_WINDOWS, valid_values, invalid_values);
    }

    #[test]
    fn native_range_check_64() {
        let k = 6;
        const WINDOW_SIZE: usize = 3;
        const NUM_BITS: usize = 64;
        const NUM_WINDOWS: usize = 22;

        let valid_values =
            vec![Fr::zero(), Fr::one(), Fr::from(u64::MAX), Fr::from(rand::random::<u64>())];

        let invalid_values = vec![
            -Fr::one(),
            Fr::from_u128(u64::MAX as u128 + 1),
            -Fr::from_u128(u64::MAX as u128 + 1),
            // The following two are valid
            // 2 = -28948022309329048855892746252171976963363056481941560715954676764349967630335
            //-F::from_str_vartime(
            //    "28948022309329048855892746252171976963363056481941560715954676764349967630335",
            //)
            //.unwrap(),
            // 1 = -28948022309329048855892746252171976963363056481941560715954676764349967630336
            //-F::from_str_vartime(
            //    "28948022309329048855892746252171976963363056481941560715954676764349967630336",
            //)
            //.unwrap(),
        ];
        test_circuit!(k, WINDOW_SIZE, NUM_BITS, NUM_WINDOWS, valid_values, invalid_values);
    }

    #[test]
    fn native_range_check_128() {
        let k = 7;
        const WINDOW_SIZE: usize = 3;
        const NUM_BITS: usize = 128;
        const NUM_WINDOWS: usize = 43;

        let valid_values = vec![
            Fr::zero(),
            Fr::one(),
            Fr::from_u128(u128::MAX),
            Fr::from_u128(rand::random::<u128>()),
        ];

        let invalid_values = vec![
            -Fr::one(),
            Fr::from_u128(u128::MAX) + Fr::one(),
            -Fr::from_u128(u128::MAX) + Fr::one(),
            -Fr::from_u128(u128::MAX),
        ];
        test_circuit!(k, WINDOW_SIZE, NUM_BITS, NUM_WINDOWS, valid_values, invalid_values);
    }
}
