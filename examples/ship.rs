//! Example of running the actual Halo2 prover and verifier on the Standard PLONK circuit.
//!
//! Note: Do not read this on first pass of this repository.
use ark_std::{end_timer, start_timer};
use clap::Parser;
use halo2_proofs::{
    arithmetic::Field,
    circuit::Value,
    dev::SimpleCircuitCost,
    halo2curves::bn256::{Bn256, Fr, G1Affine},
    plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, Circuit},
    poly::{
        commitment::ParamsProver,
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverSHPLONK, VerifierSHPLONK},
            strategy::SingleStrategy,
        },
    },
    transcript::{
        Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
    },
};
use halo2_scaffold::circuits::ship::{generate_circuit, ShipCircuit};
use rand::rngs::OsRng;

#[derive(Parser)]
#[command(about = "I am a program and I work, just pass `-h`", long_about = None)]
struct Args {
    #[arg(short, help = "2^n number of iterations")]
    n: u32,
    #[arg(short, help = "k number of rows")]
    k: u32,
}

fn run(num_iter: u32, k: u32) {
    use halo2_proofs::halo2curves::pasta::{Eq, Fp};
    let mcircuit: ShipCircuit<Fp> = generate_circuit(num_iter);
    let x = SimpleCircuitCost::<Eq, ShipCircuit<Fp>>::measure(k, &mcircuit);
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
    println!("advice: {:?}", x.max_advice_rows * x.advice_columns);
    println!("fixed: {:?}", x.max_fixed_rows * x.num_fixed_columns);

    let circuit = generate_circuit(num_iter);

    let kg_time = start_timer!(|| "Generating keys");
    // we generate a universal trusted setup of our own for testing
    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    let vk = keygen_vk(&params, &circuit).expect("vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("pk should not fail");
    end_timer!(kg_time);

    let pf_time = start_timer!(|| "Creating proof");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
    .expect("prover should not fail");
    let proof = transcript.finalize();
    end_timer!(pf_time);

    // verify the proof to make sure everything is ok
    let verifier_params = params.verifier_params();
    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierSHPLONK<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(verifier_params, pk.get_vk(), strategy, &[&[]], &mut transcript)
    .is_ok());
}

fn main() {
    let args = Args::parse();

    let num_iter = args.n;
    let k = args.k;

    println!("Number of rows: 2^{} = {}", k, 2_i32.pow(k));

    run(num_iter, k);
}
