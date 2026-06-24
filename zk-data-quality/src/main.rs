//! main.rs — folding driver.
//!
//! The step-circuit gadgets in step_circuit.rs / gadgets.rs are the load-bearing
//! part. This driver folds one transport order per IVC step with Nova
//! (C1 = BN254, C2 = Grumpkin). The FCircuit and z layout are unchanged if you
//! switch the scheme alias to HyperNova (CCS, sumcheck multifolding;
//! Kothapalli-Setty 2023) — see the note next to `type N` below.
//!
//! Run:  cargo run --release -p zk-data-quality -- 1000
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

mod gadgets;
mod orders;
mod step_circuit;

use ark_bn254::{Fr, G1Projective as Projective};
use ark_ff::PrimeField;
use ark_grumpkin::Projective as Projective2;
use ark_std::time::Instant;

use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::folding::protogalaxy::ProtoGalaxy;
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::{Error, FoldingScheme};

use orders::{synthetic_orders, FIELDS_PER_ORDER};
use step_circuit::{DataQualityStepCircuit, STATE_LEN};

/// Build the public initial state z_0.
/// `r` is a placeholder here; in the real protocol it is a Fiat-Shamir challenge
/// over the dataset commitment (see the soundness note in step_circuit.rs).
fn initial_state<F: PrimeField>(r: u64, t_min: u64, t_max: u64) -> Vec<F> {
    let mut z = vec![F::zero(); STATE_LEN];
    z[0] = F::one(); // valid starts true
    z[1] = F::zero(); // phi  = 0
    z[2] = F::one(); // pw   = r^0 = 1
    z[3] = F::from(r); // r
    z[4] = F::zero(); // prev_vehicle (unused on first step)
    z[5] = F::zero(); // prev_end
    z[6] = F::zero(); // has_prev = 0
    z[7] = F::from(t_min);
    z[8] = F::from(t_max);
    z
}

fn main() -> Result<(), Error> {
    let n: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(1000);

    let t_min = 0u64;
    let t_max = u64::MAX / 2;
    let r = 0x5eed_u64; // placeholder challenge

    let dataset = synthetic_orders(n);
    // one fold step consumes one order, flattened into FIELDS_PER_ORDER field elems
    let external_inputs: Vec<[Fr; FIELDS_PER_ORDER]> = dataset
        .iter()
        .map(|o| {
            o.flatten_field::<Fr>()
                .try_into()
                .expect("flatten_field must produce FIELDS_PER_ORDER elements")
        })
        .collect();

    let z_0 = initial_state::<Fr>(r, t_min, t_max);
    let f_circuit = DataQualityStepCircuit::<Fr>::new();

    println!(
        "folding {n} orders, {FIELDS_PER_ORDER} fields each, state_len={STATE_LEN}"
    );

    // ====================== SONOBE WIRING ====================================
    // Swap this single alias to compare folding schemes; the FCircuit and the
    // z layout stay identical. Nova would be:
    //   type N = folding_schemes::folding::nova::Nova<C1, C2, FC, CS1, CS2, false>;
    //   (Nova can use KZG for CS1; ProtoGalaxy uses Pedersen for both.)
    type C1 = Projective;
    type C2 = Projective2;
    type CS1 = Pedersen<Projective>;
    type CS2 = Pedersen<Projective2>;
    type FC = DataQualityStepCircuit<Fr>;
    type N = ProtoGalaxy<C1, C2, FC, CS1, CS2>;

    let mut rng = rand::rngs::OsRng;
    let poseidon_config = poseidon_canonical_config::<Fr>();

    // 1. preprocess: derive prover/verifier params from the FCircuit + rng.
    //    ProtoGalaxy's PreprocessorParam is just the (poseidon_config, FCircuit) tuple.
    println!("Prepare ProtoGalaxy's ProverParams & VerifierParams");
    let prep_param = (poseidon_config, f_circuit.clone());
    let pg_params = N::preprocess(&mut rng, &prep_param)?;

    // 2. init the IVC at z_0
    println!("Initialize FoldingScheme");
    let mut pg = N::init(&pg_params, f_circuit, z_0.clone())?;

    // 3. fold one order per step
    let t = Instant::now();
    for (i, ext) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        pg.prove_step(rng, *ext, None)?;
        println!("ProtoGalaxy::prove_step {i}: {:?}", start.elapsed());
    }
    let elapsed = t.elapsed();

    // 4. verify the IVC proof
    println!("Run ProtoGalaxy's IVC verifier");
    let ivc_proof = pg.ivc_proof();
    N::verify(pg_params.1, ivc_proof)?;

    // read out the running state
    let z_i = pg.state();
    let valid = z_i[0]; // must equal 1 if every order passed all checks
    let phi = z_i[1]; // RLC fingerprint -> bind to the dataset commitment / MPC

    println!("folded {n} orders in {elapsed:?}");
    println!("valid = {valid}  (1 == all orders passed every data-quality check)");
    println!("phi   = {phi}  (RLC fingerprint over the canonical field stream)");
    assert_eq!(valid, Fr::from(1u64), "some order failed a data-quality check");
    Ok(())
}


/* 100 orders
Nova::prove_step 99: 2.524447166s
Run Nova's IVC verifier
folded 100 orders in 263.432949958s
valid = 1  (1 == all orders passed every data-quality check)
phi   = 16663750667764190420402924999120457077423314795492460127242554214062020004412  (RLC fingerprint over the canonical field stream)
*/

/* 1000 orders
Nova::prove_step 999: 2.516657167s
Run Nova's IVC verifier
folded 1000 orders in 2466.361373875s
valid = 1  (1 == all orders passed every data-quality check)
phi   = 20086278831280422771215611809076114563767835786732472002048536257374972134231  (RLC fingerprint over the canonical field stream)
*/
