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
use folding_schemes::folding::hypernova::HyperNova;
use folding_schemes::folding::nova::PreprocessorParam;
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
    // z layout stay identical. Other schemes:
    //   Nova:        folding::nova::Nova<C1, C2, FC, CS1, CS2, false>  (KZG ok for CS1)
    //   ProtoGalaxy: folding::protogalaxy::ProtoGalaxy<C1, C2, FC, CS1, CS2>
    // HyperNova folds CCS via sumcheck multifolding (Kothapalli-Setty 2023). The
    // MU/NU const params are how many running/incoming instances are multifolded
    // per step; 1/1 is the standard single-instance IVC. Uses Pedersen for both.
    type C1 = Projective;
    type C2 = Projective2;
    type CS1 = Pedersen<Projective>;
    type CS2 = Pedersen<Projective2>;
    type FC = DataQualityStepCircuit<Fr>;
    const MU: usize = 1;
    const NU: usize = 1;
    type N = HyperNova<C1, C2, FC, CS1, CS2, MU, NU, false>;

    let mut rng = rand::rngs::OsRng;
    let poseidon_config = poseidon_canonical_config::<Fr>();

    // 1. preprocess: derive prover/verifier params from the FCircuit + rng.
    //    HyperNova reuses Nova's PreprocessorParam.
    println!("Prepare HyperNova's ProverParams & VerifierParams");
    let prep_param = PreprocessorParam::new(poseidon_config, f_circuit.clone());
    let hn_params = N::preprocess(&mut rng, &prep_param)?;

    // 2. init the IVC at z_0
    println!("Initialize FoldingScheme");
    let mut hn = N::init(&hn_params, f_circuit, z_0.clone())?;

    // 3. fold one order per step
    let t = Instant::now();
    for (i, ext) in external_inputs.iter().enumerate() {
        let start = Instant::now();
        hn.prove_step(rng, *ext, None)?;
        println!("HyperNova::prove_step {i}: {:?}", start.elapsed());
    }
    let elapsed = t.elapsed();

    // 4. verify the IVC proof
    println!("Run HyperNova's IVC verifier");
    let ivc_proof = hn.ivc_proof();
    N::verify(hn_params.1, ivc_proof)?;

    // read out the running state
    let z_i = hn.state();
    let valid = z_i[0]; // must equal 1 if every order passed all checks
    let phi = z_i[1]; // RLC fingerprint -> bind to the dataset commitment / MPC

    println!("folded {n} orders in {elapsed:?}");
    println!("valid = {valid}  (1 == all orders passed every data-quality check)");
    println!("phi   = {phi}  (RLC fingerprint over the canonical field stream)");
    assert_eq!(valid, Fr::from(1u64), "some order failed a data-quality check");
    Ok(())
}


/* 5 orders
folding 5 orders, 23 fields each, state_len=9
Prepare HyperNova's ProverParams & VerifierParams
Initialize FoldingScheme
HyperNova::prove_step 0: 1.365578542s
HyperNova::prove_step 1: 2.027503625s
HyperNova::prove_step 2: 2.021863625s
HyperNova::prove_step 3: 2.063503583s
HyperNova::prove_step 4: 2.075860583s
Run HyperNova's IVC verifier
folded 5 orders in 9.554398125s
valid = 1  (1 == all orders passed every data-quality check)
phi   = 17418569807843800795750841722005551770673501891093229536055977353257204643821  (RLC fingerprint over the canonical field stream)
*/
