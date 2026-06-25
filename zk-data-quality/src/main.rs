#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]

mod gadgets;
mod otm;
mod orders;
mod circuit;

use std::marker::PhantomData;

use ark_bn254::{Fr, G1Projective as BN254};
use ark_ff::PrimeField;
use ark_grumpkin::Projective as Grumpkin;
use ark_std::time::Instant;

use folding_schemes::commitment::pedersen::Pedersen;
use folding_schemes::folding::hypernova::HyperNova;
use folding_schemes::folding::nova::{Nova, PreprocessorParam};
use folding_schemes::folding::protogalaxy::ProtoGalaxy;
use folding_schemes::transcript::poseidon::poseidon_canonical_config;
use folding_schemes::{Error, FoldingScheme};

use orders::{synthetic_orders};
use circuit::{DataQualityStepCircuit, OrderInputs, STATE_LEN};

use crate::otm::FIELDS_PER_ORDER;

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

struct ProofBuilder<FS>
where FS: FoldingScheme<BN254, Grumpkin, DataQualityStepCircuit<Fr>>,
{
    n: usize,
    r: u64,
    t_min: u64,
    t_max: u64,
    _marker: std::marker::PhantomData<FS>,
}

impl<FS> ProofBuilder<FS> where FS: FoldingScheme<BN254, Grumpkin, DataQualityStepCircuit<Fr>> {
    fn new(n: usize, r: u64, t_min: u64, t_max: u64) -> Self {
        Self { n, r, t_min, t_max, _marker: PhantomData }
    }

    fn build(&self, name: &str, prep_param: FS::PreprocessorParam) -> Result<(), Error> {
        let f_circuit = DataQualityStepCircuit::<Fr>::new();
        let mut rng = rand::rngs::OsRng;

        // one fold step consumes one order, flattened into FIELDS_PER_ORDER field elems
        let external_inputs: Vec<OrderInputs<Fr>> = synthetic_orders(self.n)
            .iter()
            .map(|o| {
                let v = o.flatten_field::<Fr>();
                debug_assert_eq!(v.len(), FIELDS_PER_ORDER);
                OrderInputs(v)
            })
            .collect();

        println!(
            "[{name}] folding {} orders, {FIELDS_PER_ORDER} fields each, state_len={STATE_LEN}",
            self.n
        );

        let fs_params = FS::preprocess(&mut rng, &prep_param)?;
        let z_0 = initial_state::<Fr>(self.r, self.t_min, self.t_max);
        let mut folding = FS::init(&fs_params, f_circuit, z_0)?;

        let t = Instant::now();
        for ext in external_inputs.iter() {
            // Can print something here for each step
            folding.prove_step(rng, ext.clone(), None)?;
        }
        let elapsed = t.elapsed();

        let ivc_proof = folding.ivc_proof();
        FS::verify(fs_params.1, ivc_proof)?;

        let z_i = folding.state();
        let valid = z_i[0]; // must equal 1 if every order passed all checks
        let phi = z_i[1]; // RLC fingerprint -> bind to the dataset commitment / MPC
        println!("[{name}] folded {} orders in {elapsed:?}", self.n);
        println!("[{name}] valid = {valid}  phi = {phi}");
        assert_eq!(valid, Fr::from(1u64), "some order failed a data-quality check");
        Ok(())
    }
}

fn main() -> Result<(), Error> {
    let n: usize = std::env::args()
        .nth(1)
        .and_then(|s| s.parse().ok())
        .unwrap_or(10);


    let t_min = 0u64;
    let t_max = u64::MAX / 2;
    let r = 0x5eed_u64; // placeholder challenge

    let dataset = synthetic_orders(n);

    let f_circuit = DataQualityStepCircuit::<Fr>::new();
    let poseidon_config = poseidon_canonical_config::<Fr>();

    type FSNova = Nova<BN254, Grumpkin, DataQualityStepCircuit<Fr>, Pedersen<BN254>, Pedersen<Grumpkin>, false>;
    let nova_prep = PreprocessorParam::new(poseidon_config.clone(), f_circuit.clone());
    ProofBuilder::<FSNova>::new(n, r, t_min, t_max).build("Nova", nova_prep)?;

    type FSHyperNova = HyperNova<BN254, Grumpkin, DataQualityStepCircuit<Fr>, Pedersen<BN254>, Pedersen<Grumpkin>, 1, 1, false>;
    let hn_prep = PreprocessorParam::new(poseidon_config.clone(), f_circuit.clone());
    ProofBuilder::<FSHyperNova>::new(n, r, t_min, t_max).build("HyperNova", hn_prep)?;

    type FSProtoGalaxy = ProtoGalaxy<BN254, Grumpkin, DataQualityStepCircuit<Fr>, Pedersen<BN254>, Pedersen<Grumpkin>>;
    let pg_prep = (poseidon_config.clone(), f_circuit.clone());
    ProofBuilder::<FSProtoGalaxy>::new(n, r, t_min, t_max).build("ProtoGalaxy", pg_prep)?;



    Ok(())
}


/* 5 orders
folding 5 orders, 23 fields each, state_len=9
Prepare ProtoGalaxy's ProverParams & VerifierParams
Initialize FoldingScheme
ProtoGalaxy::prove_step 0: 1.45962425s
ProtoGalaxy::prove_step 1: 2.705653459s
ProtoGalaxy::prove_step 2: 2.709888416s
ProtoGalaxy::prove_step 3: 2.361065041s
ProtoGalaxy::prove_step 4: 2.32695725s
Run ProtoGalaxy's IVC verifier
folded 5 orders in 11.563283333s
valid = 1  (1 == all orders passed every data-quality check)
phi   = 17418569807843800795750841722005551770673501891093229536055977353257204643821  (RLC fingerprint over the canonical field stream)
*/


/* 1000 orders, with --release tag
ProtoGalaxy::prove_step 993: 174.482ms
ProtoGalaxy::prove_step 994: 186.599125ms
ProtoGalaxy::prove_step 995: 170.024666ms
ProtoGalaxy::prove_step 996: 158.400167ms
ProtoGalaxy::prove_step 997: 161.548542ms
ProtoGalaxy::prove_step 998: 157.6995ms
ProtoGalaxy::prove_step 999: 158.972917ms
Run ProtoGalaxy's IVC verifier
folded 1000 orders in 159.6129455s
valid = 1  (1 == all orders passed every data-quality check)
phi   = 20086278831280422771215611809076114563767835786732472002048536257374972134231  (RLC fingerprint over the canonical field stream)
*/

/*
[Nova] folding 1000 orders, 83 fields each, state_len=9
[Nova] folded 1000 orders in 124.862494958s
[Nova] valid = 1  phi = 18918949578341787243231063113255628687147046740496992278699480789861135955774
[HyperNova] folding 1000 orders, 83 fields each, state_len=9
[HyperNova] folded 1000 orders in 168.916731958s
[HyperNova] valid = 1  phi = 18918949578341787243231063113255628687147046740496992278699480789861135955774
[ProtoGalaxy] folding 1000 orders, 83 fields each, state_len=9
[ProtoGalaxy] folded 1000 orders in 167.991879583s
[ProtoGalaxy] valid = 1  phi = 18918949578341787243231063113255628687147046740496992278699480789861135955774
*/
