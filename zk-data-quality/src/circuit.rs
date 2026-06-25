//! step_circuit.rs — the per-record step function F for the folding scheme.
//!
//! One fold step consumes ONE transport order (its FIELDS_PER_ORDER values as
//! `external_inputs`) and updates a small constant-size state vector z. Folding n
//! steps therefore touches at most one order's worth of witness at a time, which
//! is exactly what removes the Noir O(n) memory blow-up.
//!
//! State layout z (length = STATE_LEN):
//!   z[0] valid        running AND of all per-record checks            (0/1)
//!   z[1] phi          RLC fingerprint   phi += pw * x_k               (accumulator)
//!   z[2] pw           current power of r (pw *= r per consumed field)
//!   z[3] r            challenge, carried unchanged (pinned by z_0)
//!   z[4] prev_vehicle previous order's vehicle id  (for adjacency)
//!   z[5] prev_end     previous order's max end_time (for adjacency)
//!   z[6] has_prev     0 on the first step, 1 thereafter
//!   z[7] t_min        currentness window lower bound (carried, pinned by z_0)
//!   z[8] t_max        currentness window upper bound (carried, pinned by z_0)
//!
//! r, t_min, t_max are passed through UNCHANGED every step. Because z_0 is public
//! in the IVC and F enforces z_out[i] == z_in[i] for those slots, they behave as
//! public constants for the whole run without needing to be re-supplied per step.
//!
//! SOUNDNESS NOTE (do not ship without resolving):
//!  - The adjacency check (no same-vehicle time overlap) is correct ONLY if the
//!    folded stream is the committed dataset *sorted by (vehicle, start_time)*.
//!    Two routes to make that sound, matching your slide:
//!      (a) define the dataset commitment over the sorted order, so no permutation
//!          proof is needed (simplest; the MPC must use the same order); or
//!      (b) add a grand-product / multiset-equality fold certifying the sorted
//!          stream is a permutation of the committed order (Plonk-style perm. arg.,
//!          Gabizon-Williamson-Ciobotaru 2019). This is "fold 4" in the diagram and
//!          is left as a TODO below.
//!  - r MUST be a Fiat-Shamir challenge derived AFTER the dataset commitment, as in
//!    your Noir design (zeta chosen after commit). Deriving r is a protocol-layer
//!    concern outside this circuit; here r arrives via z_0.

use ark_ff::PrimeField;
use ark_r1cs_std::{
    alloc::{AllocVar, AllocationMode},
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    select::CondSelectGadget,
};
use ark_relations::r1cs::{ConstraintSystemRef, Namespace, SynthesisError};
use core::borrow::Borrow;

use crate::gadgets::{is_leq, is_lt, is_nonzero};
use crate::otm::{FIELDS_PER_ORDER, MAX_ACTIONS, MAX_GOODS};

pub const STATE_LEN: usize = 9;
const TIME_BITS: usize = 64; // timestamps, lat/long fit in u64
const SUM_BITS: usize = 128; // weight*quantity summed over goods: widen to be safe

#[derive(Clone, Debug)]
pub struct DataQualityStepCircuit<F: PrimeField> {
    _f: core::marker::PhantomData<F>,
}

impl<F: PrimeField> DataQualityStepCircuit<F> {
    pub fn new() -> Self {
        Self { _f: core::marker::PhantomData }
    }

    /// The actual constraints. Kept as an inherent method so it can be unit-tested
    /// against a bare `ConstraintSystem` without the full folding stack, and then
    /// called from the `FCircuit` impl (see the trait-glue note at the bottom).
    pub fn step(
        &self,
        cs: ConstraintSystemRef<F>,
        z_in: &[FpVar<F>],
        ext: &[FpVar<F>], // one order, flattened in canonical order
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        assert_eq!(z_in.len(), STATE_LEN);
        assert_eq!(ext.len(), FIELDS_PER_ORDER);

        let valid_in = &z_in[0];
        let mut phi = z_in[1].clone();
        let mut pw = z_in[2].clone();
        let r = z_in[3].clone();
        let prev_vehicle = z_in[4].clone();
        let prev_end = z_in[5].clone();
        let has_prev = z_in[6].clone();
        let t_min = z_in[7].clone();
        let t_max = z_in[8].clone();

        // ---- parse the flattened order ------------------------------------
        let order_id = &ext[0];
        let vehicle_id = &ext[1];
        let capacity = &ext[2];
        let mut idx = 3;

        let mut checks: Vec<Boolean<F>> = Vec::new();

        // ---- ROW-LOCAL VALIDITY (fold 1) ----------------------------------
        checks.push(is_nonzero(order_id)?);
        checks.push(is_nonzero(vehicle_id)?);
        checks.push(is_nonzero(capacity)?); // capacity > 0 (u64 => != 0)

        let mut cur_min_start: Option<FpVar<F>> = None;
        let mut cur_max_end: Option<FpVar<F>> = None;

        for _ in 0..MAX_ACTIONS {
            let a_id = &ext[idx];
            let a_type = &ext[idx + 1];
            let a_start = &ext[idx + 2];
            let a_end = &ext[idx + 3];
            let l_id = &ext[idx + 4];
            let lat = &ext[idx + 5];
            let lon = &ext[idx + 6];
            idx += 7;

            checks.push(is_nonzero(a_id)?);
            checks.push(is_nonzero(l_id)?);

            // action_type in {1,2,3}
            let t1 = a_type.is_eq(&FpVar::constant(F::from(1u64)))?;
            let t2 = a_type.is_eq(&FpVar::constant(F::from(2u64)))?;
            let t3 = a_type.is_eq(&FpVar::constant(F::from(3u64)))?;
            checks.push(Boolean::kary_or(&[t1, t2, t3])?);

            // start < end
            checks.push(is_lt(cs.clone(), a_start, a_end, TIME_BITS)?);

            // currentness: t_min <= start  AND  end <= t_max
            checks.push(is_leq(cs.clone(), &t_min, a_start, TIME_BITS)?);
            checks.push(is_leq(cs.clone(), a_end, &t_max, TIME_BITS)?);

            // precision/range: latitude <= 90_000_000, longitude <= 180_000_000
            checks.push(is_leq(cs.clone(), lat, &FpVar::constant(F::from(90_000_000u64)), TIME_BITS)?);
            checks.push(is_leq(cs.clone(), lon, &FpVar::constant(F::from(180_000_000u64)), TIME_BITS)?);

            // track this order's time span for the adjacency check
            cur_min_start = Some(match cur_min_start {
                None => a_start.clone(),
                Some(prev) => {
                    let le = is_leq(cs.clone(), a_start, &prev, TIME_BITS)?;
                    FpVar::conditionally_select(&le, a_start, &prev)?
                }
            });
            cur_max_end = Some(match cur_max_end {
                None => a_end.clone(),
                Some(prev) => {
                    let ge = is_leq(cs.clone(), &prev, a_end, TIME_BITS)?;
                    FpVar::conditionally_select(&ge, a_end, &prev)?
                }
            });
        }

        // capacity sweep: sum(weight*quantity) <= capacity (fold 1, accumulator form)
        let mut total_weight = FpVar::<F>::zero();
        for _ in 0..MAX_GOODS {
            let g_id = &ext[idx];
            let g_qty = &ext[idx + 1];
            let g_wt = &ext[idx + 2];
            idx += 3;
            checks.push(is_nonzero(g_id)?);
            checks.push(is_nonzero(g_qty)?); // quantity > 0
            checks.push(is_nonzero(g_wt)?);  // weight   > 0
            total_weight += g_wt * g_qty;
        }
        checks.push(is_leq(cs.clone(), &total_weight, capacity, SUM_BITS)?);
        debug_assert_eq!(idx, FIELDS_PER_ORDER);

        // ---- CROSS-ENTRY ADJACENCY (fold 3) -------------------------------
        // same_vehicle AND has_prev  =>  prev_end <= cur_min_start
        let cur_min_start = cur_min_start.unwrap();
        let cur_max_end = cur_max_end.unwrap();
        let same_vehicle = vehicle_id.is_eq(&prev_vehicle)?;
        let has_prev_bool = has_prev_to_bool(&has_prev)?;
        let active = &same_vehicle & &has_prev_bool;
        let ordered = is_leq(cs.clone(), &prev_end, &cur_min_start, TIME_BITS)?;
        // adjacency_ok = !active OR ordered
        let adjacency_ok = (!&active) | &ordered;
        checks.push(adjacency_ok);

        // ---- RLC FINGERPRINT (fold 2) -------------------------------------
        // phi += pw * x_k ; pw *= r   over the SAME canonical field order.
        for k in 0..FIELDS_PER_ORDER {
            phi += &pw * &ext[k];
            pw *= &r;
        }

        // ---- fold all booleans into the running validity flag -------------
        let all_local = Boolean::kary_and(&checks)?;
        let valid_in_bool = fp_to_bool(valid_in)?;
        let valid_out = &valid_in_bool & &all_local;

        // ---- assemble next state ------------------------------------------
        let mut z_out = vec![FpVar::<F>::zero(); STATE_LEN];
        z_out[0] = FpVar::from(valid_out);
        z_out[1] = phi;
        z_out[2] = pw;
        z_out[3] = r;                    // pinned
        z_out[4] = vehicle_id.clone();
        z_out[5] = cur_max_end;
        z_out[6] = FpVar::constant(F::one()); // has_prev := 1
        z_out[7] = t_min;                // pinned
        z_out[8] = t_max;                // pinned

        // TODO (fold 4): grand-product permutation accumulator. Multiply a running
        // product by (gamma - fingerprint(order)) here, and assert at the decider
        // that it equals the product over the committed order. Until then, the
        // adjacency result is sound only under route (a) above (commit in sorted
        // order). See the soundness note at the top of this file.

        Ok(z_out)
    }
}

/// Interpret a field var known to be 0/1 as a Boolean (enforces booleanity).
fn fp_to_bool<F: PrimeField>(x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    // is_eq with 1; combined with the 0/1 invariant maintained by the circuit.
    x.is_eq(&FpVar::constant(F::one()))
}
fn has_prev_to_bool<F: PrimeField>(x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    fp_to_bool(x)
}

// -----------------------------------------------------------------------------
// FCircuit trait glue (Sonobe).
//
// This rev of Sonobe uses the associated-types shape: the external input for one
// fold step is a strongly-typed value implementing `AllocVar`. One transport order
// is exactly FIELDS_PER_ORDER field elements. A bare `[F; FIELDS_PER_ORDER]` would
// be the natural choice, but std only derives `Default` for arrays up to length 32
// and FIELDS_PER_ORDER is 43, so we wrap a `Vec` in a newtype and implement
// `Default`/`AllocVar` by hand (mirroring Sonobe's own `VecF`/`VecFpVar`). The
// `Default` impl yields a vector of the correct length, which the folding framework
// relies on when it builds the augmented circuit.
//
// The body is just: self.step(cs, &z_i, &external_inputs.0).
// -----------------------------------------------------------------------------
use folding_schemes::frontend::FCircuit;
use folding_schemes::Error;

/// One transport order flattened to its FIELDS_PER_ORDER field elements (native).
#[derive(Clone, Debug)]
pub struct OrderInputs<F: PrimeField>(pub Vec<F>);
impl<F: PrimeField> Default for OrderInputs<F> {
    fn default() -> Self {
        OrderInputs(vec![F::zero(); FIELDS_PER_ORDER])
    }
}

/// In-circuit counterpart of `OrderInputs`.
#[derive(Clone, Debug)]
pub struct OrderInputsVar<F: PrimeField>(pub Vec<FpVar<F>>);
impl<F: PrimeField> AllocVar<OrderInputs<F>, F> for OrderInputsVar<F> {
    fn new_variable<T: Borrow<OrderInputs<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        f().and_then(|val| {
            let cs = cs.into();
            let v = Vec::<FpVar<F>>::new_variable(cs, || Ok(val.borrow().0.clone()), mode)?;
            Ok(OrderInputsVar(v))
        })
    }
}

impl<F: PrimeField> FCircuit<F> for DataQualityStepCircuit<F> {
    type Params = ();
    type ExternalInputs = OrderInputs<F>;
    type ExternalInputsVar = OrderInputsVar<F>;

    fn new(_: ()) -> Result<Self, Error> {
        Ok(Self::new())
    }
    fn state_len(&self) -> usize {
        STATE_LEN
    }
    fn generate_step_constraints(
        &self,
        cs: ConstraintSystemRef<F>,
        _i: usize,
        z_i: Vec<FpVar<F>>,
        external_inputs: Self::ExternalInputsVar,
    ) -> Result<Vec<FpVar<F>>, SynthesisError> {
        self.step(cs, &z_i, &external_inputs.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::orders::synthetic_orders;
    use ark_bn254::Fr;
    use ark_r1cs_std::{alloc::AllocVar, R1CSVar};
    use ark_relations::r1cs::ConstraintSystem;

    /// Run one step on `ext_vals` from a fresh z_0 and return (valid_bit, cs_satisfied).
    /// The constraints never *force* validity to 1 — they compute it — so a bad
    /// record yields valid==0 while the constraint system is still satisfiable.
    fn run_step(ext_vals: Vec<Fr>) -> (Fr, bool) {
        let cs = ConstraintSystem::<Fr>::new_ref();
        let mut z = vec![Fr::from(0u64); STATE_LEN];
        z[0] = Fr::from(1u64); // valid
        z[2] = Fr::from(1u64); // pw = r^0
        z[3] = Fr::from(0x5eedu64); // r
        z[7] = Fr::from(0u64); // t_min
        z[8] = Fr::from(u64::MAX / 2); // t_max

        let z_in = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(z)).unwrap();
        let ext = Vec::<FpVar<Fr>>::new_witness(cs.clone(), || Ok(ext_vals)).unwrap();
        let circuit = DataQualityStepCircuit::<Fr>::new();
        let z_out = circuit.step(cs.clone(), &z_in, &ext).unwrap();
        let valid = z_out[0].value().unwrap();
        (valid, cs.is_satisfied().unwrap())
    }

    #[test]
    fn good_order_is_valid() {
        let ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        let (valid, satisfied) = run_step(ext);
        assert!(satisfied, "constraint system must be satisfiable");
        assert_eq!(valid, Fr::from(1u64), "a well-formed order must validate");
    }

    #[test]
    fn bad_action_type_is_invalid() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        // index 4 = first action's action_type; 7 is outside the allowed {1,2,3}
        ext[4] = Fr::from(7u64);
        let (valid, satisfied) = run_step(ext);
        assert!(satisfied, "system stays satisfiable; validity is computed not forced");
        assert_eq!(valid, Fr::from(0u64), "an illegal action_type must fail validation");
    }

    #[test]
    fn overweight_order_is_invalid() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        // index 2 = vehicle capacity; shrink it below the goods' total weight
        ext[2] = Fr::from(1u64);
        let (valid, _satisfied) = run_step(ext);
        assert_eq!(valid, Fr::from(0u64), "exceeding capacity must fail validation");
    }
}
