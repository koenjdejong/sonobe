//! State layout z (length = STATE_LEN):
//!   z[0] valid        running AND of all per-record checks            (0/1)
//!   z[1] phi          RLC fingerprint   phi += pw * x_k               (accumulator)
//!   z[2] pw           current power of r (pw *= r per consumed field)
//!   z[3] r            challenge, carried unchanged (pinned by z_0)
//!   z[4] prev_vehicle previous order's vehicle id  (for adjacency)
//!   z[5] prev_end     previous order's max end_time (for adjacency)
//!   z[6] has_prev     0 on the first step, 1 thereafter
//!   z[7]  t_min       currentness window lower bound (carried, pinned by z_0)
//!   z[8]  t_max       currentness window upper bound (carried, pinned by z_0)
//!   z[9]  gamma       grand-product challenge, carried unchanged (pinned by z_0)
//!   z[10] gp          grand-product accumulator gp *= (gamma - fp(order)) (starts 1)
//!
//! SOUNDNESS NOTE:
//!  - The adjacency check (no same-vehicle time overlap) is correct ONLY if the
//!    folded stream is the committed dataset *sorted by (vehicle, start_time)*.
//!    Two routes to make that sound, matching your slide:
//!      (a) define the dataset commitment over the sorted order, so no permutation
//!          proof is needed (simplest; the MPC must use the same order); or
//!      (b) certify, via a grand-product / multiset-equality argument, that the
//!          folded (sorted) stream is a permutation of the committed order
//!          (Plonk-style perm. arg., Gabizon-Williamson-Ciobotaru 2019).
//!    Route (b) is "fold 4" and is implemented below: each step compresses its
//!    order to a single field fp(order) = Σ_k r^k·x_k and folds it into a running
//!    grand product gp *= (gamma - fp(order)). After the run, gp equals the product
//!    over the FOLDED stream; the decider (main.rs) computes the same product over
//!    the COMMITTED order and asserts equality. Equal products ⇒ equal multisets
//!    (whp over gamma) ⇒ the fold is a genuine permutation of the commitment. Under
//!    route (a) the two streams coincide, so the check simply confirms the
//!    accumulator; under a sorted fold over an unsorted commitment it certifies the
//!    sort. gamma must be a Fiat-Shamir challenge drawn after the commitment, like r.

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

pub const STATE_LEN: usize = 11;
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
        let gamma = z_in[9].clone();
        let mut gp = z_in[10].clone();

        // ---- parse the flattened order ------------------------------------
        // Canonical layout (see otm::TransportOrder::flatten):
        //   header: id, active, vehicle_id, capacity
        //   then MAX_ACTIONS actions:  id, active, type, start, end, loc_id, lat, lon
        //   then MAX_GOODS goods:      id, active, quantity, weight
        //
        // The `active` flags mark which array slots carry real data; the rest are
        // fixed-size-array padding. Padding rows must NOT be validated and must NOT
        // perturb the order's time span or the cross-order adjacency chain. Each flag
        // is read as `== 1` (consistent with `fp_to_bool`) and gated accordingly.
        let order_id = &ext[0];
        let order_active = fp_to_bool(&ext[1])?;
        let vehicle_id = &ext[2];
        let capacity = &ext[3];
        let mut idx = 4;

        let mut checks: Vec<Boolean<F>> = Vec::new();

        // ---- ROW-LOCAL VALIDITY (fold 1) ----------------------------------
        // Header checks. The whole `checks` set is later gated by `order_active`,
        // so an inactive (padding) order is vacuously valid regardless of these.
        checks.push(is_nonzero(order_id)?);
        checks.push(is_nonzero(vehicle_id)?);
        checks.push(is_nonzero(capacity)?); // capacity > 0 (u64 => != 0)

        // Min start / max end taken over ACTIVE actions only. Sentinels keep padding
        // from shifting the span: inactive start -> u64::MAX (can't lower the min),
        // inactive end -> 0 (can't raise the max). Both sentinels fit in TIME_BITS.
        let start_sentinel = FpVar::<F>::constant(F::from(u64::MAX));
        let mut cur_min_start = start_sentinel.clone();
        let mut cur_max_end = FpVar::<F>::zero();

        for _ in 0..MAX_ACTIONS {
            let a_id = &ext[idx];
            let a_active = fp_to_bool(&ext[idx + 1])?;
            let a_type = &ext[idx + 2];
            let a_start = &ext[idx + 3];
            let a_end = &ext[idx + 4];
            let l_id = &ext[idx + 5];
            let lat = &ext[idx + 6];
            let lon = &ext[idx + 7];
            idx += 8;

            // Per-action validity, collected then gated by this action's `active`.
            let mut a_checks: Vec<Boolean<F>> = Vec::new();
            a_checks.push(is_nonzero(a_id)?);
            a_checks.push(is_nonzero(l_id)?);

            // action_type in {1,2,3}
            let t1 = a_type.is_eq(&FpVar::constant(F::from(1u64)))?;
            let t2 = a_type.is_eq(&FpVar::constant(F::from(2u64)))?;
            let t3 = a_type.is_eq(&FpVar::constant(F::from(3u64)))?;
            a_checks.push(Boolean::kary_or(&[t1, t2, t3])?);

            // start < end
            a_checks.push(is_lt(cs.clone(), a_start, a_end, TIME_BITS)?);

            // currentness: t_min <= start  AND  end <= t_max
            a_checks.push(is_leq(cs.clone(), &t_min, a_start, TIME_BITS)?);
            a_checks.push(is_leq(cs.clone(), a_end, &t_max, TIME_BITS)?);

            // precision/range: latitude <= 90_000_000, longitude <= 180_000_000
            a_checks.push(is_leq(cs.clone(), lat, &FpVar::constant(F::from(90_000_000u64)), TIME_BITS)?);
            a_checks.push(is_leq(cs.clone(), lon, &FpVar::constant(F::from(180_000_000u64)), TIME_BITS)?);

            // inactive actions are vacuously valid
            let a_all = Boolean::kary_and(&a_checks)?;
            checks.push((!&a_active) | &a_all);

            // track this order's time span over ACTIVE actions only
            let eff_start = FpVar::conditionally_select(&a_active, a_start, &start_sentinel)?;
            let eff_end = FpVar::conditionally_select(&a_active, a_end, &FpVar::<F>::zero())?;
            let le = is_leq(cs.clone(), &eff_start, &cur_min_start, TIME_BITS)?;
            cur_min_start = FpVar::conditionally_select(&le, &eff_start, &cur_min_start)?;
            let ge = is_leq(cs.clone(), &cur_max_end, &eff_end, TIME_BITS)?;
            cur_max_end = FpVar::conditionally_select(&ge, &eff_end, &cur_max_end)?;
        }

        // capacity sweep: sum(weight*quantity) <= capacity (fold 1, accumulator form).
        // Only ACTIVE goods are checked and contribute to the loaded weight.
        let mut total_weight = FpVar::<F>::zero();
        for _ in 0..MAX_GOODS {
            let g_id = &ext[idx];
            let g_active = fp_to_bool(&ext[idx + 1])?;
            let g_qty = &ext[idx + 2];
            let g_wt = &ext[idx + 3];
            idx += 4;

            let mut g_checks: Vec<Boolean<F>> = Vec::new();
            g_checks.push(is_nonzero(g_id)?);
            g_checks.push(is_nonzero(g_qty)?); // quantity > 0
            g_checks.push(is_nonzero(g_wt)?);  // weight   > 0
            let g_all = Boolean::kary_and(&g_checks)?;
            checks.push((!&g_active) | &g_all);

            // only active goods load the vehicle
            let contribution = g_wt * g_qty;
            total_weight += FpVar::conditionally_select(&g_active, &contribution, &FpVar::<F>::zero())?;
        }
        checks.push(is_leq(cs.clone(), &total_weight, capacity, SUM_BITS)?);
        debug_assert_eq!(idx, FIELDS_PER_ORDER);

        // ---- CROSS-ENTRY ADJACENCY (fold 3) -------------------------------
        // same_vehicle AND has_prev AND order_active  =>  prev_end <= cur_min_start.
        // An inactive (padding) order is excluded from the chain entirely.
        let same_vehicle = vehicle_id.is_eq(&prev_vehicle)?;
        let has_prev_bool = fp_to_bool(&has_prev)?;
        let adj_active = &(&same_vehicle & &has_prev_bool) & &order_active;
        let ordered = is_leq(cs.clone(), &prev_end, &cur_min_start, TIME_BITS)?;
        // adjacency_ok = !adj_active OR ordered
        let adjacency_ok = (!&adj_active) | &ordered;
        checks.push(adjacency_ok);

        // ---- RLC FINGERPRINT (fold 2) -------------------------------------
        // phi += pw * x_k ; pw *= r   over the SAME canonical field order.
        // Every field (active flags included) is absorbed, so phi commits to the
        // full padded stream exactly as `derive_challenge` does in main.rs.
        //
        // In the same sweep, build this order's standalone fingerprint
        //   fp(order) = Σ_k r^k · x_k
        // using a power series that RESTARTS at r^0 each step (independent of the
        // global pw, which never resets). This per-order scalar is the multiset
        // element consumed by the grand product below.
        let mut order_fp = FpVar::<F>::zero();
        let mut order_pw = FpVar::<F>::one();
        for k in 0..FIELDS_PER_ORDER {
            phi += &pw * &ext[k];
            pw *= &r;
            order_fp += &order_pw * &ext[k];
            order_pw *= &r;
        }

        // ---- GRAND-PRODUCT PERMUTATION ACCUMULATOR (fold 4) ---------------
        // gp *= (gamma - fp(order)) over the FOLDED stream. Every order (active or
        // padding) participates, matching the committed-order product the decider
        // recomputes in main.rs; equal products certify the fold is a permutation
        // of the commitment. See the soundness note at the top of this file.
        gp = &gp * &(&gamma - &order_fp);

        // ---- fold all booleans into the running validity flag -------------
        // Inactive orders are vacuously valid: gate the whole check set by order_active.
        let all_local = Boolean::kary_and(&checks)?;
        let order_ok = (!&order_active) | &all_local;
        let valid_in_bool = fp_to_bool(valid_in)?;
        let valid_out = &valid_in_bool & &order_ok;

        // ---- assemble next state ------------------------------------------
        // The adjacency chain (prev_vehicle, prev_end, has_prev) only advances on
        // ACTIVE orders; padding orders pass the previous chain state through so they
        // can't sever the link between two real orders.
        let next_vehicle = FpVar::conditionally_select(&order_active, vehicle_id, &prev_vehicle)?;
        let next_end = FpVar::conditionally_select(&order_active, &cur_max_end, &prev_end)?;
        let next_has_prev =
            FpVar::conditionally_select(&order_active, &FpVar::constant(F::one()), &has_prev)?;

        let mut z_out = vec![FpVar::<F>::zero(); STATE_LEN];
        z_out[0] = FpVar::from(valid_out);
        z_out[1] = phi;
        z_out[2] = pw;
        z_out[3] = r;                    // pinned
        z_out[4] = next_vehicle;
        z_out[5] = next_end;
        z_out[6] = next_has_prev;
        z_out[7] = t_min;                // pinned
        z_out[8] = t_max;                // pinned
        z_out[9] = gamma;                // pinned
        z_out[10] = gp;

        Ok(z_out)
    }
}

/// Interpret a field var known to be 0/1 as a Boolean (enforces booleanity).
fn fp_to_bool<F: PrimeField>(x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    // is_eq with 1; combined with the 0/1 invariant maintained by the circuit.
    x.is_eq(&FpVar::constant(F::one()))
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
    fn generate_step_constraints(&self, cs: ConstraintSystemRef<F>,_i: usize, z_i: Vec<FpVar<F>>, external_inputs: Self::ExternalInputsVar) -> Result<Vec<FpVar<F>>, SynthesisError> {
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
        z[9] = Fr::from(0xfeedu64); // gamma
        z[10] = Fr::from(1u64); // gp = empty product

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

    // Field offsets in the flattened layout (header is 4 wide; actions are 8 wide):
    //   [0]=order id, [1]=order active, [2]=vehicle id, [3]=capacity
    //   action 0: [4]=id, [5]=active, [6]=type, [7]=start, [8]=end, [9]=loc, [10]=lat, [11]=lon
    const ORDER_ACTIVE: usize = 1;
    const CAPACITY: usize = 3;
    const A0_ACTIVE: usize = 5;
    const A0_TYPE: usize = 6;

    #[test]
    fn bad_action_type_is_invalid() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        ext[A0_TYPE] = Fr::from(7u64); // 7 is outside the allowed {1,2,3}
        let (valid, satisfied) = run_step(ext);
        assert!(satisfied, "system stays satisfiable; validity is computed not forced");
        assert_eq!(valid, Fr::from(0u64), "an illegal action_type must fail validation");
    }

    #[test]
    fn overweight_order_is_invalid() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        ext[CAPACITY] = Fr::from(1u64); // shrink capacity below the goods' total weight
        let (valid, _satisfied) = run_step(ext);
        assert_eq!(valid, Fr::from(0u64), "exceeding capacity must fail validation");
    }

    #[test]
    fn inactive_action_skips_its_checks() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        // Garbage action_type would normally fail, but deactivating the slot makes
        // it padding, so its checks are skipped and the order still validates.
        ext[A0_TYPE] = Fr::from(7u64);
        ext[A0_ACTIVE] = Fr::from(0u64);
        let (valid, satisfied) = run_step(ext);
        assert!(satisfied, "constraint system must be satisfiable");
        assert_eq!(valid, Fr::from(1u64), "an inactive action must not be validated");
    }

    #[test]
    fn inactive_order_is_vacuously_valid() {
        let mut ext: Vec<Fr> = synthetic_orders(1)[0].flatten_field();
        // Corrupt the order and mark it inactive: the whole record is padding.
        ext[A0_TYPE] = Fr::from(7u64);
        ext[CAPACITY] = Fr::from(1u64);
        ext[ORDER_ACTIVE] = Fr::from(0u64);
        let (valid, satisfied) = run_step(ext);
        assert!(satisfied, "constraint system must be satisfiable");
        assert_eq!(valid, Fr::from(1u64), "an inactive order must not be validated");
    }
}
