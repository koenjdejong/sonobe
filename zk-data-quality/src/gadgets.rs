//! gadgets.rs — small, self-contained R1CS comparison gadgets.
//!
//! These avoid relying on ark-r1cs-std comparison helpers whose names have moved
//! between releases (`enforce_cmp`, `is_cmp`, `le_bits_to_fp_var`, ...). Everything
//! here is built from `is_eq`, Boolean algebra, and explicit bit-decomposition,
//! which are stable. If you later confirm your ark-r1cs-std version exposes a
//! native `is_cmp`, you may replace `is_leq` with it for fewer constraints.

use ark_ff::{BigInteger, PrimeField};
use ark_r1cs_std::{
    alloc::AllocVar,
    boolean::Boolean,
    eq::EqGadget,
    fields::{fp::FpVar, FieldVar},
    R1CSVar,
};
use ark_relations::r1cs::{ConstraintSystemRef, SynthesisError};

/// Boolean: x == 0.
pub fn is_zero<F: PrimeField>(x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    x.is_eq(&FpVar::<F>::zero())
}

/// Boolean: x != 0  (in Noir, `valid_id`).
pub fn is_nonzero<F: PrimeField>(x: &FpVar<F>) -> Result<Boolean<F>, SynthesisError> {
    Ok(!is_zero(x)?)
}

/// Boolean: (a <= b), SOUND ONLY when 0 <= a, b < 2^n_bits.
///
/// Method: s = b - a + 2^n. If a <= b then s in [2^n, 2^{n+1}) so bit n is 1;
/// if a > b then s in (0, 2^n) so bit n is 0. We range-bind s to (n+1) bits,
/// which is what enforces the [0, 2^n) magnitude assumption on |a - b|.
///
/// The caller is responsible for the n_bits bound on `a` and `b` themselves;
/// for u64 timestamps use 64, for the capacity*quantity sum use a wider bound.
pub fn is_leq<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
    b: &FpVar<F>,
    n_bits: usize,
) -> Result<Boolean<F>, SynthesisError> {
    let two_n = FpVar::constant(pow2::<F>(n_bits));
    let s = b - a + &two_n; // = b - a + 2^n

    // Witness the (n+1)-bit decomposition of s.
    let s_val: Option<F> = s.value().ok();
    let mut bits = Vec::with_capacity(n_bits + 1);
    for i in 0..=n_bits {
        bits.push(Boolean::new_witness(cs.clone(), || {
            s_val
                .map(|v| v.into_bigint().get_bit(i))
                .ok_or(SynthesisError::AssignmentMissing)
        })?);
    }

    // Enforce sum_i bit_i * 2^i == s  (this is the range proof for s).
    let mut acc = FpVar::<F>::zero();
    let mut coeff = F::one();
    for b in &bits {
        acc += FpVar::from(b.clone()) * FpVar::constant(coeff);
        coeff.double_in_place();
    }
    acc.enforce_equal(&s)?;

    Ok(bits[n_bits].clone()) // bit n == (a <= b)
}

/// Boolean: (a < b), same bound assumptions as `is_leq`.
pub fn is_lt<F: PrimeField>(
    cs: ConstraintSystemRef<F>,
    a: &FpVar<F>,
    b: &FpVar<F>,
    n_bits: usize,
) -> Result<Boolean<F>, SynthesisError> {
    // a < b  <=>  !(b <= a)
    Ok(!is_leq(cs, b, a, n_bits)?)
}

/// 2^n as a field element.
fn pow2<F: PrimeField>(n: usize) -> F {
    let mut acc = F::one();
    let two = F::from(2u64);
    for _ in 0..n {
        acc *= two;
    }
    acc
}
