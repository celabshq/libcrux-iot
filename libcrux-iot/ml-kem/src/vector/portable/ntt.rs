use super::arithmetic::*;
use super::vector_type::*;
use libcrux_secrets::*;

// Spec-only lane predicates, used by the `#[requires]` of `ntt_step` and
// `inv_ntt_step` below to state the coefficient magnitude bounds that
// `Vector.Portable.Ntt.{ntt_step,inv_ntt_step}_spec` assume.
//
// Written as an explicit sixteen-way conjunction over constant indices rather
// than as `hax_lib::forall(|k| hax_lib::implies(k < 16, ...))`, for two reasons:
//
//  1. a bool `&&` inside a quantifier closure makes AENEAS fail outright
//     ("Internal error ... Could not translate the body of function
//     '..::requires::{impl Fn<(usize,), hax_lib::prop::Prop> for ..closure}::call'",
//     interp/Interp.ml line 609). A Prop-level `&` on two `.to_prop()`s avoids
//     that, so short-circuiting `&&` in a `Prop` closure is the trigger.
//
//  2. even with `&`, the resulting precondition is UNSATISFIABLE, so the
//     generated `<fn>.spec` would be VACUOUS rather than fail loudly:
//     `hax_lib::prop::forall` is modelled as `ok (forall t : T, holds (...))`,
//     ranging over ALL of `usize`, while the extracted closure body indexes
//     `vec.elements[k]` BEFORE the `k < 16` guard -- out of range that index
//     fails, and `holds` of a failing computation is `False`.
//
// The unrolled form has neither problem: its `&&`s sit in an ordinary function
// rather than a `Prop` closure, and every index is in range.
//
// NOTE that this is slightly STRONGER than `ntt_step_spec` needs: the theorem
// bounds only lanes `i` and `j`, whereas this bounds all sixteen. That is the
// invariant the NTT layers actually maintain, so no caller is excluded, but it
// does mean the extracted contract asks for more than the proof consumes.
#[cfg(hax)]
fn lane_abs_le(x: FieldElement, bound: i16) -> bool {
    x >= -bound && x <= bound
}

#[cfg(hax)]
fn elements_abs_le(vec: &PortableVector, bound: i16) -> bool {
    lane_abs_le(vec.elements[0], bound)
        && lane_abs_le(vec.elements[1], bound)
        && lane_abs_le(vec.elements[2], bound)
        && lane_abs_le(vec.elements[3], bound)
        && lane_abs_le(vec.elements[4], bound)
        && lane_abs_le(vec.elements[5], bound)
        && lane_abs_le(vec.elements[6], bound)
        && lane_abs_le(vec.elements[7], bound)
        && lane_abs_le(vec.elements[8], bound)
        && lane_abs_le(vec.elements[9], bound)
        && lane_abs_le(vec.elements[10], bound)
        && lane_abs_le(vec.elements[11], bound)
        && lane_abs_le(vec.elements[12], bound)
        && lane_abs_le(vec.elements[13], bound)
        && lane_abs_le(vec.elements[14], bound)
        && lane_abs_le(vec.elements[15], bound)
}

// `ntt_step_spec` needs |vec[i]|, |vec[j]| <= 3 * 3328 = 9984.
#[hax_lib::requires(i < 16 && j < 16 && i != j && zeta >= -1664 && zeta <= 1664
    && elements_abs_le(vec, 9984))]
#[inline(always)]
pub(crate) fn ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let t = montgomery_multiply_fe_by_fer(vec.elements[j], zeta.classify());

    let a_minus_t = vec.elements[i].wrapping_sub(t);
    let a_plus_t = vec.elements[i].wrapping_add(t);

    vec.elements[j] = a_minus_t;
    vec.elements[i] = a_plus_t;
}

#[inline(always)]
pub(crate) fn ntt_layer_1_step(
    vec: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    ntt_step(vec, zeta0, 0, 2);
    ntt_step(vec, zeta0, 1, 3);
    ntt_step(vec, zeta1, 4, 6);
    ntt_step(vec, zeta1, 5, 7);
    ntt_step(vec, zeta2, 8, 10);
    ntt_step(vec, zeta2, 9, 11);
    ntt_step(vec, zeta3, 12, 14);
    ntt_step(vec, zeta3, 13, 15);
}

#[inline(always)]
pub(crate) fn ntt_layer_2_step(vec: &mut PortableVector, zeta0: i16, zeta1: i16) {
    ntt_step(vec, zeta0, 0, 4);
    ntt_step(vec, zeta0, 1, 5);
    ntt_step(vec, zeta0, 2, 6);
    ntt_step(vec, zeta0, 3, 7);
    ntt_step(vec, zeta1, 8, 12);
    ntt_step(vec, zeta1, 9, 13);
    ntt_step(vec, zeta1, 10, 14);
    ntt_step(vec, zeta1, 11, 15);
}

#[inline(always)]
pub(crate) fn ntt_layer_3_step(vec: &mut PortableVector, zeta: i16) {
    ntt_step(vec, zeta, 0, 8);
    ntt_step(vec, zeta, 1, 9);
    ntt_step(vec, zeta, 2, 10);
    ntt_step(vec, zeta, 3, 11);
    ntt_step(vec, zeta, 4, 12);
    ntt_step(vec, zeta, 5, 13);
    ntt_step(vec, zeta, 6, 14);
    ntt_step(vec, zeta, 7, 15);
}

// `inv_ntt_step_spec` needs |vec[k]| <= 4 * 3328 = 13312 for every lane.
#[hax_lib::requires(i < 16 && j < 16 && i != j && zeta >= -1664 && zeta <= 1664
    && elements_abs_le(vec, 13312))]
#[inline(always)]
pub(crate) fn inv_ntt_step(vec: &mut PortableVector, zeta: i16, i: usize, j: usize) {
    let a_minus_b = vec.elements[j].wrapping_sub(vec.elements[i]);
    let a_plus_b = vec.elements[j].wrapping_add(vec.elements[i]);

    let o0 = barrett_reduce_element(a_plus_b);
    let o1 = montgomery_multiply_fe_by_fer(a_minus_b, zeta.classify());

    vec.elements[i] = o0;
    vec.elements[j] = o1;
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_1_step(
    vec: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    inv_ntt_step(vec, zeta0, 0, 2);
    inv_ntt_step(vec, zeta0, 1, 3);
    inv_ntt_step(vec, zeta1, 4, 6);
    inv_ntt_step(vec, zeta1, 5, 7);
    inv_ntt_step(vec, zeta2, 8, 10);
    inv_ntt_step(vec, zeta2, 9, 11);
    inv_ntt_step(vec, zeta3, 12, 14);
    inv_ntt_step(vec, zeta3, 13, 15);
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_2_step(vec: &mut PortableVector, zeta0: i16, zeta1: i16) {
    inv_ntt_step(vec, zeta0, 0, 4);
    inv_ntt_step(vec, zeta0, 1, 5);
    inv_ntt_step(vec, zeta0, 2, 6);
    inv_ntt_step(vec, zeta0, 3, 7);
    inv_ntt_step(vec, zeta1, 8, 12);
    inv_ntt_step(vec, zeta1, 9, 13);
    inv_ntt_step(vec, zeta1, 10, 14);
    inv_ntt_step(vec, zeta1, 11, 15);
}

#[inline(always)]
pub(crate) fn inv_ntt_layer_3_step(vec: &mut PortableVector, zeta: i16) {
    inv_ntt_step(vec, zeta, 0, 8);
    inv_ntt_step(vec, zeta, 1, 9);
    inv_ntt_step(vec, zeta, 2, 10);
    inv_ntt_step(vec, zeta, 3, 11);
    inv_ntt_step(vec, zeta, 4, 12);
    inv_ntt_step(vec, zeta, 5, 13);
    inv_ntt_step(vec, zeta, 6, 14);
    inv_ntt_step(vec, zeta, 7, 15);
}

/// Compute the product of two Kyber binomials with respect to the
/// modulus `X² - zeta`.
///
/// This function almost implements <strong>Algorithm 11</strong> of the
/// NIST FIPS 203 standard, which is reproduced below:
///
/// ```plaintext
/// Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
/// Input: γ ∈ ℤq.
/// Output: c₀, c₁ ∈ ℤq.
///
/// c₀ ← a₀·b₀ + a₁·b₁·γ
/// c₁ ← a₀·b₁ + a₁·b₀
/// return c₀, c₁
/// ```
/// We say "almost" because the coefficients output by this function are in
/// the Montgomery domain (unlike in the specification).
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[hax_lib::requires(i < 8 && out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_binomials_fill_cache(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    out: &mut [I32],
    cache: &mut PortableVector,
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = ai.as_i32().wrapping_mul(bi.as_i32());
    let bj_zeta_ = bj.as_i32().wrapping_mul(zeta.as_i32());
    let bj_zeta = montgomery_reduce_element(bj_zeta_);
    cache.elements[i] = bj_zeta;
    let aj_bj_zeta = aj.as_i32().wrapping_mul(bj_zeta.as_i32());
    let ai_bi_aj_bj = ai_bi.wrapping_add(aj_bj_zeta);
    let o0 = ai_bi_aj_bj;

    let ai_bj = ai.as_i32().wrapping_mul(bj.as_i32());
    let aj_bi = aj.as_i32().wrapping_mul(bi.as_i32());
    let ai_bj_aj_bi = ai_bj.wrapping_add(aj_bi);
    let o1 = ai_bj_aj_bi;

    out[2 * i] = out[2 * i].wrapping_add(o0);
    out[2 * i + 1] = out[2 * i + 1].wrapping_add(o1);
}

#[hax_lib::requires(i < 8 && out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_binomials_use_cache(
    a: &PortableVector,
    b: &PortableVector,
    i: usize,
    out: &mut [I32],
    cache: &PortableVector,
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = ai.as_i32().wrapping_mul(bi.as_i32());
    let aj_bj_zeta = aj.as_i32().wrapping_mul(cache.elements[i].as_i32());
    let ai_bi_aj_bj = ai_bi.wrapping_add(aj_bj_zeta);
    let o0 = ai_bi_aj_bj;

    let ai_bj = ai.as_i32().wrapping_mul(bj.as_i32());
    let aj_bi = aj.as_i32().wrapping_mul(bi.as_i32());
    let ai_bj_aj_bi = ai_bj.wrapping_add(aj_bi);
    let o1 = ai_bj_aj_bi;

    out[2 * i] = out[2 * i].wrapping_add(o0);
    out[2 * i + 1] = out[2 * i + 1].wrapping_add(o1);
}

#[hax_lib::requires(i < 8 && out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_binomials(
    a: &PortableVector,
    b: &PortableVector,
    zeta: FieldElementTimesMontgomeryR,
    i: usize,
    out: &mut [I32],
) {
    let ai = a.elements[2 * i];
    let bi = b.elements[2 * i];
    let aj = a.elements[2 * i + 1];
    let bj = b.elements[2 * i + 1];

    let ai_bi = ai.as_i32().wrapping_mul(bi.as_i32());
    let bj_zeta_ = bj.as_i32().wrapping_mul(zeta.as_i32());
    let bj_zeta = montgomery_reduce_element(bj_zeta_);
    let aj_bj_zeta = aj.as_i32().wrapping_mul(bj_zeta.as_i32());
    let ai_bi_aj_bj = ai_bi.wrapping_add(aj_bj_zeta);
    let o0 = ai_bi_aj_bj;

    let ai_bj = ai.as_i32().wrapping_mul(bj.as_i32());
    let aj_bi = aj.as_i32().wrapping_mul(bi.as_i32());
    let ai_bj_aj_bi = ai_bj.wrapping_add(aj_bi);
    let o1 = ai_bj_aj_bi;

    out[2 * i] = out[2 * i].wrapping_add(o0);
    out[2 * i + 1] = out[2 * i + 1].wrapping_add(o1);
}

#[hax_lib::requires(out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    let nzeta0 = zeta0.wrapping_neg();
    let nzeta1 = zeta1.wrapping_neg();
    let nzeta2 = zeta2.wrapping_neg();
    let nzeta3 = zeta3.wrapping_neg();
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta0.classify(), 0, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta0.classify(), 1, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta1.classify(), 2, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta1.classify(), 3, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta2.classify(), 4, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta2.classify(), 5, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, zeta3.classify(), 6, out);
    accumulating_ntt_multiply_binomials(lhs, rhs, nzeta3.classify(), 7, out);
}

#[hax_lib::requires(out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_fill_cache(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    cache: &mut PortableVector,
    zeta0: i16,
    zeta1: i16,
    zeta2: i16,
    zeta3: i16,
) {
    let nzeta0 = zeta0.wrapping_neg();
    let nzeta1 = zeta1.wrapping_neg();
    let nzeta2 = zeta2.wrapping_neg();
    let nzeta3 = zeta3.wrapping_neg();
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta0.classify(), 0, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta0.classify(), 1, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta1.classify(), 2, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta1.classify(), 3, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta2.classify(), 4, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta2.classify(), 5, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, zeta3.classify(), 6, out, cache);
    accumulating_ntt_multiply_binomials_fill_cache(lhs, rhs, nzeta3.classify(), 7, out, cache);
}

#[hax_lib::requires(out.len() >= 16)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
#[inline(always)]
pub(crate) fn accumulating_ntt_multiply_use_cache(
    lhs: &PortableVector,
    rhs: &PortableVector,
    out: &mut [I32],
    cache: &PortableVector,
) {
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 0, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 1, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 2, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 3, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 4, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 5, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 6, out, cache);
    accumulating_ntt_multiply_binomials_use_cache(lhs, rhs, 7, out, cache);
}
