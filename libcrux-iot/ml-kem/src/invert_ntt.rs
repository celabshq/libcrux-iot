use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{montgomery_multiply_fe, Operations, FIELD_ELEMENTS_IN_VECTOR},
};

#[hax_lib::requires(*zeta_i == 128)]
#[hax_lib::ensures(|_| *future(zeta_i) == 64)]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    for round in 0..16 {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 128 - i * 4);
        *zeta_i -= 1;

        Vector::inv_ntt_layer_1_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i - 1),
            zeta(*zeta_i - 2),
            zeta(*zeta_i - 3),
        );
        *zeta_i -= 3;
    }
}

#[hax_lib::requires(*zeta_i == 64)]
#[hax_lib::ensures(|_| *future(zeta_i) == 32)]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    for round in 0..16 {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 64 - i * 2);

        *zeta_i -= 1;

        Vector::inv_ntt_layer_2_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i - 1),
        );
        *zeta_i -= 1;
    }
}

#[hax_lib::requires(*zeta_i == 32)]
#[hax_lib::ensures(|_| *future(zeta_i) == 16)]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
) {
    for round in 0..16 {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 32 - i);

        *zeta_i -= 1;
        Vector::inv_ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
    }
}

#[hax_lib::requires(a < 16 && b < 16)]
#[inline(always)]
pub(crate) fn inv_ntt_layer_int_vec_step_reduce<Vector: Operations>(
    coefficients: &mut [Vector; VECTORS_IN_RING_ELEMENT],
    a: usize,
    b: usize,
    scratch: &mut Vector,
    zeta_r: i16,
) {
    *scratch = coefficients[a];
    Vector::add(scratch, &coefficients[b]);
    Vector::barrett_reduce(scratch);
    coefficients[a] = *scratch;

    Vector::negate(scratch);
    Vector::add(scratch, &coefficients[b]);
    Vector::add(scratch, &coefficients[b]);
    montgomery_multiply_fe::<Vector>(scratch, zeta_r);
    coefficients[b] = *scratch;
}

#[hax_lib::requires(
    layer >= 4 && layer <= 7 && *zeta_i == (1 << (8 - layer))
)]
#[inline(always)]
pub(crate) fn invert_ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut Vector,
) {
    let step = 1 << layer;
    let step_vec = step / FIELD_ELEMENTS_IN_VECTOR;

    for round in 0..(128 >> layer) {
        #[cfg(hax)]
        #[cfg(not(hax_backend_lean))]
        hax_lib::loop_invariant!(|round: usize| *zeta_i == (1 << (8 - layer)) - round);
        *zeta_i -= 1;

        let a_offset = round * 2 * step_vec;
        let b_offset = a_offset + step_vec;

        for j in 0..step_vec {
            #[cfg(hax)]
            #[cfg(not(hax_backend_lean))]
            hax_lib::loop_invariant!(|_: usize| *zeta_i == (1 << (8 - layer)) - round - 1);
            inv_ntt_layer_int_vec_step_reduce(
                &mut re.coefficients,
                a_offset + j,
                b_offset + j,
                scratch,
                zeta(*zeta_i),
            );
        }
    }
}

#[inline(always)]
pub(crate) fn invert_ntt_montgomery<const K: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    // We only ever call this function after matrix/vector multiplication
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() < (K as i16) * FIELD_MODULUS));

    let mut zeta_i = super::constants::COEFFICIENTS_IN_RING_ELEMENT / 2;

    invert_ntt_at_layer_1(&mut zeta_i, re);
    invert_ntt_at_layer_2(&mut zeta_i, re);
    invert_ntt_at_layer_3(&mut zeta_i, re);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch);
    invert_ntt_at_layer_4_plus(&mut zeta_i, re, 7, scratch);
}
