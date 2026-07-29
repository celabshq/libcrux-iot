use crate::{
    hax_utils::hax_debug_assert,
    polynomial::{zeta, PolynomialRingElement, VECTORS_IN_RING_ELEMENT},
    vector::{montgomery_multiply_fe, Operations},
};

#[hax_lib::requires(*zeta_i == 63)]
#[inline(always)]
pub(crate) fn ntt_at_layer_1<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 63 + i * 4);
        *zeta_i += 1;
        Vector::ntt_layer_1_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
            zeta(*zeta_i + 2),
            zeta(*zeta_i + 3),
        );
        *zeta_i += 3;
    }
}

#[hax_lib::requires(*zeta_i == 31)]
#[inline(always)]
pub(crate) fn ntt_at_layer_2<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 31 + i * 2);
        *zeta_i += 1;
        Vector::ntt_layer_2_step(
            &mut re.coefficients[round],
            zeta(*zeta_i),
            zeta(*zeta_i + 1),
        );
        *zeta_i += 1;
    }
}

#[hax_lib::requires(*zeta_i == 15)]
#[inline(always)]
pub(crate) fn ntt_at_layer_3<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    for round in 0..16 {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| *zeta_i == 15 + i);
        *zeta_i += 1;
        Vector::ntt_layer_3_step(&mut re.coefficients[round], zeta(*zeta_i));
    }
}

#[hax_lib::requires(a < 16 && b < 16)]
#[inline(always)]
fn ntt_layer_int_vec_step<Vector: Operations>(
    coefficients: &mut [Vector; VECTORS_IN_RING_ELEMENT],
    a: usize,
    b: usize,
    scratch: &mut Vector,
    zeta_r: i16,
) {
    *scratch = coefficients[b];
    montgomery_multiply_fe::<Vector>(scratch, zeta_r);
    coefficients[b] = coefficients[a];
    Vector::add(&mut coefficients[a], scratch);
    Vector::sub(&mut coefficients[b], scratch);
}

#[hax_lib::requires(
    layer >= 4 && layer <= 7 && *zeta_i == (1 << (7 - layer)) - 1 
)]
#[inline(always)]
pub(crate) fn ntt_at_layer_4_plus<Vector: Operations>(
    zeta_i: &mut usize,
    re: &mut PolynomialRingElement<Vector>,
    layer: usize,
    scratch: &mut Vector,
    _initial_coefficient_bound: usize, // This can be used for specifying the range of values allowed in re
) {
    let step = 1 << layer;
    let step_vec = step / 16; //FIELD_ELEMENTS_IN_VECTOR;

    for round in 0..(128 >> layer) {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|round: usize| *zeta_i == (1 << (7 - layer)) - 1 + round);
        *zeta_i += 1;

        let a_offset = round * 2 * step_vec;
        let b_offset = a_offset + step_vec;
        for j in 0..step_vec {
            #[cfg(hax)]
            hax_lib::loop_invariant!(|_: usize| *zeta_i == (1 << (7 - layer)) + round);
            ntt_layer_int_vec_step(
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
pub(crate) fn ntt_at_layer_7<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    let step = VECTORS_IN_RING_ELEMENT / 2;
    for j in 0..step {
        *scratch = re.coefficients[j + step];
        Vector::multiply_by_constant(scratch, -1600);
        re.coefficients[j + step] = re.coefficients[j];
        Vector::add(&mut re.coefficients[j], scratch);
        Vector::sub(&mut re.coefficients[j + step], scratch);
    }
}

#[inline(always)]
pub(crate) fn ntt_binomially_sampled_ring_element<Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    // Due to the small coefficient bound, we can skip the first round of
    // Montgomery reductions.
    ntt_at_layer_7(re, scratch);

    let mut zeta_i = 1;
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 11207);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 11207 + 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 11207 + 2 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 11207 + 3 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 11207 + 4 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 11207 + 5 * 3328);

    re.poly_barrett_reduce()
}

#[inline(always)]
pub(crate) fn ntt_vector_u<const VECTOR_U_COMPRESSION_FACTOR: usize, Vector: Operations>(
    re: &mut PolynomialRingElement<Vector>,
    scratch: &mut Vector,
) {
    hax_debug_assert!(to_i16_array(re)
        .into_iter()
        .all(|coefficient| coefficient.abs() <= 3328));

    let mut zeta_i = 0;

    ntt_at_layer_4_plus(&mut zeta_i, re, 7, scratch, 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 6, scratch, 2 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 5, scratch, 3 * 3328);
    ntt_at_layer_4_plus(&mut zeta_i, re, 4, scratch, 4 * 3328);
    ntt_at_layer_3(&mut zeta_i, re, 5 * 3328);
    ntt_at_layer_2(&mut zeta_i, re, 6 * 3328);
    ntt_at_layer_1(&mut zeta_i, re, 7 * 3328);

    re.poly_barrett_reduce()
}
