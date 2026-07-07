/*
 * SPDX-FileCopyrightText: 2025 Cryspen Sarl <info@cryspen.com>
 *
 * SPDX-License-Identifier: MIT or Apache-2.0
 *
 * This code was generated with the following revisions:
 * Charon: e656e17bff6ca5efac8ab6919b9b74cb9a8dd8ad
 * Eurydice: aaa9fa657fb6f09802edb890252040d94cd93982
 * Karamel: 8c19d41458ce5cbfea029ebc03334ba96d149039
 * F*: unset
 * Libcrux: 95a43e554866d4eb2db411c066ca0fb528eddbfd
 */

#include "internal/libcrux_iot_mlkem_portable.h"

#include "internal/libcrux_iot_core.h"
#include "internal/libcrux_iot_sha3.h"
#include "libcrux_iot_core.h"
#include "libcrux_iot_sha3.h"

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  sha512_ema(output, input);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  sha256_ema(output, input);
}

inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN(
    Eurydice_dst_ref_shared_b4 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len) {
  for (size_t i = (size_t)0U; i < input.meta; i++) {
    size_t i0 = i;
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        outputs,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * out_len, .end = (i0 + (size_t)1U) * out_len}));
    shake256_ema(uu____0, core_array___T__N___as_slice(
                              (size_t)33U, &input.ptr[i0], uint8_t,
                              Eurydice_borrow_slice_u8));
  }
}

KRML_MUSTINLINE Eurydice_arr_7b
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_dst_ref_shared_cf input) {
  Eurydice_arr_7b shake128_state;
  libcrux_iot_sha3_state_KeccakState repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_incremental_shake128_init();
  }
  memcpy(shake128_state.data, repeat_expression,
         (size_t)4U * sizeof(libcrux_iot_sha3_state_KeccakState));
  for (size_t i = (size_t)0U; i < input.meta; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &shake128_state.data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_31 lvalue =
        libcrux_secrets_int_public_integers_classify_27_78(input.ptr[i0]);
    libcrux_iot_sha3_incremental_shake128_absorb_final(
        uu____0, Eurydice_array_to_slice_shared_e9(&lvalue));
  }
  return shake128_state;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    Eurydice_arr_7b *state, Eurydice_dst_ref_mut_8c output) {
  for (size_t i = (size_t)0U; i < output.meta; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &state->data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_mut_borrow_slice_u8 lvalue = core_array___T__N___as_mut_slice(
        (size_t)504U, &output.ptr[i0], uint8_t, Eurydice_mut_borrow_slice_u8);
    libcrux_iot_sha3_incremental_shake128_squeeze_first_three_blocks(
        uu____0, libcrux_secrets_int_classify_public_classify_ref_mut_a1_75(
                     &lvalue)[0U]);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    Eurydice_arr_7b *state, Eurydice_dst_ref_mut_c3 output) {
  for (size_t i = (size_t)0U; i < output.meta; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_KeccakState *uu____0 = &state->data[i0];
    /* original Rust expression is not an lvalue in C */
    Eurydice_mut_borrow_slice_u8 lvalue = core_array___T__N___as_mut_slice(
        (size_t)168U, &output.ptr[i0], uint8_t, Eurydice_mut_borrow_slice_u8);
    libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
        uu____0, libcrux_secrets_int_classify_public_classify_ref_mut_a1_75(
                     &lvalue)[0U]);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_G_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_kem_hash_functions_portable_G(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_hash_functions_portable_H_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_kem_hash_functions_portable_H(input, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
inline void libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
    Eurydice_dst_ref_shared_b4 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len) {
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN(input, outputs, out_len);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE Eurydice_arr_7b
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
    Eurydice_dst_ref_shared_cf input) {
  return libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
      input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
    Eurydice_arr_7b *self, Eurydice_dst_ref_mut_8c output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
      self, output);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
    Eurydice_arr_7b *self, Eurydice_dst_ref_mut_c3 output) {
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
      self, output);
}

#define ZETAS_TIMES_MONTGOMERY_R                                              \
  ((KRML_CLITERAL(Eurydice_arr_34){                                           \
      .data = {-1044, -758,  -359,  -1517, 1493,  1422,  287,   202,   -171,  \
               622,   1577,  182,   962,   -1202, -1474, 1468,  573,   -1325, \
               264,   383,   -829,  1458,  -1602, -130,  -681,  1017,  732,   \
               608,   -1542, 411,   -205,  -1571, 1223,  652,   -552,  1015,  \
               -1293, 1491,  -282,  -1544, 516,   -8,    -320,  -666,  -1618, \
               -1162, 126,   1469,  -853,  -90,   -271,  830,   107,   -1421, \
               -247,  -951,  -398,  961,   -1508, -725,  448,   -1065, 677,   \
               -1275, -1103, 430,   555,   843,   -1251, 871,   1550,  105,   \
               422,   587,   177,   -235,  -291,  -460,  1574,  1653,  -246,  \
               778,   1159,  -147,  -777,  1483,  -602,  1119,  -1590, 644,   \
               -872,  349,   418,   329,   -156,  -75,   817,   1097,  603,   \
               610,   1322,  -1285, -1465, 384,   -1215, -136,  1218,  -1335, \
               -874,  220,   -1187, -1659, -1185, -1530, -1278, 794,   -1510, \
               -854,  -870,  478,   -108,  -308,  996,   991,   958,   -1460, \
               1522,  1628}}))

static KRML_MUSTINLINE int16_t zeta(size_t i) {
  return ZETAS_TIMES_MONTGOMERY_R.data[i];
}

#define VECTORS_IN_RING_ELEMENT                                \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / \
   LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR)

KRML_MUSTINLINE Eurydice_arr_d6
libcrux_iot_ml_kem_vector_portable_vector_type_zero(void) {
  return libcrux_secrets_int_public_integers_classify_27_4b0(
      (KRML_CLITERAL(Eurydice_arr_d6){.data = {0U}}));
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE Eurydice_arr_d6
libcrux_iot_ml_kem_vector_portable_ZERO_4e(void) {
  return libcrux_iot_ml_kem_vector_portable_vector_type_zero();
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_d6 *out) {
  Eurydice_slice_copy(Eurydice_array_to_slice_mut_8a(out),
                      Eurydice_slice_subslice_shared_a6(
                          array, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)0U, .end = (size_t)16U})),
                      int16_t);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(array, out);
}

/**
 Signed Montgomery Reduction

 Given an input `value`, `montgomery_reduce` outputs a representative `o`
 such that:

 - o ≡ value · MONTGOMERY_R^(-1) (mod FIELD_MODULUS)
 - the absolute value of `o` is bound as follows:

 `|result| ≤ ceil(|value| / MONTGOMERY_R) + 1665

 In particular, if `|value| ≤ FIELD_MODULUS-1 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS-1`. And, if `|value| ≤ pow2 16 * FIELD_MODULUS-1`, then `|o| <=
 FIELD_MODULUS + 1664

*/
int16_t libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
    int32_t value) {
  int32_t k = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(value)),
      libcrux_secrets_int_as_i32_b8(libcrux_secrets_int_public_integers_classify_27_df(
          LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R)));
  int32_t k_times_modulus = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(libcrux_secrets_int_as_i16_36(k)),
      libcrux_secrets_int_as_i32_f5(
          libcrux_secrets_int_public_integers_classify_27_39(
              LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
  int16_t c = libcrux_secrets_int_as_i16_36(
      k_times_modulus >>
      (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t value_high = libcrux_secrets_int_as_i16_36(
      value >>
      (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int16_t res = core_num__i16__wrapping_sub(value_high, c);
  return res;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_reducing_from_i32_array(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_d6 *out) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
            array.ptr[i0]);
    out->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_reducing_from_i32_array(array,
                                                                        out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_add(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    lhs->data[i0] = core_num__i16__wrapping_add(lhs->data[i0], rhs->data[i0]);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_add_4e(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_sub(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_sub(lhs->data[i0], rhs->data[i0]);
    lhs->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_sub_4e(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_sub(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_arithmetic_negate(
    Eurydice_arr_d6 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_neg(vec->data[i0]);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_negate_4e(
    Eurydice_arr_d6 *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_negate(vec);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    Eurydice_arr_d6 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = core_num__i16__wrapping_mul(vec->data[i0], c);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(
    Eurydice_arr_d6 *vec, int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(vec, c);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    Eurydice_arr_d6 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->data[uu____0] &= c;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
    Eurydice_arr_d6 *vec, int16_t c) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(vec,
                                                                          c);
}

/**
 Note: This function is not secret independent
 Only use with public values.
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    Eurydice_arr_d6 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    if (libcrux_secrets_int_public_integers_declassify_d8_39(vec->data[i0]) >=
        3329) {
      int16_t uu____0 = core_num__i16__wrapping_sub(vec->data[i0], 3329);
      vec->data[i0] = uu____0;
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
    Eurydice_arr_d6 *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(vec);
}

/**
 Signed Barrett Reduction

 Given an input `value`, `barrett_reduce` outputs a representative `result`
 such that:

 - result ≡ value (mod FIELD_MODULUS)
 - the absolute value of `result` is bound as follows:

 `|result| ≤ FIELD_MODULUS / 2 · (|value|/BARRETT_R + 1)

 Note: The input bound is 28296 to prevent overflow in the multiplication of
 quotient by FIELD_MODULUS

*/
KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value) {
  int32_t t = core_num__i32__wrapping_add(
      core_num__i32__wrapping_mul(
          libcrux_secrets_int_as_i32_f5(value),
          LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER),
      LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_R >> 1U);
  int16_t quotient = libcrux_secrets_int_as_i16_36(
      t >> (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT);
  int16_t uu____0 = value;
  int16_t result = core_num__i16__wrapping_sub(
      uu____0, core_num__i16__wrapping_mul(
                   quotient, LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS));
  return result;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(
    Eurydice_arr_d6 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t vi =
        libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
            vec->data[i0]);
    vec->data[i0] = vi;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(
    Eurydice_arr_d6 *vec) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(vec);
}

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer) {
  int32_t product = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(fe), libcrux_secrets_int_as_i32_f5(fer));
  return libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
      product);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_d6 *vec, int16_t c) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 =
        libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
            vec->data[i0], c);
    vec->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
    Eurydice_arr_d6 *vec, int16_t r) {
  libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
      vec, libcrux_secrets_int_public_integers_classify_27_39(r));
}

/**
 The `compress_*` functions implement the `Compress` function specified in the
 NIST FIPS 203 standard (Page 18, Expression 4.5), which is defined as:

 ```plaintext
 Compress_d: ℤq -> ℤ_{2ᵈ}
 Compress_d(x) = ⌈(2ᵈ/q)·x⌋
 ```

 Since `⌈x⌋ = ⌊x + 1/2⌋` we have:

 ```plaintext
 Compress_d(x) = ⌊(2ᵈ/q)·x + 1/2⌋
               = ⌊(2^{d+1}·x + q) / 2q⌋
 ```

 For further information about the function implementations, consult the
 `implementation_notes.pdf` document in this directory.

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
KRML_MUSTINLINE uint8_t
libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe) {
  int16_t shifted = core_num__i16__wrapping_sub(
      libcrux_secrets_int_public_integers_classify_27_39(1664),
      libcrux_secrets_int_as_i16_ca(fe));
  int16_t mask = shifted >> 15U;
  int16_t shifted_to_positive = mask ^ shifted;
  int16_t shifted_positive_in_range =
      core_num__i16__wrapping_sub(shifted_to_positive, 832);
  int16_t r0 = shifted_positive_in_range >> 15U;
  int16_t r1 = r0 & 1;
  return libcrux_secrets_int_as_u8_f5(r1);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_compress_1(
    Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_59(
        libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
            libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_compress_1_4e(
    Eurydice_arr_d6 *a) {
  libcrux_iot_ml_kem_vector_portable_compress_compress_1(a);
}

KRML_MUSTINLINE uint32_t
libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value) {
  uint32_t uu____0 = value;
  return uu____0 & core_num__u32__wrapping_sub(1U << (uint32_t)n, 1U);
}

KRML_MUSTINLINE int16_t
libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe) {
  uint64_t compressed = libcrux_secrets_int_as_u64_ca(fe)
                        << (uint32_t)coefficient_bits;
  compressed = core_num__u64__wrapping_add(compressed, 1664ULL);
  compressed = core_num__u64__wrapping_mul(compressed, 10321340ULL);
  compressed >>= 35U;
  return libcrux_secrets_int_as_i16_b8(
      libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
          coefficient_bits, libcrux_secrets_int_as_u32_a3(compressed)));
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(
    Eurydice_arr_d6 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t t =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          vec->data[j],
          libcrux_secrets_int_public_integers_classify_27_39(zeta));
  int16_t a_minus_t = core_num__i16__wrapping_sub(vec->data[i], t);
  int16_t a_plus_t = core_num__i16__wrapping_add(vec->data[i], t);
  vec->data[j] = a_minus_t;
  vec->data[i] = a_plus_t;
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)2U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)3U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)4U,
                                                  (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)5U,
                                                  (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)8U,
                                                  (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta2, (size_t)9U,
                                                  (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)12U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta3, (size_t)13U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(a, zeta0, zeta1,
                                                          zeta2, zeta3);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)0U,
                                                  (size_t)4U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)1U,
                                                  (size_t)5U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)2U,
                                                  (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta0, (size_t)3U,
                                                  (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)8U,
                                                  (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)9U,
                                                  (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)10U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta1, (size_t)11U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    Eurydice_arr_d6 *vec, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)0U,
                                                  (size_t)8U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)1U,
                                                  (size_t)9U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)2U,
                                                  (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)3U,
                                                  (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)4U,
                                                  (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)5U,
                                                  (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)6U,
                                                  (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(vec, zeta, (size_t)7U,
                                                  (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(
    Eurydice_arr_d6 *vec, int16_t zeta, size_t i, size_t j) {
  int16_t a_minus_b = core_num__i16__wrapping_sub(vec->data[j], vec->data[i]);
  int16_t a_plus_b = core_num__i16__wrapping_add(vec->data[j], vec->data[i]);
  int16_t o0 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
          a_plus_b);
  int16_t o1 =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_39(zeta));
  vec->data[i] = o0;
  vec->data[j] = o1;
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                      (size_t)2U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                      (size_t)3U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)4U,
                                                      (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)5U,
                                                      (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)8U,
                                                      (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta2, (size_t)9U,
                                                      (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)12U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta3, (size_t)13U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(a, zeta0, zeta1,
                                                              zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)0U,
                                                      (size_t)4U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)1U,
                                                      (size_t)5U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)2U,
                                                      (size_t)6U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta0, (size_t)3U,
                                                      (size_t)7U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)8U,
                                                      (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)9U,
                                                      (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)10U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta1, (size_t)11U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(a, zeta0, zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    Eurydice_arr_d6 *vec, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)0U,
                                                      (size_t)8U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)1U,
                                                      (size_t)9U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)2U,
                                                      (size_t)10U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)3U,
                                                      (size_t)11U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)4U,
                                                      (size_t)12U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)5U,
                                                      (size_t)13U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)6U,
                                                      (size_t)14U);
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(vec, zeta, (size_t)7U,
                                                      (size_t)15U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta) {
  libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(a, zeta);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_83 out) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t bj_zeta_ = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(bj), libcrux_secrets_int_as_i32_f5(zeta));
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  int32_t aj_bj_zeta =
      core_num__i32__wrapping_mul(libcrux_secrets_int_as_i32_f5(aj),
                                  libcrux_secrets_int_as_i32_f5(bj_zeta));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  out.ptr[(size_t)2U * i] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i], o0);
  out.ptr[(size_t)2U * i + (size_t)1U] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i + (size_t)1U], o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  int16_t nzeta0 = core_num__i16__wrapping_neg(zeta0);
  int16_t nzeta1 = core_num__i16__wrapping_neg(zeta1);
  int16_t nzeta2 = core_num__i16__wrapping_neg(zeta2);
  int16_t nzeta3 = core_num__i16__wrapping_neg(zeta3);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, out);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, out);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
      lhs, rhs, out, zeta0, zeta1, zeta2, zeta3);
}

/**
 Compute the product of two Kyber binomials with respect to the
 modulus `X² - zeta`.

 This function almost implements <strong>Algorithm 11</strong> of the
 NIST FIPS 203 standard, which is reproduced below:

 ```plaintext
 Input:  a₀, a₁, b₀, b₁ ∈ ℤq.
 Input: γ ∈ ℤq.
 Output: c₀, c₁ ∈ ℤq.

 c₀ ← a₀·b₀ + a₁·b₁·γ
 c₁ ← a₀·b₁ + a₁·b₀
 return c₀, c₁
 ```
 We say "almost" because the coefficients output by this function are in
 the Montgomery domain (unlike in the specification).

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t bj_zeta_ = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(bj), libcrux_secrets_int_as_i32_f5(zeta));
  int16_t bj_zeta =
      libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_reduce_element(
          bj_zeta_);
  cache->data[i] = bj_zeta;
  int32_t aj_bj_zeta =
      core_num__i32__wrapping_mul(libcrux_secrets_int_as_i32_f5(aj),
                                  libcrux_secrets_int_as_i32_f5(bj_zeta));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  out.ptr[(size_t)2U * i] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i], o0);
  out.ptr[(size_t)2U * i + (size_t)1U] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i + (size_t)1U], o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  int16_t nzeta0 = core_num__i16__wrapping_neg(zeta0);
  int16_t nzeta1 = core_num__i16__wrapping_neg(zeta1);
  int16_t nzeta2 = core_num__i16__wrapping_neg(zeta2);
  int16_t nzeta3 = core_num__i16__wrapping_neg(zeta3);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta0),
      (size_t)0U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta0),
      (size_t)1U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta1),
      (size_t)2U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta1),
      (size_t)3U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta2),
      (size_t)4U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta2),
      (size_t)5U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(zeta3),
      (size_t)6U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
      lhs, rhs, libcrux_secrets_int_public_integers_classify_27_39(nzeta3),
      (size_t)7U, out, cache);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
      lhs, rhs, out, cache, zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, size_t i,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache) {
  int16_t ai = a->data[(size_t)2U * i];
  int16_t bi = b->data[(size_t)2U * i];
  int16_t aj = a->data[(size_t)2U * i + (size_t)1U];
  int16_t bj = b->data[(size_t)2U * i + (size_t)1U];
  int32_t ai_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bi));
  int32_t aj_bj_zeta = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj),
      libcrux_secrets_int_as_i32_f5(cache->data[i]));
  int32_t ai_bi_aj_bj = core_num__i32__wrapping_add(ai_bi, aj_bj_zeta);
  int32_t o0 = ai_bi_aj_bj;
  int32_t ai_bj = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(ai), libcrux_secrets_int_as_i32_f5(bj));
  int32_t aj_bi = core_num__i32__wrapping_mul(
      libcrux_secrets_int_as_i32_f5(aj), libcrux_secrets_int_as_i32_f5(bi));
  int32_t ai_bj_aj_bi = core_num__i32__wrapping_add(ai_bj, aj_bi);
  int32_t o1 = ai_bj_aj_bi;
  out.ptr[(size_t)2U * i] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i], o0);
  out.ptr[(size_t)2U * i + (size_t)1U] =
      core_num__i32__wrapping_add(out.ptr[(size_t)2U * i + (size_t)1U], o1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)0U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)1U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)2U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)3U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)4U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)5U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)6U, out, cache);
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
      lhs, rhs, (size_t)7U, out, cache);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache) {
  libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
      lhs, rhs, out, cache);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  out.ptr[0U] =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->data[0U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[1U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[2U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[3U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[4U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[5U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[6U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[7U]) << 7U;
  out.ptr[1U] =
      (((((((uint32_t)libcrux_secrets_int_as_u8_f5(v->data[8U]) |
            (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[9U]) << 1U) |
           (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[10U]) << 2U) |
          (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[11U]) << 3U) |
         (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[12U]) << 4U) |
        (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[13U]) << 5U) |
       (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[14U]) << 6U) |
      (uint32_t)libcrux_secrets_int_as_u8_f5(v->data[15U]) << 7U;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(a, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_borrow_slice_u8 v, Eurydice_arr_d6 *out) {
  out->data[0U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] & 1U);
  out->data[1U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 1U & 1U);
  out->data[2U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 2U & 1U);
  out->data[3U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 3U & 1U);
  out->data[4U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 4U & 1U);
  out->data[5U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 5U & 1U);
  out->data[6U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 6U & 1U);
  out->data[7U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[0U] >> 7U & 1U);
  out->data[8U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] & 1U);
  out->data[9U] = libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 1U & 1U);
  out->data[10U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 2U & 1U);
  out->data[11U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 3U & 1U);
  out->data[12U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 4U & 1U);
  out->data[13U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 5U & 1U);
  out->data[14U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 6U & 1U);
  out->data[15U] =
      libcrux_secrets_int_as_i16_59((uint32_t)v.ptr[1U] >> 7U & 1U);
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(a, out);
}

KRML_MUSTINLINE uint8_t_x4
libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t result0 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[1U]) << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[0U]);
  uint8_t result1 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[3U]) << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[2U]);
  uint8_t result2 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[5U]) << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[4U]);
  uint8_t result3 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[7U]) << 4U |
                    (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[6U]);
  return (KRML_CLITERAL(uint8_t_x4){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(result0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(result1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(result2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(result3)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x4 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  out.ptr[0U] = uu____0.fst;
  out.ptr[1U] = uu____1;
  out.ptr[2U] = uu____2;
  out.ptr[3U] = uu____3;
  uint8_t_x4 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
  uint8_t uu____5 = uu____4.snd;
  uint8_t uu____6 = uu____4.thd;
  uint8_t uu____7 = uu____4.f3;
  out.ptr[4U] = uu____4.fst;
  out.ptr[5U] = uu____5;
  out.ptr[6U] = uu____6;
  out.ptr[7U] = uu____7;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[0U] & 15U);
  int16_t v1 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[0U] >> 4U & 15U);
  int16_t v2 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[1U] & 15U);
  int16_t v3 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[1U] >> 4U & 15U);
  int16_t v4 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[2U] & 15U);
  int16_t v5 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[2U] >> 4U & 15U);
  int16_t v6 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[3U] & 15U);
  int16_t v7 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[3U] >> 4U & 15U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = (size_t)4U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)4U, .end = (size_t)8U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(a), out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(
      v.ptr[0U] | (int16_t)((uint32_t)v.ptr[1U] << 5U));
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      (v.ptr[1U] >> 3U | (int16_t)((uint32_t)v.ptr[2U] << 2U)) |
      (int16_t)((uint32_t)v.ptr[3U] << 7U));
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(
      v.ptr[3U] >> 1U | (int16_t)((uint32_t)v.ptr[4U] << 4U));
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(
      (v.ptr[4U] >> 4U | (int16_t)((uint32_t)v.ptr[5U] << 1U)) |
      (int16_t)((uint32_t)v.ptr[6U] << 6U));
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(
      v.ptr[6U] >> 2U | (int16_t)((uint32_t)v.ptr[7U] << 3U));
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  out.ptr[0U] = uu____0.fst;
  out.ptr[1U] = uu____1;
  out.ptr[2U] = uu____2;
  out.ptr[3U] = uu____3;
  out.ptr[4U] = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  out.ptr[5U] = uu____5.fst;
  out.ptr[6U] = uu____6;
  out.ptr[7U] = uu____7;
  out.ptr[8U] = uu____8;
  out.ptr[9U] = uu____9;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t v0 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[0U] & 31U);
  int16_t v1 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)bytes.ptr[1U] & 3U) << 3U | (uint32_t)bytes.ptr[0U] >> 5U);
  int16_t v2 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[1U] >> 2U & 31U);
  int16_t v3 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)bytes.ptr[2U] & 15U) << 1U | (uint32_t)bytes.ptr[1U] >> 7U);
  int16_t v4 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)bytes.ptr[3U] & 1U) << 4U | (uint32_t)bytes.ptr[2U] >> 4U);
  int16_t v5 =
      libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[3U] >> 1U & 31U);
  int16_t v6 = libcrux_secrets_int_as_i16_59(
      ((uint32_t)bytes.ptr[4U] & 7U) << 2U | (uint32_t)bytes.ptr[3U] >> 6U);
  int16_t v7 = libcrux_secrets_int_as_i16_59((uint32_t)bytes.ptr[4U] >> 3U);
  return (KRML_CLITERAL(int16_t_x8){.fst = v0,
                                    .snd = v1,
                                    .thd = v2,
                                    .f3 = v3,
                                    .f4 = v4,
                                    .f5 = v5,
                                    .f6 = v6,
                                    .f7 = v7});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = (size_t)5U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)5U, .end = (size_t)10U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(a), out);
}

KRML_MUSTINLINE uint8_t_x5
libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(v.ptr[0U] & 255);
  uint8_t r1 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[1U] & 63) << 2U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[0U] >> 8U & 3);
  uint8_t r2 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[2U] & 15) << 4U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[1U] >> 6U & 15);
  uint8_t r3 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[3U] & 3) << 6U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[2U] >> 4U & 63);
  uint8_t r4 = libcrux_secrets_int_as_u8_f5(v.ptr[3U] >> 2U & 255);
  return (KRML_CLITERAL(uint8_t_x5){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x5 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                         .end = (size_t)4U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  out.ptr[0U] = uu____0.fst;
  out.ptr[1U] = uu____1;
  out.ptr[2U] = uu____2;
  out.ptr[3U] = uu____3;
  out.ptr[4U] = uu____4;
  uint8_t_x5 uu____5 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)4U,
                                                         .end = (size_t)8U})));
  uint8_t uu____6 = uu____5.snd;
  uint8_t uu____7 = uu____5.thd;
  uint8_t uu____8 = uu____5.f3;
  uint8_t uu____9 = uu____5.f4;
  out.ptr[5U] = uu____5.fst;
  out.ptr[6U] = uu____6;
  out.ptr[7U] = uu____7;
  out.ptr[8U] = uu____8;
  out.ptr[9U] = uu____9;
  uint8_t_x5 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)8U,
                                                         .end = (size_t)12U})));
  uint8_t uu____11 = uu____10.snd;
  uint8_t uu____12 = uu____10.thd;
  uint8_t uu____13 = uu____10.f3;
  uint8_t uu____14 = uu____10.f4;
  out.ptr[10U] = uu____10.fst;
  out.ptr[11U] = uu____11;
  out.ptr[12U] = uu____12;
  out.ptr[13U] = uu____13;
  out.ptr[14U] = uu____14;
  uint8_t_x5 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)12U,
                                                         .end = (size_t)16U})));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  uint8_t uu____18 = uu____15.f3;
  uint8_t uu____19 = uu____15.f4;
  out.ptr[15U] = uu____15.fst;
  out.ptr[16U] = uu____16;
  out.ptr[17U] = uu____17;
  out.ptr[18U] = uu____18;
  out.ptr[19U] = uu____19;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t r0 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[1U]) & 3)
                << 8U) |
      (libcrux_secrets_int_as_i16_59(bytes.ptr[0U]) & 255));
  int16_t r1 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[2U]) & 15)
                << 6U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[1U]) >> 2U);
  int16_t r2 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[3U]) & 63)
                << 4U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[2U]) >> 4U);
  int16_t r3 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)libcrux_secrets_int_as_i16_59(bytes.ptr[4U]) << 2U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[3U]) >> 6U);
  int16_t r4 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[6U]) & 3)
                << 8U) |
      (libcrux_secrets_int_as_i16_59(bytes.ptr[5U]) & 255));
  int16_t r5 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[7U]) & 15)
                << 6U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[6U]) >> 2U);
  int16_t r6 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[8U]) & 63)
                << 4U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[7U]) >> 4U);
  int16_t r7 = libcrux_secrets_int_as_i16_f5(
      (int16_t)((uint32_t)libcrux_secrets_int_as_i16_59(bytes.ptr[9U]) << 2U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[8U]) >> 6U);
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = (size_t)10U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)10U, .end = (size_t)20U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(a), out);
}

KRML_MUSTINLINE uint8_t_x11
libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(v.ptr[0U]);
  uint8_t r1 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[1U] & 31) << 3U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[0U] >> 8U);
  uint8_t r2 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[2U] & 3) << 6U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[1U] >> 5U);
  uint8_t r3 = libcrux_secrets_int_as_u8_f5(v.ptr[2U] >> 2U & 255);
  uint8_t r4 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[3U] & 127) << 1U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[2U] >> 10U);
  uint8_t r5 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[4U] & 15) << 4U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[3U] >> 7U);
  uint8_t r6 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[5U] & 1) << 7U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[4U] >> 4U);
  uint8_t r7 = libcrux_secrets_int_as_u8_f5(v.ptr[5U] >> 1U & 255);
  uint8_t r8 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[6U] & 63) << 2U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[5U] >> 9U);
  uint8_t r9 = (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[7U] & 7) << 5U |
               (uint32_t)libcrux_secrets_int_as_u8_f5(v.ptr[6U] >> 6U);
  uint8_t r10 = libcrux_secrets_int_as_u8_f5(v.ptr[7U] >> 3U);
  return (KRML_CLITERAL(uint8_t_x11){
      .fst = libcrux_secrets_int_public_integers_declassify_d8_90(r0),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_90(r1),
      .thd = libcrux_secrets_int_public_integers_declassify_d8_90(r2),
      .f3 = libcrux_secrets_int_public_integers_declassify_d8_90(r3),
      .f4 = libcrux_secrets_int_public_integers_declassify_d8_90(r4),
      .f5 = libcrux_secrets_int_public_integers_declassify_d8_90(r5),
      .f6 = libcrux_secrets_int_public_integers_declassify_d8_90(r6),
      .f7 = libcrux_secrets_int_public_integers_declassify_d8_90(r7),
      .f8 = libcrux_secrets_int_public_integers_declassify_d8_90(r8),
      .f9 = libcrux_secrets_int_public_integers_declassify_d8_90(r9),
      .f10 = libcrux_secrets_int_public_integers_declassify_d8_90(r10)});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x11 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                         .end = (size_t)8U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  uint8_t uu____3 = uu____0.f3;
  uint8_t uu____4 = uu____0.f4;
  uint8_t uu____5 = uu____0.f5;
  uint8_t uu____6 = uu____0.f6;
  uint8_t uu____7 = uu____0.f7;
  uint8_t uu____8 = uu____0.f8;
  uint8_t uu____9 = uu____0.f9;
  uint8_t uu____10 = uu____0.f10;
  out.ptr[0U] = uu____0.fst;
  out.ptr[1U] = uu____1;
  out.ptr[2U] = uu____2;
  out.ptr[3U] = uu____3;
  out.ptr[4U] = uu____4;
  out.ptr[5U] = uu____5;
  out.ptr[6U] = uu____6;
  out.ptr[7U] = uu____7;
  out.ptr[8U] = uu____8;
  out.ptr[9U] = uu____9;
  out.ptr[10U] = uu____10;
  uint8_t_x11 uu____11 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)8U,
                                                         .end = (size_t)16U})));
  uint8_t uu____12 = uu____11.snd;
  uint8_t uu____13 = uu____11.thd;
  uint8_t uu____14 = uu____11.f3;
  uint8_t uu____15 = uu____11.f4;
  uint8_t uu____16 = uu____11.f5;
  uint8_t uu____17 = uu____11.f6;
  uint8_t uu____18 = uu____11.f7;
  uint8_t uu____19 = uu____11.f8;
  uint8_t uu____20 = uu____11.f9;
  uint8_t uu____21 = uu____11.f10;
  out.ptr[11U] = uu____11.fst;
  out.ptr[12U] = uu____12;
  out.ptr[13U] = uu____13;
  out.ptr[14U] = uu____14;
  out.ptr[15U] = uu____15;
  out.ptr[16U] = uu____16;
  out.ptr[17U] = uu____17;
  out.ptr[18U] = uu____18;
  out.ptr[19U] = uu____19;
  out.ptr[20U] = uu____20;
  out.ptr[21U] = uu____21;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(a, out);
}

KRML_MUSTINLINE int16_t_x8
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t r0 =
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[1U]) & 7)
                << 8U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[0U]);
  int16_t r1 =
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[2U]) & 63)
                << 5U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[1U]) >> 3U;
  int16_t r2 =
      ((int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[4U]) & 1)
                 << 10U) |
       (int16_t)((uint32_t)libcrux_secrets_int_as_i16_59(bytes.ptr[3U])
                 << 2U)) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[2U]) >> 6U;
  int16_t r3 =
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[5U]) & 15)
                << 7U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[4U]) >> 1U;
  int16_t r4 =
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[6U]) & 127)
                << 4U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[5U]) >> 4U;
  int16_t r5 =
      ((int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[8U]) & 3)
                 << 9U) |
       (int16_t)((uint32_t)libcrux_secrets_int_as_i16_59(bytes.ptr[7U])
                 << 1U)) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[6U]) >> 7U;
  int16_t r6 =
      (int16_t)((uint32_t)(libcrux_secrets_int_as_i16_59(bytes.ptr[9U]) & 31)
                << 6U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[8U]) >> 2U;
  int16_t r7 =
      (int16_t)((uint32_t)libcrux_secrets_int_as_i16_59(bytes.ptr[10U]) << 3U) |
      libcrux_secrets_int_as_i16_59(bytes.ptr[9U]) >> 5U;
  return (KRML_CLITERAL(int16_t_x8){.fst = r0,
                                    .snd = r1,
                                    .thd = r2,
                                    .f3 = r3,
                                    .f4 = r4,
                                    .f5 = r5,
                                    .f6 = r6,
                                    .f7 = r7});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out) {
  int16_t_x8 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = (size_t)11U})));
  int16_t uu____1 = uu____0.snd;
  int16_t uu____2 = uu____0.thd;
  int16_t uu____3 = uu____0.f3;
  int16_t uu____4 = uu____0.f4;
  int16_t uu____5 = uu____0.f5;
  int16_t uu____6 = uu____0.f6;
  int16_t uu____7 = uu____0.f7;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  out->data[2U] = uu____2;
  out->data[3U] = uu____3;
  out->data[4U] = uu____4;
  out->data[5U] = uu____5;
  out->data[6U] = uu____6;
  out->data[7U] = uu____7;
  int16_t_x8 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)11U, .end = (size_t)22U})));
  int16_t uu____9 = uu____8.snd;
  int16_t uu____10 = uu____8.thd;
  int16_t uu____11 = uu____8.f3;
  int16_t uu____12 = uu____8.f4;
  int16_t uu____13 = uu____8.f5;
  int16_t uu____14 = uu____8.f6;
  int16_t uu____15 = uu____8.f7;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  out->data[10U] = uu____10;
  out->data[11U] = uu____11;
  out->data[12U] = uu____12;
  out->data[13U] = uu____13;
  out->data[14U] = uu____14;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(a), out);
}

KRML_MUSTINLINE uint8_t_x3
libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_borrow_slice_i16 v) {
  uint8_t r0 = libcrux_secrets_int_as_u8_f5(v.ptr[0U] & 255);
  uint8_t r1 = libcrux_secrets_int_as_u8_f5(
      v.ptr[0U] >> 8U | (int16_t)((uint32_t)(v.ptr[1U] & 15) << 4U));
  uint8_t r2 = libcrux_secrets_int_as_u8_f5(v.ptr[1U] >> 4U & 255);
  return (KRML_CLITERAL(uint8_t_x3){.fst = r0, .snd = r1, .thd = r2});
}

KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out) {
  uint8_t_x3 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)0U,
                                                         .end = (size_t)2U})));
  uint8_t uu____1 = uu____0.snd;
  uint8_t uu____2 = uu____0.thd;
  out.ptr[0U] = uu____0.fst;
  out.ptr[1U] = uu____1;
  out.ptr[2U] = uu____2;
  uint8_t_x3 uu____3 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)2U,
                                                         .end = (size_t)4U})));
  uint8_t uu____4 = uu____3.snd;
  uint8_t uu____5 = uu____3.thd;
  out.ptr[3U] = uu____3.fst;
  out.ptr[4U] = uu____4;
  out.ptr[5U] = uu____5;
  uint8_t_x3 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)4U,
                                                         .end = (size_t)6U})));
  uint8_t uu____7 = uu____6.snd;
  uint8_t uu____8 = uu____6.thd;
  out.ptr[6U] = uu____6.fst;
  out.ptr[7U] = uu____7;
  out.ptr[8U] = uu____8;
  uint8_t_x3 uu____9 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)6U,
                                                         .end = (size_t)8U})));
  uint8_t uu____10 = uu____9.snd;
  uint8_t uu____11 = uu____9.thd;
  out.ptr[9U] = uu____9.fst;
  out.ptr[10U] = uu____10;
  out.ptr[11U] = uu____11;
  uint8_t_x3 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)8U,
                                                         .end = (size_t)10U})));
  uint8_t uu____13 = uu____12.snd;
  uint8_t uu____14 = uu____12.thd;
  out.ptr[12U] = uu____12.fst;
  out.ptr[13U] = uu____13;
  out.ptr[14U] = uu____14;
  uint8_t_x3 uu____15 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)10U,
                                                         .end = (size_t)12U})));
  uint8_t uu____16 = uu____15.snd;
  uint8_t uu____17 = uu____15.thd;
  out.ptr[15U] = uu____15.fst;
  out.ptr[16U] = uu____16;
  out.ptr[17U] = uu____17;
  uint8_t_x3 uu____18 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)12U,
                                                         .end = (size_t)14U})));
  uint8_t uu____19 = uu____18.snd;
  uint8_t uu____20 = uu____18.thd;
  out.ptr[18U] = uu____18.fst;
  out.ptr[19U] = uu____19;
  out.ptr[20U] = uu____20;
  uint8_t_x3 uu____21 =
      libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
          Eurydice_array_to_subslice_shared_e7(
              v, (KRML_CLITERAL(core_ops_range_Range_87){.start = (size_t)14U,
                                                         .end = (size_t)16U})));
  uint8_t uu____22 = uu____21.snd;
  uint8_t uu____23 = uu____21.thd;
  out.ptr[21U] = uu____21.fst;
  out.ptr[22U] = uu____22;
  out.ptr[23U] = uu____23;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(a, out);
}

KRML_MUSTINLINE int16_t_x2
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_borrow_slice_u8 bytes) {
  int16_t byte0 = libcrux_secrets_int_as_i16_59(bytes.ptr[0U]);
  int16_t byte1 = libcrux_secrets_int_as_i16_59(bytes.ptr[1U]);
  int16_t byte2 = libcrux_secrets_int_as_i16_59(bytes.ptr[2U]);
  int16_t r0 = (int16_t)((uint32_t)(byte1 & 15) << 8U) | (byte0 & 255);
  int16_t r1 = (int16_t)((uint32_t)byte2 << 4U) | (byte1 >> 4U & 15);
  return (KRML_CLITERAL(int16_t_x2){.fst = r0, .snd = r1});
}

KRML_MUSTINLINE void
libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out) {
  int16_t_x2 uu____0 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = (size_t)3U})));
  int16_t uu____1 = uu____0.snd;
  out->data[0U] = uu____0.fst;
  out->data[1U] = uu____1;
  int16_t_x2 uu____2 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)3U, .end = (size_t)6U})));
  int16_t uu____3 = uu____2.snd;
  out->data[2U] = uu____2.fst;
  out->data[3U] = uu____3;
  int16_t_x2 uu____4 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)6U, .end = (size_t)9U})));
  int16_t uu____5 = uu____4.snd;
  out->data[4U] = uu____4.fst;
  out->data[5U] = uu____5;
  int16_t_x2 uu____6 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)9U, .end = (size_t)12U})));
  int16_t uu____7 = uu____6.snd;
  out->data[6U] = uu____6.fst;
  out->data[7U] = uu____7;
  int16_t_x2 uu____8 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)12U, .end = (size_t)15U})));
  int16_t uu____9 = uu____8.snd;
  out->data[8U] = uu____8.fst;
  out->data[9U] = uu____9;
  int16_t_x2 uu____10 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)15U, .end = (size_t)18U})));
  int16_t uu____11 = uu____10.snd;
  out->data[10U] = uu____10.fst;
  out->data[11U] = uu____11;
  int16_t_x2 uu____12 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)18U, .end = (size_t)21U})));
  int16_t uu____13 = uu____12.snd;
  out->data[12U] = uu____12.fst;
  out->data[13U] = uu____13;
  int16_t_x2 uu____14 =
      libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
          Eurydice_slice_subslice_shared_c8(
              bytes, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)21U, .end = (size_t)24U})));
  int16_t uu____15 = uu____14.snd;
  out->data[14U] = uu____14.fst;
  out->data[15U] = uu____15;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE void libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out) {
  libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(a, out);
}

KRML_MUSTINLINE size_t libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < a.meta / (size_t)3U; i++) {
    size_t i0 = i;
    int16_t b1 = (int16_t)(uint32_t)a.ptr[i0 * (size_t)3U + (size_t)0U];
    int16_t b2 = (int16_t)(uint32_t)a.ptr[i0 * (size_t)3U + (size_t)1U];
    int16_t b3 = (int16_t)(uint32_t)a.ptr[i0 * (size_t)3U + (size_t)2U];
    int16_t d1 = (int16_t)((uint32_t)(b2 & 15) << 8U) | b1;
    int16_t d2 = (int16_t)((uint32_t)b3 << 4U) | b2 >> 4U;
    if (d1 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        out.ptr[sampled] = d1;
        sampled++;
      }
    }
    if (d2 < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS) {
      if (sampled < (size_t)16U) {
        out.ptr[sampled] = d2;
        sampled++;
      }
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
KRML_MUSTINLINE size_t libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out) {
  return libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(a, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
inline Eurydice_arr_d6 libcrux_iot_ml_kem_vector_portable_vector_type_clone_9c(
    const Eurydice_arr_d6 *self) {
  return self[0U];
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- $16size_t
*/
typedef struct arr_fd_s {
  Eurydice_arr_d6 data[16U];
} arr_fd;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
with const generics
- $4size_t
*/
typedef struct arr_51_s {
  arr_fd data[4U];
} arr_51;

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.ZERO_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static arr_fd ZERO_64_a7(void) {
  arr_fd lit;
  Eurydice_arr_d6 repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  }
  memcpy(lit.data, repeat_expression, (size_t)16U * sizeof(Eurydice_arr_d6));
  return lit;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.validate_public_key.call_mut_42 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static arr_fd call_mut_42_df(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12, size_t

*/
typedef struct dst_ref_mut_2f_s {
  arr_fd *ptr;
  size_t meta;
} dst_ref_mut_2f;

/**
 Only use with public values.

 This MUST NOT be used with secret inputs, like its caller
 `deserialize_ring_elements_reduced`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_to_reduced_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_to_reduced_ring_element_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes, &re->data[i0]);
    libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(&re->data[i0]);
  }
}

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_3d(
    Eurydice_borrow_slice_u8 public_key, dst_ref_mut_2f deserialized_pk) {
  Eurydice_borrow_slice_u8 public_key0 =
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key);
  for (size_t i = (size_t)0U;
       i <
       public_key0.meta / LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_c8(
        public_key0,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(ring_element,
                                           &deserialized_pk.ptr[i0]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 4
*/
static dst_ref_mut_2f array_to_slice_mut_a10(arr_51 *a) {
  dst_ref_mut_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void shift_right_ef(Eurydice_arr_d6 *vec) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    vec->data[uu____0] >>= (uint32_t)15;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.shift_right_4e
with const generics
- SHIFT_BY= 15
*/
static KRML_MUSTINLINE void shift_right_4e_ef(Eurydice_arr_d6 *vec) {
  shift_right_ef(vec);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.to_unsigned_representative with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void to_unsigned_representative_a7(
    const Eurydice_arr_d6 *a, Eurydice_arr_d6 *out) {
  out[0U] = a[0U];
  shift_right_4e_ef(out);
  libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
      out, LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS);
  libcrux_iot_ml_kem_vector_portable_add_4e(out, a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.to_unsigned_field_modulus
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void to_unsigned_field_modulus_a7(
    const Eurydice_arr_d6 *a, Eurydice_arr_d6 *out) {
  to_unsigned_representative_a7(a, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.serialize_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void serialize_uncompressed_ring_element_a7(
    const arr_fd *re, Eurydice_arr_d6 *scratch,
    Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)24U * i0,
                                     .end = (size_t)24U * i0 + (size_t)24U})));
  }
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void serialize_vector_3d(
    const arr_51 *key, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    arr_fd re = key->data[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice_mut_c8(
            out,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})));
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE void serialize_public_key_mut_df(
    const arr_51 *t_as_ntt, Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 serialized, Eurydice_arr_d6 *scratch) {
  /* original Rust expression is not an lvalue in C */
  Eurydice_mut_borrow_slice_u8 lvalue = Eurydice_slice_subslice_mut_c8(
      serialized,
      (KRML_CLITERAL(core_ops_range_Range_87){
          .start = (size_t)0U,
          .end = libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U)}));
  serialize_vector_3d(
      t_as_ntt,
      libcrux_secrets_int_classify_public_classify_ref_mut_a1_75(&lvalue)[0U],
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from_mut_6d(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)4U)),
      seed_for_a, uint8_t);
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_df(
    const Eurydice_arr_d1 *public_key) {
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_42_df(&lvalue);
  }
  arr_51 deserialized_pk = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 = Eurydice_array_to_subslice_to_shared_213(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U));
  deserialize_ring_elements_reduced_3d(
      uu____0, array_to_slice_mut_a10(&deserialized_pk));
  Eurydice_arr_d1 public_key_serialized = {.data = {0U}};
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  const arr_51 *uu____1 = &deserialized_pk;
  Eurydice_borrow_slice_u8 uu____2 = Eurydice_array_to_subslice_from_shared_5f4(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)4U));
  serialize_public_key_mut_df(
      uu____1, uu____2, Eurydice_array_to_slice_mut_b5(&public_key_serialized),
      &scratch);
  return Eurydice_array_eq((size_t)1568U, public_key, &public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_2f(
    const Eurydice_arr_a8 *private_key) {
  Eurydice_arr_ec t;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(t.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice_shared_d49(
          private_key, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = (size_t)384U * (size_t)4U,
                           .end = (size_t)768U * (size_t)4U + (size_t)32U})),
      Eurydice_array_to_slice_mut_01(&t));
  Eurydice_borrow_slice_u8 expected =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          Eurydice_array_to_subslice_shared_d49(
              private_key,
              (KRML_CLITERAL(core_ops_range_Range_87){
                  .start = (size_t)768U * (size_t)4U + (size_t)32U,
                  .end = (size_t)768U * (size_t)4U + (size_t)64U})));
  /* original Rust expression is not an lvalue in C */
  Eurydice_borrow_slice_u8 lvalue =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)32U, &t, uint8_t,
                                       Eurydice_borrow_slice_u8));
  return Eurydice_slice_eq_shared(&lvalue, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_75(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_2f(private_key);
}

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE arr_51 default_1e_3d(void) {
  arr_51 lit;
  arr_fd repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.data, repeat_expression, (size_t)4U * sizeof(arr_fd));
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
with const generics
- $16size_t
*/
typedef struct arr_8b_s {
  arr_fd data[16U];
} arr_8b;

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $4size_t
- $16size_t
*/
typedef struct IndCpaPublicKeyUnpacked_31_s {
  arr_51 t_as_ntt;
  Eurydice_arr_ec seed_for_A;
  arr_8b A;
} IndCpaPublicKeyUnpacked_31;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- K_SQUARED= 16
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_31 default_1f_df(void) {
  arr_51 uu____0;
  arr_fd repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = ZERO_64_a7();
  }
  memcpy(uu____0.data, repeat_expression0, (size_t)4U * sizeof(arr_fd));
  Eurydice_arr_ec uu____1 = {.data = {0U}};
  IndCpaPublicKeyUnpacked_31 lit;
  lit.t_as_ntt = uu____0;
  lit.seed_for_A = uu____1;
  arr_fd repeat_expression[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.A.data, repeat_expression, (size_t)16U * sizeof(arr_fd));
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.cpa_keygen_seed_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void cpa_keygen_seed_cc_3e(
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_fa seed;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d42(
          &seed,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE})),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      libcrux_secrets_int_public_integers_classify_27_90((uint8_t)(size_t)4U);
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_b5(&seed), out);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 16
*/
static dst_ref_mut_2f array_to_slice_mut_a13(arr_8b *a) {
  dst_ref_mut_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_df(
    Eurydice_dst_ref_shared_8c randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_79 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d42(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_df0(
    Eurydice_dst_ref_shared_c3 randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_c5 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d43(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_from_xof_ee2(
    Eurydice_dst_ref_shared_cf seeds,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  Eurydice_arr_7b xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_7c randomness = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_9c randomness_blocksize = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_eb2(&randomness));
  bool done = sample_from_uniform_distribution_next_df(
      Eurydice_array_to_slice_shared_eb2(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_1b2(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_df0(
          Eurydice_array_to_slice_shared_1b2(&randomness_blocksize),
          sampled_coefficients, out);
    }
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.from_i16_array_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void from_i16_array_64_a7(Eurydice_borrow_slice_i16 a,
                                                 arr_fd *out) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
        Eurydice_slice_subslice_shared_a6(
            a, (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = i0 * (size_t)16U,
                   .end = (i0 + (size_t)1U) * (size_t)16U})),
        &out->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_A
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void sample_matrix_A_ee1(dst_ref_mut_2f A_transpose,
                                                const Eurydice_arr_31 *seed,
                                                bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    Eurydice_arr_560 seeds;
    Eurydice_arr_31 repeat_expression[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression[i] = seed[0U];
    }
    memcpy(seeds.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_31));
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      seeds.data[j].data[32U] = (uint8_t)i1;
      seeds.data[j].data[33U] = (uint8_t)j;
    }
    Eurydice_arr_cc sampled_coefficients = {.data = {0U}};
    Eurydice_arr_24 out = {
        .data = {
            {.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
    sample_from_xof_ee2(Eurydice_array_to_slice_shared_6e2(&seeds),
                        Eurydice_array_to_slice_mut_4e(&sampled_coefficients),
                        Eurydice_array_to_slice_mut_f22(&out));
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      Eurydice_arr_5b sample = out.data[j];
      if (transpose) {
        Eurydice_borrow_slice_i16 uu____0 =
            libcrux_secrets_int_classify_public_classify_ref_6d_39(
                Eurydice_array_to_subslice_to_shared_a9(&sample, (size_t)256U));
        from_i16_array_64_a7(uu____0, &A_transpose.ptr[j * (size_t)4U + i1]);
      } else {
        Eurydice_borrow_slice_i16 uu____1 =
            libcrux_secrets_int_classify_public_classify_ref_6d_39(
                Eurydice_array_to_subslice_to_shared_a9(&sample, (size_t)256U));
        from_i16_array_64_a7(uu____1, &A_transpose.ptr[i1 * (size_t)4U + j]);
      }
    }
  }
}

/**
 Given a series of uniformly random bytes in `randomness`, for some number
 `eta`, the `sample_from_binomial_distribution_{eta}` functions sample a ring
 element from a binomial distribution centered at 0 that uses two sets of `eta`
 coin flips. If, for example, `eta = ETA`, each ring coefficient is a value `v`
 such such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:

 ```plaintext
 - If v < 0, Pr[v] = Pr[-v]
 - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
 ```

 The values `v < 0` are mapped to the appropriate `KyberFieldElement`.

 The expected value is:

 ```plaintext
 E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1]
 + (ETA)Pr[ETA] = 0 since Pr[-v] = Pr[v] when v < 0.
 ```

 And the variance is:

 ```plaintext
 Var(X) = E[(X - E[X])^2]
        = E[X^2]
        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) /
 2^(2 * ETA)) = ETA / 2
 ```

 This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203
 standard, which is reproduced below:

 ```plaintext
 Input: byte array B ∈ 𝔹^{64η}.
 Output: array f ∈ ℤ₂₅₆.

 b ← BytesToBits(B)
 for (i ← 0; i < 256; i++)
     x ← ∑(j=0 to η - 1) b[2iη + j]
     y ← ∑(j=0 to η - 1) b[2iη + η + j]
     f[i] ← x−y mod q
 end for
 return f
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_binomial_distribution_2 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void sample_from_binomial_distribution_2_a7(
    Eurydice_borrow_slice_u8 randomness, Eurydice_arr_04 *sampled_i16s) {
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)4U; i++) {
    size_t chunk_number = i;
    Eurydice_borrow_slice_u8 byte_chunk = Eurydice_slice_subslice_shared_c8(
        randomness, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = chunk_number * (size_t)4U,
                        .end = chunk_number * (size_t)4U + (size_t)4U}));
    uint32_t random_bits_as_u32 =
        ((libcrux_secrets_int_as_u32_59(byte_chunk.ptr[0U]) |
          libcrux_secrets_int_as_u32_59(byte_chunk.ptr[1U]) << 8U) |
         libcrux_secrets_int_as_u32_59(byte_chunk.ptr[2U]) << 16U) |
        libcrux_secrets_int_as_u32_59(byte_chunk.ptr[3U]) << 24U;
    uint32_t even_bits =
        random_bits_as_u32 &
        libcrux_secrets_int_public_integers_classify_27_df(1431655765U);
    uint32_t odd_bits =
        random_bits_as_u32 >> 1U &
        libcrux_secrets_int_public_integers_classify_27_df(1431655765U);
    uint32_t coin_toss_outcomes =
        core_num__u32__wrapping_add(even_bits, odd_bits);
    uint32_t outcome_set = 0U;
    uint32_t step = 4U;
    uint32_t end = 32U;
    bool first_iter = true;
    while (true) {
      if (first_iter) {
        first_iter = false;
        if (outcome_set >= end) {
          break;
        }
        int16_t outcome_1 = libcrux_secrets_int_as_i16_b8(
            coin_toss_outcomes >> (uint32_t)outcome_set &
            libcrux_secrets_int_public_integers_classify_27_df(3U));
        int16_t outcome_2 = libcrux_secrets_int_as_i16_b8(
            coin_toss_outcomes >>
                (uint32_t)core_num__u32__wrapping_add(outcome_set, 2U) &
            libcrux_secrets_int_public_integers_classify_27_df(3U));
        size_t offset = (size_t)(outcome_set >> 2U);
        int16_t uu____0 = core_num__i16__wrapping_sub(outcome_1, outcome_2);
        sampled_i16s->data[(size_t)8U * chunk_number + offset] = uu____0;
      } else {
        core_option_Option_7e uu____1 =
            core_num__u32__checked_add(outcome_set, step);
        if (uu____1.tag == core_option_None) {
          break;
        }
        uint32_t v = uu____1.f0;
        outcome_set = v;
        first_iter = false;
        if (outcome_set >= end) {
          break;
        }
        int16_t outcome_1 = libcrux_secrets_int_as_i16_b8(
            coin_toss_outcomes >> (uint32_t)outcome_set &
            libcrux_secrets_int_public_integers_classify_27_df(3U));
        int16_t outcome_2 = libcrux_secrets_int_as_i16_b8(
            coin_toss_outcomes >>
                (uint32_t)core_num__u32__wrapping_add(outcome_set, 2U) &
            libcrux_secrets_int_public_integers_classify_27_df(3U));
        size_t offset = (size_t)(outcome_set >> 2U);
        int16_t uu____2 = core_num__i16__wrapping_sub(outcome_1, outcome_2);
        sampled_i16s->data[(size_t)8U * chunk_number + offset] = uu____2;
      }
    }
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_binomial_distribution with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- ETA= 2
*/
static KRML_MUSTINLINE void sample_from_binomial_distribution_6e(
    Eurydice_borrow_slice_u8 randomness, Eurydice_arr_04 *output) {
  sample_from_binomial_distribution_2_a7(randomness, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_7
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_7_a7(arr_fd *re,
                                              Eurydice_arr_d6 *scratch) {
  size_t step = VECTORS_IN_RING_ELEMENT / (size_t)2U;
  for (size_t i = (size_t)0U; i < step; i++) {
    size_t j = i;
    scratch[0U] = re->data[j + step];
    libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(scratch, -1600);
    re->data[j + step] = re->data[j];
    libcrux_iot_ml_kem_vector_portable_add_4e(&re->data[j], scratch);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&re->data[j + step], scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void montgomery_multiply_fe_a7(Eurydice_arr_d6 *v,
                                                      int16_t fer) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(v, fer);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_layer_int_vec_step_a7(arr_fd *coefficients,
                                                      size_t a, size_t b,
                                                      Eurydice_arr_d6 *scratch,
                                                      int16_t zeta_r) {
  scratch[0U] = coefficients->data[b];
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients->data[b] = coefficients->data[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(&coefficients->data[a], scratch);
  libcrux_iot_ml_kem_vector_portable_sub_4e(&coefficients->data[b], scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_4_plus_a7(size_t *zeta_i, arr_fd *re,
                                                   size_t layer,
                                                   Eurydice_arr_d6 *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec = step / (size_t)16U;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U]++;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      ntt_layer_int_vec_step_a7(re, a_offset + j, b_offset + j, scratch,
                                zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_3_a7(size_t *zeta_i, arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]++;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(&re->data[round],
                                                           zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_2_a7(size_t *zeta_i, arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]++;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] + (size_t)1U));
    zeta_i[0U]++;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void ntt_at_layer_1_a7(size_t *zeta_i, arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]++;
    libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] + (size_t)1U),
        zeta(zeta_i[0U] + (size_t)2U), zeta(zeta_i[0U] + (size_t)3U));
    zeta_i[0U] += (size_t)3U;
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.poly_barrett_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void poly_barrett_reduce_64_a7(arr_fd *self) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void ntt_binomially_sampled_ring_element_a7(
    arr_fd *re, Eurydice_arr_d6 *scratch) {
  ntt_at_layer_7_a7(re, scratch);
  size_t zeta_i = (size_t)1U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 512
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b21(
    dst_ref_mut_2f re_as_ntt, const Eurydice_arr_fa *prf_input,
    uint8_t domain_separator, Eurydice_arr_d6 *scratch) {
  Eurydice_arr_890 prf_inputs;
  Eurydice_arr_fa repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)33U, prf_input, uint8_t, Eurydice_arr_fa);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_fa));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_23(&prf_inputs, domain_separator);
  Eurydice_arr_56 prf_outputs;
  uint8_t repeat_expression1[512U];
  for (size_t i = (size_t)0U; i < (size_t)512U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression1, (size_t)512U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice_shared_041(&prf_inputs),
      Eurydice_array_to_slice_mut_92(&prf_outputs), (size_t)128U);
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_d48(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = i1 * (size_t)128U,
                          .end = (i1 + (size_t)1U) * (size_t)128U}));
    Eurydice_arr_04 sample_buffer;
    int16_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_39(0);
    }
    memcpy(sample_buffer.data, repeat_expression,
           (size_t)256U * sizeof(int16_t));
    sample_from_binomial_distribution_6e(randomness, &sample_buffer);
    from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(&sample_buffer),
                         &re_as_ntt.ptr[i1]);
    ntt_binomially_sampled_ring_element_a7(&re_as_ntt.ptr[i1], scratch);
  }
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_iot_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_58 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static arr_fd call_mut_58_9f1(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12, size_t

*/
typedef struct dst_ref_shared_2f_s {
  const arr_fd *ptr;
  size_t meta;
} dst_ref_shared_2f;

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static const arr_fd *entry_3d(dst_ref_shared_2f matrix, size_t i, size_t j) {
  return &matrix.ptr[i * (size_t)4U + j];
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_fill_cache_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_fill_cache_64_a7(
    const arr_fd *self, const arr_fd *rhs, Eurydice_arr_6c *accumulator,
    arr_fd *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_44(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_87){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
        &cache->data[i0], zeta((size_t)64U + (size_t)4U * i0),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)1U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)2U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.reducing_from_i32_array_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void reducing_from_i32_array_64_a7(
    Eurydice_dst_ref_shared_83 a, arr_fd *out) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
        Eurydice_slice_subslice_shared_47(
            a, (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = i0 * (size_t)16U,
                   .end = (i0 + (size_t)1U) * (size_t)16U})),
        &out->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.to_standard_domain
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void to_standard_domain_a7(Eurydice_arr_d6 *v) {
  libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
      v,
      LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS);
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.add_standard_error_reduce_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void add_standard_error_reduce_64_a7(
    arr_fd *self, const arr_fd *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    to_standard_domain_a7(&self->data[j]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&self->data[j], &error->data[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[j]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_use_cache_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_use_cache_64_a7(
    const arr_fd *self, const arr_fd *rhs, Eurydice_arr_6c *accumulator,
    const arr_fd *cache) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_44(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_87){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
        &cache->data[i0]);
  }
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_As_plus_e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_As_plus_e_3d(
    arr_51 *t_as_ntt, dst_ref_shared_2f matrix_A, const arr_51 *s_as_ntt,
    const arr_51 *error_as_ntt, arr_51 *s_cache, Eurydice_arr_6c *accumulator) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t j = i;
    accumulating_ntt_multiply_fill_cache_64_a7(
        entry_3d(matrix_A, (size_t)0U, j), &s_as_ntt->data[j], accumulator,
        &s_cache->data[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                t_as_ntt->data);
  add_standard_error_reduce_64_a7(t_as_ntt->data, error_as_ntt->data);
  for (size_t i0 = (size_t)1U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
    Eurydice_arr_6c lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____0;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      accumulating_ntt_multiply_use_cache_64_a7(entry_3d(matrix_A, i1, j),
                                                &s_as_ntt->data[j], accumulator,
                                                &s_cache->data[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_af(accumulator), &t_as_ntt->data[i1]);
    add_standard_error_reduce_64_a7(&t_as_ntt->data[i1],
                                    &error_as_ntt->data[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 16
*/
static dst_ref_shared_2f array_to_slice_shared_a13(const arr_8b *a) {
  dst_ref_shared_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_9f1(
    Eurydice_borrow_slice_u8 key_generation_seed, arr_51 *private_key,
    IndCpaPublicKeyUnpacked_31 *public_key, arr_fd *scratch, arr_51 *s_cache,
    Eurydice_arr_6c *accumulator) {
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  cpa_keygen_seed_cc_3e(key_generation_seed,
                        Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_17(&hashed), (size_t)32U, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_A = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_for_secret_and_error = uu____0.snd;
  dst_ref_mut_2f uu____1 = array_to_slice_mut_a13(&public_key->A);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_31 lvalue0 =
      libcrux_secrets_int_public_integers_declassify_d8_78(
          libcrux_iot_ml_kem_utils_into_padded_array_de(seed_for_A));
  sample_matrix_A_ee1(uu____1, &lvalue0, true);
  Eurydice_arr_fa prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_29(seed_for_secret_and_error);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_b21(
      array_to_slice_mut_a10(private_key), &prf_input, 0U, scratch->data);
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_58_9f1(&lvalue);
  }
  arr_51 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_b21(array_to_slice_mut_a10(&error_as_ntt),
                                 &prf_input, domain_separator, scratch->data);
  compute_As_plus_e_3d(&public_key->t_as_ntt,
                       array_to_slice_shared_a13(&public_key->A),
                       &private_key[0U], &error_as_ntt, s_cache, accumulator);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_slice_mut_01(&public_key->seed_for_A);
  Eurydice_slice_copy(
      uu____2,
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_A),
      uint8_t);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.serialize_unpacked_secret_key with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- K_SQUARED= 16
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
static void serialize_unpacked_secret_key_eb(
    const IndCpaPublicKeyUnpacked_31 *public_key, const arr_51 *private_key,
    Eurydice_mut_borrow_slice_u8 serialized_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_d6 *scratch) {
  serialize_public_key_mut_df(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice_shared_01(&public_key->seed_for_A),
      serialized_public_key, scratch);
  serialize_vector_3d(private_key, serialized_private_key, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- PRIVATE_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static KRML_MUSTINLINE void generate_keypair_e51(
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 serialized_ind_cpa_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key, arr_fd *scratch,
    arr_51 *s_cache, Eurydice_arr_6c *accumulator) {
  arr_51 private_key = default_1e_3d();
  IndCpaPublicKeyUnpacked_31 public_key = default_1f_df();
  generate_keypair_unpacked_9f1(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_eb(&public_key, &private_key,
                                   serialized_ind_cpa_private_key,
                                   serialized_public_key, scratch->data);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.serialize_kem_secret_key_mut with types
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- SERIALIZED_KEY_LEN= 3168
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_2f(
    Eurydice_borrow_slice_u8 private_key, Eurydice_borrow_slice_u8 public_key,
    Eurydice_borrow_slice_u8 implicit_rejection_value,
    Eurydice_arr_a8 *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d48(
                          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                          .start = pointer,
                                          .end = pointer + private_key.meta})),
                      private_key, uint8_t);
  pointer += private_key.meta;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d48(
          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = pointer, .end = pointer + public_key.meta})),
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key),
      uint8_t);
  pointer += public_key.meta;
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key),
      Eurydice_array_to_subslice_mut_d48(
          serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = pointer,
              .end = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE})));
  pointer += LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d48(
          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = pointer,
                          .end = pointer + implicit_rejection_value.meta})),
      implicit_rejection_value, uint8_t);
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_3f
libcrux_iot_ml_kem_ind_cca_generate_keypair_de1(
    const Eurydice_arr_c7 *randomness) {
  Eurydice_borrow_slice_u8 ind_cpa_keypair_randomness =
      Eurydice_array_to_subslice_shared_d45(
          randomness,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}));
  Eurydice_borrow_slice_u8 implicit_rejection_value =
      Eurydice_array_to_subslice_from_shared_5f0(
          randomness,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE);
  Eurydice_arr_d1 public_key = {.data = {0U}};
  Eurydice_arr_a8 secret_key_serialized;
  uint8_t repeat_expression0[3168U];
  for (size_t i = (size_t)0U; i < (size_t)3168U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(secret_key_serialized.data, repeat_expression0,
         (size_t)3168U * sizeof(uint8_t));
  Eurydice_arr_df ind_cpa_private_key;
  uint8_t repeat_expression1[1536U];
  for (size_t i = (size_t)0U; i < (size_t)1536U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(ind_cpa_private_key.data, repeat_expression1,
         (size_t)1536U * sizeof(uint8_t));
  arr_fd scratch = ZERO_64_a7();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_51 s_cache;
  arr_fd repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(s_cache.data, repeat_expression, (size_t)4U * sizeof(arr_fd));
  generate_keypair_e51(ind_cpa_keypair_randomness,
                       Eurydice_array_to_slice_mut_2f(&ind_cpa_private_key),
                       Eurydice_array_to_slice_mut_b5(&public_key), &scratch,
                       &s_cache, &accumulator);
  serialize_kem_secret_key_mut_2f(
      Eurydice_array_to_slice_shared_2f(&ind_cpa_private_key),
      Eurydice_array_to_slice_shared_b50(&public_key), implicit_rejection_value,
      &secret_key_serialized);
  Eurydice_arr_a8 private_key =
      libcrux_iot_ml_kem_types_from_c2_0e(secret_key_serialized);
  return libcrux_iot_ml_kem_types_from_d9_70(
      private_key, libcrux_iot_ml_kem_types_from_08_d9(public_key));
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.entropy_preprocess_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
*/
static KRML_MUSTINLINE void entropy_preprocess_cc_3e(
    Eurydice_borrow_slice_u8 randomness, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate.call_mut_92
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static arr_fd call_mut_92_fe1(void **_) { return ZERO_64_a7(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_6f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static arr_fd call_mut_6f_841(void **_) { return ZERO_64_a7(); }

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 512
*/
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b21(
    const Eurydice_arr_fa *prf_input, uint8_t domain_separator,
    dst_ref_mut_2f error_1, Eurydice_arr_04 *sample_buffer) {
  Eurydice_arr_890 prf_inputs;
  Eurydice_arr_fa repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)33U, prf_input, uint8_t, Eurydice_arr_fa);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_fa));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_23(&prf_inputs, domain_separator);
  Eurydice_arr_56 prf_outputs;
  uint8_t repeat_expression[512U];
  for (size_t i = (size_t)0U; i < (size_t)512U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression, (size_t)512U * sizeof(uint8_t));
  Eurydice_dst_ref_shared_b4 uu____0 = core_array___T__N___as_slice(
      (size_t)4U, &prf_inputs, Eurydice_arr_fa, Eurydice_dst_ref_shared_b4);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice_mut_92(&prf_outputs), (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_d48(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = i0 * (size_t)128U,
                          .end = (i0 + (size_t)1U) * (size_t)128U}));
    sample_from_binomial_distribution_6e(randomness, sample_buffer);
    from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(sample_buffer),
                         &error_1.ptr[i0]);
  }
  return domain_separator;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_ec(Eurydice_borrow_slice_u8 input,
                                   Eurydice_mut_borrow_slice_u8 out) {
  shake256_ema(out, input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF_07
with const generics
- LEN= 128
*/
static KRML_MUSTINLINE void PRF_07_ec(Eurydice_borrow_slice_u8 input,
                                      Eurydice_mut_borrow_slice_u8 out) {
  PRF_ec(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_33
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static arr_fd call_mut_33_841(void **_) { return ZERO_64_a7(); }

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 1
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_6a(
    Eurydice_dst_ref_shared_8c randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)1U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_79 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d42(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 1
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_6a0(
    Eurydice_dst_ref_shared_c3 randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)1U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_c5 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d43(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)1U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 1
*/
static KRML_MUSTINLINE void sample_from_xof_ee(
    Eurydice_dst_ref_shared_cf seeds,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  Eurydice_arr_7b xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_d8 randomness = {.data = {{.data = {0U}}}};
  Eurydice_arr_88 randomness_blocksize = {.data = {{.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_eb(&randomness));
  bool done = sample_from_uniform_distribution_next_6a(
      Eurydice_array_to_slice_shared_eb(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_1b(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_6a0(
          Eurydice_array_to_slice_shared_1b(&randomness_blocksize),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics

*/
static KRML_MUSTINLINE void sample_matrix_entry_36(
    arr_fd *out, Eurydice_borrow_slice_u8 seed, size_t i, size_t j) {
  Eurydice_arr_31 seed_ij = {.data = {0U}};
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d43(
          &seed_ij, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = (size_t)0U, .end = (size_t)32U})),
      seed, uint8_t);
  seed_ij.data[32U] = (uint8_t)i;
  seed_ij.data[33U] = (uint8_t)j;
  Eurydice_arr_58 sampled_coefficients = {.data = {0U}};
  Eurydice_arr_28 out_raw = {.data = {{.data = {0U}}}};
  Eurydice_arr_f4 uu____0 = {.data = {seed_ij}};
  sample_from_xof_ee(Eurydice_array_to_slice_shared_6e(&uu____0),
                     Eurydice_array_to_slice_mut_31(&sampled_coefficients),
                     Eurydice_array_to_slice_mut_f2(&out_raw));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_5b lvalue =
      libcrux_secrets_int_public_integers_classify_27_19(out_raw.data[0U]);
  from_i16_array_64_a7(
      core_array___T__N___as_slice((size_t)272U, &lvalue, int16_t,
                                   Eurydice_borrow_slice_i16),
      out);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_1_a7(size_t *zeta_i,
                                                     arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]--;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] - (size_t)1U),
        zeta(zeta_i[0U] - (size_t)2U), zeta(zeta_i[0U] - (size_t)3U));
    zeta_i[0U] -= (size_t)3U;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_2_a7(size_t *zeta_i,
                                                     arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]--;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
        &re->data[round], zeta(zeta_i[0U]), zeta(zeta_i[0U] - (size_t)1U));
    zeta_i[0U]--;
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_3_a7(size_t *zeta_i,
                                                     arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t round = i;
    zeta_i[0U]--;
    libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
        &re->data[round], zeta(zeta_i[0U]));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void inv_ntt_layer_int_vec_step_reduce_a7(
    arr_fd *coefficients, size_t a, size_t b, Eurydice_arr_d6 *scratch,
    int16_t zeta_r) {
  scratch[0U] = coefficients->data[a];
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(scratch);
  coefficients->data[a] = scratch[0U];
  libcrux_iot_ml_kem_vector_portable_negate_4e(scratch);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &coefficients->data[b]);
  montgomery_multiply_fe_a7(scratch, zeta_r);
  coefficients->data[b] = scratch[0U];
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void invert_ntt_at_layer_4_plus_a7(
    size_t *zeta_i, arr_fd *re, size_t layer, Eurydice_arr_d6 *scratch) {
  size_t step = (size_t)1U << (uint32_t)layer;
  size_t step_vec =
      step / LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR;
  for (size_t i0 = (size_t)0U; i0 < (size_t)128U >> (uint32_t)layer; i0++) {
    size_t round = i0;
    zeta_i[0U]--;
    size_t a_offset = round * (size_t)2U * step_vec;
    size_t b_offset = a_offset + step_vec;
    for (size_t i = (size_t)0U; i < step_vec; i++) {
      size_t j = i;
      inv_ntt_layer_int_vec_step_reduce_a7(re, a_offset + j, b_offset + j,
                                           scratch, zeta(zeta_i[0U]));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_3d(arr_fd *re,
                                                     Eurydice_arr_d6 *scratch) {
  size_t zeta_i =
      LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_a7(&zeta_i, re);
  invert_ntt_at_layer_2_a7(&zeta_i, re);
  invert_ntt_at_layer_3_a7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.add_error_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void add_error_reduce_64_a7(arr_fd *self,
                                                   const arr_fd *error) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t j = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &self->data[j], 1441);
    libcrux_iot_ml_kem_vector_portable_add_4e(&self->data[j], &error->data[j]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&self->data[j]);
  }
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_vector_u_ee1(
    arr_fd *matrix_entry, Eurydice_borrow_slice_u8 seed,
    dst_ref_shared_2f r_as_ntt, dst_ref_shared_2f error_1,
    dst_ref_mut_2f result, Eurydice_arr_d6 *scratch, dst_ref_mut_2f cache,
    Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit0;
  int32_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] = uu____0;
  }
  memcpy(lit0.data, repeat_expression0, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit0;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t j = i;
    sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
    accumulating_ntt_multiply_fill_cache_64_a7(matrix_entry, &r_as_ntt.ptr[j],
                                               accumulator, &cache.ptr[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result.ptr);
  invert_ntt_montgomery_3d(result.ptr, scratch);
  add_error_reduce_64_a7(result.ptr, &error_1.ptr[0U]);
  for (size_t i0 = (size_t)1U; i0 < (size_t)4U; i0++) {
    size_t i1 = i0;
    int32_t uu____1 = libcrux_secrets_int_public_integers_classify_27_a8(0);
    Eurydice_arr_6c lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____1;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, i1, j);
      accumulating_ntt_multiply_use_cache_64_a7(matrix_entry, &r_as_ntt.ptr[j],
                                                accumulator, &cache.ptr[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_af(accumulator), &result.ptr[i1]);
    invert_ntt_montgomery_3d(&result.ptr[i1], scratch);
    add_error_reduce_64_a7(&result.ptr[i1], &error_1.ptr[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 4
*/
static dst_ref_shared_2f array_to_slice_shared_a10(const arr_51 *a) {
  dst_ref_shared_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void compress_ef(Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)10, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void compress_4e_ef(Eurydice_arr_d6 *a) {
  compress_ef(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void compress_c4(Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)11, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void compress_4e_c4(Eurydice_arr_d6 *a) {
  compress_c4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_11 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- BLOCK_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_11_3f(
    const arr_fd *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re->data[i0], scratch);
    compress_4e_c4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)22U * i0,
                                     .end = (size_t)22U * i0 + (size_t)22U})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_4c(
    const arr_fd *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  compress_then_serialize_11_3f(re, serialized, scratch);
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
*/
static KRML_MUSTINLINE void compress_then_serialize_u_eb(
    arr_51 input, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    arr_fd re = input.data[i0];
    compress_then_serialize_ring_element_u_4c(
        &re,
        Eurydice_slice_subslice_mut_c8(
            out, (KRML_CLITERAL(core_ops_range_Range_87){
                     .start = i0 * ((size_t)1408U / (size_t)4U),
                     .end = (i0 + (size_t)1U) * ((size_t)1408U / (size_t)4U)})),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- C1_LEN= 1408
- U_COMPRESSION_FACTOR= 11
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static KRML_MUSTINLINE void encrypt_c1_841(
    Eurydice_borrow_slice_u8 randomness, arr_fd *matrix_entry,
    Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 ciphertext, dst_ref_mut_2f r_as_ntt,
    arr_fd *error_2, Eurydice_arr_d6 *scratch, dst_ref_mut_2f cache,
    Eurydice_arr_6c *accumulator) {
  Eurydice_arr_fa prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_29(randomness);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b21(r_as_ntt, &prf_input, 0U, scratch);
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_6f_841(&lvalue);
  }
  arr_51 error_1 = arr_struct;
  Eurydice_arr_04 sampling_buffer;
  int16_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_39(0);
  }
  memcpy(sampling_buffer.data, repeat_expression0,
         (size_t)256U * sizeof(int16_t));
  uint8_t domain_separator0 = sample_ring_element_cbd_b21(
      &prf_input, domain_separator, array_to_slice_mut_a10(&error_1),
      &sampling_buffer);
  prf_input.data[32U] =
      libcrux_secrets_int_public_integers_classify_27_90(domain_separator0);
  Eurydice_arr_89 prf_output;
  uint8_t repeat_expression[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_output.data, repeat_expression, (size_t)128U * sizeof(uint8_t));
  PRF_07_ec(Eurydice_array_to_slice_shared_b5(&prf_input),
            Eurydice_array_to_slice_mut_78(&prf_output));
  sample_from_binomial_distribution_6e(
      Eurydice_array_to_slice_shared_78(&prf_output), &sampling_buffer);
  from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(&sampling_buffer),
                       error_2);
  arr_51 arr_struct0;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct0.data[i] = call_mut_33_841(&lvalue);
  }
  arr_51 u = arr_struct0;
  compute_vector_u_ee1(matrix_entry, seed_for_a,
                       (KRML_CLITERAL(dst_ref_shared_2f){
                           .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                       array_to_slice_shared_a10(&error_1),
                       array_to_slice_mut_a10(&u), scratch, cache, accumulator);
  compress_then_serialize_u_eb(u, ciphertext, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.traits.decompress_1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void decompress_1_a7(Eurydice_arr_d6 *vec) {
  libcrux_iot_ml_kem_vector_portable_negate_4e(vec);
  libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(vec, 1665);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_message with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_message_a7(
    const Eurydice_arr_ec *serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
        Eurydice_array_to_subslice_shared_d44(
            serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = (size_t)2U * i0,
                            .end = (size_t)2U * i0 + (size_t)2U})),
        &re->data[i0]);
    decompress_1_a7(&re->data[i0]);
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.add_message_error_reduce_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void add_message_error_reduce_64_a7(
    const arr_fd *self, const arr_fd *message, arr_fd *result,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &result->data[i0], 1441);
    scratch[0U] = self->data[i0];
    libcrux_iot_ml_kem_vector_portable_add_4e(scratch, &message->data[i0]);
    libcrux_iot_ml_kem_vector_portable_add_4e(&result->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&result->data[i0]);
  }
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_ring_element_v
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_ring_element_v_3d(
    Eurydice_borrow_slice_u8 public_key, arr_fd *t_as_ntt_entry,
    dst_ref_shared_2f r_as_ntt, const arr_fd *error_2, const arr_fd *message,
    arr_fd *result, Eurydice_arr_d6 *scratch, dst_ref_shared_2f cache,
    Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U;
       i <
       public_key.meta / LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_c8(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_6d_90(ring_element),
        t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(t_as_ntt_entry, &r_as_ntt.ptr[i0],
                                              accumulator, &cache.ptr[i0]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result);
  invert_ntt_montgomery_3d(result, scratch);
  add_message_error_reduce_64_a7(error_2, message, result, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void compress_d1(Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)4, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void compress_4e_d1(Eurydice_arr_d6 *a) {
  compress_d1(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_4
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_4_a7(
    arr_fd re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re.data[i0], scratch);
    compress_4e_d1(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)8U * i0,
                                     .end = (size_t)8U * i0 + (size_t)8U})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress.compress
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void compress_f4(Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int16_t uu____0 = libcrux_secrets_int_as_i16_f5(
        libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
            (uint8_t)5, libcrux_secrets_int_as_u16_f5(a->data[i0])));
    a->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.vector.portable.compress_4e
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void compress_4e_f4(Eurydice_arr_d6 *a) {
  compress_f4(a);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.serialize.compress_then_serialize_5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void compress_then_serialize_5_a7(
    arr_fd re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_representative_a7(&re.data[i0], scratch);
    compress_4e_f4(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)10U * i0,
                                     .end = (size_t)10U * i0 + (size_t)10U})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_3a(
    arr_fd re, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_d6 *scratch) {
  compress_then_serialize_5_a7(re, out, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- V_COMPRESSION_FACTOR= 5
- C2_LEN= 160
*/
static KRML_MUSTINLINE void encrypt_c2_3a(
    Eurydice_borrow_slice_u8 public_key, arr_fd *t_as_ntt_entry,
    dst_ref_shared_2f r_as_ntt, const arr_fd *error_2,
    const Eurydice_arr_ec *message, Eurydice_mut_borrow_slice_u8 ciphertext,
    Eurydice_arr_d6 *scratch, dst_ref_shared_2f cache,
    Eurydice_arr_6c *accumulator) {
  arr_fd message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  arr_fd v = ZERO_64_a7();
  compute_ring_element_v_3d(public_key, t_as_ntt_entry, r_as_ntt, error_2,
                            &message_as_ring_element, &v, scratch, cache,
                            accumulator);
  compress_then_serialize_ring_element_v_3a(v, ciphertext, scratch);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_LEN= 1408
- C2_LEN= 160
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
- BLOCK_LEN= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static KRML_MUSTINLINE void encrypt_1f1(
    Eurydice_borrow_slice_u8 public_key, const Eurydice_arr_ec *message,
    Eurydice_borrow_slice_u8 randomness,
    Eurydice_mut_borrow_slice_u8 ciphertext, arr_fd *matrix_entry,
    dst_ref_mut_2f r_as_ntt, arr_fd *error_2, Eurydice_arr_d6 *scratch,
    dst_ref_mut_2f cache, Eurydice_arr_6c *accumulator) {
  encrypt_c1_841(
      randomness, matrix_entry,
      Eurydice_slice_subslice_from_shared_6d(public_key, (size_t)1536U),
      Eurydice_slice_subslice_mut_c8(
          ciphertext, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = (size_t)0U, .end = (size_t)1408U})),
      r_as_ntt, error_2, scratch, cache, accumulator);
  encrypt_c2_3a(
      Eurydice_slice_subslice_to_shared_72(public_key, (size_t)1536U),
      matrix_entry,
      (KRML_CLITERAL(dst_ref_shared_2f){.ptr = r_as_ntt.ptr,
                                        .meta = r_as_ntt.meta}),
      error_2, message,
      Eurydice_slice_subslice_from_mut_6d(ciphertext, (size_t)1408U), scratch,
      (KRML_CLITERAL(dst_ref_shared_2f){.ptr = cache.ptr, .meta = cache.meta}),
      accumulator);
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.kdf_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE void kdf_cc_2f(Eurydice_borrow_slice_u8 shared_secret,
                                      Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
tuple_97 libcrux_iot_ml_kem_ind_cca_encapsulate_fe1(
    const Eurydice_arr_d1 *public_key, const Eurydice_arr_ec *randomness) {
  Eurydice_arr_ec processed_randomness;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(processed_randomness.data, repeat_expression0,
         (size_t)32U * sizeof(uint8_t));
  entropy_preprocess_cc_3e(
      Eurydice_array_to_slice_shared_01(randomness),
      Eurydice_array_to_slice_mut_01(&processed_randomness));
  Eurydice_arr_c7 to_hash = libcrux_iot_ml_kem_utils_into_padded_array_c9(
      Eurydice_array_to_slice_shared_01(&processed_randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d1 lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_ac(public_key[0U]);
  Eurydice_borrow_slice_u8 uu____0 = core_array___T__N___as_slice(
      (size_t)1568U, &lvalue0, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0, Eurydice_array_to_subslice_from_mut_5f(
                   &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE));
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression1[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression1, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_17(&to_hash),
      Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____1 =
      Eurydice_slice_split_at(Eurydice_array_to_slice_shared_17(&hashed),
                              LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                              uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_d1 ciphertext = {.data = {0U}};
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_92_fe1(&lvalue);
  }
  arr_51 r_as_ntt = arr_struct;
  arr_fd error_2 = ZERO_64_a7();
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_51 cache;
  arr_fd repeat_expression3[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression3[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression3, (size_t)4U * sizeof(arr_fd));
  arr_fd matrix_entry = ZERO_64_a7();
  const Eurydice_arr_d1 *uu____2 =
      libcrux_iot_ml_kem_types_as_slice_63_d9(public_key);
  encrypt_1f1(Eurydice_array_to_slice_shared_b50(uu____2),
              &processed_randomness, pseudorandomness,
              Eurydice_array_to_slice_mut_b5(&ciphertext), &matrix_entry,
              array_to_slice_mut_a10(&r_as_ntt), &error_2, &scratch,
              array_to_slice_mut_a10(&cache), &accumulator);
  Eurydice_arr_d1 ciphertext0 = libcrux_iot_ml_kem_types_from_cf_d9(ciphertext);
  Eurydice_arr_ec shared_secret_array;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_array.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_2f(shared_secret,
            Eurydice_array_to_slice_mut_01(&shared_secret_array));
  return (
      KRML_CLITERAL(tuple_97){.fst = ciphertext0, .snd = shared_secret_array});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_iot_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt.call_mut_a5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static arr_fd call_mut_a5_2f(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_to_uncompressed_ring_element with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_to_uncompressed_ring_element_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)24U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)24U, .end = i0 * (size_t)24U + (size_t)24U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(bytes, &re->data[i0]);
  }
}

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.deserialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void deserialize_vector_3d(
    Eurydice_borrow_slice_u8 secret_key, dst_ref_mut_2f secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    deserialize_to_uncompressed_ring_element_a7(
        Eurydice_slice_subslice_shared_c8(
            secret_key,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})),
        &secret_as_ntt.ptr[i0]);
  }
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked.call_mut_b7 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static arr_fd call_mut_b7_2f(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_ef(
    Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed =
        core_num__i32__wrapping_add((int32_t)((uint32_t)decompressed << 1U),
                                    (int32_t)((uint32_t)1 << (uint32_t)10));
    decompressed >>= (uint32_t)(10 + 1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 10
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_ef(
    Eurydice_arr_d6 *a) {
  decompress_ciphertext_coefficient_ef(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_10_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)20U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)20U, .end = i0 * (size_t)20U + (size_t)20U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_ef(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_c4(
    Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed =
        core_num__i32__wrapping_add((int32_t)((uint32_t)decompressed << 1U),
                                    (int32_t)((uint32_t)1 << (uint32_t)11));
    decompressed >>= (uint32_t)(11 + 1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 11
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_c4(
    Eurydice_arr_d6 *a) {
  decompress_ciphertext_coefficient_c4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_11 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_11_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)22U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)22U, .end = i0 * (size_t)22U + (size_t)22U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_c4(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_u_1d(
    Eurydice_borrow_slice_u8 serialized, arr_fd *output) {
  deserialize_then_decompress_11_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void ntt_vector_u_1d(arr_fd *re,
                                            Eurydice_arr_d6 *scratch) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.deserialize_then_decompress_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- U_COMPRESSION_FACTOR= 11
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_3a(
    Eurydice_borrow_slice_u8 ciphertext, dst_ref_mut_2f u_as_ntt,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U;
       i < ciphertext.meta /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)11U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 u_bytes = Eurydice_slice_subslice_shared_c8(
        ciphertext,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start =
                i0 *
                (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                 (size_t)11U / (size_t)8U),
            .end =
                i0 *
                    (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                     (size_t)11U / (size_t)8U) +
                LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                    (size_t)11U / (size_t)8U}));
    deserialize_then_decompress_ring_element_u_1d(u_bytes, &u_as_ntt.ptr[i0]);
    ntt_vector_u_1d(&u_as_ntt.ptr[i0], scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_d1(
    Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed =
        core_num__i32__wrapping_add((int32_t)((uint32_t)decompressed << 1U),
                                    (int32_t)((uint32_t)1 << (uint32_t)4));
    decompressed >>= (uint32_t)(4 + 1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 4
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_d1(
    Eurydice_arr_d6 *a) {
  decompress_ciphertext_coefficient_d1(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_4 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_4_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)8U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_d1(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.compress.decompress_ciphertext_coefficient
with const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_f4(
    Eurydice_arr_d6 *a) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR; i++) {
    size_t i0 = i;
    int32_t decompressed = core_num__i32__wrapping_mul(
        libcrux_secrets_int_as_i32_f5(a->data[i0]),
        libcrux_secrets_int_as_i32_f5(
            libcrux_secrets_int_public_integers_classify_27_39(
                LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS)));
    decompressed =
        core_num__i32__wrapping_add((int32_t)((uint32_t)decompressed << 1U),
                                    (int32_t)((uint32_t)1 << (uint32_t)5));
    decompressed >>= (uint32_t)(5 + 1);
    a->data[i0] = libcrux_secrets_int_as_i16_36(decompressed);
  }
}

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.vector.portable.decompress_ciphertext_coefficient_4e with
const generics
- COEFFICIENT_BITS= 5
*/
static KRML_MUSTINLINE void decompress_ciphertext_coefficient_4e_f4(
    Eurydice_arr_d6 *a) {
  decompress_ciphertext_coefficient_f4(a);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_5 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void deserialize_then_decompress_5_a7(
    Eurydice_borrow_slice_u8 serialized, arr_fd *re) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)10U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)10U, .end = i0 * (size_t)10U + (size_t)10U}));
    libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(bytes, &re->data[i0]);
    decompress_ciphertext_coefficient_4e_f4(&re->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 4
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_v_df(
    Eurydice_borrow_slice_u8 serialized, arr_fd *output) {
  deserialize_then_decompress_5_a7(serialized, output);
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.polynomial.accumulating_ntt_multiply_64 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void accumulating_ntt_multiply_64_a7(
    const arr_fd *self, const arr_fd *rhs, Eurydice_arr_6c *accumulator) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
        &self->data[i0], &rhs->data[i0],
        Eurydice_array_to_subslice_mut_44(
            accumulator, (KRML_CLITERAL(core_ops_range_Range_87){
                             .start = i0 * (size_t)16U,
                             .end = (i0 + (size_t)1U) * (size_t)16U})),
        zeta((size_t)64U + (size_t)4U * i0),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)1U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)2U),
        zeta((size_t)64U + (size_t)4U * i0 + (size_t)3U));
  }
}

/**
This function found in impl
{libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.polynomial.subtract_reduce_64
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics

*/
static KRML_MUSTINLINE void subtract_reduce_64_a7(const arr_fd *self,
                                                  arr_fd *b) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
        &b->data[i0], 1441);
    libcrux_iot_ml_kem_vector_portable_sub_4e(&b->data[i0], &self->data[i0]);
    libcrux_iot_ml_kem_vector_portable_negate_4e(&b->data[i0]);
    libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(&b->data[i0]);
  }
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_message
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
*/
static KRML_MUSTINLINE void compute_message_3d(
    const arr_fd *v, const arr_51 *secret_as_ntt, const arr_51 *u_as_ntt,
    arr_fd *result, Eurydice_arr_d6 *scratch, Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    accumulating_ntt_multiply_64_a7(&secret_as_ntt->data[i0],
                                    &u_as_ntt->data[i0], accumulator);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result);
  invert_ntt_montgomery_3d(result, scratch);
  subtract_reduce_64_a7(v, result);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_message with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics

*/
static KRML_MUSTINLINE void compress_then_serialize_message_a7(
    const arr_fd *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    libcrux_iot_ml_kem_vector_portable_compress_1_4e(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)2U * i0,
                                     .end = (size_t)2U * i0 + (size_t)2U})));
  }
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_unpacked_2f(
    const arr_51 *secret_key, const Eurydice_arr_d1 *ciphertext,
    Eurydice_mut_borrow_slice_u8 decrypted, Eurydice_arr_d6 *scratch,
    Eurydice_arr_6c *accumulator) {
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_b7_2f(&lvalue);
  }
  arr_51 u_as_ntt = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 =
      Eurydice_array_to_subslice_to_shared_213(ciphertext, (size_t)1408U);
  deserialize_then_decompress_u_3a(uu____0, array_to_slice_mut_a10(&u_as_ntt),
                                   scratch);
  arr_fd v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_df(
      Eurydice_array_to_subslice_from_shared_5f4(ciphertext, (size_t)1408U),
      &v);
  arr_fd message = ZERO_64_a7();
  compute_message_3d(&v, secret_key, &u_as_ntt, &message, scratch, accumulator);
  compress_then_serialize_message_a7(&message, decrypted, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- CIPHERTEXT_SIZE= 1568
- VECTOR_U_ENCODED_SIZE= 1408
- U_COMPRESSION_FACTOR= 11
- V_COMPRESSION_FACTOR= 5
*/
static KRML_MUSTINLINE void decrypt_2f(Eurydice_borrow_slice_u8 secret_key,
                                       const Eurydice_arr_d1 *ciphertext,
                                       Eurydice_mut_borrow_slice_u8 decrypted,
                                       Eurydice_arr_d6 *scratch,
                                       Eurydice_arr_6c *accumulator) {
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_a5_2f(&lvalue);
  }
  arr_51 secret_as_ntt = arr_struct;
  deserialize_vector_3d(secret_key, array_to_slice_mut_a10(&secret_as_ntt));
  arr_51 secret_key_unpacked = secret_as_ntt;
  decrypt_unpacked_2f(&secret_key_unpacked, ciphertext, decrypted, scratch,
                      accumulator);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_ce(Eurydice_borrow_slice_u8 input,
                                   Eurydice_mut_borrow_slice_u8 out) {
  shake256_ema(out, input);
}

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.hash_functions.portable.PRF_07
with const generics
- LEN= 32
*/
static KRML_MUSTINLINE void PRF_07_ce(Eurydice_borrow_slice_u8 input,
                                      Eurydice_mut_borrow_slice_u8 out) {
  PRF_ce(input, out);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate.call_mut_9b
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
static arr_fd call_mut_9b_5d1(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
Eurydice_arr_ec libcrux_iot_ml_kem_ind_cca_decapsulate_5d1(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *ciphertext) {
  Eurydice_borrow_slice_u8_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_e3(
          Eurydice_array_to_slice_shared_68(private_key));
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____0.snd;
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____0.f3;
  Eurydice_arr_ec decrypted;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(decrypted.data, repeat_expression0, (size_t)32U * sizeof(uint8_t));
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression1[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression1, (size_t)256U * sizeof(int32_t));
  decrypt_2f(ind_cpa_secret_key, ciphertext,
             Eurydice_array_to_slice_mut_01(&decrypted), &scratch,
             &accumulator);
  Eurydice_arr_c7 to_hash0 = libcrux_iot_ml_kem_utils_into_padded_array_c9(
      Eurydice_array_to_slice_shared_01(&decrypted));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from_mut_5f(
          &to_hash0, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE),
      libcrux_secrets_int_classify_public_classify_ref_6d_90(
          ind_cpa_public_key_hash),
      uint8_t);
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression2[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression2, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_17(&to_hash0),
      Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____1 =
      Eurydice_slice_split_at(Eurydice_array_to_slice_shared_17(&hashed),
                              LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                              uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_140 to_hash =
      libcrux_iot_ml_kem_utils_into_padded_array_49(implicit_rejection_value);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_subslice_from_mut_5f2(
          &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d1 lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_ac(ciphertext[0U]);
  Eurydice_slice_copy(
      uu____2,
      core_array___T__N___as_slice((size_t)1568U, &lvalue0, uint8_t,
                                   Eurydice_borrow_slice_u8),
      uint8_t);
  Eurydice_arr_ec implicit_rejection_shared_secret;
  uint8_t repeat_expression3[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression3[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret.data, repeat_expression3,
         (size_t)32U * sizeof(uint8_t));
  PRF_07_ce(Eurydice_array_to_slice_shared_72(&to_hash),
            Eurydice_array_to_slice_mut_01(&implicit_rejection_shared_secret));
  Eurydice_arr_d1 expected_ciphertext = {.data = {0U}};
  arr_51 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_9b_5d1(&lvalue);
  }
  arr_51 r_as_ntt = arr_struct;
  arr_fd error_2 = ZERO_64_a7();
  arr_51 cache;
  arr_fd repeat_expression4[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression4[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression4, (size_t)4U * sizeof(arr_fd));
  arr_fd matrix_entry = ZERO_64_a7();
  encrypt_1f1(ind_cpa_public_key, &decrypted, pseudorandomness,
              Eurydice_array_to_slice_mut_b5(&expected_ciphertext),
              &matrix_entry, array_to_slice_mut_a10(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_a10(&cache), &accumulator);
  Eurydice_arr_ec implicit_rejection_shared_secret_kdf;
  uint8_t repeat_expression5[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret_kdf.data, repeat_expression5,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_2f(
      Eurydice_array_to_slice_shared_01(&implicit_rejection_shared_secret),
      Eurydice_array_to_slice_mut_01(&implicit_rejection_shared_secret_kdf));
  Eurydice_arr_ec shared_secret_kdf;
  uint8_t repeat_expression6[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression6[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_kdf.data, repeat_expression6,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_2f(shared_secret, Eurydice_array_to_slice_mut_01(&shared_secret_kdf));
  Eurydice_arr_ec shared_secret0;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret0.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d1 lvalue1 =
      libcrux_secrets_int_public_integers_classify_27_ac(ciphertext[0U]);
  Eurydice_borrow_slice_u8 uu____3 = core_array___T__N___as_slice(
      (size_t)1568U, &lvalue1, uint8_t, Eurydice_borrow_slice_u8);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_d1 lvalue =
      libcrux_secrets_int_public_integers_classify_27_ac(expected_ciphertext);
  Eurydice_borrow_slice_u8 uu____4 = core_array___T__N___as_slice(
      (size_t)1568U, &lvalue, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____3, uu____4, Eurydice_array_to_slice_shared_01(&shared_secret_kdf),
      Eurydice_array_to_slice_shared_01(&implicit_rejection_shared_secret_kdf),
      Eurydice_array_to_slice_mut_01(&shared_secret0));
  return shared_secret0;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
with const generics
- $3size_t
*/
typedef struct arr_14_s {
  arr_fd data[3U];
} arr_14;

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cca::validate_public_key::closure<Vector, K,
PUBLIC_KEY_SIZE>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.validate_public_key.call_mut_42 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static arr_fd call_mut_42_21(void **_) { return ZERO_64_a7(); }

/**
 This function deserializes ring elements and reduces the result by the field
 modulus.

 This function MUST NOT be used on secret inputs.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_ring_elements_reduced with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_ring_elements_reduced_51(
    Eurydice_borrow_slice_u8 public_key, dst_ref_mut_2f deserialized_pk) {
  Eurydice_borrow_slice_u8 public_key0 =
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key);
  for (size_t i = (size_t)0U;
       i <
       public_key0.meta / LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_c8(
        public_key0,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(ring_element,
                                           &deserialized_pk.ptr[i0]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 3
*/
static dst_ref_mut_2f array_to_slice_mut_a11(arr_14 *a) {
  dst_ref_mut_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
 Call [`serialize_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void serialize_vector_51(
    const arr_14 *key, Eurydice_mut_borrow_slice_u8 out,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    arr_fd re = key->data[i0];
    serialize_uncompressed_ring_element_a7(
        &re, scratch,
        Eurydice_slice_subslice_mut_c8(
            out,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})));
  }
}

/**
 Concatenate `t` and `ρ` into the public key.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.serialize_public_key_mut
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE void serialize_public_key_mut_21(
    const arr_14 *t_as_ntt, Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 serialized, Eurydice_arr_d6 *scratch) {
  /* original Rust expression is not an lvalue in C */
  Eurydice_mut_borrow_slice_u8 lvalue = Eurydice_slice_subslice_mut_c8(
      serialized,
      (KRML_CLITERAL(core_ops_range_Range_87){
          .start = (size_t)0U,
          .end = libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U)}));
  serialize_vector_51(
      t_as_ntt,
      libcrux_secrets_int_classify_public_classify_ref_mut_a1_75(&lvalue)[0U],
      scratch);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_from_mut_6d(
          serialized,
          libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(
              (size_t)3U)),
      seed_for_a, uint8_t);
}

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_21(
    const Eurydice_arr_5f *public_key) {
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_42_21(&lvalue);
  }
  arr_14 deserialized_pk = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 = Eurydice_array_to_subslice_to_shared_212(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U));
  deserialize_ring_elements_reduced_51(
      uu____0, array_to_slice_mut_a11(&deserialized_pk));
  Eurydice_arr_5f public_key_serialized = {.data = {0U}};
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  const arr_14 *uu____1 = &deserialized_pk;
  Eurydice_borrow_slice_u8 uu____2 = Eurydice_array_to_subslice_from_shared_5f3(
      public_key,
      libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element((size_t)3U));
  serialize_public_key_mut_21(
      uu____1, uu____2, Eurydice_array_to_slice_mut_ff(&public_key_serialized),
      &scratch);
  return Eurydice_array_eq((size_t)1184U, public_key, &public_key_serialized,
                           uint8_t);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_d3(
    const Eurydice_arr_7d *private_key) {
  Eurydice_arr_ec t;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(t.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      Eurydice_array_to_subslice_shared_d47(
          private_key, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = (size_t)384U * (size_t)3U,
                           .end = (size_t)768U * (size_t)3U + (size_t)32U})),
      Eurydice_array_to_slice_mut_01(&t));
  Eurydice_borrow_slice_u8 expected =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          Eurydice_array_to_subslice_shared_d47(
              private_key,
              (KRML_CLITERAL(core_ops_range_Range_87){
                  .start = (size_t)768U * (size_t)3U + (size_t)32U,
                  .end = (size_t)768U * (size_t)3U + (size_t)64U})));
  /* original Rust expression is not an lvalue in C */
  Eurydice_borrow_slice_u8 lvalue =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)32U, &t, uint8_t,
                                       Eurydice_borrow_slice_u8));
  return Eurydice_slice_eq_shared(&lvalue, &expected, uint8_t, bool);
}

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_88(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *_ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_d3(private_key);
}

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPrivateKeyUnpacked<Vector,
K>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE arr_14 default_1e_51(void) {
  arr_14 lit;
  arr_fd repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.data, repeat_expression, (size_t)3U * sizeof(arr_fd));
  return lit;
}

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement_12
with const generics
- $9size_t
*/
typedef struct arr_510_s {
  arr_fd data[9U];
} arr_510;

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.unpacked.IndCpaPublicKeyUnpacked with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- $3size_t
- $9size_t
*/
typedef struct IndCpaPublicKeyUnpacked_3b_s {
  arr_14 t_as_ntt;
  Eurydice_arr_ec seed_for_A;
  arr_510 A;
} IndCpaPublicKeyUnpacked_3b;

/**
This function found in impl {core::default::Default for
libcrux_iot_ml_kem::ind_cpa::unpacked::IndCpaPublicKeyUnpacked<Vector, K,
K_SQUARED>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.unpacked.default_1f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- K_SQUARED= 9
*/
static KRML_MUSTINLINE IndCpaPublicKeyUnpacked_3b default_1f_21(void) {
  arr_14 uu____0;
  arr_fd repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] = ZERO_64_a7();
  }
  memcpy(uu____0.data, repeat_expression0, (size_t)3U * sizeof(arr_fd));
  Eurydice_arr_ec uu____1 = {.data = {0U}};
  IndCpaPublicKeyUnpacked_3b lit;
  lit.t_as_ntt = uu____0;
  lit.seed_for_A = uu____1;
  arr_fd repeat_expression[9U];
  for (size_t i = (size_t)0U; i < (size_t)9U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(lit.A.data, repeat_expression, (size_t)9U * sizeof(arr_fd));
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.cpa_keygen_seed_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void cpa_keygen_seed_cc_12(
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_fa seed;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d42(
          &seed,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE})),
      key_generation_seed, uint8_t);
  seed.data[LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE] =
      libcrux_secrets_int_public_integers_classify_27_90((uint8_t)(size_t)3U);
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_b5(&seed), out);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 9
*/
static dst_ref_mut_2f array_to_slice_mut_a12(arr_510 *a) {
  dst_ref_mut_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)9U;
  return lit;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- N= 504
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_21(
    Eurydice_dst_ref_shared_8c randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)504U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_79 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d42(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
 If `bytes` contains a set of uniformly random bytes, this function
 uniformly samples a ring element `â` that is treated as being the NTT
 representation of the corresponding polynomial `a`.

 Since rejection sampling is used, it is possible the supplied bytes are
 not enough to sample the element, in which case an `Err` is returned and the
 caller must try again with a fresh set of bytes.

 This function <strong>partially</strong> implements <strong>Algorithm
 6</strong> of the NIST FIPS 203 standard, We say "partially" because this
 implementation only accepts a finite set of bytes as input and returns an error
 if the set is not enough; Algorithm 6 of the FIPS 203 standard on the other
 hand samples from an infinite stream of bytes until the ring element is filled.
 Algorithm 6 is reproduced below:

 ```plaintext
 Input: byte stream B ∈ 𝔹*.
 Output: array â ∈ ℤ₂₅₆.

 i ← 0
 j ← 0
 while j < 256 do
     d₁ ← B[i] + 256·(B[i+1] mod 16)
     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
     if d₁ < q then
         â[j] ← d₁
         j ← j + 1
     end if
     if d₂ < q and j < 256 then
         â[j] ← d₂
         j ← j + 1
     end if
     i ← i + 3
 end while
 return â
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.sampling.sample_from_uniform_distribution_next with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- N= 168
*/
static KRML_MUSTINLINE bool sample_from_uniform_distribution_next_210(
    Eurydice_dst_ref_shared_c3 randomness,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)24U; i++) {
      size_t r = i;
      if (sampled_coefficients.ptr[i1] <
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        const Eurydice_arr_c5 *randomness_i = &randomness.ptr[i1];
        Eurydice_arr_5b *out_i = &out.ptr[i1];
        size_t sampled_coefficients_i = sampled_coefficients.ptr[i1];
        size_t sampled = libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
            Eurydice_array_to_subslice_shared_d43(
                randomness_i, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = r * (size_t)24U,
                                  .end = r * (size_t)24U + (size_t)24U})),
            Eurydice_array_to_subslice_mut_e7(
                out_i, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = sampled_coefficients_i,
                           .end = sampled_coefficients_i + (size_t)16U})));
        sampled_coefficients.ptr[i1] = core_num__usize__wrapping_add(
            sampled_coefficients.ptr[i1], sampled);
      }
    }
  }
  bool done = true;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    if (sampled_coefficients.ptr[i0] >=
        LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
      sampled_coefficients.ptr[i0] =
          LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT;
    } else {
      done = false;
    }
  }
  return done;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.sampling.sample_from_xof
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_from_xof_ee1(
    Eurydice_dst_ref_shared_cf seeds,
    Eurydice_dst_ref_mut_c30 sampled_coefficients,
    Eurydice_dst_ref_mut_df out) {
  Eurydice_arr_7b xof_state =
      libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
          seeds);
  Eurydice_arr_7e randomness = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Eurydice_arr_2c randomness_blocksize = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
      &xof_state, Eurydice_array_to_slice_mut_eb1(&randomness));
  bool done = sample_from_uniform_distribution_next_21(
      Eurydice_array_to_slice_shared_eb1(&randomness), sampled_coefficients,
      out);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
          &xof_state, Eurydice_array_to_slice_mut_1b1(&randomness_blocksize));
      done = sample_from_uniform_distribution_next_210(
          Eurydice_array_to_slice_shared_1b1(&randomness_blocksize),
          sampled_coefficients, out);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.sample_matrix_A
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void sample_matrix_A_ee0(dst_ref_mut_2f A_transpose,
                                                const Eurydice_arr_31 *seed,
                                                bool transpose) {
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    Eurydice_arr_81 seeds;
    Eurydice_arr_31 repeat_expression[3U];
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      repeat_expression[i] = seed[0U];
    }
    memcpy(seeds.data, repeat_expression, (size_t)3U * sizeof(Eurydice_arr_31));
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      seeds.data[j].data[32U] = (uint8_t)i1;
      seeds.data[j].data[33U] = (uint8_t)j;
    }
    Eurydice_arr_eb sampled_coefficients = {.data = {0U}};
    Eurydice_arr_b1 out = {
        .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
    sample_from_xof_ee1(Eurydice_array_to_slice_shared_6e1(&seeds),
                        Eurydice_array_to_slice_mut_20(&sampled_coefficients),
                        Eurydice_array_to_slice_mut_f21(&out));
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      Eurydice_arr_5b sample = out.data[j];
      if (transpose) {
        Eurydice_borrow_slice_i16 uu____0 =
            libcrux_secrets_int_classify_public_classify_ref_6d_39(
                Eurydice_array_to_subslice_to_shared_a9(&sample, (size_t)256U));
        from_i16_array_64_a7(uu____0, &A_transpose.ptr[j * (size_t)3U + i1]);
      } else {
        Eurydice_borrow_slice_i16 uu____1 =
            libcrux_secrets_int_classify_public_classify_ref_6d_39(
                Eurydice_array_to_subslice_to_shared_a9(&sample, (size_t)256U));
        from_i16_array_64_a7(uu____1, &A_transpose.ptr[i1 * (size_t)3U + j]);
      }
    }
  }
}

/**
 Sample a vector of ring elements from a centered binomial distribution and
 convert them into their NTT representations.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_vector_cbd_then_ntt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA= 2
- ETA_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t sample_vector_cbd_then_ntt_b20(
    dst_ref_mut_2f re_as_ntt, const Eurydice_arr_fa *prf_input,
    uint8_t domain_separator, Eurydice_arr_d6 *scratch) {
  Eurydice_arr_801 prf_inputs;
  Eurydice_arr_fa repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)33U, prf_input, uint8_t, Eurydice_arr_fa);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_fa));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_78(&prf_inputs, domain_separator);
  Eurydice_arr_b2 prf_outputs;
  uint8_t repeat_expression1[384U];
  for (size_t i = (size_t)0U; i < (size_t)384U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression1, (size_t)384U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      Eurydice_array_to_slice_shared_040(&prf_inputs),
      Eurydice_array_to_slice_mut_a9(&prf_outputs), (size_t)128U);
  for (size_t i0 = (size_t)0U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_d40(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = i1 * (size_t)128U,
                          .end = (i1 + (size_t)1U) * (size_t)128U}));
    Eurydice_arr_04 sample_buffer;
    int16_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_39(0);
    }
    memcpy(sample_buffer.data, repeat_expression,
           (size_t)256U * sizeof(int16_t));
    sample_from_binomial_distribution_6e(randomness, &sample_buffer);
    from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(&sample_buffer),
                         &re_as_ntt.ptr[i1]);
    ntt_binomially_sampled_ring_element_a7(&re_as_ntt.ptr[i1], scratch);
  }
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for
libcrux_iot_ml_kem::ind_cpa::generate_keypair_unpacked::closure<Vector, Hasher,
Scheme, K, K_SQUARED, ETA1, ETA1_RANDOMNESS_SIZE,
PRF_OUTPUT_SIZE1>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3,
TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked.call_mut_58 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static arr_fd call_mut_58_9f0(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.entry
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static const arr_fd *entry_51(dst_ref_shared_2f matrix, size_t i, size_t j) {
  return &matrix.ptr[i * (size_t)3U + j];
}

/**
 Compute Â ◦ ŝ + ê
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_As_plus_e
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_As_plus_e_51(
    arr_14 *t_as_ntt, dst_ref_shared_2f matrix_A, const arr_14 *s_as_ntt,
    const arr_14 *error_as_ntt, arr_14 *s_cache, Eurydice_arr_6c *accumulator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t j = i;
    accumulating_ntt_multiply_fill_cache_64_a7(
        entry_51(matrix_A, (size_t)0U, j), &s_as_ntt->data[j], accumulator,
        &s_cache->data[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                t_as_ntt->data);
  add_standard_error_reduce_64_a7(t_as_ntt->data, error_as_ntt->data);
  for (size_t i0 = (size_t)1U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
    Eurydice_arr_6c lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____0;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      accumulating_ntt_multiply_use_cache_64_a7(entry_51(matrix_A, i1, j),
                                                &s_as_ntt->data[j], accumulator,
                                                &s_cache->data[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_af(accumulator), &t_as_ntt->data[i1]);
    add_standard_error_reduce_64_a7(&t_as_ntt->data[i1],
                                    &error_as_ntt->data[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 9
*/
static dst_ref_shared_2f array_to_slice_shared_a12(const arr_510 *a) {
  dst_ref_shared_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)9U;
  return lit;
}

/**
 This function implements most of <strong>Algorithm 12</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE key generation
 algorithm.

 We say "most of" since Algorithm 12 samples the required randomness within
 the function itself, whereas this implementation expects it to be provided
 through the `key_generation_seed` parameter.

 Algorithm 12 is reproduced below:

 ```plaintext
 Output: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Output: decryption key dkₚₖₑ ∈ 𝔹^{384k}.

 d ←$ B
 (ρ,σ) ← G(d)
 N ← 0
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     s[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(σ,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(σ,N))
     N ← N + 1
 end for
 ŝ ← NTT(s)
 ê ← NTT(e)
 t̂ ← Â◦ŝ + ê
 ekₚₖₑ ← ByteEncode₁₂(t̂) ‖ ρ
 dkₚₖₑ ← ByteEncode₁₂(ŝ)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void generate_keypair_unpacked_9f0(
    Eurydice_borrow_slice_u8 key_generation_seed, arr_14 *private_key,
    IndCpaPublicKeyUnpacked_3b *public_key, arr_fd *scratch, arr_14 *s_cache,
    Eurydice_arr_6c *accumulator) {
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  cpa_keygen_seed_cc_12(key_generation_seed,
                        Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_17(&hashed), (size_t)32U, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_A = uu____0.fst;
  Eurydice_borrow_slice_u8 seed_for_secret_and_error = uu____0.snd;
  dst_ref_mut_2f uu____1 = array_to_slice_mut_a12(&public_key->A);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_31 lvalue0 =
      libcrux_secrets_int_public_integers_declassify_d8_78(
          libcrux_iot_ml_kem_utils_into_padded_array_de(seed_for_A));
  sample_matrix_A_ee0(uu____1, &lvalue0, true);
  Eurydice_arr_fa prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_29(seed_for_secret_and_error);
  uint8_t domain_separator = sample_vector_cbd_then_ntt_b20(
      array_to_slice_mut_a11(private_key), &prf_input, 0U, scratch->data);
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_58_9f0(&lvalue);
  }
  arr_14 error_as_ntt = arr_struct;
  sample_vector_cbd_then_ntt_b20(array_to_slice_mut_a11(&error_as_ntt),
                                 &prf_input, domain_separator, scratch->data);
  compute_As_plus_e_51(&public_key->t_as_ntt,
                       array_to_slice_shared_a12(&public_key->A),
                       &private_key[0U], &error_as_ntt, s_cache, accumulator);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_slice_mut_01(&public_key->seed_for_A);
  Eurydice_slice_copy(
      uu____2,
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_A),
      uint8_t);
}

/**
 Serialize the secret key from the unpacked key pair generation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.serialize_unpacked_secret_key with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
static void serialize_unpacked_secret_key_ab(
    const IndCpaPublicKeyUnpacked_3b *public_key, const arr_14 *private_key,
    Eurydice_mut_borrow_slice_u8 serialized_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key,
    Eurydice_arr_d6 *scratch) {
  serialize_public_key_mut_21(
      &public_key->t_as_ntt,
      Eurydice_array_to_slice_shared_01(&public_key->seed_for_A),
      serialized_public_key, scratch);
  serialize_vector_51(private_key, serialized_private_key, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- PRIVATE_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static KRML_MUSTINLINE void generate_keypair_e50(
    Eurydice_borrow_slice_u8 key_generation_seed,
    Eurydice_mut_borrow_slice_u8 serialized_ind_cpa_private_key,
    Eurydice_mut_borrow_slice_u8 serialized_public_key, arr_fd *scratch,
    arr_14 *s_cache, Eurydice_arr_6c *accumulator) {
  arr_14 private_key = default_1e_51();
  IndCpaPublicKeyUnpacked_3b public_key = default_1f_21();
  generate_keypair_unpacked_9f0(key_generation_seed, &private_key, &public_key,
                                scratch, s_cache, accumulator);
  serialize_unpacked_secret_key_ab(&public_key, &private_key,
                                   serialized_ind_cpa_private_key,
                                   serialized_public_key, scratch->data);
}

/**
 Serialize the secret key.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.serialize_kem_secret_key_mut with types
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- SERIALIZED_KEY_LEN= 2400
*/
static KRML_MUSTINLINE void serialize_kem_secret_key_mut_d3(
    Eurydice_borrow_slice_u8 private_key, Eurydice_borrow_slice_u8 public_key,
    Eurydice_borrow_slice_u8 implicit_rejection_value,
    Eurydice_arr_7d *serialized) {
  size_t pointer = (size_t)0U;
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d46(
                          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                          .start = pointer,
                                          .end = pointer + private_key.meta})),
                      private_key, uint8_t);
  pointer += private_key.meta;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d46(
          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = pointer, .end = pointer + public_key.meta})),
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key),
      uint8_t);
  pointer += public_key.meta;
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(public_key),
      Eurydice_array_to_subslice_mut_d46(
          serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = pointer,
              .end = pointer + LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE})));
  pointer += LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE;
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_mut_d46(
          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = pointer,
                          .end = pointer + implicit_rejection_value.meta})),
      implicit_rejection_value, uint8_t);
}

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_e2
libcrux_iot_ml_kem_ind_cca_generate_keypair_de0(
    const Eurydice_arr_c7 *randomness) {
  Eurydice_borrow_slice_u8 ind_cpa_keypair_randomness =
      Eurydice_array_to_subslice_shared_d45(
          randomness,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE}));
  Eurydice_borrow_slice_u8 implicit_rejection_value =
      Eurydice_array_to_subslice_from_shared_5f0(
          randomness,
          LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE);
  Eurydice_arr_5f public_key = {.data = {0U}};
  Eurydice_arr_7d secret_key_serialized;
  uint8_t repeat_expression0[2400U];
  for (size_t i = (size_t)0U; i < (size_t)2400U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(secret_key_serialized.data, repeat_expression0,
         (size_t)2400U * sizeof(uint8_t));
  Eurydice_arr_0e ind_cpa_private_key;
  uint8_t repeat_expression1[1152U];
  for (size_t i = (size_t)0U; i < (size_t)1152U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(ind_cpa_private_key.data, repeat_expression1,
         (size_t)1152U * sizeof(uint8_t));
  arr_fd scratch = ZERO_64_a7();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_14 s_cache;
  arr_fd repeat_expression[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression[i] = ZERO_64_a7();
  }
  memcpy(s_cache.data, repeat_expression, (size_t)3U * sizeof(arr_fd));
  generate_keypair_e50(ind_cpa_keypair_randomness,
                       Eurydice_array_to_slice_mut_f4(&ind_cpa_private_key),
                       Eurydice_array_to_slice_mut_ff(&public_key), &scratch,
                       &s_cache, &accumulator);
  serialize_kem_secret_key_mut_d3(
      Eurydice_array_to_slice_shared_f4(&ind_cpa_private_key),
      Eurydice_array_to_slice_shared_ff(&public_key), implicit_rejection_value,
      &secret_key_serialized);
  Eurydice_arr_7d private_key =
      libcrux_iot_ml_kem_types_from_c2_79(secret_key_serialized);
  return libcrux_iot_ml_kem_types_from_d9_bc(
      private_key, libcrux_iot_ml_kem_types_from_08_3d(public_key));
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.entropy_preprocess_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
*/
static KRML_MUSTINLINE void entropy_preprocess_cc_12(
    Eurydice_borrow_slice_u8 randomness, Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_slice_copy(out, randomness, uint8_t);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::encapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, CIPHERTEXT_SIZE, PUBLIC_KEY_SIZE,
T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE, VECTOR_U_COMPRESSION_FACTOR,
VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1, ETA1_RANDOMNESS_SIZE, ETA2,
ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1, PRF_OUTPUT_SIZE2>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate.call_mut_92
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static arr_fd call_mut_92_fe0(void **_) { return ZERO_64_a7(); }

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_6f
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static arr_fd call_mut_6f_840(void **_) { return ZERO_64_a7(); }

/**
 Sample a vector of ring elements from a centered binomial distribution.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.sample_ring_element_cbd
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- ETA2_RANDOMNESS_SIZE= 128
- ETA2= 2
- PRF_OUTPUT_SIZE= 384
*/
static KRML_MUSTINLINE uint8_t sample_ring_element_cbd_b20(
    const Eurydice_arr_fa *prf_input, uint8_t domain_separator,
    dst_ref_mut_2f error_1, Eurydice_arr_04 *sample_buffer) {
  Eurydice_arr_801 prf_inputs;
  Eurydice_arr_fa repeat_expression0[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression0[i] = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)33U, prf_input, uint8_t, Eurydice_arr_fa);
  }
  memcpy(prf_inputs.data, repeat_expression0,
         (size_t)3U * sizeof(Eurydice_arr_fa));
  domain_separator =
      libcrux_iot_ml_kem_utils_prf_input_inc_78(&prf_inputs, domain_separator);
  Eurydice_arr_b2 prf_outputs;
  uint8_t repeat_expression[384U];
  for (size_t i = (size_t)0U; i < (size_t)384U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_outputs.data, repeat_expression, (size_t)384U * sizeof(uint8_t));
  Eurydice_dst_ref_shared_b4 uu____0 = core_array___T__N___as_slice(
      (size_t)3U, &prf_inputs, Eurydice_arr_fa, Eurydice_dst_ref_shared_b4);
  libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
      uu____0, Eurydice_array_to_slice_mut_a9(&prf_outputs), (size_t)128U);
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 randomness = Eurydice_array_to_subslice_shared_d40(
        &prf_outputs, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = i0 * (size_t)128U,
                          .end = (i0 + (size_t)1U) * (size_t)128U}));
    sample_from_binomial_distribution_6e(randomness, sample_buffer);
    from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(sample_buffer),
                         &error_1.ptr[i0]);
  }
  return domain_separator;
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@2]> for libcrux_iot_ml_kem::ind_cpa::encrypt_c1::closure#1<Vector,
Hasher, K, K_SQUARED, C1_LEN, U_COMPRESSION_FACTOR, BLOCK_LEN, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2>[TraitClause@0, TraitClause@1, TraitClause@2, TraitClause@3]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1.call_mut_33
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static arr_fd call_mut_33_840(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void invert_ntt_montgomery_51(arr_fd *re,
                                                     Eurydice_arr_d6 *scratch) {
  size_t zeta_i =
      LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)2U;
  invert_ntt_at_layer_1_a7(&zeta_i, re);
  invert_ntt_at_layer_2_a7(&zeta_i, re);
  invert_ntt_at_layer_3_a7(&zeta_i, re);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  invert_ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
}

/**
 Compute u := InvertNTT(Aᵀ ◦ r̂) + e₁
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_vector_u_ee0(
    arr_fd *matrix_entry, Eurydice_borrow_slice_u8 seed,
    dst_ref_shared_2f r_as_ntt, dst_ref_shared_2f error_1,
    dst_ref_mut_2f result, Eurydice_arr_d6 *scratch, dst_ref_mut_2f cache,
    Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit0;
  int32_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] = uu____0;
  }
  memcpy(lit0.data, repeat_expression0, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit0;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t j = i;
    sample_matrix_entry_36(matrix_entry, seed, (size_t)0U, j);
    accumulating_ntt_multiply_fill_cache_64_a7(matrix_entry, &r_as_ntt.ptr[j],
                                               accumulator, &cache.ptr[j]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result.ptr);
  invert_ntt_montgomery_51(result.ptr, scratch);
  add_error_reduce_64_a7(result.ptr, &error_1.ptr[0U]);
  for (size_t i0 = (size_t)1U; i0 < (size_t)3U; i0++) {
    size_t i1 = i0;
    int32_t uu____1 = libcrux_secrets_int_public_integers_classify_27_a8(0);
    Eurydice_arr_6c lit;
    int32_t repeat_expression[256U];
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      repeat_expression[i] = uu____1;
    }
    memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
    accumulator[0U] = lit;
    for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
      size_t j = i;
      sample_matrix_entry_36(matrix_entry, seed, i1, j);
      accumulating_ntt_multiply_use_cache_64_a7(matrix_entry, &r_as_ntt.ptr[j],
                                                accumulator, &cache.ptr[j]);
    }
    reducing_from_i32_array_64_a7(
        Eurydice_array_to_slice_shared_af(accumulator), &result.ptr[i1]);
    invert_ntt_montgomery_51(&result.ptr[i1], scratch);
    add_error_reduce_64_a7(&result.ptr[i1], &error_1.ptr[i1]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_kem_polynomial_PolynomialRingElement
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- N= 3
*/
static dst_ref_shared_2f array_to_slice_shared_a11(const arr_14 *a) {
  dst_ref_shared_2f lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_10 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_10_7f(
    const arr_fd *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < VECTORS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    to_unsigned_field_modulus_a7(&re->data[i0], scratch);
    compress_4e_ef(scratch);
    libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
        scratch, Eurydice_slice_subslice_mut_c8(
                     serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                     .start = (size_t)20U * i0,
                                     .end = (size_t)20U * i0 + (size_t)20U})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_u_2e(
    const arr_fd *re, Eurydice_mut_borrow_slice_u8 serialized,
    Eurydice_arr_d6 *scratch) {
  compress_then_serialize_10_7f(re, serialized, scratch);
}

/**
 Call [`compress_then_serialize_ring_element_u`] on each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.compress_then_serialize_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
*/
static KRML_MUSTINLINE void compress_then_serialize_u_ab(
    arr_14 input, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    arr_fd re = input.data[i0];
    compress_then_serialize_ring_element_u_2e(
        &re,
        Eurydice_slice_subslice_mut_c8(
            out, (KRML_CLITERAL(core_ops_range_Range_87){
                     .start = i0 * ((size_t)960U / (size_t)3U),
                     .end = (i0 + (size_t)1U) * ((size_t)960U / (size_t)3U)})),
        scratch);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c1
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- C1_LEN= 960
- U_COMPRESSION_FACTOR= 10
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void encrypt_c1_840(
    Eurydice_borrow_slice_u8 randomness, arr_fd *matrix_entry,
    Eurydice_borrow_slice_u8 seed_for_a,
    Eurydice_mut_borrow_slice_u8 ciphertext, dst_ref_mut_2f r_as_ntt,
    arr_fd *error_2, Eurydice_arr_d6 *scratch, dst_ref_mut_2f cache,
    Eurydice_arr_6c *accumulator) {
  Eurydice_arr_fa prf_input =
      libcrux_iot_ml_kem_utils_into_padded_array_29(randomness);
  uint8_t domain_separator =
      sample_vector_cbd_then_ntt_b20(r_as_ntt, &prf_input, 0U, scratch);
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_6f_840(&lvalue);
  }
  arr_14 error_1 = arr_struct;
  Eurydice_arr_04 sampling_buffer;
  int16_t repeat_expression0[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_39(0);
  }
  memcpy(sampling_buffer.data, repeat_expression0,
         (size_t)256U * sizeof(int16_t));
  uint8_t domain_separator0 = sample_ring_element_cbd_b20(
      &prf_input, domain_separator, array_to_slice_mut_a11(&error_1),
      &sampling_buffer);
  prf_input.data[32U] =
      libcrux_secrets_int_public_integers_classify_27_90(domain_separator0);
  Eurydice_arr_89 prf_output;
  uint8_t repeat_expression[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(prf_output.data, repeat_expression, (size_t)128U * sizeof(uint8_t));
  PRF_07_ec(Eurydice_array_to_slice_shared_b5(&prf_input),
            Eurydice_array_to_slice_mut_78(&prf_output));
  sample_from_binomial_distribution_6e(
      Eurydice_array_to_slice_shared_78(&prf_output), &sampling_buffer);
  from_i16_array_64_a7(Eurydice_array_to_slice_shared_990(&sampling_buffer),
                       error_2);
  arr_14 arr_struct0;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct0.data[i] = call_mut_33_840(&lvalue);
  }
  arr_14 u = arr_struct0;
  compute_vector_u_ee0(matrix_entry, seed_for_a,
                       (KRML_CLITERAL(dst_ref_shared_2f){
                           .ptr = r_as_ntt.ptr, .meta = r_as_ntt.meta}),
                       array_to_slice_shared_a11(&error_1),
                       array_to_slice_mut_a11(&u), scratch, cache, accumulator);
  compress_then_serialize_u_ab(u, ciphertext, scratch);
}

/**
 Compute InverseNTT(tᵀ ◦ r̂) + e₂ + message
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_ring_element_v
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_ring_element_v_51(
    Eurydice_borrow_slice_u8 public_key, arr_fd *t_as_ntt_entry,
    dst_ref_shared_2f r_as_ntt, const arr_fd *error_2, const arr_fd *message,
    arr_fd *result, Eurydice_arr_d6 *scratch, dst_ref_shared_2f cache,
    Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U;
       i <
       public_key.meta / LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 ring_element = Eurydice_slice_subslice_shared_c8(
        public_key,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
            .end = i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT +
                   LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT}));
    deserialize_to_reduced_ring_element_a7(
        libcrux_secrets_int_classify_public_classify_ref_6d_90(ring_element),
        t_as_ntt_entry);
    accumulating_ntt_multiply_use_cache_64_a7(t_as_ntt_entry, &r_as_ntt.ptr[i0],
                                              accumulator, &cache.ptr[i0]);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result);
  invert_ntt_montgomery_51(result, scratch);
  add_message_error_reduce_64_a7(error_2, message, result, scratch);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.compress_then_serialize_ring_element_v with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void compress_then_serialize_ring_element_v_82(
    arr_fd re, Eurydice_mut_borrow_slice_u8 out, Eurydice_arr_d6 *scratch) {
  compress_then_serialize_4_a7(re, out, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt_c2
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- V_COMPRESSION_FACTOR= 4
- C2_LEN= 128
*/
static KRML_MUSTINLINE void encrypt_c2_82(
    Eurydice_borrow_slice_u8 public_key, arr_fd *t_as_ntt_entry,
    dst_ref_shared_2f r_as_ntt, const arr_fd *error_2,
    const Eurydice_arr_ec *message, Eurydice_mut_borrow_slice_u8 ciphertext,
    Eurydice_arr_d6 *scratch, dst_ref_shared_2f cache,
    Eurydice_arr_6c *accumulator) {
  arr_fd message_as_ring_element = ZERO_64_a7();
  deserialize_then_decompress_message_a7(message, &message_as_ring_element);
  arr_fd v = ZERO_64_a7();
  compute_ring_element_v_51(public_key, t_as_ntt_entry, r_as_ntt, error_2,
                            &message_as_ring_element, &v, scratch, cache,
                            accumulator);
  compress_then_serialize_ring_element_v_82(v, ciphertext, scratch);
}

/**
 This function implements <strong>Algorithm 13</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE encryption algorithm.

 Algorithm 13 is reproduced below:

 ```plaintext
 Input: encryption key ekₚₖₑ ∈ 𝔹^{384k+32}.
 Input: message m ∈ 𝔹^{32}.
 Input: encryption randomness r ∈ 𝔹^{32}.
 Output: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.

 N ← 0
 t̂ ← ByteDecode₁₂(ekₚₖₑ[0:384k])
 ρ ← ekₚₖₑ[384k: 384k + 32]
 for (i ← 0; i < k; i++)
     for(j ← 0; j < k; j++)
         Â[i,j] ← SampleNTT(XOF(ρ, i, j))
     end for
 end for
 for(i ← 0; i < k; i++)
     r[i] ← SamplePolyCBD_{η₁}(PRF_{η₁}(r,N))
     N ← N + 1
 end for
 for(i ← 0; i < k; i++)
     e₁[i] ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
     N ← N + 1
 end for
 e₂ ← SamplePolyCBD_{η₂}(PRF_{η₂}(r,N))
 r̂ ← NTT(r)
 u ← NTT-¹(Âᵀ ◦ r̂) + e₁
 μ ← Decompress₁(ByteDecode₁(m)))
 v ← NTT-¹(t̂ᵀ ◦ rˆ) + e₂ + μ
 c₁ ← ByteEncode_{dᵤ}(Compress_{dᵤ}(u))
 c₂ ← ByteEncode_{dᵥ}(Compress_{dᵥ}(v))
 return c ← (c₁ ‖ c₂)
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.encrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_LEN= 960
- C2_LEN= 128
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
- BLOCK_LEN= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
static KRML_MUSTINLINE void encrypt_1f0(
    Eurydice_borrow_slice_u8 public_key, const Eurydice_arr_ec *message,
    Eurydice_borrow_slice_u8 randomness,
    Eurydice_mut_borrow_slice_u8 ciphertext, arr_fd *matrix_entry,
    dst_ref_mut_2f r_as_ntt, arr_fd *error_2, Eurydice_arr_d6 *scratch,
    dst_ref_mut_2f cache, Eurydice_arr_6c *accumulator) {
  encrypt_c1_840(
      randomness, matrix_entry,
      Eurydice_slice_subslice_from_shared_6d(public_key, (size_t)1152U),
      Eurydice_slice_subslice_mut_c8(
          ciphertext, (KRML_CLITERAL(core_ops_range_Range_87){
                          .start = (size_t)0U, .end = (size_t)960U})),
      r_as_ntt, error_2, scratch, cache, accumulator);
  encrypt_c2_82(
      Eurydice_slice_subslice_to_shared_72(public_key, (size_t)1152U),
      matrix_entry,
      (KRML_CLITERAL(dst_ref_shared_2f){.ptr = r_as_ntt.ptr,
                                        .meta = r_as_ntt.meta}),
      error_2, message,
      Eurydice_slice_subslice_from_mut_6d(ciphertext, (size_t)960U), scratch,
      (KRML_CLITERAL(dst_ref_shared_2f){.ptr = cache.ptr, .meta = cache.meta}),
      accumulator);
}

/**
This function found in impl {libcrux_iot_ml_kem::variant::Variant for
libcrux_iot_ml_kem::variant::MlKem}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.variant.kdf_cc
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE void kdf_cc_d3(Eurydice_borrow_slice_u8 shared_secret,
                                      Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_slice_copy(out, shared_secret, uint8_t);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CIPHERTEXT_SIZE= 1088
- PUBLIC_KEY_SIZE= 1184
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
*/
tuple_bf libcrux_iot_ml_kem_ind_cca_encapsulate_fe0(
    const Eurydice_arr_5f *public_key, const Eurydice_arr_ec *randomness) {
  Eurydice_arr_ec processed_randomness;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(processed_randomness.data, repeat_expression0,
         (size_t)32U * sizeof(uint8_t));
  entropy_preprocess_cc_12(
      Eurydice_array_to_slice_shared_01(randomness),
      Eurydice_array_to_slice_mut_01(&processed_randomness));
  Eurydice_arr_c7 to_hash = libcrux_iot_ml_kem_utils_into_padded_array_c9(
      Eurydice_array_to_slice_shared_01(&processed_randomness));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_5f lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_c20(public_key[0U]);
  Eurydice_borrow_slice_u8 uu____0 = core_array___T__N___as_slice(
      (size_t)1184U, &lvalue0, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_hash_functions_portable_H_07(
      uu____0, Eurydice_array_to_subslice_from_mut_5f(
                   &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE));
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression1[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression1, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_17(&to_hash),
      Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____1 =
      Eurydice_slice_split_at(Eurydice_array_to_slice_shared_17(&hashed),
                              LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                              uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_2b ciphertext = {.data = {0U}};
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_92_fe0(&lvalue);
  }
  arr_14 r_as_ntt = arr_struct;
  arr_fd error_2 = ZERO_64_a7();
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression2[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression2, (size_t)256U * sizeof(int32_t));
  arr_14 cache;
  arr_fd repeat_expression3[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression3[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression3, (size_t)3U * sizeof(arr_fd));
  arr_fd matrix_entry = ZERO_64_a7();
  const Eurydice_arr_5f *uu____2 =
      libcrux_iot_ml_kem_types_as_slice_63_3d(public_key);
  encrypt_1f0(Eurydice_array_to_slice_shared_ff(uu____2), &processed_randomness,
              pseudorandomness, Eurydice_array_to_slice_mut_06(&ciphertext),
              &matrix_entry, array_to_slice_mut_a11(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_a11(&cache), &accumulator);
  Eurydice_arr_2b ciphertext0 = libcrux_iot_ml_kem_types_from_cf_52(ciphertext);
  Eurydice_arr_ec shared_secret_array;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_array.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_d3(shared_secret,
            Eurydice_array_to_slice_mut_01(&shared_secret_array));
  return (
      KRML_CLITERAL(tuple_bf){.fst = ciphertext0, .snd = shared_secret_array});
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for libcrux_iot_ml_kem::ind_cpa::decrypt::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt.call_mut_a5
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static arr_fd call_mut_a5_3e(void **_) { return ZERO_64_a7(); }

/**
 Call [`deserialize_to_uncompressed_ring_element`] for each ring element.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.deserialize_vector
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void deserialize_vector_51(
    Eurydice_borrow_slice_u8 secret_key, dst_ref_mut_2f secret_as_ntt) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    deserialize_to_uncompressed_ring_element_a7(
        Eurydice_slice_subslice_shared_c8(
            secret_key,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 * LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT})),
        &secret_as_ntt.ptr[i0]);
  }
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@1]> for
libcrux_iot_ml_kem::ind_cpa::decrypt_unpacked::closure<Vector, K,
CIPHERTEXT_SIZE, VECTOR_U_ENCODED_SIZE, U_COMPRESSION_FACTOR,
V_COMPRESSION_FACTOR>[TraitClause@0, TraitClause@1]}
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked.call_mut_b7 with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static arr_fd call_mut_b7_3e(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_u with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_u_7b(
    Eurydice_borrow_slice_u8 serialized, arr_fd *output) {
  deserialize_then_decompress_10_a7(serialized, output);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ntt.ntt_vector_u
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- VECTOR_U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void ntt_vector_u_7b(arr_fd *re,
                                            Eurydice_arr_d6 *scratch) {
  size_t zeta_i = (size_t)0U;
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)7U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)6U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)5U, scratch);
  ntt_at_layer_4_plus_a7(&zeta_i, re, (size_t)4U, scratch);
  ntt_at_layer_3_a7(&zeta_i, re);
  ntt_at_layer_2_a7(&zeta_i, re);
  ntt_at_layer_1_a7(&zeta_i, re);
  poly_barrett_reduce_64_a7(re);
}

/**
 Call [`deserialize_then_decompress_ring_element_u`] on each ring element
 in the `ciphertext`.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cpa.deserialize_then_decompress_u with types
libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- U_COMPRESSION_FACTOR= 10
*/
static KRML_MUSTINLINE void deserialize_then_decompress_u_82(
    Eurydice_borrow_slice_u8 ciphertext, dst_ref_mut_2f u_as_ntt,
    Eurydice_arr_d6 *scratch) {
  for (size_t i = (size_t)0U;
       i < ciphertext.meta /
               (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                (size_t)10U / (size_t)8U);
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 u_bytes = Eurydice_slice_subslice_shared_c8(
        ciphertext,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start =
                i0 *
                (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                 (size_t)10U / (size_t)8U),
            .end =
                i0 *
                    (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                     (size_t)10U / (size_t)8U) +
                LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT *
                    (size_t)10U / (size_t)8U}));
    deserialize_then_decompress_ring_element_u_7b(u_bytes, &u_as_ntt.ptr[i0]);
    ntt_vector_u_7b(&u_as_ntt.ptr[i0], scratch);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.serialize.deserialize_then_decompress_ring_element_v with
types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector with const
generics
- K= 3
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void deserialize_then_decompress_ring_element_v_21(
    Eurydice_borrow_slice_u8 serialized, arr_fd *output) {
  deserialize_then_decompress_4_a7(serialized, output);
}

/**
 The following functions compute various expressions involving
 vectors and matrices. The computation of these expressions has been
 abstracted away into these functions in order to save on loop iterations.
 Compute v − InverseNTT(sᵀ ◦ NTT(u))
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.matrix.compute_message
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
*/
static KRML_MUSTINLINE void compute_message_51(
    const arr_fd *v, const arr_14 *secret_as_ntt, const arr_14 *u_as_ntt,
    arr_fd *result, Eurydice_arr_d6 *scratch, Eurydice_arr_6c *accumulator) {
  int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(0);
  Eurydice_arr_6c lit;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] = uu____0;
  }
  memcpy(lit.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  accumulator[0U] = lit;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    accumulating_ntt_multiply_64_a7(&secret_as_ntt->data[i0],
                                    &u_as_ntt->data[i0], accumulator);
  }
  reducing_from_i32_array_64_a7(Eurydice_array_to_slice_shared_af(accumulator),
                                result);
  invert_ntt_montgomery_51(result, scratch);
  subtract_reduce_64_a7(v, result);
}

/**
 This function implements <strong>Algorithm 14</strong> of the
 NIST FIPS 203 specification; this is the Kyber CPA-PKE decryption algorithm.

 Algorithm 14 is reproduced below:

 ```plaintext
 Input: decryption key dkₚₖₑ ∈ 𝔹^{384k}.
 Input: ciphertext c ∈ 𝔹^{32(dᵤk + dᵥ)}.
 Output: message m ∈ 𝔹^{32}.

 c₁ ← c[0 : 32dᵤk]
 c₂ ← c[32dᵤk : 32(dᵤk + dᵥ)]
 u ← Decompress_{dᵤ}(ByteDecode_{dᵤ}(c₁))
 v ← Decompress_{dᵥ}(ByteDecode_{dᵥ}(c₂))
 ŝ ← ByteDecode₁₂(dkₚₖₑ)
 w ← v - NTT-¹(ŝᵀ ◦ NTT(u))
 m ← ByteEncode₁(Compress₁(w))
 return m
 ```

 The NIST FIPS 203 standard can be found at
 <https://csrc.nist.gov/pubs/fips/203/ipd>.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt_unpacked
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_unpacked_3e(
    const arr_14 *secret_key, const Eurydice_arr_2b *ciphertext,
    Eurydice_mut_borrow_slice_u8 decrypted, Eurydice_arr_d6 *scratch,
    Eurydice_arr_6c *accumulator) {
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_b7_3e(&lvalue);
  }
  arr_14 u_as_ntt = arr_struct;
  Eurydice_borrow_slice_u8 uu____0 =
      Eurydice_array_to_subslice_to_shared_211(ciphertext, (size_t)960U);
  deserialize_then_decompress_u_82(uu____0, array_to_slice_mut_a11(&u_as_ntt),
                                   scratch);
  arr_fd v = ZERO_64_a7();
  deserialize_then_decompress_ring_element_v_21(
      Eurydice_array_to_subslice_from_shared_5f2(ciphertext, (size_t)960U), &v);
  arr_fd message = ZERO_64_a7();
  compute_message_51(&v, secret_key, &u_as_ntt, &message, scratch, accumulator);
  compress_then_serialize_message_a7(&message, decrypted, scratch);
}

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cpa.decrypt
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- CIPHERTEXT_SIZE= 1088
- VECTOR_U_ENCODED_SIZE= 960
- U_COMPRESSION_FACTOR= 10
- V_COMPRESSION_FACTOR= 4
*/
static KRML_MUSTINLINE void decrypt_3e(Eurydice_borrow_slice_u8 secret_key,
                                       const Eurydice_arr_2b *ciphertext,
                                       Eurydice_mut_borrow_slice_u8 decrypted,
                                       Eurydice_arr_d6 *scratch,
                                       Eurydice_arr_6c *accumulator) {
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_a5_3e(&lvalue);
  }
  arr_14 secret_as_ntt = arr_struct;
  deserialize_vector_51(secret_key, array_to_slice_mut_a11(&secret_as_ntt));
  arr_14 secret_key_unpacked = secret_as_ntt;
  decrypt_unpacked_3e(&secret_key_unpacked, ciphertext, decrypted, scratch,
                      accumulator);
}

/**
This function found in impl {core::ops::function::FnMut<(usize),
libcrux_iot_ml_kem::polynomial::PolynomialRingElement<Vector>[TraitClause@0,
TraitClause@3]> for libcrux_iot_ml_kem::ind_cca::decapsulate::closure<Vector,
Hasher, Scheme, K, K_SQUARED, SECRET_KEY_SIZE, CPA_SECRET_KEY_SIZE,
PUBLIC_KEY_SIZE, CIPHERTEXT_SIZE, T_AS_NTT_ENCODED_SIZE, C1_SIZE, C2_SIZE,
VECTOR_U_COMPRESSION_FACTOR, VECTOR_V_COMPRESSION_FACTOR, C1_BLOCK_SIZE, ETA1,
ETA1_RANDOMNESS_SIZE, ETA2, ETA2_RANDOMNESS_SIZE, PRF_OUTPUT_SIZE1,
PRF_OUTPUT_SIZE2, IMPLICIT_REJECTION_HASH_INPUT_SIZE>[TraitClause@0,
TraitClause@1, TraitClause@2, TraitClause@3, TraitClause@4, TraitClause@5]}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate.call_mut_9b
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
static arr_fd call_mut_9b_5d0(void **_) { return ZERO_64_a7(); }

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- SECRET_KEY_SIZE= 2400
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
- CIPHERTEXT_SIZE= 1088
- T_AS_NTT_ENCODED_SIZE= 1152
- C1_SIZE= 960
- C2_SIZE= 128
- VECTOR_U_COMPRESSION_FACTOR= 10
- VECTOR_V_COMPRESSION_FACTOR= 4
- C1_BLOCK_SIZE= 320
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
- PRF_OUTPUT_SIZE2= 384
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1120
*/
Eurydice_arr_ec libcrux_iot_ml_kem_ind_cca_decapsulate_5d0(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext) {
  Eurydice_borrow_slice_u8_x4 uu____0 =
      libcrux_iot_ml_kem_types_unpack_private_key_64(
          Eurydice_array_to_slice_shared_51(private_key));
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____0.snd;
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____0.thd;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____0.f3;
  Eurydice_arr_ec decrypted;
  uint8_t repeat_expression0[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(decrypted.data, repeat_expression0, (size_t)32U * sizeof(uint8_t));
  Eurydice_arr_d6 scratch = libcrux_iot_ml_kem_vector_portable_ZERO_4e();
  Eurydice_arr_6c accumulator;
  int32_t repeat_expression1[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(accumulator.data, repeat_expression1, (size_t)256U * sizeof(int32_t));
  decrypt_3e(ind_cpa_secret_key, ciphertext,
             Eurydice_array_to_slice_mut_01(&decrypted), &scratch,
             &accumulator);
  Eurydice_arr_c7 to_hash0 = libcrux_iot_ml_kem_utils_into_padded_array_c9(
      Eurydice_array_to_slice_shared_01(&decrypted));
  Eurydice_slice_copy(
      Eurydice_array_to_subslice_from_mut_5f(
          &to_hash0, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE),
      libcrux_secrets_int_classify_public_classify_ref_6d_90(
          ind_cpa_public_key_hash),
      uint8_t);
  Eurydice_arr_c7 hashed;
  uint8_t repeat_expression2[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(hashed.data, repeat_expression2, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_kem_hash_functions_portable_G_07(
      Eurydice_array_to_slice_shared_17(&to_hash0),
      Eurydice_array_to_slice_mut_17(&hashed));
  Eurydice_borrow_slice_u8_x2 uu____1 =
      Eurydice_slice_split_at(Eurydice_array_to_slice_shared_17(&hashed),
                              LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE,
                              uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 shared_secret = uu____1.fst;
  Eurydice_borrow_slice_u8 pseudorandomness = uu____1.snd;
  Eurydice_arr_af to_hash =
      libcrux_iot_ml_kem_utils_into_padded_array_66(implicit_rejection_value);
  Eurydice_mut_borrow_slice_u8 uu____2 =
      Eurydice_array_to_subslice_from_mut_5f1(
          &to_hash, LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2b lvalue0 =
      libcrux_secrets_int_public_integers_classify_27_53(ciphertext[0U]);
  Eurydice_slice_copy(
      uu____2,
      core_array___T__N___as_slice((size_t)1088U, &lvalue0, uint8_t,
                                   Eurydice_borrow_slice_u8),
      uint8_t);
  Eurydice_arr_ec implicit_rejection_shared_secret;
  uint8_t repeat_expression3[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression3[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret.data, repeat_expression3,
         (size_t)32U * sizeof(uint8_t));
  PRF_07_ce(Eurydice_array_to_slice_shared_81(&to_hash),
            Eurydice_array_to_slice_mut_01(&implicit_rejection_shared_secret));
  Eurydice_arr_2b expected_ciphertext = {.data = {0U}};
  arr_14 arr_struct;
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    /* original Rust expression is not an lvalue in C */
    void *lvalue = (void *)0U;
    arr_struct.data[i] = call_mut_9b_5d0(&lvalue);
  }
  arr_14 r_as_ntt = arr_struct;
  arr_fd error_2 = ZERO_64_a7();
  arr_14 cache;
  arr_fd repeat_expression4[3U];
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    repeat_expression4[i] = ZERO_64_a7();
  }
  memcpy(cache.data, repeat_expression4, (size_t)3U * sizeof(arr_fd));
  arr_fd matrix_entry = ZERO_64_a7();
  encrypt_1f0(ind_cpa_public_key, &decrypted, pseudorandomness,
              Eurydice_array_to_slice_mut_06(&expected_ciphertext),
              &matrix_entry, array_to_slice_mut_a11(&r_as_ntt), &error_2,
              &scratch, array_to_slice_mut_a11(&cache), &accumulator);
  Eurydice_arr_ec implicit_rejection_shared_secret_kdf;
  uint8_t repeat_expression5[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(implicit_rejection_shared_secret_kdf.data, repeat_expression5,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_d3(
      Eurydice_array_to_slice_shared_01(&implicit_rejection_shared_secret),
      Eurydice_array_to_slice_mut_01(&implicit_rejection_shared_secret_kdf));
  Eurydice_arr_ec shared_secret_kdf;
  uint8_t repeat_expression6[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression6[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret_kdf.data, repeat_expression6,
         (size_t)32U * sizeof(uint8_t));
  kdf_cc_d3(shared_secret, Eurydice_array_to_slice_mut_01(&shared_secret_kdf));
  Eurydice_arr_ec shared_secret0;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(shared_secret0.data, repeat_expression, (size_t)32U * sizeof(uint8_t));
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2b lvalue1 =
      libcrux_secrets_int_public_integers_classify_27_53(ciphertext[0U]);
  Eurydice_borrow_slice_u8 uu____3 = core_array___T__N___as_slice(
      (size_t)1088U, &lvalue1, uint8_t, Eurydice_borrow_slice_u8);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_2b lvalue =
      libcrux_secrets_int_public_integers_classify_27_53(expected_ciphertext);
  Eurydice_borrow_slice_u8 uu____4 = core_array___T__N___as_slice(
      (size_t)1088U, &lvalue, uint8_t, Eurydice_borrow_slice_u8);
  libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
      uu____3, uu____4, Eurydice_array_to_slice_shared_01(&shared_secret_kdf),
      Eurydice_array_to_slice_shared_01(&implicit_rejection_shared_secret_kdf),
      Eurydice_array_to_slice_mut_01(&shared_secret0));
  return shared_secret0;
}
