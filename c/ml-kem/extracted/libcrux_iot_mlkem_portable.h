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
 * Libcrux: eeb10e030981128f3c8dce2ffcb86b40032b404f
 */

#ifndef libcrux_iot_mlkem_portable_H
#define libcrux_iot_mlkem_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue_additions.h"
#include "libcrux_iot_core.h"
#include "libcrux_iot_sha3.h"

void libcrux_iot_ml_kem_hash_functions_portable_G(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output);

void libcrux_iot_ml_kem_hash_functions_portable_H(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output);

void libcrux_iot_ml_kem_hash_functions_portable_PRFxN(
    Eurydice_dst_ref_shared_b4 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len);

typedef Eurydice_arr_7b libcrux_iot_ml_kem_hash_functions_portable_PortableHash;

Eurydice_arr_7b
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final(
    Eurydice_dst_ref_shared_cf input);

void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks(
    Eurydice_arr_7b *state, Eurydice_dst_ref_mut_8c output);

void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block(
    Eurydice_arr_7b *state, Eurydice_dst_ref_mut_c3 output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_G_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_H_07(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_PRFxN_07(
    Eurydice_dst_ref_shared_b4 input, Eurydice_mut_borrow_slice_u8 outputs,
    size_t out_len);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
Eurydice_arr_7b
libcrux_iot_ml_kem_hash_functions_portable_shake128_init_absorb_final_07(
    Eurydice_dst_ref_shared_cf input);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_first_three_blocks_07(
    Eurydice_arr_7b *self, Eurydice_dst_ref_mut_8c output);

/**
This function found in impl {libcrux_iot_ml_kem::hash_functions::Hash for
libcrux_iot_ml_kem::hash_functions::portable::PortableHash}
*/
void libcrux_iot_ml_kem_hash_functions_portable_shake128_squeeze_next_block_07(
    Eurydice_arr_7b *self, Eurydice_dst_ref_mut_c3 output);

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_ELEMENTS_IN_VECTOR ((size_t)16U)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_FIELD_MODULUS (3329)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS \
  (1353)

typedef Eurydice_arr_d6
    libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector;

Eurydice_arr_d6 libcrux_iot_ml_kem_vector_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_d6 libcrux_iot_ml_kem_vector_portable_ZERO_4e(void);

void libcrux_iot_ml_kem_vector_portable_vector_type_from_i16_array(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_from_i16_array_4e(
    Eurydice_borrow_slice_i16 array, Eurydice_arr_d6 *out);

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (62209U)

#define LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (16U)

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
    int32_t value);

void libcrux_iot_ml_kem_vector_portable_arithmetic_reducing_from_i32_array(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_reducing_from_i32_array_4e(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_d6 *out);

void libcrux_iot_ml_kem_vector_portable_arithmetic_add(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_add_4e(Eurydice_arr_d6 *lhs,
                                               const Eurydice_arr_d6 *rhs);

void libcrux_iot_ml_kem_vector_portable_arithmetic_sub(
    Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_sub_4e(Eurydice_arr_d6 *lhs,
                                               const Eurydice_arr_d6 *rhs);

void libcrux_iot_ml_kem_vector_portable_arithmetic_negate(Eurydice_arr_d6 *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_negate_4e(Eurydice_arr_d6 *vec);

void libcrux_iot_ml_kem_vector_portable_arithmetic_multiply_by_constant(
    Eurydice_arr_d6 *vec, int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_multiply_by_constant_4e(
    Eurydice_arr_d6 *vec, int16_t c);

void libcrux_iot_ml_kem_vector_portable_arithmetic_bitwise_and_with_constant(
    Eurydice_arr_d6 *vec, int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_bitwise_and_with_constant_4e(
    Eurydice_arr_d6 *vec, int16_t c);

/**
 Note: This function is not secret independent
 Only use with public values.
*/
void libcrux_iot_ml_kem_vector_portable_arithmetic_cond_subtract_3329(
    Eurydice_arr_d6 *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_cond_subtract_3329_4e(
    Eurydice_arr_d6 *vec);

#define LIBCRUX_IOT_ML_KEM_VECTOR_PORTABLE_ARITHMETIC_BARRETT_MULTIPLIER (20159)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT (26)

#define LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_R \
  (                                                \
      (int32_t)((uint32_t)1                        \
                << (uint32_t)LIBCRUX_IOT_ML_KEM_VECTOR_TRAITS_BARRETT_SHIFT))

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
int16_t libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce_element(
    int16_t value);

void libcrux_iot_ml_kem_vector_portable_arithmetic_barrett_reduce(
    Eurydice_arr_d6 *vec);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_barrett_reduce_4e(Eurydice_arr_d6 *vec);

/**
 If `fe` is some field element 'x' of the Kyber field and `fer` is congruent to
 `y · MONTGOMERY_R`, this procedure outputs a value that is congruent to
 `x · y`, as follows:

    `fe · fer ≡ x · y · MONTGOMERY_R (mod FIELD_MODULUS)`

 `montgomery_reduce` takes the value `x · y · MONTGOMERY_R` and outputs a
 representative `x · y · MONTGOMERY_R * MONTGOMERY_R^{-1} ≡ x · y (mod
 FIELD_MODULUS)`.
*/
int16_t
libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int16_t fe, int16_t fer);

void libcrux_iot_ml_kem_vector_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_d6 *vec, int16_t c);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_montgomery_multiply_by_constant_4e(
    Eurydice_arr_d6 *vec, int16_t r);

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
uint8_t
libcrux_iot_ml_kem_vector_portable_compress_compress_message_coefficient(
    uint16_t fe);

void libcrux_iot_ml_kem_vector_portable_compress_compress_1(Eurydice_arr_d6 *a);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_compress_1_4e(Eurydice_arr_d6 *a);

uint32_t
libcrux_iot_ml_kem_vector_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint32_t value);

int16_t
libcrux_iot_ml_kem_vector_portable_compress_compress_ciphertext_coefficient(
    uint8_t coefficient_bits, uint16_t fe);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_step(Eurydice_arr_d6 *vec,
                                                     int16_t zeta, size_t i,
                                                     size_t j);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_1_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_1_step_4e(Eurydice_arr_d6 *a,
                                                            int16_t zeta0,
                                                            int16_t zeta1,
                                                            int16_t zeta2,
                                                            int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_2_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_2_step_4e(Eurydice_arr_d6 *a,
                                                            int16_t zeta0,
                                                            int16_t zeta1);

void libcrux_iot_ml_kem_vector_portable_ntt_ntt_layer_3_step(
    Eurydice_arr_d6 *vec, int16_t zeta);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_ntt_layer_3_step_4e(Eurydice_arr_d6 *a,
                                                            int16_t zeta);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_step(Eurydice_arr_d6 *vec,
                                                         int16_t zeta, size_t i,
                                                         size_t j);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_1_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_1_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_2_step(
    Eurydice_arr_d6 *vec, int16_t zeta0, int16_t zeta1);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_2_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta0, int16_t zeta1);

void libcrux_iot_ml_kem_vector_portable_ntt_inv_ntt_layer_3_step(
    Eurydice_arr_d6 *vec, int16_t zeta);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_inv_ntt_layer_3_step_4e(
    Eurydice_arr_d6 *a, int16_t zeta);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_83 out);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, int16_t zeta0, int16_t zeta1, int16_t zeta2,
    int16_t zeta3);

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
void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_fill_cache(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, int16_t zeta, size_t i,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_fill_cache(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_fill_cache_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, Eurydice_arr_d6 *cache, int16_t zeta0,
    int16_t zeta1, int16_t zeta2, int16_t zeta3);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_binomials_use_cache(
    const Eurydice_arr_d6 *a, const Eurydice_arr_d6 *b, size_t i,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache);

void libcrux_iot_ml_kem_vector_portable_ntt_accumulating_ntt_multiply_use_cache(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_accumulating_ntt_multiply_use_cache_4e(
    const Eurydice_arr_d6 *lhs, const Eurydice_arr_d6 *rhs,
    Eurydice_dst_ref_mut_83 out, const Eurydice_arr_d6 *cache);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_1(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_1_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_1(
    Eurydice_borrow_slice_u8 v, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_1_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

typedef struct uint8_t_x4_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
} uint8_t_x4;

uint8_t_x4 libcrux_iot_ml_kem_vector_portable_serialize_serialize_4_int(
    Eurydice_borrow_slice_i16 v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_4(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_4_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

typedef struct int16_t_x8_s {
  int16_t fst;
  int16_t snd;
  int16_t thd;
  int16_t f3;
  int16_t f4;
  int16_t f5;
  int16_t f6;
  int16_t f7;
} int16_t_x8;

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4_int(
    Eurydice_borrow_slice_u8 bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_4(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_4_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

typedef struct uint8_t_x5_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
} uint8_t_x5;

uint8_t_x5 libcrux_iot_ml_kem_vector_portable_serialize_serialize_5_int(
    Eurydice_borrow_slice_i16 v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_5(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_5_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5_int(
    Eurydice_borrow_slice_u8 bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_5(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_5_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

uint8_t_x5 libcrux_iot_ml_kem_vector_portable_serialize_serialize_10_int(
    Eurydice_borrow_slice_i16 v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_10(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_10_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10_int(
    Eurydice_borrow_slice_u8 bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_10(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_10_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

typedef struct uint8_t_x11_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
  uint8_t f3;
  uint8_t f4;
  uint8_t f5;
  uint8_t f6;
  uint8_t f7;
  uint8_t f8;
  uint8_t f9;
  uint8_t f10;
} uint8_t_x11;

uint8_t_x11 libcrux_iot_ml_kem_vector_portable_serialize_serialize_11_int(
    Eurydice_borrow_slice_i16 v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_11(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_11_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

int16_t_x8 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11_int(
    Eurydice_borrow_slice_u8 bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_11(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_11_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

typedef struct uint8_t_x3_s {
  uint8_t fst;
  uint8_t snd;
  uint8_t thd;
} uint8_t_x3;

uint8_t_x3 libcrux_iot_ml_kem_vector_portable_serialize_serialize_12_int(
    Eurydice_borrow_slice_i16 v);

void libcrux_iot_ml_kem_vector_portable_serialize_serialize_12(
    const Eurydice_arr_d6 *v, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_serialize_12_4e(
    const Eurydice_arr_d6 *a, Eurydice_mut_borrow_slice_u8 out);

typedef struct int16_t_x2_s {
  int16_t fst;
  int16_t snd;
} int16_t_x2;

int16_t_x2 libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12_int(
    Eurydice_borrow_slice_u8 bytes);

void libcrux_iot_ml_kem_vector_portable_serialize_deserialize_12(
    Eurydice_borrow_slice_u8 bytes, Eurydice_arr_d6 *out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
void libcrux_iot_ml_kem_vector_portable_deserialize_12_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_arr_d6 *out);

size_t libcrux_iot_ml_kem_vector_portable_sampling_rej_sample(
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out);

/**
This function found in impl {libcrux_iot_ml_kem::vector::traits::Operations for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
size_t libcrux_iot_ml_kem_vector_portable_rej_sample_4e(
    Eurydice_borrow_slice_u8 a, Eurydice_mut_borrow_slice_i16 out);

typedef int16_t
    libcrux_iot_ml_kem_vector_portable_arithmetic_FieldElementTimesMontgomeryR;

typedef int16_t
    libcrux_iot_ml_kem_vector_portable_arithmetic_MontgomeryFieldElement;

typedef int16_t libcrux_iot_ml_kem_vector_portable_vector_type_FieldElement;

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_kem::vector::portable::vector_type::PortableVector}
*/
Eurydice_arr_d6 libcrux_iot_ml_kem_vector_portable_vector_type_clone_9c(
    const Eurydice_arr_d6 *self);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mlkem_portable_H_DEFINED
#endif /* libcrux_iot_mlkem_portable_H */
