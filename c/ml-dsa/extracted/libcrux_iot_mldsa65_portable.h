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

#ifndef libcrux_iot_mldsa65_portable_H
#define libcrux_iot_mldsa65_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_mldsa_core.h"
#include "libcrux_iot_sha3.h"

#define libcrux_iot_ml_dsa_constants_Eta_Two 2
#define libcrux_iot_ml_dsa_constants_Eta_Four 4

typedef uint8_t libcrux_iot_ml_dsa_constants_Eta;

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT /    \
   LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH \
  ((size_t)23U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T         \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH - \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH \
  ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN ((size_t)255U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS (8380417)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_GAMMA2_V261_888 (261888)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_GAMMA2_V95_232 (95232)

typedef int32_t libcrux_iot_ml_dsa_constants_Gamma2;

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_KEY_GENERATION_RANDOMNESS_SIZE \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_MASK_SEED_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_MESSAGE_REPRESENTATIVE_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN ((size_t)814U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T *     \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T *     \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_SIGNING_RANDOMNESS_SIZE ((size_t)32U)

int32_t libcrux_iot_ml_dsa_constants_beta(size_t ones_in_verifier_challenge,
                                          libcrux_iot_ml_dsa_constants_Eta eta);

size_t libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient);

size_t libcrux_iot_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a);

size_t libcrux_iot_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient);

size_t libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient);

size_t libcrux_iot_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient);

size_t libcrux_iot_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size);

size_t libcrux_iot_ml_dsa_constants_verification_key_size(size_t rows_in_a);

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)6U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)3U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)18U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Two)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT ((size_t)17U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - 1) / 88)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT ((size_t)80U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)39U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)20U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A ((size_t)5U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE \
  ((size_t)48U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Four)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT ((size_t)19U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - 1) / 32)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT ((size_t)55U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)49U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A ((size_t)6U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT \
  ((size_t)3U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT \
  ((size_t)20U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A ((size_t)7U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE \
  ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA \
  (libcrux_iot_ml_dsa_constants_Eta_Two)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT ((size_t)19U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2 \
  ((LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS - 1) / 32)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT ((size_t)75U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE \
  ((size_t)60U)

#define LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A ((size_t)8U)

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::constants::Eta}
*/
libcrux_iot_ml_dsa_constants_Eta libcrux_iot_ml_dsa_constants_clone_44(
    const libcrux_iot_ml_dsa_constants_Eta *self);

size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
    libcrux_iot_ml_dsa_constants_Eta eta);

void libcrux_iot_ml_dsa_encoding_signature_set_hint(
    Eurydice_dst_ref_mut_20 out_hint, size_t i, size_t j);

#define LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT ((size_t)13U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW ((size_t)10U)

#define LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT \
  ((size_t)10U)

typedef libcrux_iot_sha3_incremental_UnbufferedXofState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128;

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4;

typedef libcrux_iot_sha3_incremental_UnbufferedXofState
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256;

typedef struct libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4_s {
  libcrux_iot_sha3_state_KeccakState state0;
  libcrux_iot_sha3_state_KeccakState state1;
  libcrux_iot_sha3_state_KeccakState state2;
  libcrux_iot_sha3_state_KeccakState state3;
} libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4;

typedef libcrux_iot_sha3_incremental_Shake256Xof
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof;

libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_borrow_slice_u8 input);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out);

libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state,
    Eurydice_arr_d1 *out0, Eurydice_arr_d1 *out1, Eurydice_arr_d1 *out2,
    Eurydice_arr_d1 *out3);

typedef struct Eurydice_arr_c5_x4_s {
  Eurydice_arr_c5 fst;
  Eurydice_arr_c5 snd;
  Eurydice_arr_c5 thd;
  Eurydice_arr_c5 f3;
} Eurydice_arr_c5_x4;

Eurydice_arr_c5_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state);

libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

typedef struct Eurydice_arr_ff_x4_s {
  Eurydice_arr_ff fst;
  Eurydice_arr_ff snd;
  Eurydice_arr_ff thd;
  Eurydice_arr_ff f3;
} Eurydice_arr_ff_x4;

Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state);

Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state);

Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_d1 *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_c5 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self,
    Eurydice_arr_d1 *out0, Eurydice_arr_d1 *out1, Eurydice_arr_d1 *out2,
    Eurydice_arr_d1 *out3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
Eurydice_arr_c5_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_bd
libcrux_iot_ml_dsa_hash_functions_portable_init_88(void);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self);

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE ((size_t)168U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_FIVE_BLOCKS_SIZE \
  (LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE128_BLOCK_SIZE * (size_t)5U)

#define LIBCRUX_IOT_ML_DSA_HASH_FUNCTIONS_SHAKE256_BLOCK_SIZE ((size_t)136U)

typedef struct uint8_t_x2_s {
  uint8_t fst;
  uint8_t snd;
} uint8_t_x2;

uint16_t libcrux_iot_ml_dsa_sample_generate_domain_separator(uint8_t_x2 _);

Eurydice_arr_31 libcrux_iot_ml_dsa_sample_add_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint8_t_x2 indices);

Eurydice_arr_91 libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint16_t domain_separator);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_ERROR_COEFFICIENT))

typedef Eurydice_arr_4d
    libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients;

Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_vector_type_zero(void);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_zero_c5(void);

void libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_4d *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_4d *out);

void libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    const Eurydice_arr_4d *value, Eurydice_dst_ref_mut_83 out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    const Eurydice_arr_4d *value, Eurydice_dst_ref_mut_83 out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_add_c5(Eurydice_arr_4d *lhs,
                                             const Eurydice_arr_4d *rhs);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_subtract_c5(Eurydice_arr_4d *lhs,
                                                  const Eurydice_arr_4d *rhs);

bool libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    const Eurydice_arr_4d *simd_unit, int32_t bound);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    const Eurydice_arr_4d *simd_unit, int32_t bound);

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS (8380417)

typedef struct int32_t_x2_s {
  int32_t fst;
  int32_t snd;
} int32_t_x2;

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
    int32_t gamma2, int32_t r);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *low,
    Eurydice_arr_4d *high);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *low,
    Eurydice_arr_4d *high);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
    int32_t low, int32_t high, int32_t gamma2);

size_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    const Eurydice_arr_4d *low, const Eurydice_arr_4d *high, int32_t gamma2,
    Eurydice_arr_4d *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    const Eurydice_arr_4d *low, const Eurydice_arr_4d *high, int32_t gamma2,
    Eurydice_arr_4d *hint);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(int32_t gamma2,
                                                                 int32_t r,
                                                                 int32_t hint);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *hint);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *hint);

uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT (32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R \
  (58728449ULL)

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs);

int32_t libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe);

int32_t_x2 libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
    int32_t t);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(
    Eurydice_arr_4d *t0, Eurydice_arr_4d *t1);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_power2round_c5(Eurydice_arr_4d *t0,
                                                     Eurydice_arr_4d *t1);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)((uint32_t)1 << 17U))

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)((uint32_t)1 << 19U))

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 \
  ((int32_t)((uint32_t)1 << 17U))

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK \
  ((int32_t)((uint32_t)                                                                                             \
                 LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1        \
             << 1U) -                                                                                               \
   1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 \
  ((int32_t)((uint32_t)1 << 19U))

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK \
  ((int32_t)((uint32_t)                                                                                             \
                 LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1        \
             << 1U) -                                                                                               \
   1)

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out,
    size_t gamma1_exponent);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out,
    size_t gamma1_exponent);

void libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA \
  (4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA \
  (2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_4d *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_4d *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA \
  (4)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_units);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA \
  (2)

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit);

void libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_4d *out);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_4d *out);

int32_t libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
    int32_t t0);

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK \
  ((int32_t)((uint32_t)1 << (uint32_t)(int32_t)                                               \
                 LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) -                      \
   1)

void libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 out);

void libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out);

void libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_4d *simd_unit, int32_t c);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_ef_s {
  Eurydice_arr_4d data[32U];
} Eurydice_arr_ef;

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_30(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_300(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_42(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_301(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_82(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_420(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_302(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_43(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_820(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_421(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_61(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe0(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_38(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_303(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_25(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_430(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_f4(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_821(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1d(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea0(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d8(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_422(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_60(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_610(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_29(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe1(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_9d(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_380(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_5f(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(Eurydice_arr_ef *re);

int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    Eurydice_arr_4d *simd_unit, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    Eurydice_arr_4d *simd_unit, int32_t zeta1, int32_t zeta2);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_0, int32_t zeta_1);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_0, int32_t zeta_1,
    int32_t zeta_2, int32_t zeta_3);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(Eurydice_arr_ef *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_c5(Eurydice_arr_ef *simd_units);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta0, int32_t zeta1,
    int32_t zeta2, int32_t zeta3);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_00, int32_t zeta_01);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    Eurydice_arr_4d *simd_unit, int32_t zeta);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta1);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    Eurydice_arr_ef *re);

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    const Eurydice_arr_4d *self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_30(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_25(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_43(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_f4(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_82(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1d(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d8(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_42(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_60(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_61(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_29(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_9d(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_38(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_5f(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_300(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_430(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_820(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea0(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_420(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_610(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe0(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_380(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_301(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_821(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_421(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe1(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_302(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_422(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_303(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    Eurydice_arr_ef *re);

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    Eurydice_arr_ef *re);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    Eurydice_arr_ef *simd_units);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 0
*/
void libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_c3(
    Eurydice_arr_4d *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.shift_left_then_reduce_c5 with const generics
- SHIFT_BY= 0
*/
void libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_c3(
    Eurydice_arr_4d *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_reduce_c5(Eurydice_arr_ef *simd_units);

uint8_t_x2 libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width);

/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients

*/
typedef Eurydice_arr_ef libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_f8_s {
  Eurydice_arr_ef data[16U];
} Eurydice_arr_f8;

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.zero_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
Eurydice_arr_ef libcrux_iot_ml_dsa_polynomial_zero_c2_08(void);

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, size_t

*/
typedef struct Eurydice_dst_ref_mut_90_s {
  Eurydice_arr_ef *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_90;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d, size_t

*/
typedef struct Eurydice_dst_ref_shared_90_s {
  const Eurydice_arr_ef *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_90;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.from_i32_array_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_ef *result);

/**
 Sample and write out up to four ring elements.

 If i <= `elements_requested`, a field element with domain separated
 seed according to the provided index is generated in
 `tmp_stack[i]`. After successful rejection sampling in
 `tmp_stack[i]`, the ring element is written to `matrix` at the
 provided index in `indices[i]`.
 `rand_stack` is a working buffer that holds initial Shake output.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_up_to_four_ring_elements_flat with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 matrix, Eurydice_arr_d1 *rand_stack0,
    Eurydice_arr_d1 *rand_stack1, Eurydice_arr_d1 *rand_stack2,
    Eurydice_arr_d1 *rand_stack3, Eurydice_dst_ref_mut_33 tmp_stack,
    size_t start_index, size_t elements_requested);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(size_t columns,
                                                Eurydice_borrow_slice_u8 seed,
                                                Eurydice_dst_ref_mut_90 matrix);

/**
This function found in impl {libcrux_iot_ml_dsa::samplex4::X4Sampler for
libcrux_iot_ml_dsa::samplex4::portable::PortableSampler}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.portable.matrix_flat_ad
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 matrix);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_62_s {
  Eurydice_arr_ef data[8U];
} Eurydice_arr_62;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 randomness,
    size_t *sampled, Eurydice_arr_d0 *out);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_four_error_ring_elements with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    uint16_t start_index, Eurydice_dst_ref_mut_90 re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 s1_s2);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_f5_s {
  Eurydice_arr_ef data[4U];
} Eurydice_arr_f5;

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_08(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    Eurydice_arr_ef *lhs, const Eurydice_arr_ef *rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.add_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_add_c2_08(Eurydice_arr_ef *self,
                                             const Eurydice_arr_ef *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_reduce_08(Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(Eurydice_arr_ef *re);

/**
 Compute InvertNTT(Â ◦ ŝ₁) + s₂
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_as1_plus_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_90 a_as_ntt,
    Eurydice_dst_ref_shared_90 s1_ntt, Eurydice_dst_ref_shared_90 s1_s2,
    Eurydice_dst_ref_mut_90 result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
    Eurydice_dst_ref_mut_90 t0, Eurydice_dst_ref_mut_90 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_borrow_slice_u8 seed, Eurydice_dst_ref_shared_90 t1,
    Eurydice_mut_borrow_slice_u8 verification_key_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_c9(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c7 *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 64
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c7 *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_ef *re,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_borrow_slice_u8 seed_matrix, Eurydice_borrow_slice_u8 seed_signing,
    Eurydice_borrow_slice_u8 verification_key, Eurydice_dst_ref_shared_90 s1_2,
    Eurydice_dst_ref_shared_90 t0,
    Eurydice_mut_borrow_slice_u8 signing_key_serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_10 *signing_key,
    Eurydice_arr_02 *verification_key);

/**
 Generate an ML-DSA-44 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_85
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    Eurydice_arr_ec randomness);

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_c9

*/
typedef struct Option_57_s {
  Option_87_tags tag;
  Eurydice_arr_c9 f0;
} Option_57;

typedef struct libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext_s {
  Eurydice_borrow_slice_u8 context;
  Option_57 pre_hash_oid;
} libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext;

#define libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError 0

typedef uint8_t libcrux_iot_ml_dsa_pre_hash_DomainSeparationError;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext,
libcrux_iot_ml_dsa_pre_hash_DomainSeparationError

*/
typedef struct Result_80_s {
  Result_8e_tags tag;
  union {
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError case_Err;
  } val;
} Result_80;

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(Eurydice_borrow_slice_u8 context,
                                             Option_57 pre_hash_oid);

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
const Option_57 *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Eurydice_borrow_slice_u8 libcrux_iot_ml_dsa_pre_hash_context_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT))

bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(
    Eurydice_borrow_slice_u8 randomness, size_t *out_index, uint64_t *signs,
    Eurydice_arr_6c *result);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.option.Option
with types libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext

*/
typedef struct Option_e3_s {
  Option_87_tags tag;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext f0;
} Option_e3;

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_87_s {
  Result_8e_tags tag;
  libcrux_iot_ml_dsa_types_SigningError f0;
} Result_87;

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_28,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_b2_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_85 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_b2;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_ef *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_90 ring_elements);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_ef *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_90 ring_elements);

/**
 This corresponds to line 6 in algorithm 7 in FIPS 204 (line 7 in algorithm
 8, resp.).

 If `domain_separation_context` is supplied, applies domain
 separation and length encoding to the context string,
 before appending the message (in the regular variant) or the
 pre-hash OID as well as the pre-hashed message digest. Otherwise,
 it is assumed that `message` already contains domain separation
 information.

 In FIPS 204 M' is the concatenation of the domain separated context, any
 potential pre-hash OID and the message (or the message pre-hash). We do not
 explicitely construct the concatenation in memory since it is of statically
 unknown length, but feed its components directly into the incremental XOF.

 Refer to line 10 of Algorithm 2 (and line 5 of Algorithm 3, resp.) in [FIPS
 204](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.204.pdf#section.5)
 for details on the domain separation for regular ML-DSA. Line
 23 of Algorithm 4 (and line 18 of Algorithm 5,resp.) describe domain separation
 for the HashMl-DSA variant.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.derive_message_representative with types
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
    Eurydice_borrow_slice_u8 verification_key_hash,
    const Option_e3 *domain_separation_context,
    Eurydice_borrow_slice_u8 message, Eurydice_arr_c7 *message_representative);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_22 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_5a(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_22 *out0, Eurydice_arr_22 *out1, Eurydice_arr_22 *out2,
    Eurydice_arr_22 *out3);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_ef *result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_20 *out);

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_0e(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_20 *out0, Eurydice_arr_20 *out1, Eurydice_arr_20 *out2,
    Eurydice_arr_20 *out3);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 576
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_5a(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_22 *out);

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256_a1
with const generics
- OUTPUT_LENGTH= 640
*/
void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_0e(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_20 *out);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    const Eurydice_arr_91 *seed, Eurydice_arr_ef *result,
    size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
    size_t dimension, size_t gamma1_exponent, const Eurydice_arr_c7 *seed,
    uint16_t *domain_separator, Eurydice_dst_ref_mut_90 mask);

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_90 matrix,
    Eurydice_dst_ref_shared_90 mask, Eurydice_dst_ref_mut_90 result);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
    size_t dimension, int32_t gamma2, Eurydice_dst_ref_shared_90 t,
    Eurydice_dst_ref_mut_90 low, Eurydice_dst_ref_mut_90 high);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_dst_ref_shared_90 vector,
    Eurydice_mut_borrow_slice_u8 serialized);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_borrow_slice_u8 seed, size_t number_of_ones, Eurydice_arr_ef *re);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_dst_ref_mut_90 vector, const Eurydice_arr_ef *ring_element);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_add_vectors_08(size_t dimension,
                                              Eurydice_dst_ref_mut_90 lhs,
                                              Eurydice_dst_ref_shared_90 rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.subtract_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(Eurydice_arr_ef *self,
                                                  const Eurydice_arr_ef *rhs);

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_90 lhs,
    Eurydice_dst_ref_shared_90 rhs);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.infinity_norm_exceeds_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
bool libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
    const Eurydice_arr_ef *self, int32_t bound);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.arithmetic.vector_infinity_norm_exceeds with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
bool libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_dst_ref_shared_90 vector, int32_t bound);

/**
This function found in impl
{libcrux_iot_ml_dsa::polynomial::PolynomialRingElement<SIMDUnit>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.polynomial.to_i32_array_c2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
Eurydice_arr_6c libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(
    const Eurydice_arr_ef *self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(
    Eurydice_dst_ref_shared_90 low, Eurydice_dst_ref_shared_90 high,
    int32_t gamma2, Eurydice_dst_ref_mut_20 hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_borrow_slice_u8 commitment_hash,
    Eurydice_dst_ref_shared_90 signer_response, Eurydice_dst_ref_shared_20 hint,
    size_t commitment_hash_size, size_t columns_in_a, size_t rows_in_a,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_mut_borrow_slice_u8 signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_b2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature);

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature);

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_SHAKE128_OID \
  ((KRML_CLITERAL(Eurydice_arr_c9){              \
      .data = {6U, 9U, 96U, 134U, 72U, 1U, 101U, 3U, 4U, 2U, 11U}}))

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
Eurydice_arr_c9 libcrux_iot_ml_dsa_pre_hash_oid_0b(void);

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.pre_hash.hash_0b
with types libcrux_iot_ml_dsa_hash_functions_portable_Shake128
with const generics

*/
void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
    Eurydice_borrow_slice_u8 message, Eurydice_mut_borrow_slice_u8 output);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Sign (pre-hashed).
*/
Result_b2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.result.Result
with types (), libcrux_iot_ml_dsa_types_VerificationError

*/
typedef struct Result_5c_s {
  Result_8e_tags tag;
  libcrux_iot_ml_dsa_types_VerificationError f0;
} Result_5c;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_ef *result);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
void libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_90 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
Result_5c libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_mut_borrow_slice_u8 out_commitment_hash,
    Eurydice_dst_ref_mut_90 out_signer_response,
    Eurydice_dst_ref_mut_20 out_hint);

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_borrow_slice_u8 seed, uint8_t_x2 indices, Eurydice_arr_ef *out,
    Eurydice_arr_d1 *rand_stack, Eurydice_arr_c5 *rand_block,
    Eurydice_arr_d0 *tmp_stack);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    Eurydice_arr_4d *simd_unit);

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.shift_left_then_reduce_c5 with const generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
    Eurydice_arr_4d *simd_unit);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
void libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
    Eurydice_arr_ef *re);

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_w_approx
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_borrow_slice_u8 seed,
    Eurydice_arr_d1 *rand_stack, Eurydice_arr_c5 *rand_block,
    Eurydice_arr_d0 *tmp_stack, Eurydice_arr_ef *poly_slot,
    Eurydice_dst_ref_shared_90 signer_response,
    const Eurydice_arr_ef *verifier_challenge_as_ntt,
    Eurydice_dst_ref_mut_90 t1);

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_arithmetic_use_hint_08(
    int32_t gamma2, Eurydice_dst_ref_shared_20 hint,
    Eurydice_dst_ref_mut_90 re_vector);

/**
 The internal verification API.

 If no `domain_separation_context` is supplied, it is assumed that
 `message` already contains the domain separation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_85 *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    const Eurydice_arr_02 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_85 *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature);

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    const Eurydice_arr_02 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_85 *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_85 *signature);

/**
 Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $30size_t
*/
typedef struct Eurydice_arr_51_s {
  Eurydice_arr_ef data[30U];
} Eurydice_arr_51;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $11size_t
*/
typedef struct Eurydice_arr_3d_s {
  Eurydice_arr_ef data[11U];
} Eurydice_arr_3d;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $6size_t
*/
typedef struct Eurydice_arr_05_s {
  Eurydice_arr_ef data[6U];
} Eurydice_arr_05;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_15_s {
  Eurydice_arr_ef data[5U];
} Eurydice_arr_15;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_24 *signing_key,
    Eurydice_arr_29 *verification_key);

/**
 Generate an ML-DSA-65 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    Eurydice_arr_ec randomness);

/**
 Generate an ML-DSA-65 Key Pair
*/
void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    Eurydice_arr_ec randomness, Eurydice_arr_24 *signing_key,
    Eurydice_arr_29 *verification_key);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_aa,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_0f_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_0c case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_0f;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_0f
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature);

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Sign (pre-hashed).
*/
Result_0f
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_GAMMA1_COEFFICIENT))

/**
 The internal verification API.

 If no `domain_separation_context` is supplied, it is assumed that
 `message` already contains the domain separation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_0c *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    const Eurydice_arr_29 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_0c *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature);

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    const Eurydice_arr_29 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_0c *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_0c *signature);

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_error_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_ERROR_COEFFICIENT))

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $56size_t
*/
typedef struct Eurydice_arr_b4_s {
  Eurydice_arr_ef data[56U];
} Eurydice_arr_b4;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $15size_t
*/
typedef struct Eurydice_arr_48_s {
  Eurydice_arr_ef data[15U];
} Eurydice_arr_48;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement_8d
with const generics
- $7size_t
*/
typedef struct Eurydice_arr_33_s {
  Eurydice_arr_ef data[7U];
} Eurydice_arr_33;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.generate_key_pair with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
void libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key);

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_e2 *signing_key,
    Eurydice_arr_43 *verification_key);

/**
 Generate an ML-DSA-87 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_850
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    Eurydice_arr_ec randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_commitment_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA                 \
  (libcrux_iot_ml_dsa_constants_beta(                                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE \
  (libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT))

/**
A monomorphic instance of core.result.Result
with types libcrux_iot_ml_dsa_types_MLDSASignature_06,
libcrux_iot_ml_dsa_types_SigningError

*/
typedef struct Result_20_s {
  Result_8e_tags tag;
  union {
    Eurydice_arr_930 case_Ok;
    libcrux_iot_ml_dsa_types_SigningError case_Err;
  } val;
} Result_20;

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_20
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature);

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_pre_hashed_mut with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Sign (pre-hashed).
*/
Result_20
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness);

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_verification_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNATURE_SIZE \
  (libcrux_iot_ml_dsa_constants_signature_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,            \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,         \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,     \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_GAMMA1_COEFFICIENT))

/**
 The internal verification API.

 If no `domain_separation_context` is supplied, it is assumed that
 `message` already contains the domain separation.
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify_internal with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_930 *signature_serialized);

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    const Eurydice_arr_43 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_930 *signature_serialized);

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature);

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature);

/**
A monomorphic instance of
libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify_pre_hashed with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_pre_hash_SHAKE128_PH with const generics

*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    const Eurydice_arr_43 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_930 *signature_serialized);

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_930 *signature);

/**
 Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature);

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_85
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44KeyPair;

typedef Eurydice_arr_85
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44Signature;

typedef Eurydice_arr_10
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44SigningKey;

typedef Eurydice_arr_02
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_MLDSA44VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROWS_PLUS_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A +                 \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ROWS_TIMES_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A *                  \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65KeyPair;

typedef Eurydice_arr_0c
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65Signature;

typedef Eurydice_arr_24
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65SigningKey;

typedef Eurydice_arr_29
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_MLDSA65VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROWS_PLUS_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A +                 \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ROWS_TIMES_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A *                  \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_VECTOR_SIZE    \
  (libcrux_iot_ml_dsa_constants_commitment_vector_size(                       \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_BITS_PER_COMMITMENT_COEFFICIENT, \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A))

typedef libcrux_iot_ml_dsa_types_MLDSAKeyPair_850
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87KeyPair;

typedef Eurydice_arr_930
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87Signature;

typedef Eurydice_arr_e2
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87SigningKey;

typedef Eurydice_arr_43
    libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_MLDSA87VerificationKey;

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROWS_PLUS_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A +                 \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ROWS_TIMES_COLUMNS \
  (LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A *                  \
   LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)

#define LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNING_KEY_SIZE \
  (libcrux_iot_ml_dsa_constants_signing_key_size(                    \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,              \
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,           \
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE))

#define LIBCRUX_IOT_ML_DSA_PRE_HASH_PRE_HASH_OID_LEN ((size_t)11U)

typedef Eurydice_arr_c9 libcrux_iot_ml_dsa_pre_hash_PreHashOID;

typedef Result_80 libcrux_iot_ml_dsa_pre_hash_PreHashResult;

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::SigningError}
*/
libcrux_iot_ml_dsa_types_SigningError libcrux_iot_ml_dsa_pre_hash_from_49(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e);

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::VerificationError}
*/
libcrux_iot_ml_dsa_types_VerificationError libcrux_iot_ml_dsa_pre_hash_from_97(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e);

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_3_STEP \
  ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_3_STEP_BY \
  ((size_t)1U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_4_STEP \
  ((size_t)16U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_4_STEP_BY \
  ((size_t)2U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_5_STEP \
  ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_5_STEP_BY \
  ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_6_STEP \
  ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_6_STEP_BY \
  ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_7_STEP \
  ((size_t)128U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_INVNTT_INVERT_NTT_AT_LAYER_7_STEP_BY \
  ((size_t)16U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_3_STEP ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_3_STEP_BY ((size_t)1U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_4_STEP ((size_t)16U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_4_STEP_BY ((size_t)2U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_5_STEP ((size_t)32U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_5_STEP_BY ((size_t)4U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_6_STEP ((size_t)64U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_6_STEP_BY ((size_t)8U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_7_STEP ((size_t)128U)

#define LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_NTT_NTT_AT_LAYER_7_STEP_BY \
  ((size_t)16U)

typedef int32_t libcrux_iot_ml_dsa_simd_portable_vector_type_FieldElement;

typedef int32_t libcrux_iot_ml_dsa_simd_traits_FieldElementTimesMontgomeryR;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mldsa65_portable_H_DEFINED
#endif /* libcrux_iot_mldsa65_portable_H */
