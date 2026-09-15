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

#include "internal/libcrux_iot_mldsa65_portable.h"

#include "internal/libcrux_iot_mldsa_core.h"
#include "internal/libcrux_iot_sha3.h"
#include "libcrux_iot_mldsa_core.h"
#include "libcrux_iot_sha3.h"

int32_t libcrux_iot_ml_dsa_constants_beta(
    size_t ones_in_verifier_challenge, libcrux_iot_ml_dsa_constants_Eta eta) {
  size_t eta_val;
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      eta_val = (size_t)2U;
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      eta_val = (size_t)4U;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (int32_t)(ones_in_verifier_challenge * eta_val);
}

size_t libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
    size_t bits_per_commitment_coefficient) {
  return bits_per_commitment_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_commitment_vector_size(
    size_t bits_per_commitment_coefficient, size_t rows_in_a) {
  return libcrux_iot_ml_dsa_constants_commitment_ring_element_size(
             bits_per_commitment_coefficient) *
         rows_in_a;
}

size_t libcrux_iot_ml_dsa_constants_error_ring_element_size(
    size_t bits_per_error_coefficient) {
  return bits_per_error_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
    size_t bits_per_gamma1_coefficient) {
  return bits_per_gamma1_coefficient *
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT / (size_t)8U;
}

size_t libcrux_iot_ml_dsa_constants_signature_size(
    size_t rows_in_a, size_t columns_in_a, size_t max_ones_in_hint,
    size_t commitment_hash_size, size_t bits_per_gamma1_coefficient) {
  return commitment_hash_size +
         columns_in_a * libcrux_iot_ml_dsa_constants_gamma1_ring_element_size(
                            bits_per_gamma1_coefficient) +
         max_ones_in_hint + rows_in_a;
}

size_t libcrux_iot_ml_dsa_constants_signing_key_size(
    size_t rows_in_a, size_t columns_in_a, size_t error_ring_element_size) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH +
         (rows_in_a + columns_in_a) * error_ring_element_size +
         rows_in_a * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
}

size_t libcrux_iot_ml_dsa_constants_verification_key_size(size_t rows_in_a) {
  return LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
         LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * rows_in_a *
             (LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS_MINUS_ONE_BIT_LENGTH -
              LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T) /
             (size_t)8U;
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::constants::Eta}
*/
inline libcrux_iot_ml_dsa_constants_Eta libcrux_iot_ml_dsa_constants_clone_44(
    const libcrux_iot_ml_dsa_constants_Eta *self) {
  return self[0U];
}

KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_encoding_error_chunk_size(
    libcrux_iot_ml_dsa_constants_Eta eta) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      return (size_t)4U;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return (size_t)3U;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_set_hint(
    Eurydice_dst_ref_mut_20 out_hint, size_t i, size_t j) {
  out_hint.ptr[i].data[j] = 1;
}

KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_incremental_shake256_init();
  libcrux_iot_sha3_incremental_shake256_absorb_final(&state, input);
  return state;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake128(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_shake128_ema(out, input);
}

KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  libcrux_iot_sha3_state_KeccakState state0 =
      libcrux_iot_sha3_incremental_shake128_init();
  libcrux_iot_sha3_incremental_shake128_absorb_final(&state0, input0);
  libcrux_iot_sha3_state_KeccakState state1 =
      libcrux_iot_sha3_incremental_shake128_init();
  libcrux_iot_sha3_incremental_shake128_absorb_final(&state1, input1);
  libcrux_iot_sha3_state_KeccakState state2 =
      libcrux_iot_sha3_incremental_shake128_init();
  libcrux_iot_sha3_incremental_shake128_absorb_final(&state2, input2);
  libcrux_iot_sha3_state_KeccakState state3 =
      libcrux_iot_sha3_incremental_shake128_init();
  libcrux_iot_sha3_incremental_shake128_absorb_final(&state3, input3);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state,
    Eurydice_arr_d1 *out0, Eurydice_arr_d1 *out1, Eurydice_arr_d1 *out2,
    Eurydice_arr_d1 *out3) {
  libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
      &state->state0, Eurydice_array_to_slice_mut_4c(out0));
  libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
      &state->state1, Eurydice_array_to_slice_mut_4c(out1));
  libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
      &state->state2, Eurydice_array_to_slice_mut_4c(out2));
  libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
      &state->state3, Eurydice_array_to_slice_mut_4c(out3));
}

KRML_MUSTINLINE Eurydice_arr_c5_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *state) {
  Eurydice_arr_c5 out0;
  uint8_t repeat_expression0[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out0.data, repeat_expression0, (size_t)168U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice_mut_2c(&out0));
  Eurydice_arr_c5 out1;
  uint8_t repeat_expression1[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out1.data, repeat_expression1, (size_t)168U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice_mut_2c(&out1));
  Eurydice_arr_c5 out2;
  uint8_t repeat_expression2[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out2.data, repeat_expression2, (size_t)168U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice_mut_2c(&out2));
  Eurydice_arr_c5 out3;
  uint8_t repeat_expression[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out3.data, repeat_expression, (size_t)168U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice_mut_2c(&out3));
  return (KRML_CLITERAL(Eurydice_arr_c5_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  libcrux_iot_sha3_state_KeccakState state0 =
      libcrux_iot_sha3_incremental_shake256_init();
  libcrux_iot_sha3_incremental_shake256_absorb_final(&state0, input0);
  libcrux_iot_sha3_state_KeccakState state1 =
      libcrux_iot_sha3_incremental_shake256_init();
  libcrux_iot_sha3_incremental_shake256_absorb_final(&state1, input1);
  libcrux_iot_sha3_state_KeccakState state2 =
      libcrux_iot_sha3_incremental_shake256_init();
  libcrux_iot_sha3_incremental_shake256_absorb_final(&state2, input2);
  libcrux_iot_sha3_state_KeccakState state3 =
      libcrux_iot_sha3_incremental_shake256_init();
  libcrux_iot_sha3_incremental_shake256_absorb_final(&state3, input3);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4){
      .state0 = state0, .state1 = state1, .state2 = state2, .state3 = state3});
}

KRML_MUSTINLINE Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  Eurydice_arr_ff out0;
  uint8_t repeat_expression0[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out0.data, repeat_expression0, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
      &state->state0, Eurydice_array_to_slice_mut_58(&out0));
  Eurydice_arr_ff out1;
  uint8_t repeat_expression1[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out1.data, repeat_expression1, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
      &state->state1, Eurydice_array_to_slice_mut_58(&out1));
  Eurydice_arr_ff out2;
  uint8_t repeat_expression2[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out2.data, repeat_expression2, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
      &state->state2, Eurydice_array_to_slice_mut_58(&out2));
  Eurydice_arr_ff out3;
  uint8_t repeat_expression[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out3.data, repeat_expression, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
      &state->state3, Eurydice_array_to_slice_mut_58(&out3));
  return (KRML_CLITERAL(Eurydice_arr_ff_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

KRML_MUSTINLINE Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *state) {
  Eurydice_arr_ff out0;
  uint8_t repeat_expression0[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out0.data, repeat_expression0, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
      &state->state0, Eurydice_array_to_slice_mut_58(&out0));
  Eurydice_arr_ff out1;
  uint8_t repeat_expression1[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out1.data, repeat_expression1, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
      &state->state1, Eurydice_array_to_slice_mut_58(&out1));
  Eurydice_arr_ff out2;
  uint8_t repeat_expression2[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out2.data, repeat_expression2, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
      &state->state2, Eurydice_array_to_slice_mut_58(&out2));
  Eurydice_arr_ff out3;
  uint8_t repeat_expression[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out3.data, repeat_expression, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
      &state->state3, Eurydice_array_to_slice_mut_58(&out3));
  return (KRML_CLITERAL(Eurydice_arr_ff_x4){
      .fst = out0, .snd = out1, .thd = out2, .f3 = out3});
}

KRML_MUSTINLINE Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state) {
  Eurydice_arr_ff out;
  uint8_t repeat_expression[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
      state, Eurydice_array_to_slice_mut_58(&out));
  return out;
}

KRML_MUSTINLINE Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
    libcrux_iot_sha3_state_KeccakState *state) {
  Eurydice_arr_ff out;
  uint8_t repeat_expression[136U];
  for (size_t i = (size_t)0U; i < (size_t)136U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)136U * sizeof(uint8_t));
  libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
      state, Eurydice_array_to_slice_mut_58(&out));
  return out;
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_sha3_incremental_shake128_init();
  libcrux_iot_sha3_incremental_shake128_absorb_final(&state, input);
  return state;
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_d1 *out) {
  libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
      self, Eurydice_array_to_slice_mut_4c(out));
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_c5 *out) {
  libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
      self, Eurydice_array_to_slice_mut_2c(out));
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128}
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(
    Eurydice_borrow_slice_u8 input, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128(input, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self,
    Eurydice_arr_d1 *out0, Eurydice_arr_d1 *out1, Eurydice_arr_d1 *out2,
    Eurydice_arr_d1 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_x4(
      self, out0, out1, out2, out3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake128::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake128X4}
*/
KRML_MUSTINLINE Eurydice_arr_c5_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_x4(
      self);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(
    Eurydice_borrow_slice_u8 input) {
  return libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_shake256(
      input);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
KRML_MUSTINLINE Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(
    libcrux_iot_sha3_state_KeccakState *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_shake256(
      self);
}

/**
This function found in impl
{libcrux_iot_ml_dsa::hash_functions::shake256::DsaXof for
libcrux_iot_ml_dsa::hash_functions::portable::Shake256}
*/
KRML_MUSTINLINE Eurydice_arr_ff
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
    libcrux_iot_sha3_state_KeccakState *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_shake256(
      self);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_incremental_absorb_e2(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_incremental_absorb_final_e2(self, input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_bd
libcrux_iot_ml_dsa_hash_functions_portable_init_88(void) {
  return libcrux_iot_sha3_incremental_new_e2();
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::Xof
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256Xof}
*/
void libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_incremental_squeeze_e2(self, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4
libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_init_absorb_x4(
      input0, input1, input2, input3);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_first_block_x4(
      self);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
KRML_MUSTINLINE Eurydice_arr_ff_x4
libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
    libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 *self) {
  return libcrux_iot_ml_dsa_hash_functions_portable_shake256_squeeze_next_block_x4(
      self);
}

KRML_MUSTINLINE uint16_t
libcrux_iot_ml_dsa_sample_generate_domain_separator(uint8_t_x2 _) {
  uint8_t row = _.fst;
  uint8_t column = _.snd;
  return (uint32_t)(uint16_t)(uint32_t)column |
         (uint32_t)(uint16_t)(uint32_t)row << 8U;
}

KRML_MUSTINLINE Eurydice_arr_31 libcrux_iot_ml_dsa_sample_add_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint8_t_x2 indices) {
  Eurydice_arr_31 out = {.data = {0U}};
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d41(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  uint16_t domain_separator =
      libcrux_iot_ml_dsa_sample_generate_domain_separator(indices);
  out.data[32U] = (uint8_t)(uint32_t)domain_separator;
  out.data[33U] = (uint8_t)((uint32_t)domain_separator >> 8U & 0xFFFFU);
  return out;
}

KRML_MUSTINLINE Eurydice_arr_91
libcrux_iot_ml_dsa_sample_add_error_domain_separator(
    Eurydice_borrow_slice_u8 slice, uint16_t domain_separator) {
  Eurydice_arr_91 out;
  uint8_t repeat_expression[66U];
  for (size_t i = (size_t)0U; i < (size_t)66U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)66U * sizeof(uint8_t));
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d42(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  out.data[64U] = libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)(uint32_t)domain_separator);
  out.data[65U] = libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)((uint32_t)domain_separator >> 8U & 0xFFFFU));
  return out;
}

Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_vector_type_zero(void) {
  Eurydice_arr_4d lit;
  int32_t repeat_expression[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(lit.data, repeat_expression, (size_t)8U * sizeof(int32_t));
  return lit;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_zero_c5(void) {
  return libcrux_iot_ml_dsa_simd_portable_vector_type_zero();
}

void libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_4d *out) {
  Eurydice_slice_copy(
      Eurydice_array_to_slice_mut_fd(out),
      Eurydice_slice_subslice_shared_47(
          array,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end =
                  LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})),
      int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_4d *out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_from_coefficient_array(array,
                                                                      out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(
    const Eurydice_arr_4d *value, Eurydice_dst_ref_mut_83 out) {
  Eurydice_dst_ref_mut_83 uu____0 = out;
  Eurydice_slice_copy(
      uu____0,
      Eurydice_array_to_slice_shared_fd(
          libcrux_secrets_int_public_integers_declassify_ref_ad_70(value)),
      int32_t);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
    const Eurydice_arr_4d *value, Eurydice_dst_ref_mut_83 out) {
  libcrux_iot_ml_dsa_simd_portable_vector_type_to_coefficient_array(value, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_add(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->data[uu____0] += rhs->data[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_add_c5(Eurydice_arr_4d *lhs,
                                             const Eurydice_arr_4d *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_add(lhs, rhs);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    size_t uu____0 = i0;
    lhs->data[uu____0] -= rhs->data[i0];
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_subtract_c5(Eurydice_arr_4d *lhs,
                                                  const Eurydice_arr_4d *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(lhs, rhs);
}

KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
    const Eurydice_arr_4d *simd_unit, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t coefficient = simd_unit->data[i0];
    int32_t sign = coefficient >> 31U;
    int32_t normalized =
        coefficient -
        (sign &
         libcrux_secrets_int_public_integers_classify_27_a8(2) * coefficient);
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_secrets_int_public_integers_declassify_d8_a8(
                    normalized) >= bound;
    }
    result = uu____0;
  }
  return result;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
bool libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
    const Eurydice_arr_4d *simd_unit, int32_t bound) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_infinity_norm_exceeds(
      simd_unit, bound);
}

KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(int32_t gamma2,
                                                              int32_t r) {
  int32_t r0 = r + (r >> 31U & LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t ceil_of_r_by_128 = (r0 + 127) >> 7U;
  int32_t r1;
  switch (gamma2) {
    case 95232: {
      int32_t result =
          (ceil_of_r_by_128 * 11275 + (int32_t)((uint32_t)1 << 23U)) >> 24U;
      r1 = (result ^
            (libcrux_secrets_int_public_integers_classify_27_a8(43) - result) >>
                31U) &
           result;
      break;
    }
    case 261888: {
      int32_t result =
          (ceil_of_r_by_128 * 1025 + (int32_t)((uint32_t)1 << 21U)) >> 22U;
      r1 = result & 15;
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  int32_t alpha = gamma2 * 2;
  int32_t r00 = r0 - r1 * alpha;
  r00 -= (libcrux_secrets_int_public_integers_classify_27_a8(
              (LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS - 1) / 2) -
          r00) >>
             31U &
         LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
  return (KRML_CLITERAL(int32_t_x2){.fst = r00, .snd = r1});
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *low,
    Eurydice_arr_4d *high) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
            gamma2, simd_unit->data[i0]);
    int32_t uu____1 = uu____0.snd;
    low->data[i0] = uu____0.fst;
    high->data[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_decompose_c5(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *low,
    Eurydice_arr_4d *high) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose(gamma2, simd_unit, low,
                                                        high);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(int32_t low,
                                                             int32_t high,
                                                             int32_t gamma2) {
  int32_t uu____0;
  if (low > gamma2) {
    uu____0 = 1;
  } else if (low < -gamma2) {
    uu____0 = 1;
  } else if (low == -gamma2) {
    if (high != 0) {
      uu____0 = 1;
    } else {
      uu____0 = 0;
    }
  } else {
    uu____0 = 0;
  }
  return uu____0;
}

KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(
    const Eurydice_arr_4d *low, const Eurydice_arr_4d *high, int32_t gamma2,
    Eurydice_arr_4d *hint) {
  size_t one_hints_count = (size_t)0U;
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(
        libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_one_hint(
            libcrux_secrets_int_public_integers_declassify_d8_a8(low->data[i0]),
            libcrux_secrets_int_public_integers_declassify_d8_a8(
                high->data[i0]),
            gamma2));
    hint->data[i0] = uu____0;
    one_hints_count +=
        (size_t)libcrux_secrets_int_public_integers_declassify_d8_a8(
            hint->data[i0]);
  }
  return one_hints_count;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
    const Eurydice_arr_4d *low, const Eurydice_arr_4d *high, int32_t gamma2,
    Eurydice_arr_4d *hint) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_compute_hint(low, high,
                                                                  gamma2, hint);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(int32_t gamma2,
                                                         int32_t r,
                                                         int32_t hint) {
  int32_t_x2 uu____0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_decompose_element(
          gamma2, libcrux_secrets_int_public_integers_classify_27_a8(r));
  int32_t r00 = uu____0.fst;
  int32_t r10 = uu____0.snd;
  int32_t_x2 uu____1 = {
      .fst = libcrux_secrets_int_public_integers_declassify_d8_a8(r00),
      .snd = libcrux_secrets_int_public_integers_declassify_d8_a8(r10)};
  int32_t r0 = uu____1.fst;
  int32_t r1 = uu____1.snd;
  int32_t uu____2;
  if (!(hint == 0)) {
    switch (gamma2) {
      case 95232: {
        if (r0 > 0) {
          if (r1 == 43) {
            uu____2 = 0;
          } else {
            uu____2 = r1 + hint;
          }
        } else if (r1 == 0) {
          uu____2 = 43;
        } else {
          uu____2 = r1 - hint;
        }
        break;
      }
      case 261888: {
        if (r0 > 0) {
          uu____2 = (r1 + hint) & 15;
        } else {
          uu____2 = (r1 - hint) & 15;
        }
        break;
      }
      default: {
        KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                          "panic!");
        KRML_HOST_EXIT(255U);
      }
    }
    return uu____2;
  }
  return r1;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *hint) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t uu____0 = libcrux_secrets_int_public_integers_classify_27_a8(
        libcrux_iot_ml_dsa_simd_portable_arithmetic_use_one_hint(
            gamma2,
            libcrux_secrets_int_public_integers_declassify_d8_a8(
                simd_unit->data[i0]),
            libcrux_secrets_int_public_integers_declassify_d8_a8(
                hint->data[i0])));
    hint->data[i0] = uu____0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
    int32_t gamma2, const Eurydice_arr_4d *simd_unit, Eurydice_arr_4d *hint) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_use_hint(gamma2, simd_unit, hint);
}

KRML_MUSTINLINE uint64_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
    uint8_t n, uint64_t value) {
  return value & ((1ULL << (uint32_t)n) - 1ULL);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
    int64_t value) {
  uint64_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT,
          libcrux_secrets_int_as_u64_60(value)) *
      LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_INVERSE_OF_MODULUS_MOD_MONTGOMERY_R;
  int32_t k = libcrux_secrets_int_as_i32_a3(
      libcrux_iot_ml_dsa_simd_portable_arithmetic_get_n_least_significant_bits(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT, t));
  int64_t k_times_modulus =
      libcrux_secrets_int_as_i64_36(k) *
      libcrux_secrets_int_public_integers_classify_27_b8(
          (int64_t)LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t c = libcrux_secrets_int_as_i32_60(
      k_times_modulus >>
      (uint32_t)LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  int32_t value_high = libcrux_secrets_int_as_i32_60(
      value >>
      (uint32_t)LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ARITHMETIC_MONTGOMERY_SHIFT);
  return value_high - c;
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    lhs->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            libcrux_secrets_int_as_i64_36(lhs->data[i0]) *
            libcrux_secrets_int_as_i64_36(rhs->data[i0]));
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(
    Eurydice_arr_4d *lhs, const Eurydice_arr_4d *rhs) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply(lhs, rhs);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(int32_t fe) {
  int32_t quotient = (fe + (int32_t)((uint32_t)1 << 22U)) >> 23U;
  return fe - quotient * LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS;
}

KRML_MUSTINLINE int32_t_x2
libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(int32_t t) {
  int32_t t2 = t + (t >> 31U & LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_FIELD_MODULUS);
  int32_t t1 =
      (t2 - 1 +
       (int32_t)((uint32_t)1
                 << (uint32_t)(LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                               (size_t)1U))) >>
      (uint32_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T;
  int32_t t0 =
      t2 - (int32_t)((uint32_t)t1 << (uint32_t)
                         LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T);
  return (KRML_CLITERAL(int32_t_x2){.fst = t0, .snd = t1});
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(
    Eurydice_arr_4d *t0, Eurydice_arr_4d *t1) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    int32_t_x2 uu____0 =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round_element(
            t0->data[i0]);
    int32_t uu____1 = uu____0.snd;
    t0->data[i0] = uu____0.fst;
    t1->data[i0] = uu____1;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_power2round_c5(Eurydice_arr_4d *t0,
                                                     Eurydice_arr_4d *t1) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_power2round(t0, t1);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)3U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        randomness, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = _cloop_i * (size_t)3U,
                        .end = _cloop_i * (size_t)3U + (size_t)3U}));
    int32_t b0 = (int32_t)(uint32_t)bytes.ptr[0U];
    int32_t b1 = (int32_t)(uint32_t)bytes.ptr[1U];
    int32_t b2 = (int32_t)(uint32_t)bytes.ptr[2U];
    int32_t coefficient =
        (((int32_t)((uint32_t)b2 << 16U) | (int32_t)((uint32_t)b1 << 8U)) |
         b0) &
        8388607;
    if (coefficient < LIBCRUX_IOT_ML_DSA_CONSTANTS_FIELD_MODULUS) {
      out.ptr[sampled] = coefficient;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_field_modulus(
      randomness, out);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    uint8_t try_0 = (uint32_t)byte[0U] & 15U;
    uint8_t try_1 = (uint32_t)byte[0U] >> 4U;
    if (libcrux_secrets_int_public_integers_declassify_d8_90(try_0) < 15U) {
      int32_t try_00 = libcrux_secrets_int_as_i32_59(try_0);
      int32_t try_0_mod_5 = try_00 - (try_00 * 26 >> 7U) * 5;
      out.ptr[sampled] =
          libcrux_secrets_int_public_integers_classify_27_a8(2) - try_0_mod_5;
      sampled++;
    }
    if (libcrux_secrets_int_public_integers_declassify_d8_90(try_1) < 15U) {
      int32_t try_10 = libcrux_secrets_int_as_i32_59(try_1);
      int32_t try_1_mod_5 = try_10 - (try_10 * 26 >> 7U) * 5;
      out.ptr[sampled] =
          libcrux_secrets_int_public_integers_classify_27_a8(2) - try_1_mod_5;
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_2(
      randomness, out);
}

KRML_MUSTINLINE size_t
libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  size_t sampled = (size_t)0U;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    uint8_t try_0 = (uint32_t)byte[0U] & 15U;
    uint8_t try_1 = (uint32_t)byte[0U] >> 4U;
    if (libcrux_secrets_int_public_integers_declassify_d8_90(try_0) < 9U) {
      out.ptr[sampled] = libcrux_secrets_int_public_integers_classify_27_a8(4) -
                         libcrux_secrets_int_as_i32_59(try_0);
      sampled++;
    }
    if (libcrux_secrets_int_public_integers_declassify_d8_90(try_1) < 9U) {
      out.ptr[sampled] = libcrux_secrets_int_public_integers_classify_27_a8(4) -
                         libcrux_secrets_int_as_i32_59(try_1);
      sampled++;
    }
  }
  return sampled;
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
size_t
libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
    Eurydice_borrow_slice_u8 randomness, Eurydice_dst_ref_mut_83 out) {
  return libcrux_iot_ml_dsa_simd_portable_sample_rejection_sample_less_than_eta_equals_4(
      randomness, out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_83 coefficients =
        Eurydice_array_to_subslice_shared_44(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = i0 * (size_t)4U,
                           .end = i0 * (size_t)4U + (size_t)4U}));
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[0U]);
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[1U]);
    int32_t coefficient2 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[2U]);
    int32_t coefficient3 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[3U]);
    serialized.ptr[(size_t)9U * i0] = (uint8_t)coefficient0;
    serialized.ptr[(size_t)9U * i0 + (size_t)1U] =
        (uint8_t)(coefficient0 >> 8U);
    serialized.ptr[(size_t)9U * i0 + (size_t)2U] =
        (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)9U * i0 + (size_t)2U;
    serialized.ptr[uu____0] =
        (uint32_t)serialized.ptr[uu____0] |
        (uint32_t)(uint8_t)(int32_t)((uint32_t)coefficient1 << 2U);
    serialized.ptr[(size_t)9U * i0 + (size_t)3U] =
        (uint8_t)(coefficient1 >> 6U);
    serialized.ptr[(size_t)9U * i0 + (size_t)4U] =
        (uint8_t)(coefficient1 >> 14U);
    size_t uu____1 = (size_t)9U * i0 + (size_t)4U;
    serialized.ptr[uu____1] =
        (uint32_t)serialized.ptr[uu____1] |
        (uint32_t)(uint8_t)(int32_t)((uint32_t)coefficient2 << 4U);
    serialized.ptr[(size_t)9U * i0 + (size_t)5U] =
        (uint8_t)(coefficient2 >> 4U);
    serialized.ptr[(size_t)9U * i0 + (size_t)6U] =
        (uint8_t)(coefficient2 >> 12U);
    size_t uu____2 = (size_t)9U * i0 + (size_t)6U;
    serialized.ptr[uu____2] =
        (uint32_t)serialized.ptr[uu____2] |
        (uint32_t)(uint8_t)(int32_t)((uint32_t)coefficient3 << 6U);
    serialized.ptr[(size_t)9U * i0 + (size_t)7U] =
        (uint8_t)(coefficient3 >> 2U);
    serialized.ptr[(size_t)9U * i0 + (size_t)8U] =
        (uint8_t)(coefficient3 >> 10U);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_83 coefficients =
        Eurydice_array_to_subslice_shared_44(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    int32_t coefficient0 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[0U]);
    int32_t coefficient1 =
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_SERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1 -
        libcrux_secrets_int_public_integers_declassify_d8_a8(
            coefficients.ptr[1U]);
    serialized.ptr[(size_t)5U * i0] = (uint8_t)coefficient0;
    serialized.ptr[(size_t)5U * i0 + (size_t)1U] =
        (uint8_t)(coefficient0 >> 8U);
    serialized.ptr[(size_t)5U * i0 + (size_t)2U] =
        (uint8_t)(coefficient0 >> 16U);
    size_t uu____0 = (size_t)5U * i0 + (size_t)2U;
    serialized.ptr[uu____0] =
        (uint32_t)serialized.ptr[uu____0] |
        (uint32_t)(uint8_t)(int32_t)((uint32_t)coefficient1 << 4U);
    serialized.ptr[(size_t)5U * i0 + (size_t)3U] =
        (uint8_t)(coefficient1 >> 4U);
    serialized.ptr[(size_t)5U * i0 + (size_t)4U] =
        (uint8_t)(coefficient1 >> 12U);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  switch ((uint32_t)(uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_17(
          simd_unit, serialized);
      break;
    }
    case 19U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize_when_gamma1_is_2_pow_19(
          simd_unit, serialized);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_serialize(
      simd_unit, serialized, gamma1_exponent);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)9U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)9U, .end = i0 * (size_t)9U + (size_t)9U}));
    int32_t coefficient0 = libcrux_secrets_int_as_i32_59(bytes.ptr[0U]);
    coefficient0 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[1U]) << 8U);
    coefficient0 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[2U])
                  << 16U);
    coefficient0 &=
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 = libcrux_secrets_int_as_i32_59(bytes.ptr[2U]) >> 2U;
    coefficient1 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[3U]) << 6U);
    coefficient1 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[4U])
                  << 14U);
    coefficient1 &=
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient2 = libcrux_secrets_int_as_i32_59(bytes.ptr[4U]) >> 4U;
    coefficient2 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[5U]) << 4U);
    coefficient2 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[6U])
                  << 12U);
    coefficient2 &=
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient3 = libcrux_secrets_int_as_i32_59(bytes.ptr[6U]) >> 6U;
    coefficient3 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[7U]) << 2U);
    coefficient3 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[8U])
                  << 10U);
    coefficient3 &=
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1_TIMES_2_BITMASK;
    simd_unit->data[(size_t)4U * i0] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1) -
        coefficient0;
    simd_unit->data[(size_t)4U * i0 + (size_t)1U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1) -
        coefficient1;
    simd_unit->data[(size_t)4U * i0 + (size_t)2U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1) -
        coefficient2;
    simd_unit->data[(size_t)4U * i0 + (size_t)3U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_17_GAMMA1) -
        coefficient3;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit) {
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)5U, .end = i0 * (size_t)5U + (size_t)5U}));
    int32_t coefficient0 = libcrux_secrets_int_as_i32_59(bytes.ptr[0U]);
    coefficient0 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[1U]) << 8U);
    coefficient0 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[2U])
                  << 16U);
    coefficient0 &=
        LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1_TIMES_2_BITMASK;
    int32_t coefficient1 = libcrux_secrets_int_as_i32_59(bytes.ptr[2U]) >> 4U;
    coefficient1 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[3U]) << 4U);
    coefficient1 |=
        (int32_t)((uint32_t)libcrux_secrets_int_as_i32_59(bytes.ptr[4U])
                  << 12U);
    simd_unit->data[(size_t)2U * i0] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1) -
        coefficient0;
    simd_unit->data[(size_t)2U * i0 + (size_t)1U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_GAMMA1_DESERIALIZE_WHEN_GAMMA1_IS_2_POW_19_GAMMA1) -
        coefficient1;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out,
    size_t gamma1_exponent) {
  switch ((uint32_t)(uint8_t)gamma1_exponent) {
    case 17U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_17(
          serialized, out);
      break;
    }
    case 19U: {
      libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize_when_gamma1_is_2_pow_19(
          serialized, out);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out,
    size_t gamma1_exponent) {
  libcrux_iot_ml_dsa_simd_portable_encoding_gamma1_deserialize(serialized, out,
                                                               gamma1_exponent);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  switch ((uint32_t)(uint8_t)serialized.meta) {
    case 4U: {
      break;
    }
    case 6U: {
      for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
        size_t i0 = i;
        Eurydice_dst_ref_shared_83 coefficients =
            Eurydice_array_to_subslice_shared_44(
                simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                               .start = i0 * (size_t)4U,
                               .end = i0 * (size_t)4U + (size_t)4U}));
        uint8_t coefficient0 =
            libcrux_secrets_int_as_u8_36(coefficients.ptr[0U]);
        uint8_t coefficient1 =
            libcrux_secrets_int_as_u8_36(coefficients.ptr[1U]);
        uint8_t coefficient2 =
            libcrux_secrets_int_as_u8_36(coefficients.ptr[2U]);
        uint8_t coefficient3 =
            libcrux_secrets_int_as_u8_36(coefficients.ptr[3U]);
        serialized.ptr[(size_t)3U * i0] =
            (uint32_t)coefficient1 << 6U | (uint32_t)coefficient0;
        serialized.ptr[(size_t)3U * i0 + (size_t)1U] =
            (uint32_t)coefficient2 << 4U | (uint32_t)coefficient1 >> 2U;
        serialized.ptr[(size_t)3U * i0 + (size_t)2U] =
            (uint32_t)coefficient3 << 2U | (uint32_t)coefficient2 >> 4U;
      }
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_83 coefficients =
        Eurydice_array_to_subslice_shared_44(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    uint8_t coefficient0 = libcrux_secrets_int_as_u8_36(coefficients.ptr[0U]);
    uint8_t coefficient1 = libcrux_secrets_int_as_u8_36(coefficients.ptr[1U]);
    serialized.ptr[i0] = (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_commitment_serialize(simd_unit,
                                                                 serialized);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)2U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_83 coefficients =
        Eurydice_array_to_subslice_shared_44(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = i0 * (size_t)2U,
                           .end = i0 * (size_t)2U + (size_t)2U}));
    uint8_t coefficient0 = libcrux_secrets_int_as_u8_36(
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA) -
        coefficients.ptr[0U]);
    uint8_t coefficient1 = libcrux_secrets_int_as_u8_36(
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_4_ETA) -
        coefficients.ptr[1U]);
    serialized.ptr[i0] = (uint32_t)coefficient1 << 4U | (uint32_t)coefficient0;
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  uint8_t coefficient0 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[0U]);
  uint8_t coefficient1 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[1U]);
  uint8_t coefficient2 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[2U]);
  uint8_t coefficient3 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[3U]);
  uint8_t coefficient4 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[4U]);
  uint8_t coefficient5 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[5U]);
  uint8_t coefficient6 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[6U]);
  uint8_t coefficient7 = libcrux_secrets_int_as_u8_36(
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_SERIALIZE_WHEN_ETA_IS_2_ETA) -
      simd_unit->data[7U]);
  serialized.ptr[0U] =
      ((uint32_t)coefficient2 << 6U | (uint32_t)coefficient1 << 3U) |
      (uint32_t)coefficient0;
  serialized.ptr[1U] =
      (((uint32_t)coefficient5 << 7U | (uint32_t)coefficient4 << 4U) |
       (uint32_t)coefficient3 << 1U) |
      (uint32_t)coefficient2 >> 2U;
  serialized.ptr[2U] =
      ((uint32_t)coefficient7 << 5U | (uint32_t)coefficient6 << 2U) |
      (uint32_t)coefficient5 >> 1U;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_4d *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_4(
          simd_unit, serialized);
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize_when_eta_is_2(
      simd_unit, serialized);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_4d *simd_unit,
    Eurydice_mut_borrow_slice_u8 serialized) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_serialize(eta, simd_unit,
                                                            serialized);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_units) {
  for (size_t i = (size_t)0U; i < serialized.meta; i++) {
    size_t i0 = i;
    const uint8_t *byte = &serialized.ptr[i0];
    simd_units->data[(size_t)2U * i0] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA) -
        libcrux_secrets_int_as_i32_59((uint32_t)byte[0U] & 15U);
    simd_units->data[(size_t)2U * i0 + (size_t)1U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_4_ETA) -
        libcrux_secrets_int_as_i32_59((uint32_t)byte[0U] >> 4U);
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit) {
  int32_t byte0 = libcrux_secrets_int_as_i32_59(serialized.ptr[0U]);
  int32_t byte1 = libcrux_secrets_int_as_i32_59(serialized.ptr[1U]);
  int32_t byte2 = libcrux_secrets_int_as_i32_59(serialized.ptr[2U]);
  simd_unit->data[0U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte0 & 7);
  simd_unit->data[1U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte0 >> 3U & 7);
  simd_unit->data[2U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      ((byte0 >> 6U | (int32_t)((uint32_t)byte1 << 2U)) & 7);
  simd_unit->data[3U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte1 >> 1U & 7);
  simd_unit->data[4U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte1 >> 4U & 7);
  simd_unit->data[5U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      ((byte1 >> 7U | (int32_t)((uint32_t)byte2 << 1U)) & 7);
  simd_unit->data[6U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte2 >> 2U & 7);
  simd_unit->data[7U] =
      libcrux_secrets_int_public_integers_classify_27_a8(
          LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_ERROR_DESERIALIZE_WHEN_ETA_IS_2_ETA) -
      (byte2 >> 5U & 7);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_4d *out) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_4(
          serialized, out);
      return;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize_when_eta_is_2(
      serialized, out);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_4d *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_error_deserialize(eta, serialized,
                                                              out);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(int32_t t0) {
  return libcrux_secrets_int_public_integers_classify_27_a8((
             int32_t)((uint32_t)1
                      << (uint32_t)(LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_LOWER_PART_OF_T -
                                    (size_t)1U))) -
         t0;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  int32_t coefficient0 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[0U]);
  int32_t coefficient1 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[1U]);
  int32_t coefficient2 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[2U]);
  int32_t coefficient3 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[3U]);
  int32_t coefficient4 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[4U]);
  int32_t coefficient5 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[5U]);
  int32_t coefficient6 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[6U]);
  int32_t coefficient7 =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          simd_unit->data[7U]);
  serialized.ptr[0U] = libcrux_secrets_int_as_u8_36(coefficient0);
  serialized.ptr[1U] = libcrux_secrets_int_as_u8_36(coefficient0 >> 8U);
  size_t uu____0 = (size_t)1U;
  serialized.ptr[uu____0] = (uint32_t)serialized.ptr[uu____0] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient1 << 5U));
  serialized.ptr[2U] = libcrux_secrets_int_as_u8_36(coefficient1 >> 3U);
  serialized.ptr[3U] = libcrux_secrets_int_as_u8_36(coefficient1 >> 11U);
  size_t uu____1 = (size_t)3U;
  serialized.ptr[uu____1] = (uint32_t)serialized.ptr[uu____1] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient2 << 2U));
  serialized.ptr[4U] = libcrux_secrets_int_as_u8_36(coefficient2 >> 6U);
  size_t uu____2 = (size_t)4U;
  serialized.ptr[uu____2] = (uint32_t)serialized.ptr[uu____2] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient3 << 7U));
  serialized.ptr[5U] = libcrux_secrets_int_as_u8_36(coefficient3 >> 1U);
  serialized.ptr[6U] = libcrux_secrets_int_as_u8_36(coefficient3 >> 9U);
  size_t uu____3 = (size_t)6U;
  serialized.ptr[uu____3] = (uint32_t)serialized.ptr[uu____3] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient4 << 4U));
  serialized.ptr[7U] = libcrux_secrets_int_as_u8_36(coefficient4 >> 4U);
  serialized.ptr[8U] = libcrux_secrets_int_as_u8_36(coefficient4 >> 12U);
  size_t uu____4 = (size_t)8U;
  serialized.ptr[uu____4] = (uint32_t)serialized.ptr[uu____4] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient5 << 1U));
  serialized.ptr[9U] = libcrux_secrets_int_as_u8_36(coefficient5 >> 7U);
  size_t uu____5 = (size_t)9U;
  serialized.ptr[uu____5] = (uint32_t)serialized.ptr[uu____5] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient6 << 6U));
  serialized.ptr[10U] = libcrux_secrets_int_as_u8_36(coefficient6 >> 2U);
  serialized.ptr[11U] = libcrux_secrets_int_as_u8_36(coefficient6 >> 10U);
  size_t uu____6 = (size_t)11U;
  serialized.ptr[uu____6] = (uint32_t)serialized.ptr[uu____6] |
                            (uint32_t)libcrux_secrets_int_as_u8_36(
                                (int32_t)((uint32_t)coefficient7 << 3U));
  serialized.ptr[12U] = libcrux_secrets_int_as_u8_36(coefficient7 >> 5U);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_serialize(simd_unit, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit) {
  int32_t byte0 = libcrux_secrets_int_as_i32_59(serialized.ptr[0U]);
  int32_t byte1 = libcrux_secrets_int_as_i32_59(serialized.ptr[1U]);
  int32_t byte2 = libcrux_secrets_int_as_i32_59(serialized.ptr[2U]);
  int32_t byte3 = libcrux_secrets_int_as_i32_59(serialized.ptr[3U]);
  int32_t byte4 = libcrux_secrets_int_as_i32_59(serialized.ptr[4U]);
  int32_t byte5 = libcrux_secrets_int_as_i32_59(serialized.ptr[5U]);
  int32_t byte6 = libcrux_secrets_int_as_i32_59(serialized.ptr[6U]);
  int32_t byte7 = libcrux_secrets_int_as_i32_59(serialized.ptr[7U]);
  int32_t byte8 = libcrux_secrets_int_as_i32_59(serialized.ptr[8U]);
  int32_t byte9 = libcrux_secrets_int_as_i32_59(serialized.ptr[9U]);
  int32_t byte10 = libcrux_secrets_int_as_i32_59(serialized.ptr[10U]);
  int32_t byte11 = libcrux_secrets_int_as_i32_59(serialized.ptr[11U]);
  int32_t byte12 = libcrux_secrets_int_as_i32_59(serialized.ptr[12U]);
  int32_t coefficient0 = byte0;
  coefficient0 |= (int32_t)((uint32_t)byte1 << 8U);
  coefficient0 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient1 = byte1 >> 5U;
  coefficient1 |= (int32_t)((uint32_t)byte2 << 3U);
  coefficient1 |= (int32_t)((uint32_t)byte3 << 11U);
  coefficient1 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient2 = byte3 >> 2U;
  coefficient2 |= (int32_t)((uint32_t)byte4 << 6U);
  coefficient2 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient3 = byte4 >> 7U;
  coefficient3 |= (int32_t)((uint32_t)byte5 << 1U);
  coefficient3 |= (int32_t)((uint32_t)byte6 << 9U);
  coefficient3 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient4 = byte6 >> 4U;
  coefficient4 |= (int32_t)((uint32_t)byte7 << 4U);
  coefficient4 |= (int32_t)((uint32_t)byte8 << 12U);
  coefficient4 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient5 = byte8 >> 1U;
  coefficient5 |= (int32_t)((uint32_t)byte9 << 7U);
  coefficient5 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient6 = byte9 >> 6U;
  coefficient6 |= (int32_t)((uint32_t)byte10 << 2U);
  coefficient6 |= (int32_t)((uint32_t)byte11 << 10U);
  coefficient6 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  int32_t coefficient7 = byte11 >> 3U;
  coefficient7 |= (int32_t)((uint32_t)byte12 << 5U);
  coefficient7 &=
      LIBCRUX_IOT_ML_DSA_SIMD_PORTABLE_ENCODING_T0_DESERIALIZE_BITS_IN_LOWER_PART_OF_T_MASK;
  simd_unit->data[0U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient0);
  simd_unit->data[1U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient1);
  simd_unit->data[2U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient2);
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient3);
  simd_unit->data[4U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient4);
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient5);
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient6);
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_encoding_t0_change_t0_interval(
          coefficient7);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t0_deserialize(serialized, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)8U / (size_t)4U; i++) {
    size_t i0 = i;
    Eurydice_dst_ref_shared_83 coefficients =
        Eurydice_array_to_subslice_shared_44(
            simd_unit, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = i0 * (size_t)4U,
                           .end = i0 * (size_t)4U + (size_t)4U}));
    serialized.ptr[(size_t)5U * i0] =
        (uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                      coefficients.ptr[0U]) &
                  255);
    serialized.ptr[(size_t)5U * i0 + (size_t)1U] =
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[1U]) &
                            63)
            << 2U |
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[0U]) >>
                                8U &
                            3);
    serialized.ptr[(size_t)5U * i0 + (size_t)2U] =
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[2U]) &
                            15)
            << 4U |
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[1U]) >>
                                6U &
                            15);
    serialized.ptr[(size_t)5U * i0 + (size_t)3U] =
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[3U]) &
                            3)
            << 6U |
        (uint32_t)(uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                                coefficients.ptr[2U]) >>
                                4U &
                            63);
    serialized.ptr[(size_t)5U * i0 + (size_t)4U] =
        (uint8_t)(libcrux_secrets_int_public_integers_declassify_d8_a8(
                      coefficients.ptr[3U]) >>
                      2U &
                  255);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
    const Eurydice_arr_4d *simd_unit, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_serialize(simd_unit, out);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *simd_unit) {
  int32_t mask =
      (int32_t)((uint32_t)1 << (uint32_t)
                    LIBCRUX_IOT_ML_DSA_CONSTANTS_BITS_IN_UPPER_PART_OF_T) -
      1;
  for (size_t i = (size_t)0U; i < serialized.meta / (size_t)5U; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)5U, .end = i0 * (size_t)5U + (size_t)5U}));
    int32_t byte0 = (int32_t)(uint32_t)bytes.ptr[0U];
    int32_t byte1 = (int32_t)(uint32_t)bytes.ptr[1U];
    int32_t byte2 = (int32_t)(uint32_t)bytes.ptr[2U];
    int32_t byte3 = (int32_t)(uint32_t)bytes.ptr[3U];
    int32_t byte4 = (int32_t)(uint32_t)bytes.ptr[4U];
    simd_unit->data[(size_t)4U * i0] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            (byte0 | (int32_t)((uint32_t)byte1 << 8U)) & mask);
    simd_unit->data[(size_t)4U * i0 + (size_t)1U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            (byte1 >> 2U | (int32_t)((uint32_t)byte2 << 6U)) & mask);
    simd_unit->data[(size_t)4U * i0 + (size_t)2U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            (byte2 >> 4U | (int32_t)((uint32_t)byte3 << 4U)) & mask);
    simd_unit->data[(size_t)4U * i0 + (size_t)3U] =
        libcrux_secrets_int_public_integers_classify_27_a8(
            (byte3 >> 6U | (int32_t)((uint32_t)byte4 << 2U)) & mask);
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_4d *out) {
  libcrux_iot_ml_dsa_simd_portable_encoding_t1_deserialize(serialized, out);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
    Eurydice_arr_4d *simd_unit, int32_t c) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    simd_unit->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
            libcrux_secrets_int_as_i64_36(simd_unit->data[i0]) *
            libcrux_secrets_int_as_i64_36(c));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_30(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)16U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(25847));
    re->data[j + (size_t)16U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)16U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_30(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -2608894
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_300(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-2608894));
    re->data[j + (size_t)8U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)8U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -518909
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_42(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)8U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-518909));
    re->data[j + (size_t)8U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)8U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_300(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_42(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 237124
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_301(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(237124));
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -777960
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_82(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-777960));
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -876248
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_420(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-876248));
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 466468
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)4U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(466468));
    re->data[j + (size_t)4U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)4U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_301(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_82(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_420(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 1826347
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_302(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(1826347));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 2353451
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_43(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(2353451));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -359251
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_820(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-359251));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= -2091905
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-2091905));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= 3119733
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_421(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(3119733));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -2884855
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_61(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-2884855));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 3111497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe0(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(3111497));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 2680103
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_38(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)2U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(2680103));
    re->data[j + (size_t)2U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)2U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_302(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_43(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_820(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_421(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_61(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_38(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 2725464
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_303(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(2725464));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 1024112
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_25(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(1024112));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -1079900
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_430(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-1079900));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 3585928
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_f4(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(3585928));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -549488
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_821(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-549488));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1119584
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1d(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-1119584));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= 2619752
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea0(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(2619752));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2108549
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d8(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-2108549));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2118186
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_422(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-2118186));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= -3859737
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_60(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-3859737));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1399561
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_610(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-1399561));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -3277672
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_29(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-3277672));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 1757237
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe1(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(1757237));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -19422
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_9d(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(-19422));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 4010497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_380(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(4010497));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 280005
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_5f(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d tmp = re->data[j + (size_t)1U];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &tmp, libcrux_secrets_int_public_integers_classify_27_a8(280005));
    re->data[j + (size_t)1U] = re->data[j];
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(
        &re->data[j + (size_t)1U], &tmp);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &tmp);
  }
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_303(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_25(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_430(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_f4(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_821(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_1d(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_ea0(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_d8(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_422(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_60(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_610(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_29(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_fe1(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_9d(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_380(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_outer_3_plus_5f(re);
}

KRML_MUSTINLINE int32_t
libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
    int32_t fe, int32_t fer) {
  return libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_reduce_element(
      libcrux_secrets_int_as_i64_36(fe) * libcrux_secrets_int_as_i64_36(fer));
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
    Eurydice_arr_4d *simd_unit, int32_t zeta) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[4U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  simd_unit->data[4U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] += t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[5U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  simd_unit->data[5U] = simd_unit->data[1U] - t0;
  simd_unit->data[1U] += t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[6U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  simd_unit->data[6U] = simd_unit->data[2U] - t1;
  simd_unit->data[2U] += t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  simd_unit->data[7U] = simd_unit->data[3U] - t2;
  simd_unit->data[3U] += t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_2(
      &re->data[index], zeta);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)0U,
                                                            2706023);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)1U,
                                                            95776);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)2U,
                                                            3077325);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)3U,
                                                            3530437);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)4U,
                                                            -1661693);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)5U,
                                                            -3592148);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)6U,
                                                            -2537516);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)7U,
                                                            3915439);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)8U,
                                                            -3861115);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)9U,
                                                            -3043716);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)10U,
                                                            3574422);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)11U,
                                                            -2867647);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)12U,
                                                            3539968);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)13U,
                                                            -300467);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)14U,
                                                            2348700);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)15U,
                                                            -539299);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)16U,
                                                            -1699267);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)17U,
                                                            -1643818);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)18U,
                                                            3505694);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)19U,
                                                            -3821735);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)20U,
                                                            3507263);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)21U,
                                                            -2140649);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)22U,
                                                            -1600420);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)23U,
                                                            3699596);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)24U,
                                                            811944);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)25U,
                                                            531354);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)26U,
                                                            954230);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)27U,
                                                            3881043);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)28U,
                                                            3900724);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)29U,
                                                            -2556880);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)30U,
                                                            2071892);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2_round(re, (size_t)31U,
                                                            -2797779);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
    Eurydice_arr_4d *simd_unit, int32_t zeta1, int32_t zeta2) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[2U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
  simd_unit->data[2U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] += t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[3U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
  simd_unit->data[3U] = simd_unit->data[1U] - t0;
  simd_unit->data[1U] += t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[6U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta2));
  simd_unit->data[6U] = simd_unit->data[4U] - t1;
  simd_unit->data[4U] += t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta2));
  simd_unit->data[7U] = simd_unit->data[5U] - t2;
  simd_unit->data[5U] += t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_0, int32_t zeta_1) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_1(
      &re->data[index], zeta_0, zeta_1);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)0U,
                                                            -3930395, -1528703);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)1U,
                                                            -3677745, -3041255);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)2U,
                                                            -1452451, 3475950);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)3U,
                                                            2176455, -1585221);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)4U,
                                                            -1257611, 1939314);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)5U,
                                                            -4083598, -1000202);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)6U,
                                                            -3190144, -3157330);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)7U,
                                                            -3632928, 126922);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)8U,
                                                            3412210, -983419);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)9U,
                                                            2147896, 2715295);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)10U,
                                                            -2967645, -3693493);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)11U,
                                                            -411027, -2477047);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)12U,
                                                            -671102, -1228525);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)13U,
                                                            -22981, -1308169);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)14U,
                                                            -381987, 1349076);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)15U,
                                                            1852771, -1430430);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)16U,
                                                            -3343383, 264944);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)17U,
                                                            508951, 3097992);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)18U,
                                                            44288, -1100098);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)19U,
                                                            904516, 3958618);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)20U,
                                                            -3724342, -8578);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)21U,
                                                            1653064, -3249728);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)22U,
                                                            2389356, -210977);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)23U,
                                                            759969, -1316856);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)24U,
                                                            189548, -3553272);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)25U,
                                                            3159746, -1851402);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)26U,
                                                            -2409325, -177440);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)27U,
                                                            1315589, 1341330);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)28U,
                                                            1285669, -1584928);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)29U,
                                                            -812732, -1439742);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)30U,
                                                            -3019102, -3881060);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1_round(re, (size_t)31U,
                                                            -3628969, 3839961);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3) {
  int32_t t =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[1U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta0));
  simd_unit->data[1U] = simd_unit->data[0U] - t;
  simd_unit->data[0U] += t;
  int32_t t0 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[3U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
  simd_unit->data[3U] = simd_unit->data[2U] - t0;
  simd_unit->data[2U] += t0;
  int32_t t1 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[5U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta2));
  simd_unit->data[5U] = simd_unit->data[4U] - t1;
  simd_unit->data[4U] += t1;
  int32_t t2 =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          simd_unit->data[7U],
          libcrux_secrets_int_public_integers_classify_27_a8(zeta3));
  simd_unit->data[7U] = simd_unit->data[6U] - t2;
  simd_unit->data[6U] += t2;
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_0, int32_t zeta_1,
    int32_t zeta_2, int32_t zeta_3) {
  libcrux_iot_ml_dsa_simd_portable_ntt_simd_unit_ntt_at_layer_0(
      &re->data[index], zeta_0, zeta_1, zeta_2, zeta_3);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)0U, 2091667, 3407706, 2316500, 3817976);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)1U, -3342478, 2244091, -2446433, -3562462);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)2U, 266997, 2434439, -1235728, 3513181);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)3U, -3520352, -3759364, -1197226, -3193378);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)4U, 900702, 1859098, 909542, 819034);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)5U, 495491, -1613174, -43260, -522500);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)6U, -655327, -3122442, 2031748, 3207046);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)7U, -3556995, -525098, -768622, -3595838);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)8U, 342297, 286988, -2437823, 4108315);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)9U, 3437287, -3342277, 1735879, 203044);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)10U, 2842341, 2691481, -2590150, 1265009);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)11U, 4055324, 1247620, 2486353, 1595974);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)12U, -3767016, 1250494, 2635921, -3548272);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)13U, -2994039, 1869119, 1903435, -1050970);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)14U, -1333058, 1237275, -3318210, -1430225);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)15U, -451100, 1312455, 3306115, -1962642);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)16U, -1279661, 1917081, -2546312, -1374803);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)17U, 1500165, 777191, 2235880, 3406031);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)18U, -542412, -2831860, -1671176, -1846953);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)19U, -2584293, -3724270, 594136, -3776993);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)20U, -2013608, 2432395, 2454455, -164721);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)21U, 1957272, 3369112, 185531, -1207385);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)22U, -3183426, 162844, 1616392, 3014001);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)23U, 810149, 1652634, -3694233, -1799107);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)24U, -3038916, 3523897, 3866901, 269760);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)25U, 2213111, -975884, 1717735, 472078);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)26U, -426683, 1723600, -1803090, 1910376);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)27U, -1667432, -1104333, -260646, -3833893);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)28U, -2939036, -2235985, -420899, -2286327);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)29U, 183443, -976891, 1612842, -3545687);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)30U, -554416, 3919660, -48306, -1362209);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0_round(
      re, (size_t)31U, 3937738, 1400424, -846154, 1976782);
}

KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_ntt_ntt(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_7(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_6(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_5(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_4(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_3(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_2(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_1(re);
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt_at_layer_0(re);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_ntt_c5(Eurydice_arr_ef *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_ntt_ntt(simd_units);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1, int32_t zeta2,
    int32_t zeta3) {
  int32_t a_minus_b = simd_unit->data[1U] - simd_unit->data[0U];
  simd_unit->data[0U] += simd_unit->data[1U];
  simd_unit->data[1U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_a8(zeta0));
  int32_t a_minus_b0 = simd_unit->data[3U] - simd_unit->data[2U];
  simd_unit->data[2U] += simd_unit->data[3U];
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
  int32_t a_minus_b1 = simd_unit->data[5U] - simd_unit->data[4U];
  simd_unit->data[4U] += simd_unit->data[5U];
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta2));
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[6U];
  simd_unit->data[6U] += simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta3));
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta0, int32_t zeta1,
    int32_t zeta2, int32_t zeta3) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_0(
      &re->data[index], zeta0, zeta1, zeta2, zeta3);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)0U, 1976782, -846154, 1400424, 3937738);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)1U, -1362209, -48306, 3919660, -554416);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)2U, -3545687, 1612842, -976891, 183443);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)3U, -2286327, -420899, -2235985, -2939036);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)4U, -3833893, -260646, -1104333, -1667432);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)5U, 1910376, -1803090, 1723600, -426683);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)6U, 472078, 1717735, -975884, 2213111);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)7U, 269760, 3866901, 3523897, -3038916);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)8U, -1799107, -3694233, 1652634, 810149);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)9U, 3014001, 1616392, 162844, -3183426);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)10U, -1207385, 185531, 3369112, 1957272);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)11U, -164721, 2454455, 2432395, -2013608);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)12U, -3776993, 594136, -3724270, -2584293);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)13U, -1846953, -1671176, -2831860, -542412);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)14U, 3406031, 2235880, 777191, 1500165);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)15U, -1374803, -2546312, 1917081, -1279661);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)16U, -1962642, 3306115, 1312455, -451100);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)17U, -1430225, -3318210, 1237275, -1333058);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)18U, -1050970, 1903435, 1869119, -2994039);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)19U, -3548272, 2635921, 1250494, -3767016);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)20U, 1595974, 2486353, 1247620, 4055324);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)21U, 1265009, -2590150, 2691481, 2842341);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)22U, 203044, 1735879, -3342277, 3437287);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)23U, 4108315, -2437823, 286988, 342297);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)24U, -3595838, -768622, -525098, -3556995);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)25U, 3207046, 2031748, -3122442, -655327);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)26U, -522500, -43260, -1613174, 495491);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)27U, 819034, 909542, 1859098, 900702);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)28U, -3193378, -1197226, -3759364, -3520352);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)29U, 3513181, -1235728, 2434439, 266997);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)30U, -3562462, -2446433, 2244091, -3342478);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0_round(
      re, (size_t)31U, 3817976, 2316500, 3407706, 2091667);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
    Eurydice_arr_4d *simd_unit, int32_t zeta0, int32_t zeta1) {
  int32_t a_minus_b = simd_unit->data[2U] - simd_unit->data[0U];
  simd_unit->data[0U] += simd_unit->data[2U];
  simd_unit->data[2U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_a8(zeta0));
  int32_t a_minus_b0 = simd_unit->data[3U] - simd_unit->data[1U];
  simd_unit->data[1U] += simd_unit->data[3U];
  simd_unit->data[3U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta0));
  int32_t a_minus_b1 = simd_unit->data[6U] - simd_unit->data[4U];
  simd_unit->data[4U] += simd_unit->data[6U];
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[5U];
  simd_unit->data[5U] += simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2,
          libcrux_secrets_int_public_integers_classify_27_a8(zeta1));
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta_00, int32_t zeta_01) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_1(
      &re->data[index], zeta_00, zeta_01);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)0U, 3839961, -3628969);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)1U, -3881060, -3019102);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)2U, -1439742, -812732);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)3U, -1584928, 1285669);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)4U, 1341330, 1315589);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)5U, -177440, -2409325);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)6U, -1851402, 3159746);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)7U, -3553272, 189548);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)8U, -1316856, 759969);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)9U, -210977, 2389356);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)10U, -3249728, 1653064);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)11U, -8578, -3724342);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)12U, 3958618, 904516);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)13U, -1100098, 44288);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)14U, 3097992, 508951);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)15U, 264944, -3343383);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)16U, -1430430, 1852771);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)17U, 1349076, -381987);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)18U, -1308169, -22981);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)19U, -1228525, -671102);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)20U, -2477047, -411027);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)21U, -3693493, -2967645);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)22U, 2715295, 2147896);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)23U, -983419, 3412210);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)24U, 126922, -3632928);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)25U, -3157330, -3190144);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)26U, -1000202, -4083598);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)27U, 1939314, -1257611);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)28U, -1585221, 2176455);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)29U, 3475950, -1452451);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)30U, -3041255, -3677745);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1_round(
      re, (size_t)31U, -1528703, -3930395);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
    Eurydice_arr_4d *simd_unit, int32_t zeta) {
  int32_t a_minus_b = simd_unit->data[4U] - simd_unit->data[0U];
  simd_unit->data[0U] += simd_unit->data[4U];
  simd_unit->data[4U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b, libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  int32_t a_minus_b0 = simd_unit->data[5U] - simd_unit->data[1U];
  simd_unit->data[1U] += simd_unit->data[5U];
  simd_unit->data[5U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b0, libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  int32_t a_minus_b1 = simd_unit->data[6U] - simd_unit->data[2U];
  simd_unit->data[2U] += simd_unit->data[6U];
  simd_unit->data[6U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b1, libcrux_secrets_int_public_integers_classify_27_a8(zeta));
  int32_t a_minus_b2 = simd_unit->data[7U] - simd_unit->data[3U];
  simd_unit->data[3U] += simd_unit->data[7U];
  simd_unit->data[7U] =
      libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_fe_by_fer(
          a_minus_b2, libcrux_secrets_int_public_integers_classify_27_a8(zeta));
}

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
    Eurydice_arr_ef *re, size_t index, int32_t zeta1) {
  libcrux_iot_ml_dsa_simd_portable_invntt_simd_unit_invert_ntt_at_layer_2(
      &re->data[index], zeta1);
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)0U, -2797779);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)1U, 2071892);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)2U, -2556880);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)3U, 3900724);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)4U, 3881043);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)5U, 954230);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)6U, 531354);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)7U, 811944);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)8U, 3699596);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)9U, -1600420);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)10U, -2140649);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)11U, 3507263);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)12U, -3821735);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)13U, 3505694);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)14U, -1643818);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)15U, -1699267);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)16U, -539299);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)17U, 2348700);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)18U, -300467);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)19U, 3539968);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)20U, -2867647);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)21U, 3574422);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)22U, -3043716);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)23U, -3861115);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)24U, 3915439);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)25U, -2537516);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)26U, -3592148);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)27U, -1661693);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)28U, 3530437);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)29U, 3077325);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)30U, 95776);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2_round(
      re, (size_t)31U, 2706023);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
inline Eurydice_arr_4d libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
    const Eurydice_arr_4d *self) {
  return self[0U];
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 1
- ZETA= 280005
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_30(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(280005));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 2
- STEP_BY= 1
- ZETA= 4010497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_25(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)2U; i < (size_t)2U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(4010497));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 1
- ZETA= -19422
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_43(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-19422));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 6
- STEP_BY= 1
- ZETA= 1757237
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_f4(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)6U; i < (size_t)6U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(1757237));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 1
- ZETA= -3277672
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_82(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-3277672));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 10
- STEP_BY= 1
- ZETA= -1399561
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1d(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)10U; i < (size_t)10U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-1399561));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 1
- ZETA= -3859737
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-3859737));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 14
- STEP_BY= 1
- ZETA= -2118186
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d8(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)14U; i < (size_t)14U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-2118186));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 1
- ZETA= -2108549
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_42(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-2108549));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 18
- STEP_BY= 1
- ZETA= 2619752
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_60(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)18U; i < (size_t)18U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(2619752));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 1
- ZETA= -1119584
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_61(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-1119584));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 22
- STEP_BY= 1
- ZETA= -549488
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_29(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)22U; i < (size_t)22U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-549488));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 1
- ZETA= 3585928
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(3585928));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 26
- STEP_BY= 1
- ZETA= -1079900
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_9d(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)26U; i < (size_t)26U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(-1079900));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 1
- ZETA= 1024112
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_38(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(1024112));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 30
- STEP_BY= 1
- ZETA= 2725464
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_5f(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)30U; i < (size_t)30U + (size_t)1U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)1U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)1U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)1U],
        libcrux_secrets_int_public_integers_classify_27_a8(2725464));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_30(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_25(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_43(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_f4(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_82(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_1d(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_d8(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_42(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_60(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_61(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_29(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_9d(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_38(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_5f(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 2
- ZETA= 2680103
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_300(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(2680103));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 4
- STEP_BY= 2
- ZETA= 3111497
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_430(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)4U; i < (size_t)4U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(3111497));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 2
- ZETA= -2884855
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_820(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(-2884855));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 12
- STEP_BY= 2
- ZETA= 3119733
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea0(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)12U; i < (size_t)12U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(3119733));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 2
- ZETA= -2091905
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_420(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(-2091905));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 20
- STEP_BY= 2
- ZETA= -359251
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_610(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)20U; i < (size_t)20U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(-359251));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 2
- ZETA= 2353451
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe0(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(2353451));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 28
- STEP_BY= 2
- ZETA= 1826347
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_380(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)28U; i < (size_t)28U + (size_t)2U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)2U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)2U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)2U],
        libcrux_secrets_int_public_integers_classify_27_a8(1826347));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_300(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_430(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_820(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_ea0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_420(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_610(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_380(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 4
- ZETA= 466468
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_301(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U],
        libcrux_secrets_int_public_integers_classify_27_a8(466468));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 8
- STEP_BY= 4
- ZETA= -876248
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_821(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)8U; i < (size_t)8U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U],
        libcrux_secrets_int_public_integers_classify_27_a8(-876248));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 4
- ZETA= -777960
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_421(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U],
        libcrux_secrets_int_public_integers_classify_27_a8(-777960));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 24
- STEP_BY= 4
- ZETA= 237124
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe1(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)24U; i < (size_t)24U + (size_t)4U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)4U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)4U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)4U],
        libcrux_secrets_int_public_integers_classify_27_a8(237124));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_301(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_821(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_421(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_fe1(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 8
- ZETA= -518909
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_302(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)8U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)8U],
        libcrux_secrets_int_public_integers_classify_27_a8(-518909));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 16
- STEP_BY= 8
- ZETA= -2608894
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_422(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)16U; i < (size_t)16U + (size_t)8U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)8U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)8U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)8U],
        libcrux_secrets_int_public_integers_classify_27_a8(-2608894));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_302(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_422(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.simd.portable.invntt.outer_3_plus
with const generics
- OFFSET= 0
- STEP_BY= 16
- ZETA= 25847
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_303(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)0U + (size_t)16U; i++) {
    size_t j = i;
    Eurydice_arr_4d rejs =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(
            &re->data[j + (size_t)16U]);
    Eurydice_arr_4d a_minus_b =
        libcrux_iot_ml_dsa_simd_portable_vector_type_clone_c2(&rejs);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_subtract(&a_minus_b,
                                                         &re->data[j]);
    libcrux_iot_ml_dsa_simd_portable_arithmetic_add(&re->data[j], &rejs);
    re->data[j + (size_t)16U] = a_minus_b;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[j + (size_t)16U],
        libcrux_secrets_int_public_integers_classify_27_a8(25847));
  }
}

KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_outer_3_plus_303(re);
}

void libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_0(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_1(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_2(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_3(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_4(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_5(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_6(re);
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_at_layer_7(re);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_arithmetic_montgomery_multiply_by_constant(
        &re->data[i0],
        libcrux_secrets_int_public_integers_classify_27_a8(41978));
  }
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(
    Eurydice_arr_ef *simd_units) {
  libcrux_iot_ml_dsa_simd_portable_invntt_invert_ntt_montgomery(simd_units);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 0
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_c3(
    Eurydice_arr_4d *simd_unit) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    simd_unit->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(
            (int32_t)((uint32_t)simd_unit->data[i0] << (uint32_t)0));
  }
}

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
    Eurydice_arr_4d *simd_unit) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_c3(
      simd_unit);
}

/**
This function found in impl {libcrux_iot_ml_dsa::simd::traits::Operations for
libcrux_iot_ml_dsa::simd::portable::vector_type::Coefficients}
*/
void libcrux_iot_ml_dsa_simd_portable_reduce_c5(Eurydice_arr_ef *simd_units) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_c3(
        &simd_units->data[i0]);
  }
}

uint8_t_x2 libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
    size_t index, size_t width) {
  return (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)(index / width),
                                    .snd = (uint8_t)(index % width)});
}

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
Eurydice_arr_ef libcrux_iot_ml_dsa_polynomial_zero_c2_08(void) {
  Eurydice_arr_ef lit;
  Eurydice_arr_4d repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_simd_portable_zero_c5();
  }
  memcpy(lit.data, repeat_expression, (size_t)32U * sizeof(Eurydice_arr_4d));
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_field_modulus with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)24U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_c8(
        randomness, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = _cloop_i * (size_t)24U,
                        .end = _cloop_i * (size_t)24U + (size_t)24U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_field_modulus_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_11(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] += sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

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
    Eurydice_dst_ref_shared_83 array, Eurydice_arr_ef *result) {
  for (size_t i = (size_t)0U;
       i < LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_SIMD_UNITS_IN_RING_ELEMENT; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_from_coefficient_array_c5(
        Eurydice_slice_subslice_shared_47(
            array,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})),
        &result->data[i0]);
  }
}

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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 matrix, Eurydice_arr_d1 *rand_stack0,
    Eurydice_arr_d1 *rand_stack1, Eurydice_arr_d1 *rand_stack2,
    Eurydice_arr_d1 *rand_stack3, Eurydice_dst_ref_mut_33 tmp_stack,
    size_t start_index, size_t elements_requested) {
  Eurydice_arr_31 seed0 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index, columns));
  Eurydice_arr_31 seed1 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)1U, columns));
  Eurydice_arr_31 seed2 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)2U, columns));
  Eurydice_arr_31 seed3 = libcrux_iot_ml_dsa_sample_add_domain_separator(
      seed, libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_xy(
                start_index + (size_t)3U, columns));
  Eurydice_borrow_slice_u8 uu____0 = Eurydice_array_to_slice_shared_e9(
      libcrux_secrets_int_public_integers_classify_ref_c5_78(&seed0));
  Eurydice_borrow_slice_u8 uu____1 = Eurydice_array_to_slice_shared_e9(
      libcrux_secrets_int_public_integers_classify_ref_c5_78(&seed1));
  Eurydice_borrow_slice_u8 uu____2 = Eurydice_array_to_slice_shared_e9(
      libcrux_secrets_int_public_integers_classify_ref_c5_78(&seed2));
  libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_33(
          uu____0, uu____1, uu____2,
          Eurydice_array_to_slice_shared_e9(
              libcrux_secrets_int_public_integers_classify_ref_c5_78(&seed3)));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_five_blocks_33(
      &state, rand_stack0, rand_stack1, rand_stack2, rand_stack3);
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  Eurydice_borrow_slice_u8 uu____3 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)840U, rand_stack0, uint8_t,
                                       Eurydice_borrow_slice_u8));
  bool done0 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          uu____3, &sampled0, tmp_stack.ptr);
  Eurydice_borrow_slice_u8 uu____4 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)840U, rand_stack1, uint8_t,
                                       Eurydice_borrow_slice_u8));
  bool done1 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          uu____4, &sampled1, &tmp_stack.ptr[1U]);
  Eurydice_borrow_slice_u8 uu____5 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)840U, rand_stack2, uint8_t,
                                       Eurydice_borrow_slice_u8));
  bool done2 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          uu____5, &sampled2, &tmp_stack.ptr[2U]);
  Eurydice_borrow_slice_u8 uu____6 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          core_array___T__N___as_slice((size_t)840U, rand_stack3, uint8_t,
                                       Eurydice_borrow_slice_u8));
  bool done3 =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          uu____6, &sampled3, &tmp_stack.ptr[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            Eurydice_arr_c5_x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                    &state);
            if (!done0) {
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_2c(
                          libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                              &randomnesses.fst)),
                      &sampled0, tmp_stack.ptr);
            }
            if (!done1) {
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_2c(
                          libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                              &randomnesses.snd)),
                      &sampled1, &tmp_stack.ptr[1U]);
            }
            if (!done2) {
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_2c(
                          libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                              &randomnesses.thd)),
                      &sampled2, &tmp_stack.ptr[2U]);
            }
            if (!done3) {
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                      Eurydice_array_to_slice_shared_2c(
                          libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                              &randomnesses.f3)),
                      &sampled3, &tmp_stack.ptr[3U]);
            }
          }
        } else {
          Eurydice_arr_c5_x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                  &state);
          if (!done0) {
            done0 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_2c(
                        libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                            &randomnesses.fst)),
                    &sampled0, tmp_stack.ptr);
          }
          if (!done1) {
            done1 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_2c(
                        libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                            &randomnesses.snd)),
                    &sampled1, &tmp_stack.ptr[1U]);
          }
          if (!done2) {
            done2 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_2c(
                        libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                            &randomnesses.thd)),
                    &sampled2, &tmp_stack.ptr[2U]);
          }
          if (!done3) {
            done3 =
                libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                    Eurydice_array_to_slice_shared_2c(
                        libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                            &randomnesses.f3)),
                    &sampled3, &tmp_stack.ptr[3U]);
          }
        }
      } else {
        Eurydice_arr_c5_x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
                &state);
        if (!done0) {
          done0 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_2c(
                      libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                          &randomnesses.fst)),
                  &sampled0, tmp_stack.ptr);
        }
        if (!done1) {
          done1 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_2c(
                      libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                          &randomnesses.snd)),
                  &sampled1, &tmp_stack.ptr[1U]);
        }
        if (!done2) {
          done2 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_2c(
                      libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                          &randomnesses.thd)),
                  &sampled2, &tmp_stack.ptr[2U]);
        }
        if (!done3) {
          done3 =
              libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                  Eurydice_array_to_slice_shared_2c(
                      libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                          &randomnesses.f3)),
                  &sampled3, &tmp_stack.ptr[3U]);
        }
      }
    } else {
      Eurydice_arr_c5_x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_33(
              &state);
      if (!done0) {
        done0 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_2c(
                    libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                        &randomnesses.fst)),
                &sampled0, tmp_stack.ptr);
      }
      if (!done1) {
        done1 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_2c(
                    libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                        &randomnesses.snd)),
                &sampled1, &tmp_stack.ptr[1U]);
      }
      if (!done2) {
        done2 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_2c(
                    libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                        &randomnesses.thd)),
                &sampled2, &tmp_stack.ptr[2U]);
      }
      if (!done3) {
        done3 =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                Eurydice_array_to_slice_shared_2c(
                    libcrux_secrets_int_public_integers_declassify_ref_ad_33(
                        &randomnesses.f3)),
                &sampled3, &tmp_stack.ptr[3U]);
      }
    }
  }
  for (size_t i = (size_t)0U; i < elements_requested; i++) {
    size_t k = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_2c0(
            libcrux_secrets_int_public_integers_classify_ref_c5_72(
                &tmp_stack.ptr[k])),
        &matrix.ptr[start_index + k]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.matrix_flat
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_matrix_flat_15(
    size_t columns, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 matrix) {
  Eurydice_arr_d1 rand_stack0;
  uint8_t repeat_expression0[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack0.data, repeat_expression0, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_d1 rand_stack1;
  uint8_t repeat_expression1[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack1.data, repeat_expression1, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_d1 rand_stack2;
  uint8_t repeat_expression2[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression2[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack2.data, repeat_expression2, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_d1 rand_stack3;
  uint8_t repeat_expression[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack3.data, repeat_expression, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_93 tmp_stack = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  size_t full_quartets = matrix.meta / (size_t)4U;
  for (size_t i = (size_t)0U; i < full_quartets; i++) {
    size_t start_index = i;
    libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
        columns, seed, matrix, &rand_stack0, &rand_stack1, &rand_stack2,
        &rand_stack3, Eurydice_array_to_slice_mut_7e(&tmp_stack),
        start_index * (size_t)4U, (size_t)4U);
  }
  size_t uu____0 = columns;
  Eurydice_borrow_slice_u8 uu____1 = seed;
  Eurydice_dst_ref_mut_90 uu____2 = matrix;
  Eurydice_arr_d1 *uu____3 = &rand_stack0;
  Eurydice_arr_d1 *uu____4 = &rand_stack1;
  Eurydice_arr_d1 *uu____5 = &rand_stack2;
  Eurydice_arr_d1 *uu____6 = &rand_stack3;
  libcrux_iot_ml_dsa_sample_sample_up_to_four_ring_elements_flat_15(
      uu____0, uu____1, uu____2, uu____3, uu____4, uu____5, uu____6,
      Eurydice_array_to_slice_mut_7e(&tmp_stack), full_quartets * (size_t)4U,
      matrix.meta % (size_t)4U);
}

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
    Eurydice_dst_ref_mut_90 matrix) {
  libcrux_iot_ml_dsa_samplex4_matrix_flat_15(columns, seed, matrix);
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 16
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_71(Eurydice_arr_f8 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_4 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_c8(
        randomness, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = _cloop_i * (size_t)4U,
                        .end = _cloop_i * (size_t)4U + (size_t)4U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_4_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_11(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] += sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta_equals_2 with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
    Eurydice_borrow_slice_u8 randomness, size_t *sampled_coefficients,
    Eurydice_arr_d0 *out) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta / (size_t)4U; i++) {
    size_t _cloop_i = i;
    Eurydice_borrow_slice_u8 random_bytes = Eurydice_slice_subslice_shared_c8(
        randomness, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = _cloop_i * (size_t)4U,
                        .end = _cloop_i * (size_t)4U + (size_t)4U}));
    if (!done) {
      size_t sampled =
          libcrux_iot_ml_dsa_simd_portable_rejection_sample_less_than_eta_equals_2_c5(
              random_bytes, Eurydice_array_to_subslice_from_mut_11(
                                out, sampled_coefficients[0U]));
      sampled_coefficients[0U] += sampled;
      if (sampled_coefficients[0U] >=
          LIBCRUX_IOT_ML_DSA_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT) {
        done = true;
      }
    }
  }
  return done;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.rejection_sample_less_than_eta with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 randomness,
    size_t *sampled, Eurydice_arr_d0 *out) {
  switch (eta) {
    case libcrux_iot_ml_dsa_constants_Eta_Two: {
      break;
    }
    case libcrux_iot_ml_dsa_constants_Eta_Four: {
      return libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_4_08(
          randomness, sampled, out);
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_equals_2_08(
      randomness, sampled, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_four_error_ring_elements with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    uint16_t start_index, Eurydice_dst_ref_mut_90 re) {
  Eurydice_arr_91 seed0 =
      libcrux_iot_ml_dsa_sample_add_error_domain_separator(seed, start_index);
  Eurydice_arr_91 seed1 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 1U);
  Eurydice_arr_91 seed2 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 2U);
  Eurydice_arr_91 seed3 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      seed, (uint32_t)start_index + 3U);
  libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_x4_29(
          Eurydice_array_to_slice_shared_f1(&seed0),
          Eurydice_array_to_slice_shared_f1(&seed1),
          Eurydice_array_to_slice_shared_f1(&seed2),
          Eurydice_array_to_slice_shared_f1(&seed3));
  Eurydice_arr_ff_x4 randomnesses0 =
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_x4_29(
          &state);
  Eurydice_arr_93 out;
  Eurydice_arr_d0 repeat_expression0[4U];
  for (size_t i0 = (size_t)0U; i0 < (size_t)4U; i0++) {
    Eurydice_arr_d0 lit;
    int32_t repeat_expression[263U];
    for (size_t i = (size_t)0U; i < (size_t)263U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_a8(0);
    }
    memcpy(lit.data, repeat_expression, (size_t)263U * sizeof(int32_t));
    repeat_expression0[i0] = lit;
  }
  memcpy(out.data, repeat_expression0, (size_t)4U * sizeof(Eurydice_arr_d0));
  size_t sampled0 = (size_t)0U;
  size_t sampled1 = (size_t)0U;
  size_t sampled2 = (size_t)0U;
  size_t sampled3 = (size_t)0U;
  libcrux_iot_ml_dsa_constants_Eta uu____0 = eta;
  bool done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____0, Eurydice_array_to_slice_shared_58(&randomnesses0.fst), &sampled0,
      out.data);
  libcrux_iot_ml_dsa_constants_Eta uu____1 = eta;
  bool done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____1, Eurydice_array_to_slice_shared_58(&randomnesses0.snd), &sampled1,
      &out.data[1U]);
  libcrux_iot_ml_dsa_constants_Eta uu____2 = eta;
  bool done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____2, Eurydice_array_to_slice_shared_58(&randomnesses0.thd), &sampled2,
      &out.data[2U]);
  libcrux_iot_ml_dsa_constants_Eta uu____3 = eta;
  bool done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
      uu____3, Eurydice_array_to_slice_shared_58(&randomnesses0.f3), &sampled3,
      &out.data[3U]);
  while (true) {
    if (done0) {
      if (done1) {
        if (done2) {
          if (done3) {
            break;
          } else {
            Eurydice_arr_ff_x4 randomnesses =
                libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                    &state);
            if (!done0) {
              libcrux_iot_ml_dsa_constants_Eta uu____4 = eta;
              done0 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____4,
                      Eurydice_array_to_slice_shared_58(&randomnesses.fst),
                      &sampled0, out.data);
            }
            if (!done1) {
              libcrux_iot_ml_dsa_constants_Eta uu____5 = eta;
              done1 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____5,
                      Eurydice_array_to_slice_shared_58(&randomnesses.snd),
                      &sampled1, &out.data[1U]);
            }
            if (!done2) {
              libcrux_iot_ml_dsa_constants_Eta uu____6 = eta;
              done2 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____6,
                      Eurydice_array_to_slice_shared_58(&randomnesses.thd),
                      &sampled2, &out.data[2U]);
            }
            if (!done3) {
              libcrux_iot_ml_dsa_constants_Eta uu____7 = eta;
              done3 =
                  libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                      uu____7,
                      Eurydice_array_to_slice_shared_58(&randomnesses.f3),
                      &sampled3, &out.data[3U]);
            }
          }
        } else {
          Eurydice_arr_ff_x4 randomnesses =
              libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                  &state);
          if (!done0) {
            libcrux_iot_ml_dsa_constants_Eta uu____8 = eta;
            done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____8, Eurydice_array_to_slice_shared_58(&randomnesses.fst),
                &sampled0, out.data);
          }
          if (!done1) {
            libcrux_iot_ml_dsa_constants_Eta uu____9 = eta;
            done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____9, Eurydice_array_to_slice_shared_58(&randomnesses.snd),
                &sampled1, &out.data[1U]);
          }
          if (!done2) {
            libcrux_iot_ml_dsa_constants_Eta uu____10 = eta;
            done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____10, Eurydice_array_to_slice_shared_58(&randomnesses.thd),
                &sampled2, &out.data[2U]);
          }
          if (!done3) {
            libcrux_iot_ml_dsa_constants_Eta uu____11 = eta;
            done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
                uu____11, Eurydice_array_to_slice_shared_58(&randomnesses.f3),
                &sampled3, &out.data[3U]);
          }
        }
      } else {
        Eurydice_arr_ff_x4 randomnesses =
            libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
                &state);
        if (!done0) {
          libcrux_iot_ml_dsa_constants_Eta uu____12 = eta;
          done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____12, Eurydice_array_to_slice_shared_58(&randomnesses.fst),
              &sampled0, out.data);
        }
        if (!done1) {
          libcrux_iot_ml_dsa_constants_Eta uu____13 = eta;
          done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____13, Eurydice_array_to_slice_shared_58(&randomnesses.snd),
              &sampled1, &out.data[1U]);
        }
        if (!done2) {
          libcrux_iot_ml_dsa_constants_Eta uu____14 = eta;
          done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____14, Eurydice_array_to_slice_shared_58(&randomnesses.thd),
              &sampled2, &out.data[2U]);
        }
        if (!done3) {
          libcrux_iot_ml_dsa_constants_Eta uu____15 = eta;
          done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
              uu____15, Eurydice_array_to_slice_shared_58(&randomnesses.f3),
              &sampled3, &out.data[3U]);
        }
      }
    } else {
      Eurydice_arr_ff_x4 randomnesses =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_x4_29(
              &state);
      if (!done0) {
        libcrux_iot_ml_dsa_constants_Eta uu____16 = eta;
        done0 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____16, Eurydice_array_to_slice_shared_58(&randomnesses.fst),
            &sampled0, out.data);
      }
      if (!done1) {
        libcrux_iot_ml_dsa_constants_Eta uu____17 = eta;
        done1 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____17, Eurydice_array_to_slice_shared_58(&randomnesses.snd),
            &sampled1, &out.data[1U]);
      }
      if (!done2) {
        libcrux_iot_ml_dsa_constants_Eta uu____18 = eta;
        done2 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____18, Eurydice_array_to_slice_shared_58(&randomnesses.thd),
            &sampled2, &out.data[2U]);
      }
      if (!done3) {
        libcrux_iot_ml_dsa_constants_Eta uu____19 = eta;
        done3 = libcrux_iot_ml_dsa_sample_rejection_sample_less_than_eta_08(
            uu____19, Eurydice_array_to_slice_shared_58(&randomnesses.f3),
            &sampled3, &out.data[3U]);
      }
    }
  }
  size_t max0 = (size_t)(uint32_t)start_index + (size_t)4U;
  size_t max;
  if (re.meta < max0) {
    max = re.meta;
  } else {
    max = max0;
  }
  for (size_t i = (size_t)(uint32_t)start_index; i < max; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_2c0(&out.data[i0 % (size_t)4U]),
        &re.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.samplex4.sample_s1_and_s2
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 seed,
    Eurydice_dst_ref_mut_90 s1_s2) {
  size_t len = s1_s2.meta;
  for (size_t i = (size_t)0U; i < len / (size_t)4U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
        eta, seed, 4U * (uint32_t)(uint16_t)i0, s1_s2);
  }
  size_t remainder = len % (size_t)4U;
  if (remainder != (size_t)0U) {
    libcrux_iot_ml_dsa_sample_sample_four_error_ring_elements_e7(
        eta, seed, (uint16_t)(len - remainder), s1_s2);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_710(Eurydice_arr_62 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 4
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_711(Eurydice_arr_f5 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static Eurydice_dst_ref_shared_90 array_to_subslice_shared_72(
    const Eurydice_arr_62 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_90){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_08(Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_ntt_c5(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.ntt_multiply_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
    Eurydice_arr_ef *lhs, const Eurydice_arr_ef *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_montgomery_multiply_c5(&lhs->data[i0],
                                                            &rhs->data[i0]);
  }
}

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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_add_c2_08(
    Eurydice_arr_ef *self, const Eurydice_arr_ef *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_add_c5(&self->data[i0], &rhs->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_reduce_08(Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_reduce_c5(re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ntt.invert_ntt_montgomery
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(
    Eurydice_arr_ef *re) {
  libcrux_iot_ml_dsa_simd_portable_invert_ntt_montgomery_c5(re);
}

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
    Eurydice_dst_ref_mut_90 result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      Eurydice_arr_ef product = a_as_ntt.ptr[i1 * columns_in_a + j];
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(&product,
                                                        &s1_ntt.ptr[j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i1], &product);
    }
  }
  for (size_t i = (size_t)0U; i < result.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_reduce_08(&result.ptr[i0]);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&result.ptr[i0]);
    libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i0],
                                            &s1_s2.ptr[columns_in_a + i0]);
  }
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 16
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_71(
    const Eurydice_arr_f8 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 4
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_710(
    const Eurydice_arr_f5 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 8
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_711(
    const Eurydice_arr_62 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)8U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.power2round_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
    Eurydice_dst_ref_mut_90 t0, Eurydice_dst_ref_mut_90 t1) {
  for (size_t i0 = (size_t)0U; i0 < t0.meta; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_power2round_c5(&t0.ptr[i1].data[j],
                                                      &t1.ptr[i1].data[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t1_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_t1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T1_SERIALIZE_OUTPUT_BYTES_PER_SIMD_UNIT})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
    Eurydice_borrow_slice_u8 seed, Eurydice_dst_ref_shared_90 t1,
    Eurydice_mut_borrow_slice_u8 verification_key_serialized) {
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          verification_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE})),
      seed, uint8_t);
  for (size_t i = (size_t)0U; i < t1.meta; i++) {
    size_t i0 = i;
    const Eurydice_arr_ef *ring_element = &t1.ptr[i0];
    size_t offset = LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE +
                    i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE;
    libcrux_iot_ml_dsa_encoding_t1_serialize_08(
        ring_element,
        Eurydice_slice_subslice_mut_c8(
            verification_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = offset,
                .end =
                    offset +
                    LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 64
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_c9(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c7 *out) {
  libcrux_iot_sha3_shake256_ema(Eurydice_array_to_slice_mut_17(out), input);
}

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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_c7 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_c9(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_serialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, const Eurydice_arr_ef *re,
    Eurydice_mut_borrow_slice_u8 serialized) {
  size_t output_bytes_per_simd_unit =
      libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_error_serialize_c5(
        eta, simd_unit,
        Eurydice_slice_subslice_mut_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = i0 * output_bytes_per_simd_unit,
                .end = (i0 + (size_t)1U) * output_bytes_per_simd_unit})));
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_t0_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.signing_key.generate_serialized with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t error_ring_element_size,
    Eurydice_borrow_slice_u8 seed_matrix, Eurydice_borrow_slice_u8 seed_signing,
    Eurydice_borrow_slice_u8 verification_key, Eurydice_dst_ref_shared_90 s1_2,
    Eurydice_dst_ref_shared_90 t0,
    Eurydice_mut_borrow_slice_u8 signing_key_serialized) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = offset,
              .end = offset + LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE})),
      seed_matrix, uint8_t);
  offset += LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = offset,
              .end = offset +
                     LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE})),
      seed_signing, uint8_t);
  offset += LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE;
  Eurydice_arr_c7 verification_key_hash;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(verification_key_hash.data, repeat_expression,
         (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(verification_key),
      &verification_key_hash);
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          signing_key_serialized,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = offset,
              .end =
                  offset +
                  LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH})),
      Eurydice_array_to_slice_shared_17(&verification_key_hash), uint8_t);
  offset += LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH;
  for (size_t i = (size_t)0U; i < s1_2.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_error_serialize_08(
        eta, &s1_2.ptr[i0],
        Eurydice_slice_subslice_mut_c8(
            signing_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = offset, .end = offset + error_ring_element_size})));
    offset += error_ring_element_size;
  }
  for (size_t i = (size_t)0U; i < t0.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_ef *ring_element = &t0.ptr[_cloop_j];
    libcrux_iot_ml_dsa_encoding_t0_serialize_08(
        ring_element,
        Eurydice_slice_subslice_mut_c8(
            signing_key_serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = offset,
                .end =
                    offset +
                    LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE})));
    offset += LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
  }
}

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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_89 seed_expanded0;
  uint8_t repeat_expression0[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed_expanded0.data, repeat_expression0,
         (size_t)128U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____0 = &shake;
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A),
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A)}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      uu____0, Eurydice_array_to_slice_shared_82(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_78(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_78(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____2.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____2.snd;
  Eurydice_arr_f8 a_as_ntt;
  Eurydice_arr_ef repeat_expression1[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression1,
         (size_t)16U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____3 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, uu____3,
      array_to_slice_mut_71(&a_as_ntt));
  Eurydice_arr_62 s1_s2;
  Eurydice_arr_ef repeat_expression2[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression2, (size_t)8U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA, seed_for_error_vectors,
      array_to_slice_mut_710(&s1_s2));
  Eurydice_arr_f5 t0;
  Eurydice_arr_ef repeat_expression3[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression3, (size_t)4U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_f5 s1_ntt;
  Eurydice_arr_ef repeat_expression4[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression4, (size_t)4U * sizeof(Eurydice_arr_ef));
  Eurydice_slice_copy(
      array_to_slice_mut_711(&s1_ntt),
      array_to_subslice_shared_72(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A})),
      Eurydice_arr_ef);
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      array_to_slice_shared_71(&a_as_ntt), array_to_slice_shared_710(&s1_ntt),
      array_to_slice_shared_711(&s1_s2), array_to_slice_mut_711(&t0));
  Eurydice_arr_f5 t1;
  Eurydice_arr_ef repeat_expression[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)4U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      array_to_slice_mut_711(&t0), array_to_slice_mut_711(&t1));
  Eurydice_borrow_slice_u8 uu____4 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      uu____4, array_to_slice_shared_710(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      array_to_slice_shared_711(&s1_s2), array_to_slice_shared_710(&t0),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_10 *signing_key,
    Eurydice_arr_02 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_34(signing_key),
      Eurydice_array_to_slice_mut_9f0(verification_key));
}

/**
 Generate an ML-DSA-44 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_85
libcrux_iot_ml_dsa_ml_dsa_44_portable_generate_key_pair(
    Eurydice_arr_ec randomness) {
  Eurydice_arr_10 signing_key;
  uint8_t repeat_expression[2560U];
  for (size_t i = (size_t)0U; i < (size_t)2560U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(signing_key.data, repeat_expression, (size_t)2560U * sizeof(uint8_t));
  Eurydice_arr_02 verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_85){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_ab(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_7d(verification_key)});
}

/**
 `context` must be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Result_80 libcrux_iot_ml_dsa_pre_hash_new_c9(Eurydice_borrow_slice_u8 context,
                                             Option_57 pre_hash_oid) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    return (KRML_CLITERAL(Result_80){
        .tag = Ok,
        .val = {
            .case_Ok = {.context = context, .pre_hash_oid = pre_hash_oid}}});
  }
  return (KRML_CLITERAL(Result_80){
      .tag = Err,
      .val = {
          .case_Err =
              libcrux_iot_ml_dsa_pre_hash_DomainSeparationError_ContextTooLongError}});
}

/**
 Returns the pre-hash OID, if any.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
const Option_57 *libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return &self->pre_hash_oid;
}

/**
 Returns the context, guaranteed to be at most 255 bytes long.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::pre_hash::DomainSeparationContext<'a>}
*/
Eurydice_borrow_slice_u8 libcrux_iot_ml_dsa_pre_hash_context_c9(
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext *self) {
  return self->context;
}

KRML_MUSTINLINE bool libcrux_iot_ml_dsa_sample_inside_out_shuffle(
    Eurydice_borrow_slice_u8 randomness, size_t *out_index, uint64_t *signs,
    Eurydice_arr_6c *result) {
  bool done = false;
  for (size_t i = (size_t)0U; i < randomness.meta; i++) {
    size_t _cloop_j = i;
    const uint8_t *byte = &randomness.ptr[_cloop_j];
    if (!done) {
      size_t sample_at = (size_t)(uint32_t)
          libcrux_secrets_int_public_integers_declassify_d8_90(byte[0U]);
      if (sample_at <= out_index[0U]) {
        result->data[out_index[0U]] = result->data[sample_at];
        out_index[0U]++;
        result->data[sample_at] =
            libcrux_secrets_int_public_integers_classify_27_a8(1) -
            libcrux_secrets_int_public_integers_classify_27_a8(2) *
                libcrux_secrets_int_as_i32_a3(signs[0U] & 1ULL);
        signs[0U] >>= 1U;
      }
      done = out_index[0U] == (size_t)256U;
    }
  }
  return done;
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$8size_t]], core_array_TryFromSliceError

*/
static Eurydice_array_u8x8 unwrap_26_e0(Result_8e self) {
  if (self.tag == Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_ec

*/
typedef struct Option_14_s {
  Option_87_tags tag;
  Eurydice_arr_ec f0;
} Option_14;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_b7

*/
typedef struct Option_51_s {
  Option_87_tags tag;
  Eurydice_arr_b7 f0;
} Option_51;

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.error.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_error_deserialize_08(
    libcrux_iot_ml_dsa_constants_Eta eta, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_ef *result) {
  size_t chunk_size = libcrux_iot_ml_dsa_encoding_error_chunk_size(eta);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_error_deserialize_c5(
        eta,
        Eurydice_slice_subslice_shared_c8(
            serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = i0 * chunk_size,
                            .end = (i0 + (size_t)1U) * chunk_size})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.error.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
    libcrux_iot_ml_dsa_constants_Eta eta, size_t ring_element_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_dst_ref_mut_90 ring_elements) {
  for (size_t i = (size_t)0U; i < serialized.meta / ring_element_size; i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                        .start = i0 * ring_element_size,
                        .end = i0 * ring_element_size + ring_element_size}));
    libcrux_iot_ml_dsa_encoding_error_deserialize_08(eta, bytes,
                                                     &ring_elements.ptr[i0]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&ring_elements.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t0.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_t0_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_ef *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t0_deserialize_c5(
        Eurydice_slice_subslice_shared_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_ENCODING_T0_OUTPUT_BYTES_PER_SIMD_UNIT})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.t0.deserialize_to_vector_then_ntt with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_dst_ref_mut_90 ring_elements) {
  for (size_t i = (size_t)0U;
       i <
       serialized.meta / LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE;
       i++) {
    size_t i0 = i;
    Eurydice_borrow_slice_u8 bytes = Eurydice_slice_subslice_shared_c8(
        serialized,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE,
            .end = i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE +
                   LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T0S_SIZE}));
    libcrux_iot_ml_dsa_encoding_t0_deserialize_08(bytes,
                                                  &ring_elements.ptr[i0]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&ring_elements.ptr[i0]);
  }
}

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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
    Eurydice_borrow_slice_u8 verification_key_hash,
    const Option_e3 *domain_separation_context,
    Eurydice_borrow_slice_u8 message, Eurydice_arr_c7 *message_representative) {
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, libcrux_secrets_int_classify_public_classify_ref_6d_90(
                  verification_key_hash));
  if (domain_separation_context->tag == Some) {
    const libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        *domain_separation_context0 = &domain_separation_context->f0;
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____0 = &shake;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_82 lvalue0 = {
        .data = {libcrux_secrets_int_public_integers_classify_27_90(
            (uint8_t)
                core_option__core__option__Option_T__TraitClause_0___is_some(
                    libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(
                        domain_separation_context0),
                    Eurydice_arr_c9, bool))}};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____0, Eurydice_array_to_slice_shared_79(&lvalue0));
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____1 = &shake;
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_82 lvalue = {
        .data = {libcrux_secrets_int_public_integers_classify_27_90(
            (uint8_t)libcrux_iot_ml_dsa_pre_hash_context_c9(
                domain_separation_context0)
                .meta)}};
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        uu____1, Eurydice_array_to_slice_shared_79(&lvalue));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake, libcrux_secrets_int_classify_public_classify_ref_6d_90(
                    libcrux_iot_ml_dsa_pre_hash_context_c9(
                        domain_separation_context0)));
    const Option_57 *uu____2 =
        libcrux_iot_ml_dsa_pre_hash_pre_hash_oid_c9(domain_separation_context0);
    if (uu____2->tag == Some) {
      const Eurydice_arr_c9 *pre_hash_oid = &uu____2->f0;
      libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____3 = &shake;
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          uu____3, Eurydice_array_to_slice_shared_2f(
                       libcrux_secrets_int_public_integers_classify_ref_c5_95(
                           pre_hash_oid)));
    }
  }
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, libcrux_secrets_int_classify_public_classify_ref_6d_90(message));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_17(message_representative));
}

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_f5

*/
typedef struct Option_76_s {
  Option_87_tags tag;
  Eurydice_arr_f5 f0;
} Option_76;

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 576
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_22 *out) {
  libcrux_iot_sha3_shake256_ema(Eurydice_array_to_slice_mut_8a(out), input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 576
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_5a(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_22 *out0, Eurydice_arr_22 *out1, Eurydice_arr_22 *out2,
    Eurydice_arr_22 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(input0, out0);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(input1, out1);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(input2, out2);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(input3, out3);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
    size_t gamma1_exponent, Eurydice_borrow_slice_u8 serialized,
    Eurydice_arr_ef *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_gamma1_deserialize_c5(
        Eurydice_slice_subslice_shared_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = i0 * (gamma1_exponent + (size_t)1U),
                .end = (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U)})),
        &result->data[i0], gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.hash_functions.portable.shake256
with const generics
- OUTPUT_LENGTH= 640
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_20 *out) {
  libcrux_iot_sha3_shake256_ema(Eurydice_array_to_slice_mut_4f(out), input);
}

/**
This function found in impl {libcrux_iot_ml_dsa::hash_functions::shake256::XofX4
for libcrux_iot_ml_dsa::hash_functions::portable::Shake256X4}
*/
/**
A monomorphic instance of
libcrux_iot_ml_dsa.hash_functions.portable.shake256_x4_29 with const generics
- OUT_LEN= 640
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_0e(
    Eurydice_borrow_slice_u8 input0, Eurydice_borrow_slice_u8 input1,
    Eurydice_borrow_slice_u8 input2, Eurydice_borrow_slice_u8 input3,
    Eurydice_arr_20 *out0, Eurydice_arr_20 *out1, Eurydice_arr_20 *out2,
    Eurydice_arr_20 *out3) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(input0, out0);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(input1, out1);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(input2, out2);
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(input3, out3);
}

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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_5a(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_22 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_5a(input, out);
}

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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_0e(
    Eurydice_borrow_slice_u8 input, Eurydice_arr_20 *out) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake256_0e(input, out);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(
    const Eurydice_arr_91 *seed, Eurydice_arr_ef *result,
    size_t gamma1_exponent) {
  switch ((uint32_t)(uint8_t)gamma1_exponent) {
    case 17U: {
      Eurydice_arr_22 out;
      uint8_t repeat_expression[576U];
      for (size_t i = (size_t)0U; i < (size_t)576U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out.data, repeat_expression, (size_t)576U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_5a(
          Eurydice_array_to_slice_shared_f1(seed), &out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_8a(&out), result);
      break;
    }
    case 19U: {
      Eurydice_arr_20 out;
      uint8_t repeat_expression[640U];
      for (size_t i = (size_t)0U; i < (size_t)640U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out.data, repeat_expression, (size_t)640U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_0e(
          Eurydice_array_to_slice_shared_f1(seed), &out);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_4f(&out), result);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_mask_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
    size_t dimension, size_t gamma1_exponent, const Eurydice_arr_c7 *seed,
    uint16_t *domain_separator, Eurydice_dst_ref_mut_90 mask) {
  Eurydice_arr_91 seed0 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_17(seed), domain_separator[0U]);
  Eurydice_arr_91 seed1 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_17(seed),
      (uint32_t)domain_separator[0U] + 1U);
  Eurydice_arr_91 seed2 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_17(seed),
      (uint32_t)domain_separator[0U] + 2U);
  Eurydice_arr_91 seed3 = libcrux_iot_ml_dsa_sample_add_error_domain_separator(
      Eurydice_array_to_slice_shared_17(seed),
      (uint32_t)domain_separator[0U] + 3U);
  domain_separator[0U] = (uint32_t)domain_separator[0U] + 4U;
  switch ((uint32_t)(uint8_t)gamma1_exponent) {
    case 17U: {
      Eurydice_arr_22 out0;
      uint8_t repeat_expression0[576U];
      for (size_t i = (size_t)0U; i < (size_t)576U; i++) {
        repeat_expression0[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out0.data, repeat_expression0, (size_t)576U * sizeof(uint8_t));
      Eurydice_arr_22 out1;
      uint8_t repeat_expression1[576U];
      for (size_t i = (size_t)0U; i < (size_t)576U; i++) {
        repeat_expression1[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out1.data, repeat_expression1, (size_t)576U * sizeof(uint8_t));
      Eurydice_arr_22 out2;
      uint8_t repeat_expression2[576U];
      for (size_t i = (size_t)0U; i < (size_t)576U; i++) {
        repeat_expression2[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out2.data, repeat_expression2, (size_t)576U * sizeof(uint8_t));
      Eurydice_arr_22 out3;
      uint8_t repeat_expression[576U];
      for (size_t i = (size_t)0U; i < (size_t)576U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out3.data, repeat_expression, (size_t)576U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_5a(
          Eurydice_array_to_slice_shared_f1(&seed0),
          Eurydice_array_to_slice_shared_f1(&seed1),
          Eurydice_array_to_slice_shared_f1(&seed2),
          Eurydice_array_to_slice_shared_f1(&seed3), &out0, &out1, &out2,
          &out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_8a(&out0), mask.ptr);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_8a(&out1),
          &mask.ptr[1U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_8a(&out2),
          &mask.ptr[2U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_8a(&out3),
          &mask.ptr[3U]);
      break;
    }
    case 19U: {
      Eurydice_arr_20 out0;
      uint8_t repeat_expression0[640U];
      for (size_t i = (size_t)0U; i < (size_t)640U; i++) {
        repeat_expression0[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out0.data, repeat_expression0, (size_t)640U * sizeof(uint8_t));
      Eurydice_arr_20 out1;
      uint8_t repeat_expression1[640U];
      for (size_t i = (size_t)0U; i < (size_t)640U; i++) {
        repeat_expression1[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out1.data, repeat_expression1, (size_t)640U * sizeof(uint8_t));
      Eurydice_arr_20 out2;
      uint8_t repeat_expression2[640U];
      for (size_t i = (size_t)0U; i < (size_t)640U; i++) {
        repeat_expression2[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out2.data, repeat_expression2, (size_t)640U * sizeof(uint8_t));
      Eurydice_arr_20 out3;
      uint8_t repeat_expression[640U];
      for (size_t i = (size_t)0U; i < (size_t)640U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(out3.data, repeat_expression, (size_t)640U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_x4_29_0e(
          Eurydice_array_to_slice_shared_f1(&seed0),
          Eurydice_array_to_slice_shared_f1(&seed1),
          Eurydice_array_to_slice_shared_f1(&seed2),
          Eurydice_array_to_slice_shared_f1(&seed3), &out0, &out1, &out2,
          &out3);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_4f(&out0), mask.ptr);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_4f(&out1),
          &mask.ptr[1U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_4f(&out2),
          &mask.ptr[2U]);
      libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
          gamma1_exponent, Eurydice_array_to_slice_shared_4f(&out3),
          &mask.ptr[3U]);
      break;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                        "panic!");
      KRML_HOST_EXIT(255U);
    }
  }
  for (size_t i = (size_t)4U; i < dimension; i++) {
    size_t i0 = i;
    Eurydice_arr_91 seed4 =
        libcrux_iot_ml_dsa_sample_add_error_domain_separator(
            Eurydice_array_to_slice_shared_17(seed), domain_separator[0U]);
    domain_separator[0U] = (uint32_t)domain_separator[0U] + 1U;
    libcrux_iot_ml_dsa_sample_sample_mask_ring_element_1b(&seed4, &mask.ptr[i0],
                                                          gamma1_exponent);
  }
}

/**
 Compute InvertNTT(Â ◦ ŷ)
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_matrix_x_mask
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_dst_ref_shared_90 matrix,
    Eurydice_dst_ref_shared_90 mask, Eurydice_dst_ref_mut_90 result) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      Eurydice_arr_ef product = mask.ptr[j];
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          &product, &matrix.ptr[i1 * columns_in_a + j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&result.ptr[i1], &product);
    }
    libcrux_iot_ml_dsa_ntt_reduce_08(&result.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&result.ptr[i1]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.decompose_vector
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
    size_t dimension, int32_t gamma2, Eurydice_dst_ref_shared_90 t,
    Eurydice_dst_ref_mut_90 low, Eurydice_dst_ref_mut_90 high) {
  for (size_t i0 = (size_t)0U; i0 < dimension; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_simd_portable_decompose_c5(gamma2, &t.ptr[i1].data[j],
                                                    &low.ptr[i1].data[j],
                                                    &high.ptr[i1].data[j]);
    }
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.commitment.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized) {
  size_t output_bytes_per_simd_unit =
      serialized.meta / ((size_t)8U * (size_t)4U);
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_commitment_serialize_c5(
        simd_unit, Eurydice_slice_subslice_mut_c8(
                       serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                       .start = i0 * output_bytes_per_simd_unit,
                                       .end = (i0 + (size_t)1U) *
                                              output_bytes_per_simd_unit})));
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.commitment.serialize_vector with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
    size_t ring_element_size, Eurydice_dst_ref_shared_90 vector,
    Eurydice_mut_borrow_slice_u8 serialized) {
  size_t offset = (size_t)0U;
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_ef *ring_element = &vector.ptr[_cloop_j];
    libcrux_iot_ml_dsa_encoding_commitment_serialize_08(
        ring_element, Eurydice_slice_subslice_mut_c8(
                          serialized, (KRML_CLITERAL(core_ops_range_Range_87){
                                          .start = offset,
                                          .end = offset + ring_element_size})));
    offset += ring_element_size;
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.sample.sample_challenge_ring_element with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256 with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
    Eurydice_borrow_slice_u8 seed, size_t number_of_ones, Eurydice_arr_ef *re) {
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_init_absorb_final_a1(seed);
  Eurydice_arr_ff randomness0 =
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_first_block_a1(&state);
  Eurydice_array_u8x8 arr;
  memcpy(arr.data,
         Eurydice_array_to_subslice_shared_d40(
             &randomness0, (KRML_CLITERAL(core_ops_range_Range_87){
                               .start = (size_t)0U, .end = (size_t)8U}))
             .ptr,
         (size_t)8U * sizeof(uint8_t));
  uint64_t signs = core_num__u64__from_le_bytes(unwrap_26_e0(
      (KRML_CLITERAL(Result_8e){.tag = Ok, .val = {.case_Ok = arr}})));
  Eurydice_arr_6c result;
  int32_t repeat_expression[256U];
  for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_a8(0);
  }
  memcpy(result.data, repeat_expression, (size_t)256U * sizeof(int32_t));
  size_t out_index = (size_t)256U - number_of_ones;
  bool done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
      Eurydice_array_to_subslice_from_shared_5f(&randomness0, (size_t)8U),
      &out_index, &signs, &result);
  while (true) {
    if (done) {
      break;
    } else {
      Eurydice_arr_ff randomness =
          libcrux_iot_ml_dsa_hash_functions_portable_squeeze_next_block_a1(
              &state);
      done = libcrux_iot_ml_dsa_sample_inside_out_shuffle(
          Eurydice_array_to_slice_shared_58(&randomness), &out_index, &signs,
          &result);
    }
  }
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
      Eurydice_array_to_slice_shared_af(&result), re);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.vector_times_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
    Eurydice_dst_ref_mut_90 vector, const Eurydice_arr_ef *ring_element) {
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(&vector.ptr[i0],
                                                      ring_element);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&vector.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.add_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_add_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_90 lhs,
    Eurydice_dst_ref_shared_90 rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_add_c2_08(&lhs.ptr[i0], &rhs.ptr[i0]);
  }
}

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
KRML_MUSTINLINE void libcrux_iot_ml_dsa_polynomial_subtract_c2_08(
    Eurydice_arr_ef *self, const Eurydice_arr_ef *rhs) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_subtract_c5(&self->data[i0],
                                                 &rhs->data[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.subtract_vectors
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
    size_t dimension, Eurydice_dst_ref_mut_90 lhs,
    Eurydice_dst_ref_shared_90 rhs) {
  for (size_t i = (size_t)0U; i < dimension; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(&lhs.ptr[i0], &rhs.ptr[i0]);
  }
}

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
KRML_MUSTINLINE bool libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
    const Eurydice_arr_ef *self, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_iot_ml_dsa_simd_portable_infinity_norm_exceeds_c5(
          &self->data[i0], bound);
    }
    result = uu____0;
  }
  return result;
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.arithmetic.vector_infinity_norm_exceeds with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE bool
libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
    Eurydice_dst_ref_shared_90 vector, int32_t bound) {
  bool result = false;
  for (size_t i = (size_t)0U; i < vector.meta; i++) {
    size_t _cloop_j = i;
    const Eurydice_arr_ef *ring_element = &vector.ptr[_cloop_j];
    bool uu____0;
    if (result) {
      uu____0 = true;
    } else {
      uu____0 = libcrux_iot_ml_dsa_polynomial_infinity_norm_exceeds_c2_08(
          ring_element, bound);
    }
    result = uu____0;
  }
  return result;
}

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
    const Eurydice_arr_ef *self) {
  Eurydice_arr_6c result = {.data = {0U}};
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &self->data[i0];
    libcrux_iot_ml_dsa_simd_portable_to_coefficient_array_c5(
        simd_unit,
        Eurydice_array_to_subslice_mut_44(
            &result,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT,
                .end =
                    (i0 + (size_t)1U) *
                    LIBCRUX_IOT_ML_DSA_SIMD_TRAITS_COEFFICIENTS_IN_SIMD_UNIT})));
  }
  return result;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.make_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE size_t libcrux_iot_ml_dsa_arithmetic_make_hint_08(
    Eurydice_dst_ref_shared_90 low, Eurydice_dst_ref_shared_90 high,
    int32_t gamma2, Eurydice_dst_ref_mut_20 hint) {
  size_t true_hints = (size_t)0U;
  Eurydice_arr_ef hint_simd = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  for (size_t i0 = (size_t)0U; i0 < low.meta; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      size_t j = i;
      size_t one_hints_count = libcrux_iot_ml_dsa_simd_portable_compute_hint_c5(
          &low.ptr[i1].data[j], &high.ptr[i1].data[j], gamma2,
          &hint_simd.data[j]);
      true_hints += one_hints_count;
    }
    Eurydice_arr_6c uu____0 =
        libcrux_iot_ml_dsa_polynomial_to_i32_array_c2_08(&hint_simd);
    hint.ptr[i1] = uu____0;
  }
  return true_hints;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.gamma1.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
    const Eurydice_arr_ef *re, Eurydice_mut_borrow_slice_u8 serialized,
    size_t gamma1_exponent) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    const Eurydice_arr_4d *simd_unit = &re->data[i0];
    libcrux_iot_ml_dsa_simd_portable_gamma1_serialize_c5(
        simd_unit,
        Eurydice_slice_subslice_mut_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = i0 * (gamma1_exponent + (size_t)1U),
                .end = (i0 + (size_t)1U) * (gamma1_exponent + (size_t)1U)})),
        gamma1_exponent);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.serialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_encoding_signature_serialize_08(
    Eurydice_borrow_slice_u8 commitment_hash,
    Eurydice_dst_ref_shared_90 signer_response, Eurydice_dst_ref_shared_20 hint,
    size_t commitment_hash_size, size_t columns_in_a, size_t rows_in_a,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, Eurydice_mut_borrow_slice_u8 signature) {
  size_t offset = (size_t)0U;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          signature,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = offset, .end = offset + commitment_hash_size})),
      commitment_hash, uint8_t);
  offset += commitment_hash_size;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_gamma1_serialize_08(
        &signer_response.ptr[i0],
        Eurydice_slice_subslice_mut_c8(
            signature,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = offset, .end = offset + gamma1_ring_element_size})),
        gamma1_exponent);
    offset += gamma1_ring_element_size;
  }
  size_t true_hints_seen = (size_t)0U;
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    for (size_t i = (size_t)0U; i < (size_t)256U; i++) {
      size_t j = i;
      if (hint.ptr[i1].data[j] == 1) {
        signature.ptr[offset + true_hints_seen] = (uint8_t)j;
        true_hints_seen++;
      }
    }
    signature.ptr[offset + max_ones_in_hint + i1] = (uint8_t)true_hints_seen;
  }
}

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_f5 s1_as_ntt;
  Eurydice_arr_ef repeat_expression0[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)4U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_f5 s2_as_ntt;
  Eurydice_arr_ef repeat_expression1[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)4U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_f5 t0_as_ntt;
  Eurydice_arr_ef repeat_expression2[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)4U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, array_to_slice_mut_711(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, array_to_slice_mut_711(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, array_to_slice_mut_711(&t0_as_ntt));
  Eurydice_arr_f8 matrix;
  Eurydice_arr_ef repeat_expression3[16U];
  for (size_t i = (size_t)0U; i < (size_t)16U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)16U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____5 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, uu____5,
      array_to_slice_mut_71(&matrix));
  Eurydice_arr_c7 message_representative;
  uint8_t repeat_expression4[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression4[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(message_representative.data, repeat_expression4,
         (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          verification_key_hash),
      &domain_separation_context,
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
      &message_representative);
  Eurydice_arr_c7 mask_seed;
  uint8_t repeat_expression5[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(mask_seed.data, repeat_expression5, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_17(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_17(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_14 commitment_hash0 = {.tag = None};
  Option_76 signer_response0 = {.tag = None};
  Option_51 hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_f5 mask;
    Eurydice_arr_ef repeat_expression6[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression6, (size_t)4U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_f5 w0;
    Eurydice_arr_ef repeat_expression7[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression7[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression7, (size_t)4U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_f5 commitment;
    Eurydice_arr_ef repeat_expression8[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression8[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression8,
           (size_t)4U * sizeof(Eurydice_arr_ef));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, array_to_slice_mut_711(&mask));
    Eurydice_arr_f5 a_x_mask;
    Eurydice_arr_ef repeat_expression9[4U];
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      repeat_expression9[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression9,
           (size_t)4U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_f5 mask_ntt = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)4U, &mask, Eurydice_arr_ef, Eurydice_arr_f5);
    for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        array_to_slice_shared_71(&matrix), array_to_slice_shared_710(&mask_ntt),
        array_to_slice_mut_711(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
        array_to_slice_shared_710(&a_x_mask), array_to_slice_mut_711(&w0),
        array_to_slice_mut_711(&commitment));
    Eurydice_arr_ec commitment_hash_candidate;
    uint8_t repeat_expression10[32U];
    for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
      repeat_expression10[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_hash_candidate.data, repeat_expression10,
           (size_t)32U * sizeof(uint8_t));
    Eurydice_arr_d2 commitment_serialized;
    uint8_t repeat_expression[768U];
    for (size_t i = (size_t)0U; i < (size_t)768U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_serialized.data, repeat_expression,
           (size_t)768U * sizeof(uint8_t));
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
        array_to_slice_shared_710(&commitment),
        Eurydice_array_to_slice_mut_27(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake0 =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake0, Eurydice_array_to_slice_shared_17(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake0, Eurydice_array_to_slice_shared_27(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake0, Eurydice_array_to_slice_mut_01(&commitment_hash_candidate));
    Eurydice_arr_ef verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_01(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_f5 challenge_times_s1 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)4U, &s1_as_ntt, Eurydice_arr_ef, Eurydice_arr_f5);
    Eurydice_arr_f5 challenge_times_s2 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)4U, &s2_as_ntt, Eurydice_arr_ef, Eurydice_arr_f5);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_711(&challenge_times_s1), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_711(&challenge_times_s2), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
        array_to_slice_mut_711(&mask),
        array_to_slice_shared_710(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
        array_to_slice_mut_711(&w0),
        array_to_slice_shared_710(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_710(&mask),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              array_to_slice_shared_710(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
        Eurydice_arr_f5 challenge_times_t0 =
            core_array__core__clone__Clone_for__T__N___clone(
                (size_t)4U, &t0_as_ntt, Eurydice_arr_ef, Eurydice_arr_f5);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            array_to_slice_mut_711(&challenge_times_t0), &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                array_to_slice_shared_710(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
              array_to_slice_mut_711(&w0),
              array_to_slice_shared_710(&challenge_times_t0));
          Eurydice_arr_b7 hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              array_to_slice_shared_710(&w0),
              array_to_slice_shared_710(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
              Eurydice_array_to_slice_mut_86(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_14){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_76){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_51){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____6;
  if (commitment_hash0.tag == None) {
    uu____6 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_ec commitment_hash = commitment_hash0.f0;
    Eurydice_arr_ec commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_f5 signer_response = signer_response0.f0;
      Eurydice_arr_f5 signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_b7 hint = hint0.f0;
        Eurydice_arr_b7 hint1 = hint;
        const Eurydice_arr_ec *uu____7 =
            libcrux_secrets_int_public_integers_declassify_ref_ad_4b(
                &commitment_hash1);
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_01(uu____7),
            array_to_slice_shared_710(&signer_response1),
            Eurydice_array_to_slice_shared_86(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_0d(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____6;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
      signing_key,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_b2 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_85 signature = libcrux_iot_ml_dsa_types_zero_ad_37();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_b2 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_b2){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_b2){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
Result_b2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_c4(
      Eurydice_array_to_slice_shared_34(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_ab(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_mut_c4(
      Eurydice_array_to_slice_shared_34(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_mut(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_mut(
      libcrux_iot_ml_dsa_types_as_ref_f8_ab(signing_key), message, context,
      randomness, signature);
}

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
Eurydice_arr_c9 libcrux_iot_ml_dsa_pre_hash_oid_0b(void) {
  return LIBCRUX_IOT_ML_DSA_PRE_HASH_SHAKE128_OID;
}

/**
This function found in impl {libcrux_iot_ml_dsa::pre_hash::PreHash for
libcrux_iot_ml_dsa::pre_hash::SHAKE128_PH}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.pre_hash.hash_0b
with types libcrux_iot_ml_dsa_hash_functions_portable_Shake128
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
    Eurydice_borrow_slice_u8 message, Eurydice_mut_borrow_slice_u8 output) {
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_e2(message, output);
}

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_85 *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
        libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
        pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_57){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
KRML_MUSTINLINE Result_b2
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  Eurydice_arr_85 signature = libcrux_iot_ml_dsa_types_zero_ad_37();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_b2 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_b2){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_b2){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
Result_b2
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_34(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_b2 libcrux_iot_ml_dsa_ml_dsa_44_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_10 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_10 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_ab(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer), randomness);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.t1.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
void libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
    Eurydice_borrow_slice_u8 serialized, Eurydice_arr_ef *result) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_t1_deserialize_c5(
        Eurydice_slice_subslice_shared_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start = i0 * LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_DSA_ENCODING_T1_DESERIALIZE_WINDOW})),
        &result->data[i0]);
  }
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.encoding.verification_key.deserialize with types
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics

*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
    size_t rows_in_a, size_t verification_key_size,
    Eurydice_borrow_slice_u8 serialized, Eurydice_dst_ref_mut_90 t1) {
  for (size_t i = (size_t)0U; i < rows_in_a; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_encoding_t1_deserialize_08(
        Eurydice_slice_subslice_shared_c8(
            serialized,
            (KRML_CLITERAL(core_ops_range_Range_87){
                .start =
                    i0 * LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE,
                .end = (i0 + (size_t)1U) *
                       LIBCRUX_IOT_ML_DSA_CONSTANTS_RING_ELEMENT_OF_T1S_SIZE})),
        &t1.ptr[i0]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.encoding.signature.deserialize
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE Result_5c libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
    size_t columns_in_a, size_t rows_in_a, size_t commitment_hash_size,
    size_t gamma1_exponent, size_t gamma1_ring_element_size,
    size_t max_ones_in_hint, size_t signature_size,
    Eurydice_borrow_slice_u8 serialized,
    Eurydice_mut_borrow_slice_u8 out_commitment_hash,
    Eurydice_dst_ref_mut_90 out_signer_response,
    Eurydice_dst_ref_mut_20 out_hint) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      serialized, commitment_hash_size, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 commitment_hash = uu____0.fst;
  Eurydice_borrow_slice_u8 rest_of_serialized = uu____0.snd;
  Eurydice_slice_copy(
      Eurydice_slice_subslice_mut_c8(
          out_commitment_hash,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U, .end = commitment_hash_size})),
      commitment_hash, uint8_t);
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      rest_of_serialized, gamma1_ring_element_size * columns_in_a, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 signer_response_serialized = uu____1.fst;
  Eurydice_borrow_slice_u8 hint_serialized = uu____1.snd;
  for (size_t i = (size_t)0U; i < columns_in_a; i++) {
    size_t i0 = i;
    /* original Rust expression is not an lvalue in C */
    Eurydice_borrow_slice_u8 lvalue =
        libcrux_secrets_int_classify_public_classify_ref_6d_90(
            Eurydice_slice_subslice_shared_c8(
                signer_response_serialized,
                (KRML_CLITERAL(core_ops_range_Range_87){
                    .start = i0 * gamma1_ring_element_size,
                    .end = (i0 + (size_t)1U) * gamma1_ring_element_size})));
    libcrux_iot_ml_dsa_encoding_gamma1_deserialize_08(
        gamma1_exponent, lvalue, &out_signer_response.ptr[i0]);
  }
  size_t previous_true_hints_seen = (size_t)0U;
  size_t i0 = (size_t)0U;
  bool malformed_hint = false;
  while (true) {
    if (malformed_hint) {
      break;
    } else {
      if (!(i0 < rows_in_a)) {
        break;
      }
      size_t current_true_hints_seen =
          (size_t)(uint32_t)hint_serialized.ptr[max_ones_in_hint + i0];
      if (current_true_hints_seen < previous_true_hints_seen) {
        malformed_hint = true;
      } else if (current_true_hints_seen > max_ones_in_hint) {
        malformed_hint = true;
      }
      size_t j = previous_true_hints_seen;
      while (true) {
        if (malformed_hint) {
          break;
        } else {
          if (!(j < current_true_hints_seen)) {
            break;
          }
          if (j > previous_true_hints_seen) {
            if (hint_serialized.ptr[j] <= hint_serialized.ptr[j - (size_t)1U]) {
              malformed_hint = true;
            }
          }
          if (!malformed_hint) {
            libcrux_iot_ml_dsa_encoding_signature_set_hint(
                out_hint, i0, (size_t)(uint32_t)hint_serialized.ptr[j]);
            j++;
          }
        }
      }
      if (!malformed_hint) {
        previous_true_hints_seen = current_true_hints_seen;
        i0++;
      }
    }
  }
  i0 = previous_true_hints_seen;
  for (size_t i = i0; i < max_ones_in_hint; i++) {
    size_t j = i;
    if (hint_serialized.ptr[j] != 0U) {
      malformed_hint = true;
      break;
    }
  }
  if (!malformed_hint) {
    return (KRML_CLITERAL(Result_5c){.tag = Ok});
  }
  return (KRML_CLITERAL(Result_5c){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError});
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.sample.sample_ring_element
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_sample_sample_ring_element_08(
    Eurydice_borrow_slice_u8 seed, uint8_t_x2 indices, Eurydice_arr_ef *out,
    Eurydice_arr_d1 *rand_stack, Eurydice_arr_c5 *rand_block,
    Eurydice_arr_d0 *tmp_stack) {
  Eurydice_arr_31 domain_separated_seed =
      libcrux_iot_ml_dsa_sample_add_domain_separator(seed, indices);
  /* original Rust expression is not an lvalue in C */
  Eurydice_arr_31 lvalue =
      libcrux_secrets_int_public_integers_classify_27_78(domain_separated_seed);
  libcrux_iot_sha3_state_KeccakState state =
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_init_absorb_b5(
          Eurydice_array_to_slice_shared_e9(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_first_five_blocks_b5(
      &state, rand_stack);
  size_t sampled = (size_t)0U;
  bool done =
      libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
          libcrux_secrets_int_classify_public_declassify_ref_5c_90(
              core_array___T__N___as_slice((size_t)840U, rand_stack, uint8_t,
                                           Eurydice_borrow_slice_u8)),
          &sampled, tmp_stack);
  while (true) {
    if (done) {
      break;
    } else {
      libcrux_iot_ml_dsa_hash_functions_portable_shake128_squeeze_next_block_b5(
          &state, rand_block);
      if (!done) {
        done =
            libcrux_iot_ml_dsa_sample_rejection_sample_less_than_field_modulus_08(
                libcrux_secrets_int_classify_public_declassify_ref_5c_90(
                    core_array___T__N___as_slice((size_t)168U, rand_block,
                                                 uint8_t,
                                                 Eurydice_borrow_slice_u8)),
                &sampled, tmp_stack);
      }
    }
  }
  /* original Rust expression is not an lvalue in C */
  Eurydice_dst_ref_shared_83 lvalue0 =
      libcrux_secrets_int_classify_public_classify_ref_6d_a8(
          Eurydice_array_to_subslice_to_shared_25(tmp_stack, (size_t)256U));
  libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(lvalue0, out);
}

/**
A monomorphic instance of
libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce with const
generics
- SHIFT_BY= 13
*/
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
    Eurydice_arr_4d *simd_unit) {
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    size_t i0 = i;
    simd_unit->data[i0] =
        libcrux_iot_ml_dsa_simd_portable_arithmetic_reduce_element(
            (int32_t)((uint32_t)simd_unit->data[i0] << (uint32_t)13));
  }
}

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
    Eurydice_arr_4d *simd_unit) {
  libcrux_iot_ml_dsa_simd_portable_arithmetic_shift_left_then_reduce_84(
      simd_unit);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.shift_left_then_reduce
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics
- SHIFT_BY= 13
*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(
    Eurydice_arr_ef *re) {
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_simd_portable_shift_left_then_reduce_c5_84(
        &re->data[i0]);
  }
}

/**
 Compute InvertNTT(Â ◦ ẑ - ĉ ◦ NTT(t₁2ᵈ))
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.matrix.compute_w_approx
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
    size_t rows_in_a, size_t columns_in_a, Eurydice_borrow_slice_u8 seed,
    Eurydice_arr_d1 *rand_stack, Eurydice_arr_c5 *rand_block,
    Eurydice_arr_d0 *tmp_stack, Eurydice_arr_ef *poly_slot,
    Eurydice_dst_ref_shared_90 signer_response,
    const Eurydice_arr_ef *verifier_challenge_as_ntt,
    Eurydice_dst_ref_mut_90 t1) {
  for (size_t i0 = (size_t)0U; i0 < rows_in_a; i0++) {
    size_t i1 = i0;
    Eurydice_arr_ef inner_result = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    for (size_t i = (size_t)0U; i < columns_in_a; i++) {
      size_t j = i;
      libcrux_iot_ml_dsa_sample_sample_ring_element_08(
          seed,
          (KRML_CLITERAL(uint8_t_x2){.fst = (uint8_t)i1, .snd = (uint8_t)j}),
          poly_slot, rand_stack, rand_block, tmp_stack);
      libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
          poly_slot, &signer_response.ptr[j]);
      libcrux_iot_ml_dsa_polynomial_add_c2_08(&inner_result, poly_slot);
    }
    libcrux_iot_ml_dsa_arithmetic_shift_left_then_reduce_41(&t1.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_ntt_08(&t1.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_ntt_multiply_montgomery_08(
        &t1.ptr[i1], verifier_challenge_as_ntt);
    libcrux_iot_ml_dsa_polynomial_subtract_c2_08(&inner_result, &t1.ptr[i1]);
    t1.ptr[i1] = inner_result;
    libcrux_iot_ml_dsa_ntt_reduce_08(&t1.ptr[i1]);
    libcrux_iot_ml_dsa_ntt_invert_ntt_montgomery_08(&t1.ptr[i1]);
  }
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.arithmetic.use_hint
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients
with const generics

*/
KRML_MUSTINLINE void libcrux_iot_ml_dsa_arithmetic_use_hint_08(
    int32_t gamma2, Eurydice_dst_ref_shared_20 hint,
    Eurydice_dst_ref_mut_90 re_vector) {
  for (size_t i = (size_t)0U; i < re_vector.meta; i++) {
    size_t i0 = i;
    Eurydice_arr_ef tmp = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    /* original Rust expression is not an lvalue in C */
    Eurydice_arr_6c lvalue =
        libcrux_secrets_int_public_integers_classify_27_9d(hint.ptr[i0]);
    libcrux_iot_ml_dsa_polynomial_from_i32_array_c2_08(
        Eurydice_array_to_slice_shared_af(&lvalue), &tmp);
    for (size_t i1 = (size_t)0U; i1 < (size_t)32U; i1++) {
      size_t j = i1;
      libcrux_iot_ml_dsa_simd_portable_use_hint_c5(
          gamma2, &re_vector.ptr[i0].data[j], &tmp.data[j]);
    }
    re_vector.ptr[i0] = tmp;
  }
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_85 *signature_serialized) {
  Eurydice_arr_d1 rand_stack;
  uint8_t repeat_expression0[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack.data, repeat_expression0, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_c5 rand_block;
  uint8_t repeat_expression1[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_block.data, repeat_expression1, (size_t)168U * sizeof(uint8_t));
  Eurydice_arr_d0 tmp_stack = {.data = {0U}};
  Eurydice_arr_ef poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_9f(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_f5 t1;
  Eurydice_arr_ef repeat_expression2[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression2, (size_t)4U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_VERIFICATION_KEY_SIZE,
      t1_serialized, array_to_slice_mut_711(&t1));
  Eurydice_arr_ec deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_f5 deserialized_signer_response;
  Eurydice_arr_ef repeat_expression3[4U];
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression3,
         (size_t)4U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_b7 deserialized_hint = {
      .data = {{.data = {0U}}, {.data = {0U}}, {.data = {0U}}, {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_0d(signature_serialized),
      Eurydice_array_to_slice_mut_01(&deserialized_commitment_hash),
      array_to_slice_mut_711(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_86(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_710(&deserialized_signer_response),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_c7 verification_key_hash;
      uint8_t repeat_expression4[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression4[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(verification_key_hash.data, repeat_expression4,
             (size_t)64U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
          Eurydice_array_to_slice_shared_9f(
              libcrux_secrets_int_public_integers_classify_ref_c5_8d(
                  verification_key)),
          &verification_key_hash);
      Eurydice_arr_c7 message_representative;
      uint8_t repeat_expression5[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression5[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(message_representative.data, repeat_expression5,
             (size_t)64U * sizeof(uint8_t));
      Eurydice_borrow_slice_u8 uu____3 = Eurydice_array_to_slice_shared_17(
          libcrux_secrets_int_public_integers_declassify_ref_ad_56(
              &verification_key_hash));
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          uu____3, &domain_separation_context,
          libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
          &message_representative);
      Eurydice_arr_ef verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_01(
              libcrux_secrets_int_public_integers_classify_ref_c5_4b(
                  &deserialized_commitment_hash)),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          array_to_slice_shared_710(&deserialized_signer_response),
          &verifier_challenge, array_to_slice_mut_711(&t1));
      Eurydice_arr_ec recomputed_commitment_hash;
      uint8_t repeat_expression6[32U];
      for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
        repeat_expression6[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(recomputed_commitment_hash.data, repeat_expression6,
             (size_t)32U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_44_GAMMA2,
          Eurydice_array_to_slice_shared_86(&deserialized_hint),
          array_to_slice_mut_711(&t1));
      Eurydice_arr_d2 commitment_serialized;
      uint8_t repeat_expression[768U];
      for (size_t i = (size_t)0U; i < (size_t)768U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(commitment_serialized.data, repeat_expression,
             (size_t)768U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_44_COMMITMENT_RING_ELEMENT_SIZE,
          array_to_slice_shared_710(&t1),
          Eurydice_array_to_slice_mut_27(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_17(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_27(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_01(&recomputed_commitment_hash));
      if (Eurydice_array_eq(
              (size_t)32U, &deserialized_commitment_hash,
              libcrux_secrets_int_public_integers_declassify_ref_ad_4b(
                  &recomputed_commitment_hash),
              uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_44.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_MUSTINLINE Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
    const Eurydice_arr_02 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_85 *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-44 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_7d(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_37(signature));
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
    const Eurydice_arr_02 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_85 *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_85 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_44_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-44 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_44_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_02 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_85 *signature) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_02 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_7d(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_44_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_37(signature));
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 30
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_712(Eurydice_arr_51 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)30U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_713(Eurydice_arr_3d *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 5
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_714(Eurydice_arr_15 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)5U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static Eurydice_dst_ref_shared_90 array_to_subslice_shared_720(
    const Eurydice_arr_3d *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_90){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 30
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_712(
    const Eurydice_arr_51 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)30U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 5
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_713(
    const Eurydice_arr_15 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)5U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 11
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_714(
    const Eurydice_arr_3d *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)11U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 6
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_715(Eurydice_arr_05 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 6
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_715(
    const Eurydice_arr_05 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)6U;
  return lit;
}

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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_89 seed_expanded0;
  uint8_t repeat_expression0[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed_expanded0.data, repeat_expression0,
         (size_t)128U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____0 = &shake;
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A),
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A)}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      uu____0, Eurydice_array_to_slice_shared_82(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_78(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_78(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____2.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____2.snd;
  Eurydice_arr_51 a_as_ntt;
  Eurydice_arr_ef repeat_expression1[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression1,
         (size_t)30U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____3 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, uu____3,
      array_to_slice_mut_712(&a_as_ntt));
  Eurydice_arr_3d s1_s2;
  Eurydice_arr_ef repeat_expression2[11U];
  for (size_t i = (size_t)0U; i < (size_t)11U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression2, (size_t)11U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA, seed_for_error_vectors,
      array_to_slice_mut_713(&s1_s2));
  Eurydice_arr_05 t0;
  Eurydice_arr_ef repeat_expression3[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression3, (size_t)6U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_15 s1_ntt;
  Eurydice_arr_ef repeat_expression4[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression4, (size_t)5U * sizeof(Eurydice_arr_ef));
  Eurydice_slice_copy(
      array_to_slice_mut_714(&s1_ntt),
      array_to_subslice_shared_720(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A})),
      Eurydice_arr_ef);
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      array_to_slice_shared_712(&a_as_ntt), array_to_slice_shared_713(&s1_ntt),
      array_to_slice_shared_714(&s1_s2), array_to_slice_mut_715(&t0));
  Eurydice_arr_05 t1;
  Eurydice_arr_ef repeat_expression[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)6U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      array_to_slice_mut_715(&t0), array_to_slice_mut_715(&t1));
  Eurydice_borrow_slice_u8 uu____4 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      uu____4, array_to_slice_shared_715(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      array_to_slice_shared_714(&s1_s2), array_to_slice_shared_715(&t0),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_24 *signing_key,
    Eurydice_arr_29 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_98(signing_key),
      Eurydice_array_to_slice_mut_37(verification_key));
}

/**
 Generate an ML-DSA-65 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5
libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair(
    Eurydice_arr_ec randomness) {
  Eurydice_arr_24 signing_key;
  uint8_t repeat_expression[4032U];
  for (size_t i = (size_t)0U; i < (size_t)4032U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(signing_key.data, repeat_expression, (size_t)4032U * sizeof(uint8_t));
  Eurydice_arr_29 verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_e5(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_a2(verification_key)});
}

/**
 Generate an ML-DSA-65 Key Pair
*/
void libcrux_iot_ml_dsa_ml_dsa_65_portable_generate_key_pair_mut(
    Eurydice_arr_ec randomness, Eurydice_arr_24 *signing_key,
    Eurydice_arr_29 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_generate_key_pair(
      randomness, signing_key, verification_key);
}

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_65

*/
typedef struct Option_81_s {
  Option_87_tags tag;
  Eurydice_arr_65 f0;
} Option_81;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_5d

*/
typedef struct Option_1e_s {
  Option_87_tags tag;
  Eurydice_arr_5d f0;
} Option_1e;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_15

*/
typedef struct Option_9d_s {
  Option_87_tags tag;
  Eurydice_arr_15 f0;
} Option_9d;

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_15 s1_as_ntt;
  Eurydice_arr_ef repeat_expression0[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)5U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_05 s2_as_ntt;
  Eurydice_arr_ef repeat_expression1[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)6U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_05 t0_as_ntt;
  Eurydice_arr_ef repeat_expression2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)6U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, array_to_slice_mut_714(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, array_to_slice_mut_715(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, array_to_slice_mut_715(&t0_as_ntt));
  Eurydice_arr_51 matrix;
  Eurydice_arr_ef repeat_expression3[30U];
  for (size_t i = (size_t)0U; i < (size_t)30U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)30U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____5 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, uu____5,
      array_to_slice_mut_712(&matrix));
  Eurydice_arr_c7 message_representative;
  uint8_t repeat_expression4[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression4[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(message_representative.data, repeat_expression4,
         (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          verification_key_hash),
      &domain_separation_context,
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
      &message_representative);
  Eurydice_arr_c7 mask_seed;
  uint8_t repeat_expression5[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(mask_seed.data, repeat_expression5, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_17(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_17(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_81 commitment_hash0 = {.tag = None};
  Option_9d signer_response0 = {.tag = None};
  Option_1e hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_15 mask;
    Eurydice_arr_ef repeat_expression6[5U];
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression6, (size_t)5U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_05 w0;
    Eurydice_arr_ef repeat_expression7[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression7[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression7, (size_t)6U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_05 commitment;
    Eurydice_arr_ef repeat_expression8[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression8[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression8,
           (size_t)6U * sizeof(Eurydice_arr_ef));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, array_to_slice_mut_714(&mask));
    Eurydice_arr_05 a_x_mask;
    Eurydice_arr_ef repeat_expression9[6U];
    for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
      repeat_expression9[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression9,
           (size_t)6U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_15 mask_ntt = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)5U, &mask, Eurydice_arr_ef, Eurydice_arr_15);
    for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        array_to_slice_shared_712(&matrix),
        array_to_slice_shared_713(&mask_ntt),
        array_to_slice_mut_715(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
        array_to_slice_shared_715(&a_x_mask), array_to_slice_mut_715(&w0),
        array_to_slice_mut_715(&commitment));
    Eurydice_arr_65 commitment_hash_candidate;
    uint8_t repeat_expression10[48U];
    for (size_t i = (size_t)0U; i < (size_t)48U; i++) {
      repeat_expression10[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_hash_candidate.data, repeat_expression10,
           (size_t)48U * sizeof(uint8_t));
    Eurydice_arr_d2 commitment_serialized;
    uint8_t repeat_expression[768U];
    for (size_t i = (size_t)0U; i < (size_t)768U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_serialized.data, repeat_expression,
           (size_t)768U * sizeof(uint8_t));
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
        array_to_slice_shared_715(&commitment),
        Eurydice_array_to_slice_mut_27(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake0 =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake0, Eurydice_array_to_slice_shared_17(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake0, Eurydice_array_to_slice_shared_27(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake0, Eurydice_array_to_slice_mut_9f(&commitment_hash_candidate));
    Eurydice_arr_ef verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_9f0(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_15 challenge_times_s1 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)5U, &s1_as_ntt, Eurydice_arr_ef, Eurydice_arr_15);
    Eurydice_arr_05 challenge_times_s2 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)6U, &s2_as_ntt, Eurydice_arr_ef, Eurydice_arr_05);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_714(&challenge_times_s1), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_715(&challenge_times_s2), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
        array_to_slice_mut_714(&mask),
        array_to_slice_shared_713(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
        array_to_slice_mut_715(&w0),
        array_to_slice_shared_715(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_713(&mask),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              array_to_slice_shared_715(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
        Eurydice_arr_05 challenge_times_t0 =
            core_array__core__clone__Clone_for__T__N___clone(
                (size_t)6U, &t0_as_ntt, Eurydice_arr_ef, Eurydice_arr_05);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            array_to_slice_mut_715(&challenge_times_t0), &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                array_to_slice_shared_715(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
              array_to_slice_mut_715(&w0),
              array_to_slice_shared_715(&challenge_times_t0));
          Eurydice_arr_5d hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              array_to_slice_shared_715(&w0),
              array_to_slice_shared_715(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
              Eurydice_array_to_slice_mut_860(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_81){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_9d){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_1e){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____6;
  if (commitment_hash0.tag == None) {
    uu____6 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_65 commitment_hash = commitment_hash0.f0;
    Eurydice_arr_65 commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_15 signer_response = signer_response0.f0;
      Eurydice_arr_15 signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_5d hint = hint0.f0;
        Eurydice_arr_5d hint1 = hint;
        const Eurydice_arr_65 *uu____7 =
            libcrux_secrets_int_public_integers_declassify_ref_ad_69(
                &commitment_hash1);
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_9f0(uu____7),
            array_to_slice_shared_713(&signer_response1),
            Eurydice_array_to_slice_shared_860(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_6b(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____6;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
      signing_key,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_0f libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_0c signature = libcrux_iot_ml_dsa_types_zero_ad_5c();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_0f uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_0f){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_0f){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
Result_0f
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_c4(
      Eurydice_array_to_slice_shared_980(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_65_portable_sign(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_e5(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_mut_c4(
      Eurydice_array_to_slice_shared_980(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_mut(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_mut(
      signing_key, message, context, randomness, signature);
}

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_0c *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
        libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
        pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_57){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
KRML_MUSTINLINE Result_0f
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  Eurydice_arr_0c signature = libcrux_iot_ml_dsa_types_zero_ad_5c();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_0f uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_0f){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_0f){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
Result_0f
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_980(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_0f libcrux_iot_ml_dsa_ml_dsa_65_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_24 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_24 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_e5(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer), randomness);
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_0c *signature_serialized) {
  Eurydice_arr_d1 rand_stack;
  uint8_t repeat_expression0[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack.data, repeat_expression0, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_c5 rand_block;
  uint8_t repeat_expression1[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_block.data, repeat_expression1, (size_t)168U * sizeof(uint8_t));
  Eurydice_arr_d0 tmp_stack = {.data = {0U}};
  Eurydice_arr_ef poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_37(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_05 t1;
  Eurydice_arr_ef repeat_expression2[6U];
  for (size_t i = (size_t)0U; i < (size_t)6U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression2, (size_t)6U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_VERIFICATION_KEY_SIZE,
      t1_serialized, array_to_slice_mut_715(&t1));
  Eurydice_arr_65 deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_15 deserialized_signer_response;
  Eurydice_arr_ef repeat_expression3[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression3,
         (size_t)5U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_5d deserialized_hint = {.data = {{.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_6b(signature_serialized),
      Eurydice_array_to_slice_mut_9f(&deserialized_commitment_hash),
      array_to_slice_mut_714(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_860(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_713(&deserialized_signer_response),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_c7 verification_key_hash;
      uint8_t repeat_expression4[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression4[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(verification_key_hash.data, repeat_expression4,
             (size_t)64U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
          Eurydice_array_to_slice_shared_37(
              libcrux_secrets_int_public_integers_classify_ref_c5_bb(
                  verification_key)),
          &verification_key_hash);
      Eurydice_arr_c7 message_representative;
      uint8_t repeat_expression5[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression5[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(message_representative.data, repeat_expression5,
             (size_t)64U * sizeof(uint8_t));
      Eurydice_borrow_slice_u8 uu____3 = Eurydice_array_to_slice_shared_17(
          libcrux_secrets_int_public_integers_declassify_ref_ad_56(
              &verification_key_hash));
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          uu____3, &domain_separation_context,
          libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
          &message_representative);
      Eurydice_arr_ef verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_9f0(
              libcrux_secrets_int_public_integers_classify_ref_c5_69(
                  &deserialized_commitment_hash)),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          array_to_slice_shared_713(&deserialized_signer_response),
          &verifier_challenge, array_to_slice_mut_715(&t1));
      Eurydice_arr_65 recomputed_commitment_hash;
      uint8_t repeat_expression6[48U];
      for (size_t i = (size_t)0U; i < (size_t)48U; i++) {
        repeat_expression6[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(recomputed_commitment_hash.data, repeat_expression6,
             (size_t)48U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_65_GAMMA2,
          Eurydice_array_to_slice_shared_860(&deserialized_hint),
          array_to_slice_mut_715(&t1));
      Eurydice_arr_d2 commitment_serialized;
      uint8_t repeat_expression[768U];
      for (size_t i = (size_t)0U; i < (size_t)768U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(commitment_serialized.data, repeat_expression,
             (size_t)768U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_65_COMMITMENT_RING_ELEMENT_SIZE,
          array_to_slice_shared_715(&t1),
          Eurydice_array_to_slice_mut_27(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_17(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_27(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_9f(&recomputed_commitment_hash));
      if (Eurydice_array_eq(
              (size_t)48U, &deserialized_commitment_hash,
              libcrux_secrets_int_public_integers_declassify_ref_ad_69(
                  &recomputed_commitment_hash),
              uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_65.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_MUSTINLINE Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
    const Eurydice_arr_29 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_0c *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-65 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_a2(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_5c(signature));
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
    const Eurydice_arr_29 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_0c *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_0c *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_65_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-65 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_65_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_29 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_0c *signature) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_29 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_a2(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_65_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_5c(signature));
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 56
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_716(Eurydice_arr_b4 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)56U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_717(Eurydice_arr_48 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)15U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 7
*/
static Eurydice_dst_ref_mut_90 array_to_slice_mut_718(Eurydice_arr_33 *a) {
  Eurydice_dst_ref_mut_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)7U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients, core_ops_range_Range
size_t, Eurydice_derefed_slice
libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static Eurydice_dst_ref_shared_90 array_to_subslice_shared_721(
    const Eurydice_arr_48 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_90){.ptr = a->data + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 56
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_716(
    const Eurydice_arr_b4 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)56U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 7
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_717(
    const Eurydice_arr_33 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)7U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types libcrux_iot_ml_dsa_polynomial_PolynomialRingElement
libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients with const generics
- N= 15
*/
static Eurydice_dst_ref_shared_90 array_to_slice_shared_718(
    const Eurydice_arr_48 *a) {
  Eurydice_dst_ref_shared_90 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)15U;
  return lit;
}

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
KRML_MUSTINLINE void
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
    Eurydice_arr_ec randomness, Eurydice_mut_borrow_slice_u8 signing_key,
    Eurydice_mut_borrow_slice_u8 verification_key) {
  Eurydice_arr_89 seed_expanded0;
  uint8_t repeat_expression0[128U];
  for (size_t i = (size_t)0U; i < (size_t)128U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(seed_expanded0.data, repeat_expression0,
         (size_t)128U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd *uu____0 = &shake;
  /* original Rust expression is not an lvalue in C */
  Eurydice_array_u8x2 lvalue = {
      .data = {
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A),
          libcrux_secrets_int_public_integers_classify_27_90(
              (uint8_t)LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A)}};
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      uu____0, Eurydice_array_to_slice_shared_82(&lvalue));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_78(&seed_expanded0));
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_78(&seed_expanded0),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____1.fst;
  Eurydice_borrow_slice_u8 seed_expanded = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      seed_expanded, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_ERROR_VECTORS_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_error_vectors = uu____2.fst;
  Eurydice_borrow_slice_u8 seed_for_signing = uu____2.snd;
  Eurydice_arr_b4 a_as_ntt;
  Eurydice_arr_ef repeat_expression1[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(a_as_ntt.data, repeat_expression1,
         (size_t)56U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____3 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, uu____3,
      array_to_slice_mut_716(&a_as_ntt));
  Eurydice_arr_48 s1_s2;
  Eurydice_arr_ef repeat_expression2[15U];
  for (size_t i = (size_t)0U; i < (size_t)15U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_s2.data, repeat_expression2, (size_t)15U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_samplex4_sample_s1_and_s2_e7(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA, seed_for_error_vectors,
      array_to_slice_mut_717(&s1_s2));
  Eurydice_arr_62 t0;
  Eurydice_arr_ef repeat_expression3[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0.data, repeat_expression3, (size_t)8U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_33 s1_ntt;
  Eurydice_arr_ef repeat_expression4[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression4[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_ntt.data, repeat_expression4, (size_t)7U * sizeof(Eurydice_arr_ef));
  Eurydice_slice_copy(
      array_to_slice_mut_718(&s1_ntt),
      array_to_subslice_shared_721(
          &s1_s2,
          (KRML_CLITERAL(core_ops_range_Range_87){
              .start = (size_t)0U,
              .end = LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A})),
      Eurydice_arr_ef);
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    size_t i0 = i;
    libcrux_iot_ml_dsa_ntt_ntt_08(&s1_ntt.data[i0]);
  }
  libcrux_iot_ml_dsa_matrix_compute_as1_plus_s2_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      array_to_slice_shared_716(&a_as_ntt), array_to_slice_shared_717(&s1_ntt),
      array_to_slice_shared_718(&s1_s2), array_to_slice_mut_710(&t0));
  Eurydice_arr_62 t1;
  Eurydice_arr_ef repeat_expression[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression, (size_t)8U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_arithmetic_power2round_vector_08(
      array_to_slice_mut_710(&t0), array_to_slice_mut_710(&t1));
  Eurydice_borrow_slice_u8 uu____4 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_encoding_verification_key_generate_serialized_08(
      uu____4, array_to_slice_shared_711(&t1), verification_key);
  libcrux_iot_ml_dsa_encoding_signing_key_generate_serialized_1b(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      seed_for_a, seed_for_signing,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = verification_key.ptr,
                                               .meta = verification_key.meta}),
      array_to_slice_shared_718(&s1_s2), array_to_slice_shared_711(&t0),
      signing_key);
}

/**
 Generate key pair.
*/
void libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
    Eurydice_arr_ec randomness, Eurydice_arr_e2 *signing_key,
    Eurydice_arr_43 *verification_key) {
  libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_generate_key_pair_c4(
      randomness, Eurydice_array_to_slice_mut_f7(signing_key),
      Eurydice_array_to_slice_mut_fc(verification_key));
}

/**
 Generate an ML-DSA-87 Key Pair
*/
libcrux_iot_ml_dsa_types_MLDSAKeyPair_850
libcrux_iot_ml_dsa_ml_dsa_87_portable_generate_key_pair(
    Eurydice_arr_ec randomness) {
  Eurydice_arr_e2 signing_key;
  uint8_t repeat_expression[4896U];
  for (size_t i = (size_t)0U; i < (size_t)4896U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(signing_key.data, repeat_expression, (size_t)4896U * sizeof(uint8_t));
  Eurydice_arr_43 verification_key = {.data = {0U}};
  libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_generate_key_pair(
      randomness, &signing_key, &verification_key);
  return (KRML_CLITERAL(libcrux_iot_ml_dsa_types_MLDSAKeyPair_850){
      .signing_key = libcrux_iot_ml_dsa_types_new_f8_72(signing_key),
      .verification_key =
          libcrux_iot_ml_dsa_types_new_e9_c6(verification_key)});
}

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_c7

*/
typedef struct Option_b2_s {
  Option_87_tags tag;
  Eurydice_arr_c7 f0;
} Option_b2;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_81

*/
typedef struct Option_45_s {
  Option_87_tags tag;
  Eurydice_arr_81 f0;
} Option_45;

/**
A monomorphic instance of core.option.Option
with types Eurydice_arr_33

*/
typedef struct Option_56_s {
  Option_87_tags tag;
  Eurydice_arr_33 f0;
} Option_56;

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      signing_key, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 remaining_serialized0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      remaining_serialized0, LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_SIGNING_SIZE,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_signing = uu____1.fst;
  Eurydice_borrow_slice_u8 remaining_serialized1 = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      remaining_serialized1,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_BYTES_FOR_VERIFICATION_KEY_HASH, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 verification_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 remaining_serialized2 = uu____2.snd;
  Eurydice_borrow_slice_u8_x2 uu____3 = Eurydice_slice_split_at(
      remaining_serialized2,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s1_serialized = uu____3.fst;
  Eurydice_borrow_slice_u8 remaining_serialized = uu____3.snd;
  Eurydice_borrow_slice_u8_x2 uu____4 = Eurydice_slice_split_at(
      remaining_serialized,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE *
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 s2_serialized = uu____4.fst;
  Eurydice_borrow_slice_u8 t0_serialized = uu____4.snd;
  Eurydice_arr_33 s1_as_ntt;
  Eurydice_arr_ef repeat_expression0[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression0[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s1_as_ntt.data, repeat_expression0,
         (size_t)7U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_62 s2_as_ntt;
  Eurydice_arr_ef repeat_expression1[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression1[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(s2_as_ntt.data, repeat_expression1,
         (size_t)8U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_62 t0_as_ntt;
  Eurydice_arr_ef repeat_expression2[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t0_as_ntt.data, repeat_expression2,
         (size_t)8U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s1_serialized, array_to_slice_mut_718(&s1_as_ntt));
  libcrux_iot_ml_dsa_encoding_error_deserialize_to_vector_then_ntt_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ETA,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_ERROR_RING_ELEMENT_SIZE,
      s2_serialized, array_to_slice_mut_710(&s2_as_ntt));
  libcrux_iot_ml_dsa_encoding_t0_deserialize_to_vector_then_ntt_08(
      t0_serialized, array_to_slice_mut_710(&t0_as_ntt));
  Eurydice_arr_b4 matrix;
  Eurydice_arr_ef repeat_expression3[56U];
  for (size_t i = (size_t)0U; i < (size_t)56U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(matrix.data, repeat_expression3,
         (size_t)56U * sizeof(Eurydice_arr_ef));
  Eurydice_borrow_slice_u8 uu____5 =
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(seed_for_a);
  libcrux_iot_ml_dsa_samplex4_portable_matrix_flat_ad_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, uu____5,
      array_to_slice_mut_716(&matrix));
  Eurydice_arr_c7 message_representative;
  uint8_t repeat_expression4[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression4[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(message_representative.data, repeat_expression4,
         (size_t)64U * sizeof(uint8_t));
  libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          verification_key_hash),
      &domain_separation_context,
      libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
      &message_representative);
  Eurydice_arr_c7 mask_seed;
  uint8_t repeat_expression5[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression5[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(mask_seed.data, repeat_expression5, (size_t)64U * sizeof(uint8_t));
  libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
      libcrux_iot_ml_dsa_hash_functions_portable_init_88();
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(&shake,
                                                       seed_for_signing);
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
      &shake, Eurydice_array_to_slice_shared_01(&randomness));
  libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
      &shake, Eurydice_array_to_slice_shared_17(&message_representative));
  libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
      &shake, Eurydice_array_to_slice_mut_17(&mask_seed));
  uint16_t domain_separator_for_mask = 0U;
  size_t attempt = (size_t)0U;
  Option_b2 commitment_hash0 = {.tag = None};
  Option_56 signer_response0 = {.tag = None};
  Option_45 hint0 = {.tag = None};
  while (attempt < LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN) {
    attempt++;
    Eurydice_arr_33 mask;
    Eurydice_arr_ef repeat_expression6[7U];
    for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
      repeat_expression6[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(mask.data, repeat_expression6, (size_t)7U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_62 w0;
    Eurydice_arr_ef repeat_expression7[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression7[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(w0.data, repeat_expression7, (size_t)8U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_62 commitment;
    Eurydice_arr_ef repeat_expression8[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression8[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(commitment.data, repeat_expression8,
           (size_t)8U * sizeof(Eurydice_arr_ef));
    libcrux_iot_ml_dsa_sample_sample_mask_vector_1a(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT, &mask_seed,
        &domain_separator_for_mask, array_to_slice_mut_718(&mask));
    Eurydice_arr_62 a_x_mask;
    Eurydice_arr_ef repeat_expression9[8U];
    for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
      repeat_expression9[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    }
    memcpy(a_x_mask.data, repeat_expression9,
           (size_t)8U * sizeof(Eurydice_arr_ef));
    Eurydice_arr_33 mask_ntt = core_array__core__clone__Clone_for__T__N___clone(
        (size_t)7U, &mask, Eurydice_arr_ef, Eurydice_arr_33);
    for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
      size_t i0 = i;
      libcrux_iot_ml_dsa_ntt_ntt_08(&mask_ntt.data[i0]);
    }
    libcrux_iot_ml_dsa_matrix_compute_matrix_x_mask_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        array_to_slice_shared_716(&matrix),
        array_to_slice_shared_717(&mask_ntt),
        array_to_slice_mut_710(&a_x_mask));
    libcrux_iot_ml_dsa_arithmetic_decompose_vector_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
        array_to_slice_shared_711(&a_x_mask), array_to_slice_mut_710(&w0),
        array_to_slice_mut_710(&commitment));
    Eurydice_arr_c7 commitment_hash_candidate;
    uint8_t repeat_expression10[64U];
    for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
      repeat_expression10[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_hash_candidate.data, repeat_expression10,
           (size_t)64U * sizeof(uint8_t));
    Eurydice_arr_1b commitment_serialized;
    uint8_t repeat_expression[1024U];
    for (size_t i = (size_t)0U; i < (size_t)1024U; i++) {
      repeat_expression[i] =
          libcrux_secrets_int_public_integers_classify_27_90(0U);
    }
    memcpy(commitment_serialized.data, repeat_expression,
           (size_t)1024U * sizeof(uint8_t));
    libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
        LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
        array_to_slice_shared_711(&commitment),
        Eurydice_array_to_slice_mut_68(&commitment_serialized));
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake0 =
        libcrux_iot_ml_dsa_hash_functions_portable_init_88();
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
        &shake0, Eurydice_array_to_slice_shared_17(&message_representative));
    libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
        &shake0, Eurydice_array_to_slice_shared_68(&commitment_serialized));
    libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
        &shake0, Eurydice_array_to_slice_mut_17(&commitment_hash_candidate));
    Eurydice_arr_ef verifier_challenge =
        libcrux_iot_ml_dsa_polynomial_zero_c2_08();
    libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
        Eurydice_array_to_slice_shared_17(&commitment_hash_candidate),
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
        &verifier_challenge);
    libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
    Eurydice_arr_33 challenge_times_s1 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)7U, &s1_as_ntt, Eurydice_arr_ef, Eurydice_arr_33);
    Eurydice_arr_62 challenge_times_s2 =
        core_array__core__clone__Clone_for__T__N___clone(
            (size_t)8U, &s2_as_ntt, Eurydice_arr_ef, Eurydice_arr_62);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_718(&challenge_times_s1), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
        array_to_slice_mut_710(&challenge_times_s2), &verifier_challenge);
    libcrux_iot_ml_dsa_matrix_add_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
        array_to_slice_mut_718(&mask),
        array_to_slice_shared_717(&challenge_times_s1));
    libcrux_iot_ml_dsa_matrix_subtract_vectors_08(
        LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
        array_to_slice_mut_710(&w0),
        array_to_slice_shared_711(&challenge_times_s2));
    if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_717(&mask),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
              array_to_slice_shared_711(&w0),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2 -
                  LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
        Eurydice_arr_62 challenge_times_t0 =
            core_array__core__clone__Clone_for__T__N___clone(
                (size_t)8U, &t0_as_ntt, Eurydice_arr_ef, Eurydice_arr_62);
        libcrux_iot_ml_dsa_matrix_vector_times_ring_element_08(
            array_to_slice_mut_710(&challenge_times_t0), &verifier_challenge);
        if (!libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
                array_to_slice_shared_711(&challenge_times_t0),
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2)) {
          libcrux_iot_ml_dsa_matrix_add_vectors_08(
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
              array_to_slice_mut_710(&w0),
              array_to_slice_shared_711(&challenge_times_t0));
          Eurydice_arr_81 hint_candidate = {.data = {{.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}},
                                                     {.data = {0U}}}};
          size_t ones_in_hint = libcrux_iot_ml_dsa_arithmetic_make_hint_08(
              array_to_slice_shared_711(&w0),
              array_to_slice_shared_711(&commitment),
              LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
              Eurydice_array_to_slice_mut_861(&hint_candidate));
          if (!(ones_in_hint >
                LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT)) {
            attempt = LIBCRUX_IOT_ML_DSA_CONSTANTS_REJECTION_SAMPLE_BOUND_SIGN;
            commitment_hash0 = (KRML_CLITERAL(Option_b2){
                .tag = Some, .f0 = commitment_hash_candidate});
            signer_response0 =
                (KRML_CLITERAL(Option_56){.tag = Some, .f0 = mask});
            hint0 =
                (KRML_CLITERAL(Option_45){.tag = Some, .f0 = hint_candidate});
          }
        }
      }
    }
  }
  Result_87 uu____6;
  if (commitment_hash0.tag == None) {
    uu____6 = (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
  } else {
    Eurydice_arr_c7 commitment_hash = commitment_hash0.f0;
    Eurydice_arr_c7 commitment_hash1 = commitment_hash;
    if (signer_response0.tag == None) {
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    } else {
      Eurydice_arr_33 signer_response = signer_response0.f0;
      Eurydice_arr_33 signer_response1 = signer_response;
      if (!(hint0.tag == None)) {
        Eurydice_arr_81 hint = hint0.f0;
        Eurydice_arr_81 hint1 = hint;
        const Eurydice_arr_c7 *uu____7 =
            libcrux_secrets_int_public_integers_declassify_ref_ad_56(
                &commitment_hash1);
        libcrux_iot_ml_dsa_encoding_signature_serialize_08(
            Eurydice_array_to_slice_shared_17(uu____7),
            array_to_slice_shared_717(&signer_response1),
            Eurydice_array_to_slice_shared_861(&hint1),
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
            LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
            LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
            Eurydice_array_to_slice_mut_11(signature));
        return (KRML_CLITERAL(Result_87){.tag = Ok});
      }
      uu____6 = (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError});
    }
  }
  return uu____6;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign_mut
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_87){
        .tag = Err,
        .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
      signing_key,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      randomness, signature);
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.sign
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256X4 with const generics

*/
KRML_MUSTINLINE Result_20 libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_930 signature = libcrux_iot_ml_dsa_types_zero_ad_f1();
  Result_87 uu____0 = libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
      signing_key, message, context, randomness, &signature);
  Result_20 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_20){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_20){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign.
*/
Result_20
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_c4(
      Eurydice_array_to_slice_shared_f7(signing_key), message, context,
      randomness);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign(
      libcrux_iot_ml_dsa_types_as_ref_f8_72(signing_key), message, context,
      randomness);
}

/**
 Sign.
*/
Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_mut_c4(
      Eurydice_array_to_slice_shared_f7(signing_key), message, context,
      randomness, signature);
}

/**
 Generate an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_87 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_mut(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_mut(
      libcrux_iot_ml_dsa_types_as_ref_f8_72(signing_key), message, context,
      randomness, signature);
}

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
KRML_MUSTINLINE Result_87
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness,
    Eurydice_arr_930 *signature) {
  if (!(context.meta > LIBCRUX_IOT_ML_DSA_CONSTANTS_CONTEXT_MAX_LEN)) {
    libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
        libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
        pre_hash_buffer);
    Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
        context, (KRML_CLITERAL(Option_57){
                     .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
    if (!(uu____0.tag == Ok)) {
      return (KRML_CLITERAL(Result_87){
          .tag = Err,
          .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
    }
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc =
        uu____0.val.case_Ok;
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
        domain_separation_context = dsc;
    return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_internal_c4(
        signing_key,
        (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                                 .meta = pre_hash_buffer.meta}),
        (KRML_CLITERAL(Option_e3){.tag = Some,
                                  .f0 = domain_separation_context}),
        randomness, signature);
  }
  return (KRML_CLITERAL(Result_87){
      .tag = Err,
      .f0 = libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError});
}

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
KRML_MUSTINLINE Result_20
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
    Eurydice_borrow_slice_u8 signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  Eurydice_arr_930 signature = libcrux_iot_ml_dsa_types_zero_ad_f1();
  Result_87 uu____0 =
      libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_mut_36(
          signing_key, message, context, pre_hash_buffer, randomness,
          &signature);
  Result_20 uu____1;
  if (uu____0.tag == Ok) {
    uu____1 =
        (KRML_CLITERAL(Result_20){.tag = Ok, .val = {.case_Ok = signature}});
  } else {
    libcrux_iot_ml_dsa_types_SigningError e = uu____0.f0;
    uu____1 = (KRML_CLITERAL(Result_20){.tag = Err, .val = {.case_Err = e}});
  }
  return uu____1;
}

/**
 Sign (pre-hashed).
*/
Result_20
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer, Eurydice_arr_ec randomness) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_sign_pre_hashed_36(
      Eurydice_array_to_slice_shared_f7(signing_key), message, context,
      pre_hash_buffer, randomness);
}

/**
 Generate a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_20 libcrux_iot_ml_dsa_ml_dsa_87_portable_sign_pre_hashed_shake128(
    const Eurydice_arr_e2 *signing_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, Eurydice_arr_ec randomness) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_e2 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_f8_72(signing_key);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_sign_pre_hashed_shake128(
      uu____0, message, context,
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer), randomness);
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Option_e3 domain_separation_context,
    const Eurydice_arr_930 *signature_serialized) {
  Eurydice_arr_d1 rand_stack;
  uint8_t repeat_expression0[840U];
  for (size_t i = (size_t)0U; i < (size_t)840U; i++) {
    repeat_expression0[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_stack.data, repeat_expression0, (size_t)840U * sizeof(uint8_t));
  Eurydice_arr_c5 rand_block;
  uint8_t repeat_expression1[168U];
  for (size_t i = (size_t)0U; i < (size_t)168U; i++) {
    repeat_expression1[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(rand_block.data, repeat_expression1, (size_t)168U * sizeof(uint8_t));
  Eurydice_arr_d0 tmp_stack = {.data = {0U}};
  Eurydice_arr_ef poly_slot = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      Eurydice_array_to_slice_shared_fc(verification_key),
      LIBCRUX_IOT_ML_DSA_CONSTANTS_SEED_FOR_A_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 seed_for_a = uu____0.fst;
  Eurydice_borrow_slice_u8 t1_serialized = uu____0.snd;
  Eurydice_arr_62 t1;
  Eurydice_arr_ef repeat_expression2[8U];
  for (size_t i = (size_t)0U; i < (size_t)8U; i++) {
    repeat_expression2[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(t1.data, repeat_expression2, (size_t)8U * sizeof(Eurydice_arr_ef));
  libcrux_iot_ml_dsa_encoding_verification_key_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_VERIFICATION_KEY_SIZE,
      t1_serialized, array_to_slice_mut_710(&t1));
  Eurydice_arr_c7 deserialized_commitment_hash = {.data = {0U}};
  Eurydice_arr_33 deserialized_signer_response;
  Eurydice_arr_ef repeat_expression3[7U];
  for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
    repeat_expression3[i] = libcrux_iot_ml_dsa_polynomial_zero_c2_08();
  }
  memcpy(deserialized_signer_response.data, repeat_expression3,
         (size_t)7U * sizeof(Eurydice_arr_ef));
  Eurydice_arr_81 deserialized_hint = {.data = {{.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}},
                                                {.data = {0U}}}};
  Result_5c uu____1 = libcrux_iot_ml_dsa_encoding_signature_deserialize_08(
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COMMITMENT_HASH_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_GAMMA1_RING_ELEMENT_SIZE,
      LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_MAX_ONES_IN_HINT,
      LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_SIGNATURE_SIZE,
      Eurydice_array_to_slice_shared_11(signature_serialized),
      Eurydice_array_to_slice_mut_17(&deserialized_commitment_hash),
      array_to_slice_mut_718(&deserialized_signer_response),
      Eurydice_array_to_slice_mut_861(&deserialized_hint));
  Result_5c uu____2;
  if (uu____1.tag == Ok) {
    if (libcrux_iot_ml_dsa_arithmetic_vector_infinity_norm_exceeds_08(
            array_to_slice_shared_717(&deserialized_signer_response),
            (int32_t)((uint32_t)1 << (uint32_t)
                          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA1_EXPONENT) -
                LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_BETA)) {
      uu____2 = (KRML_CLITERAL(Result_5c){
          .tag = Err,
          .f0 =
              libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError});
    } else {
      Eurydice_arr_c7 verification_key_hash;
      uint8_t repeat_expression4[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression4[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(verification_key_hash.data, repeat_expression4,
             (size_t)64U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_hash_functions_portable_shake256_a1_c9(
          Eurydice_array_to_slice_shared_fc(
              libcrux_secrets_int_public_integers_classify_ref_c5_81(
                  verification_key)),
          &verification_key_hash);
      Eurydice_arr_c7 message_representative;
      uint8_t repeat_expression5[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression5[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(message_representative.data, repeat_expression5,
             (size_t)64U * sizeof(uint8_t));
      Eurydice_borrow_slice_u8 uu____3 = Eurydice_array_to_slice_shared_17(
          libcrux_secrets_int_public_integers_declassify_ref_ad_56(
              &verification_key_hash));
      libcrux_iot_ml_dsa_ml_dsa_generic_derive_message_representative_fd(
          uu____3, &domain_separation_context,
          libcrux_secrets_int_classify_public_declassify_ref_5c_90(message),
          &message_representative);
      Eurydice_arr_ef verifier_challenge =
          libcrux_iot_ml_dsa_polynomial_zero_c2_08();
      libcrux_iot_ml_dsa_sample_sample_challenge_ring_element_1b(
          Eurydice_array_to_slice_shared_17(
              libcrux_secrets_int_public_integers_classify_ref_c5_56(
                  &deserialized_commitment_hash)),
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ONES_IN_VERIFIER_CHALLENGE,
          &verifier_challenge);
      libcrux_iot_ml_dsa_ntt_ntt_08(&verifier_challenge);
      for (size_t i = (size_t)0U; i < (size_t)7U; i++) {
        size_t i0 = i;
        libcrux_iot_ml_dsa_ntt_ntt_08(&deserialized_signer_response.data[i0]);
      }
      libcrux_iot_ml_dsa_matrix_compute_w_approx_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_ROWS_IN_A,
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_COLUMNS_IN_A, seed_for_a,
          &rand_stack, &rand_block, &tmp_stack, &poly_slot,
          array_to_slice_shared_717(&deserialized_signer_response),
          &verifier_challenge, array_to_slice_mut_710(&t1));
      Eurydice_arr_c7 recomputed_commitment_hash;
      uint8_t repeat_expression6[64U];
      for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
        repeat_expression6[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(recomputed_commitment_hash.data, repeat_expression6,
             (size_t)64U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_arithmetic_use_hint_08(
          LIBCRUX_IOT_ML_DSA_CONSTANTS_ML_DSA_87_GAMMA2,
          Eurydice_array_to_slice_shared_861(&deserialized_hint),
          array_to_slice_mut_710(&t1));
      Eurydice_arr_1b commitment_serialized;
      uint8_t repeat_expression[1024U];
      for (size_t i = (size_t)0U; i < (size_t)1024U; i++) {
        repeat_expression[i] =
            libcrux_secrets_int_public_integers_classify_27_90(0U);
      }
      memcpy(commitment_serialized.data, repeat_expression,
             (size_t)1024U * sizeof(uint8_t));
      libcrux_iot_ml_dsa_encoding_commitment_serialize_vector_08(
          LIBCRUX_IOT_ML_DSA_ML_DSA_GENERIC_ML_DSA_87_COMMITMENT_RING_ELEMENT_SIZE,
          array_to_slice_shared_711(&t1),
          Eurydice_array_to_slice_mut_68(&commitment_serialized));
      libcrux_iot_sha3_keccak_KeccakSpongeState_bd shake =
          libcrux_iot_ml_dsa_hash_functions_portable_init_88();
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_88(
          &shake, Eurydice_array_to_slice_shared_17(&message_representative));
      libcrux_iot_ml_dsa_hash_functions_portable_absorb_final_88(
          &shake, Eurydice_array_to_slice_shared_68(&commitment_serialized));
      libcrux_iot_ml_dsa_hash_functions_portable_squeeze_88(
          &shake, Eurydice_array_to_slice_mut_17(&recomputed_commitment_hash));
      if (Eurydice_array_eq(
              (size_t)64U, &deserialized_commitment_hash,
              libcrux_secrets_int_public_integers_declassify_ref_ad_56(
                  &recomputed_commitment_hash),
              uint8_t)) {
        uu____2 = (KRML_CLITERAL(Result_5c){.tag = Ok});
      } else {
        uu____2 = (KRML_CLITERAL(Result_5c){
            .tag = Err,
            .f0 =
                libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError});
      }
    }
  } else {
    libcrux_iot_ml_dsa_types_VerificationError e = uu____1.f0;
    uu____2 = (KRML_CLITERAL(Result_5c){.tag = Err, .f0 = e});
  }
  return uu____2;
}

/**
A monomorphic instance of libcrux_iot_ml_dsa.ml_dsa_generic.ml_dsa_87.verify
with types libcrux_iot_ml_dsa_simd_portable_vector_type_Coefficients,
libcrux_iot_ml_dsa_samplex4_portable_PortableSampler,
libcrux_iot_ml_dsa_hash_functions_portable_Shake128X4,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256,
libcrux_iot_ml_dsa_hash_functions_portable_Shake256Xof with const generics

*/
KRML_MUSTINLINE Result_5c libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
    const Eurydice_arr_43 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    const Eurydice_arr_930 *signature_serialized) {
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){.tag = None}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized,
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify.
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_c4(
      verification_key, message, context, signature);
}

/**
 Verify an ML-DSA-87 Signature

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify(
      libcrux_iot_ml_dsa_types_as_ref_e9_c6(verification_key), message, context,
      libcrux_iot_ml_dsa_types_as_ref_ad_f1(signature));
}

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
KRML_MUSTINLINE Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
    const Eurydice_arr_43 *verification_key_serialized,
    Eurydice_borrow_slice_u8 message, Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_930 *signature_serialized) {
  libcrux_iot_ml_dsa_pre_hash_hash_0b_1a(
      libcrux_secrets_int_classify_public_classify_ref_6d_90(message),
      pre_hash_buffer);
  Result_80 uu____0 = libcrux_iot_ml_dsa_pre_hash_new_c9(
      context, (KRML_CLITERAL(Option_57){
                   .tag = Some, .f0 = libcrux_iot_ml_dsa_pre_hash_oid_0b()}));
  if (!(uu____0.tag == Ok)) {
    return (KRML_CLITERAL(Result_5c){
        .tag = Err,
        .f0 =
            libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError});
  }
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext dsc = uu____0.val.case_Ok;
  libcrux_iot_ml_dsa_pre_hash_DomainSeparationContext
      domain_separation_context = dsc;
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_internal_c4(
      verification_key_serialized,
      (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = pre_hash_buffer.ptr,
                                               .meta = pre_hash_buffer.meta}),
      (KRML_CLITERAL(Option_e3){.tag = Some, .f0 = domain_separation_context}),
      signature_serialized);
}

/**
 Verify (pre-hashed with SHAKE-128).
*/
Result_5c
libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context,
    Eurydice_mut_borrow_slice_u8 pre_hash_buffer,
    const Eurydice_arr_930 *signature) {
  return libcrux_iot_ml_dsa_ml_dsa_generic_ml_dsa_87_verify_pre_hashed_36(
      verification_key, message, context, pre_hash_buffer, signature);
}

/**
 Verify a HashML-DSA-87 Signature, with a SHAKE128 pre-hashing

 The parameter `context` is used for domain separation
 and is a byte string of length at most 255 bytes. It
 may also be empty.
*/
Result_5c libcrux_iot_ml_dsa_ml_dsa_87_portable_verify_pre_hashed_shake128(
    const Eurydice_arr_43 *verification_key, Eurydice_borrow_slice_u8 message,
    Eurydice_borrow_slice_u8 context, const Eurydice_arr_930 *signature) {
  Eurydice_arr_ec pre_hash_buffer;
  uint8_t repeat_expression[32U];
  for (size_t i = (size_t)0U; i < (size_t)32U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(pre_hash_buffer.data, repeat_expression,
         (size_t)32U * sizeof(uint8_t));
  const Eurydice_arr_43 *uu____0 =
      libcrux_iot_ml_dsa_types_as_ref_e9_c6(verification_key);
  Eurydice_borrow_slice_u8 uu____1 = message;
  Eurydice_borrow_slice_u8 uu____2 = context;
  Eurydice_mut_borrow_slice_u8 uu____3 =
      Eurydice_array_to_slice_mut_01(&pre_hash_buffer);
  return libcrux_iot_ml_dsa_ml_dsa_generic_instantiations_portable_ml_dsa_87_verify_pre_hashed_shake128(
      uu____0, uu____1, uu____2, uu____3,
      libcrux_iot_ml_dsa_types_as_ref_ad_f1(signature));
}

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::SigningError}
*/
libcrux_iot_ml_dsa_types_SigningError libcrux_iot_ml_dsa_pre_hash_from_49(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError;
}

/**
This function found in impl
{core::convert::From<libcrux_iot_ml_dsa::pre_hash::DomainSeparationError> for
libcrux_iot_ml_dsa::types::VerificationError}
*/
libcrux_iot_ml_dsa_types_VerificationError libcrux_iot_ml_dsa_pre_hash_from_97(
    libcrux_iot_ml_dsa_pre_hash_DomainSeparationError e) {
  return libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError;
}
