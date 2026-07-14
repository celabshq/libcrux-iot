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

#include "internal/libcrux_iot_sha3.h"

#include "internal/libcrux_iot_core.h"
#include "libcrux_iot_core.h"

/**
 Returns the size of a digest in bytes for a given [`Algorithm`].
*/
size_t digest_size(Algorithm mode) {
  switch (mode) {
    case libcrux_iot_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_iot_sha3_Algorithm_Sha256: {
      return SHA3_256_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha384: {
      return SHA3_384_DIGEST_SIZE;
    }
    case libcrux_iot_sha3_Algorithm_Sha512: {
      return SHA3_512_DIGEST_SIZE;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return SHA3_224_DIGEST_SIZE;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_from_ints_8d(Eurydice_arr_a0 value) {
  return value;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0 libcrux_iot_sha3_lane_zero_8d(void) {
  return libcrux_iot_sha3_lane_from_ints_8d(
      libcrux_secrets_int_public_integers_classify_27_aa(
          (KRML_CLITERAL(Eurydice_arr_a0){.data = {0U}})));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE libcrux_iot_sha3_state_KeccakState
libcrux_iot_sha3_state_new_18(void) {
  Eurydice_arr_c0 uu____0;
  Eurydice_arr_a0 repeat_expression0[25U];
  for (size_t i = (size_t)0U; i < (size_t)25U; i++) {
    repeat_expression0[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____0.data, repeat_expression0,
         (size_t)25U * sizeof(Eurydice_arr_a0));
  Eurydice_arr_44 uu____1;
  Eurydice_arr_a0 repeat_expression1[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression1[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(uu____1.data, repeat_expression1,
         (size_t)5U * sizeof(Eurydice_arr_a0));
  libcrux_iot_sha3_state_KeccakState lit;
  lit.st = uu____0;
  lit.c = uu____1;
  Eurydice_arr_a0 repeat_expression[5U];
  for (size_t i = (size_t)0U; i < (size_t)5U; i++) {
    repeat_expression[i] = libcrux_iot_sha3_lane_zero_8d();
  }
  memcpy(lit.d.data, repeat_expression, (size_t)5U * sizeof(Eurydice_arr_a0));
  lit.i = (size_t)0U;
  return lit;
}

/**
This function found in impl {core::convert::From<[u32; 2usize]> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_from_29(Eurydice_arr_a0 value) {
  return value;
}

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE const uint32_t *libcrux_iot_sha3_lane_index_cc(
    const Eurydice_arr_a0 *self, size_t index) {
  return &self->data[index];
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_interleave_8d(Eurydice_arr_a0 self) {
  uint64_t lane_u64 =
      libcrux_secrets_int_as_u64_b8(
          libcrux_iot_sha3_lane_index_cc(&self, (size_t)0U)[0U]) |
      libcrux_secrets_int_as_u64_b8(
          libcrux_iot_sha3_lane_index_cc(&self, (size_t)1U)[0U])
          << 32U;
  uint64_t even_bits = lane_u64 & 6148914691236517205ULL;
  even_bits = (even_bits ^ even_bits >> 1U) & 3689348814741910323ULL;
  even_bits = (even_bits ^ even_bits >> 2U) & 1085102592571150095ULL;
  even_bits = (even_bits ^ even_bits >> 4U) & 71777214294589695ULL;
  even_bits = (even_bits ^ even_bits >> 8U) & 281470681808895ULL;
  even_bits = (even_bits ^ even_bits >> 16U) & 4294967295ULL;
  uint64_t odd_bits = lane_u64 >> 1U & 6148914691236517205ULL;
  odd_bits = (odd_bits ^ odd_bits >> 1U) & 3689348814741910323ULL;
  odd_bits = (odd_bits ^ odd_bits >> 2U) & 1085102592571150095ULL;
  odd_bits = (odd_bits ^ odd_bits >> 4U) & 71777214294589695ULL;
  odd_bits = (odd_bits ^ odd_bits >> 8U) & 281470681808895ULL;
  odd_bits = (odd_bits ^ odd_bits >> 16U) & 4294967295ULL;
  return libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
      .data = {libcrux_secrets_int_as_u32_a3(even_bits),
               libcrux_secrets_int_as_u32_a3(odd_bits)}}));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE Eurydice_arr_a0 libcrux_iot_sha3_state_get_lane_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j) {
  return self->st.data[(size_t)5U * j + i];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    Eurydice_arr_a0 lane) {
  self->st.data[(size_t)5U * j + i] = lane;
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE uint32_t libcrux_iot_sha3_state_get_with_zeta_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    size_t zeta) {
  return libcrux_iot_sha3_lane_index_cc(&self->st.data[(size_t)5U * j + i],
                                        zeta)[0U];
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_lane_value_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    uint32_t value) {
  self->c.data[i].data[j] = value;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta_d(s);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v) {
  self->st.data[(size_t)5U * j + i].data[zeta] = v;
}

typedef struct uint32_t_x2_s {
  uint32_t fst;
  uint32_t snd;
} uint32_t_x2;

typedef struct uint32_t_x3_s {
  uint32_t fst;
  uint32_t snd;
  uint32_t thd;
} uint32_t_x3;

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 2U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 23U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 13U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 0U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 12U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 8U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 14U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 7U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 13U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 21U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 20U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 20U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta1(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta_d(s);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 2U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 23U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 13U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 0U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 12U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 8U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 14U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 7U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 13U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 21U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 20U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 20U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta1(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta_d(s);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 2U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 23U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 13U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 0U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 12U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 8U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 14U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 7U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 13U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 21U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 20U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 20U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta1(s);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)0U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)0U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)0U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)0U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)0U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)0U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)1U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)1U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)1U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)1U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)1U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)1U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)2U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)2U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)2U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)2U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)2U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)2U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)1U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)3U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)3U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)3U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)3U, (size_t)0U);
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)3U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)3U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)1U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)0U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)1U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)0U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)0U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)0U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t ax_3 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)3U, (size_t)4U, (size_t)0U);
  uint32_t ax_1 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)1U, (size_t)4U, (size_t)1U);
  uint32_t ax_4 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)4U, (size_t)4U, (size_t)0U);
  uint32_t ax_2 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)2U, (size_t)4U, (size_t)1U);
  uint32_t ax_0 = libcrux_iot_sha3_state_get_with_zeta_18(
      s, (size_t)0U, (size_t)4U, (size_t)1U);
  libcrux_iot_sha3_state_set_lane_value_18(
      s, (size_t)4U, (size_t)1U, (((ax_0 ^ ax_1) ^ ax_2) ^ ax_3) ^ ax_4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_d(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t c_x4_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)0U)[0U];
  uint32_t c_x1_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)1U)[0U];
  uint32_t c_x3_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)0U)[0U];
  uint32_t c_x0_zeta1 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)1U)[0U];
  uint32_t c_x2_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)0U)[0U];
  uint32_t c_x4_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[4U], (size_t)1U)[0U];
  uint32_t d_x0_zeta0 = c_x4_zeta0 ^ core_num__u32__rotate_left(c_x1_zeta1, 1U);
  s->d.data->data[0U] = d_x0_zeta0;
  uint32_t d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
  s->d.data[2U].data[1U] = d_x2_zeta1;
  uint32_t d_x4_zeta0 = c_x3_zeta0 ^ core_num__u32__rotate_left(c_x0_zeta1, 1U);
  s->d.data[4U].data[0U] = d_x4_zeta0;
  uint32_t d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
  s->d.data[1U].data[1U] = d_x1_zeta1;
  uint32_t d_x3_zeta0 = c_x2_zeta0 ^ core_num__u32__rotate_left(c_x4_zeta1, 1U);
  s->d.data[3U].data[0U] = d_x3_zeta0;
  uint32_t c_x1_zeta0 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[1U], (size_t)0U)[0U];
  uint32_t c_x3_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[3U], (size_t)1U)[0U];
  uint32_t c_x2_zeta1 =
      libcrux_iot_sha3_lane_index_cc(&s->c.data[2U], (size_t)1U)[0U];
  uint32_t c_x0_zeta0 =
      libcrux_iot_sha3_lane_index_cc(s->c.data, (size_t)0U)[0U];
  uint32_t d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
  s->d.data->data[1U] = d_x0_zeta1;
  uint32_t d_x2_zeta0 = c_x1_zeta0 ^ core_num__u32__rotate_left(c_x3_zeta1, 1U);
  s->d.data[2U].data[0U] = d_x2_zeta0;
  uint32_t d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
  s->d.data[4U].data[1U] = d_x4_zeta1;
  uint32_t d_x1_zeta0 = c_x0_zeta0 ^ core_num__u32__rotate_left(c_x2_zeta1, 1U);
  s->d.data[1U].data[0U] = d_x1_zeta0;
  uint32_t d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
  s->d.data[3U].data[1U] = d_x3_zeta1;
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_theta(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta_d(s);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 2U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 23U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 1U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx2 = uu____0.fst;
  uint32_t bx3 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 30U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 14U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 10U)};
  uint32_t bx4 = uu____1.fst;
  uint32_t bx0 = uu____1.snd;
  uint32_t bx1 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 13U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 9U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 0U)};
  uint32_t bx4 = uu____0.fst;
  uint32_t bx0 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 3U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 12U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 4U)};
  uint32_t bx1 = uu____1.fst;
  uint32_t bx2 = uu____1.snd;
  uint32_t bx3 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 8U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 14U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 18U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 5U)};
  uint32_t bx1 = uu____0.fst;
  uint32_t bx2 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 7U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 13U)};
  uint32_t bx3 = uu____1.fst;
  uint32_t bx4 = uu____1.snd;
  uint32_t bx0 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 21U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 28U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 20U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
}

KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 20U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 1U)};
  uint32_t bx3 = uu____0.fst;
  uint32_t bx4 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 31U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 27U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 19U)};
  uint32_t bx0 = uu____1.fst;
  uint32_t bx1 = uu____1.snd;
  uint32_t bx2 = uu____1.thd;
  uint32_t ax0 = bx0 ^ (~bx1 & bx2);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax4);
}

KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta1(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta1(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 22U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 11U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[s->i];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)0U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 21U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 10U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[s->i];
  s->i++;
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)4U, (size_t)1U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta1(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 22U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 11U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[s->i];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)1U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 21U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 10U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[s->i];
  s->i++;
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)4U, (size_t)0U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta1(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 22U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 11U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[s->i];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)1U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)2U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)4U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)1U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)3U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 21U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 10U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[s->i];
  s->i++;
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)2U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)4U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)1U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)3U, (size_t)4U, (size_t)0U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta1(s);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)0U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)0U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)0U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)0U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)0U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)1U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)0U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)1U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)0U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)0U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 22U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 11U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0.data[s->i];
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)0U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)0U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)0U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)0U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)0U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void
libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  uint32_t a0 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)0U, (size_t)1U);
  uint32_t d0 = libcrux_iot_sha3_lane_index_cc(s->d.data, (size_t)1U)[0U];
  uint32_t a1 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)1U, (size_t)1U);
  uint32_t d1 = libcrux_iot_sha3_lane_index_cc(&s->d.data[1U], (size_t)1U)[0U];
  uint32_t_x2 uu____0 = {.fst = core_num__u32__rotate_left(a0 ^ d0, 0U),
                         .snd = core_num__u32__rotate_left(a1 ^ d1, 22U)};
  uint32_t bx0 = uu____0.fst;
  uint32_t bx1 = uu____0.snd;
  uint32_t a2 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)2U, (size_t)1U);
  uint32_t d2 = libcrux_iot_sha3_lane_index_cc(&s->d.data[2U], (size_t)0U)[0U];
  uint32_t a3 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)3U, (size_t)1U);
  uint32_t d3 = libcrux_iot_sha3_lane_index_cc(&s->d.data[3U], (size_t)0U)[0U];
  uint32_t a4 = libcrux_iot_sha3_state_get_with_zeta_18(s, (size_t)0U,
                                                        (size_t)4U, (size_t)1U);
  uint32_t d4 = libcrux_iot_sha3_lane_index_cc(&s->d.data[4U], (size_t)1U)[0U];
  uint32_t_x3 uu____1 = {.fst = core_num__u32__rotate_left(a2 ^ d2, 21U),
                         .snd = core_num__u32__rotate_left(a3 ^ d3, 10U),
                         .thd = core_num__u32__rotate_left(a4 ^ d4, 7U)};
  uint32_t bx2 = uu____1.fst;
  uint32_t bx3 = uu____1.snd;
  uint32_t bx4 = uu____1.thd;
  uint32_t ax0 = (bx0 ^ (~bx1 & bx2)) ^
                 LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1.data[s->i];
  s->i++;
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)0U, (size_t)1U,
                                          ax0);
  uint32_t ax1 = bx1 ^ (~bx2 & bx3);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)1U, (size_t)1U,
                                          ax1);
  uint32_t ax2 = bx2 ^ (~bx3 & bx4);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)2U, (size_t)1U,
                                          ax2);
  uint32_t ax3 = bx3 ^ (~bx4 & bx0);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)3U, (size_t)1U,
                                          ax3);
  uint32_t ax4 = bx4 ^ (~bx0 & bx1);
  libcrux_iot_sha3_state_set_with_zeta_18(s, (size_t)0U, (size_t)4U, (size_t)1U,
                                          ax4);
}

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta0(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta1(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 0
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccakf1600_4rounds_56(
    libcrux_iot_sha3_state_KeccakState *s) {
  libcrux_iot_sha3_keccak_keccakf1600_round0_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_theta(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_56(s);
  libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(s);
}

KRML_NOINLINE void libcrux_iot_sha3_keccak_keccakf1600(
    libcrux_iot_sha3_state_KeccakState *s) {
  for (int32_t i = 0; i < 6; i++) {
    libcrux_iot_sha3_keccak_keccakf1600_4rounds_56(s);
  }
  s->i = (size_t)0U;
}

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
KRML_MUSTINLINE Eurydice_arr_a0
libcrux_iot_sha3_lane_deinterleave_8d(Eurydice_arr_a0 self) {
  uint32_t even_bits = self.data[0U];
  uint32_t odd_bits = self.data[1U];
  uint32_t even_spaced_lo = even_bits & 65535U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 16U) & 65535U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 8U) & 16711935U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 4U) & 252645135U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 2U) & 858993459U;
  even_spaced_lo = (even_spaced_lo ^ even_spaced_lo << 1U) & 1431655765U;
  uint32_t even_spaced_hi = even_bits >> 16U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 16U) & 65535U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 8U) & 16711935U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 4U) & 252645135U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 2U) & 858993459U;
  even_spaced_hi = (even_spaced_hi ^ even_spaced_hi << 1U) & 1431655765U;
  uint32_t odd_spaced_lo = odd_bits & 65535U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 16U) & 65535U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 8U) & 16711935U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 4U) & 252645135U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 2U) & 858993459U;
  odd_spaced_lo = (odd_spaced_lo ^ odd_spaced_lo << 1U) & 1431655765U;
  uint32_t odd_spaced_hi = odd_bits >> 16U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 16U) & 65535U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 8U) & 16711935U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 4U) & 252645135U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 2U) & 858993459U;
  odd_spaced_hi = (odd_spaced_hi ^ odd_spaced_hi << 1U) & 1431655765U;
  return (KRML_CLITERAL(Eurydice_arr_a0){
      .data = {even_spaced_lo | odd_spaced_lo << 1U,
               even_spaced_hi | odd_spaced_hi << 1U}});
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 lane =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
            .data = {
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U],
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_9e(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_9e(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_9e(
      keccak_state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_9e(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)144U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_9e(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)144U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_9e(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_9e(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_9e(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_9e(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_9e(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_9e(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_9e(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_9e(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_3a(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)144U;
  size_t rem = data.meta % (size_t)144U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)144U;
  size_t last = outlen - outlen % (size_t)144U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_9e(&s, data, start);
    start += (size_t)144U;
  }
  libcrux_iot_sha3_keccak_absorb_final_3a(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_9e(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_9e(&s, out);
    size_t offset = (size_t)144U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_9e(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)144U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_9e(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void keccakx1_3a(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_3a(data, out);
}

/**
 Writes SHA3-224 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_224_DIGEST_SIZE`] bytes long
*/
void sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_3a(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 lane =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
            .data = {
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U],
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_b2(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_b2(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_b2(
      keccak_state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_b2(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_22(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_b2(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)136U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_b2(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_b2(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_b2(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_b2(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_b2(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_b2(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_b2(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_b2(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_22(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)136U;
  size_t rem = data.meta % (size_t)136U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_b2(&s, data, start);
    start += (size_t)136U;
  }
  libcrux_iot_sha3_keccak_absorb_final_22(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_b2(&s, out);
    size_t offset = (size_t)136U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_b2(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)136U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_b2(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void keccakx1_22(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_22(data, out);
}

/**
 Writes SHA3-256 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_256_DIGEST_SIZE`] bytes long
*/
void sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_22(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_53(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 lane =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
            .data = {
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U],
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_53(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_53(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_53(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_53(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_53(
      keccak_state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_53(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_53(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_dc(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)104U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_53(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)104U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_53(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_53(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_53(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_53(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_53(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_53(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_53(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_53(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_53(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_53(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_dc(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)104U;
  size_t rem = data.meta % (size_t)104U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)104U;
  size_t last = outlen - outlen % (size_t)104U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_53(&s, data, start);
    start += (size_t)104U;
  }
  libcrux_iot_sha3_keccak_absorb_final_dc(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_53(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_53(&s, out);
    size_t offset = (size_t)104U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_53(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)104U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_53(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void keccakx1_dc(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_dc(data, out);
}

/**
 Writes SHA3-384 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_384_DIGEST_SIZE`] bytes long
*/
void sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_dc(payload, digest);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 lane =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
            .data = {
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U],
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_c6(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_c6(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_c6(
      keccak_state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_c6(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_dc0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(6U);
  size_t uu____0 = (size_t)72U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_c6(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)72U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_c6(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_c6(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_c6(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_c6(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_c6(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_c6(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_c6(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_c6(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_dc0(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)72U;
  size_t rem = data.meta % (size_t)72U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)72U;
  size_t last = outlen - outlen % (size_t)72U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_c6(&s, data, start);
    start += (size_t)72U;
  }
  libcrux_iot_sha3_keccak_absorb_final_dc0(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_c6(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_c6(&s, out);
    size_t offset = (size_t)72U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_c6(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)72U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_c6(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void keccakx1_dc0(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_dc0(data, out);
}

/**
 Writes SHA3-512 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_512_DIGEST_SIZE`] bytes long
*/
void sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload) {
  keccakx1_dc0(payload, digest);
}

/**
 Returns SHA3-224 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_a2 sha224(Eurydice_borrow_slice_u8 payload) {
  Eurydice_arr_a2 out = libcrux_secrets_int_public_integers_classify_27_96(
      (KRML_CLITERAL(Eurydice_arr_a2){.data = {0U}}));
  sha224_ema(Eurydice_array_to_slice_mut_5e(&out), payload);
  return out;
}

/**
 Returns SHA3-256 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_ec sha256(Eurydice_borrow_slice_u8 payload) {
  Eurydice_arr_ec out = libcrux_secrets_int_public_integers_classify_27_4b(
      (KRML_CLITERAL(Eurydice_arr_ec){.data = {0U}}));
  sha256_ema(Eurydice_array_to_slice_mut_01(&out), payload);
  return out;
}

/**
 Returns SHA3-384 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_65 sha384(Eurydice_borrow_slice_u8 payload) {
  Eurydice_arr_65 out = libcrux_secrets_int_public_integers_classify_27_69(
      (KRML_CLITERAL(Eurydice_arr_65){.data = {0U}}));
  sha384_ema(Eurydice_array_to_slice_mut_9f(&out), payload);
  return out;
}

/**
 Returns SHA3-512 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_c7 sha512(Eurydice_borrow_slice_u8 payload) {
  Eurydice_arr_c7 out = libcrux_secrets_int_public_integers_classify_27_56(
      (KRML_CLITERAL(Eurydice_arr_c7){.data = {0U}}));
  sha512_ema(Eurydice_array_to_slice_mut_17(&out), payload);
  return out;
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_2u32_60(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    size_t offset = start + (size_t)8U * i0;
    Eurydice_array_u8x4 arr0;
    memcpy(arr0.data,
           Eurydice_slice_subslice_shared_c8(
               blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                           .start = offset, .end = offset + (size_t)4U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t a = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr0}})));
    Eurydice_array_u8x4 arr;
    memcpy(arr.data,
           Eurydice_slice_subslice_shared_c8(
               blocks,
               (KRML_CLITERAL(core_ops_range_Range_87){
                   .start = offset + (size_t)4U, .end = offset + (size_t)8U}))
               .ptr,
           (size_t)4U * sizeof(uint8_t));
    uint32_t b = core_num__u32__from_le_bytes(
        core_result_unwrap_26_cc((KRML_CLITERAL(core_result_Result_c7){
            .tag = core_result_Ok, .val = {.case_Ok = arr}})));
    Eurydice_arr_a0 lane =
        libcrux_iot_sha3_lane_interleave_8d(libcrux_iot_sha3_lane_from_29(
            (KRML_CLITERAL(Eurydice_arr_a0){.data = {a, b}})));
    Eurydice_arr_a0 got = libcrux_iot_sha3_state_get_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U);
    libcrux_iot_sha3_state_set_lane_18(
        keccak_state, i0 / (size_t)5U, i0 % (size_t)5U,
        libcrux_iot_sha3_lane_from_ints_8d((KRML_CLITERAL(Eurydice_arr_a0){
            .data = {
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)0U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)0U)[0U],
                libcrux_iot_sha3_lane_index_cc(&got, (size_t)1U)[0U] ^
                    libcrux_iot_sha3_lane_index_cc(&lane, (size_t)1U)[0U]}})));
  }
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_18_60(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_60(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_18_60(s, blocks, start);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_2u32_60(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start) {
  libcrux_iot_sha3_state_load_block_2u32_60(
      keccak_state, Eurydice_array_to_slice_shared_15(blocks), start);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_load_block_full_18_60(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start) {
  libcrux_iot_sha3_state_load_block_full_2u32_60(self, blocks, start);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_37(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)168U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_60(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  for (size_t i = (size_t)0U; i < (size_t)168U / (size_t)8U; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(s, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = (size_t)8U * i0, .end = (size_t)8U * i0 + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = (size_t)8U * i0 + (size_t)4U,
                 .end = (size_t)8U * i0 + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_2u32_60(
      s, Eurydice_array_to_slice_mut_15(out));
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_full_18_60(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out) {
  libcrux_iot_sha3_state_store_block_full_2u32_60(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_and_last_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_60(s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_block_18_60(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_2u32_60(self, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_first_block_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_state_store_block_18_60(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_next_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(s);
  libcrux_iot_sha3_state_store_block_18_60(s, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_last_60(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccakf1600(&s);
  Eurydice_arr_5c b = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  libcrux_iot_sha3_state_store_block_full_18_60(&s, &b);
  Eurydice_slice_copy(out,
                      Eurydice_array_to_subslice_shared_d4(
                          &b, (KRML_CLITERAL(core_ops_range_Range_87){
                                  .start = (size_t)0U, .end = out.meta})),
                      uint8_t);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_37(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)168U;
  size_t rem = data.meta % (size_t)168U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)168U;
  size_t last = outlen - outlen % (size_t)168U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_60(&s, data, start);
    start += (size_t)168U;
  }
  libcrux_iot_sha3_keccak_absorb_final_37(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_60(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_60(&s, out);
    size_t offset = (size_t)168U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_60(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)168U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_60(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void keccakx1_37(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_37(data, out);
}

/**
 Writes SHAKE-128 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data) {
  keccakx1_37(data, out);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_220(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len) {
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (len > (size_t)0U) {
    Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d4(
                            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                                         .start = (size_t)0U, .end = len})),
                        Eurydice_slice_subslice_shared_c8(
                            last, (KRML_CLITERAL(core_ops_range_Range_87){
                                      .start = start, .end = start + len})),
                        uint8_t);
  }
  blocks.data[len] = libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_b2(s, &blocks, (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(s);
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_keccak_220(
    Eurydice_borrow_slice_u8 data, Eurydice_mut_borrow_slice_u8 out) {
  size_t n = data.meta / (size_t)136U;
  size_t rem = data.meta % (size_t)136U;
  size_t outlen = out.meta;
  size_t blocks = outlen / (size_t)136U;
  size_t last = outlen - outlen % (size_t)136U;
  libcrux_iot_sha3_state_KeccakState s = libcrux_iot_sha3_state_new_18();
  size_t start = (size_t)0U;
  for (size_t i = (size_t)0U; i < n; i++) {
    libcrux_iot_sha3_keccak_absorb_block_b2(&s, data, start);
    start += (size_t)136U;
  }
  libcrux_iot_sha3_keccak_absorb_final_220(&s, data, data.meta - rem, rem);
  if (blocks == (size_t)0U) {
    libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(&s, out);
  } else {
    libcrux_iot_sha3_keccak_squeeze_first_block_b2(&s, out);
    size_t offset = (size_t)136U;
    for (size_t i = (size_t)1U; i < blocks; i++) {
      libcrux_iot_sha3_keccak_squeeze_next_block_b2(
          &s, Eurydice_slice_subslice_from_mut_6d(out, offset));
      offset += (size_t)136U;
    }
    if (last < outlen) {
      libcrux_iot_sha3_keccak_squeeze_last_b2(
          s, Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void keccakx1_220(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_keccak_220(data, out);
}

/**
 Writes SHAKE256 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes.

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data) {
  keccakx1_220(data, out);
}

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.fill_buffer_08
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_fill_buffer_08_b2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_len = inputs.meta;
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (input_len >= (size_t)136U - self->buf_len) {
      consumed = (size_t)136U - self->buf_len;
      Eurydice_slice_copy(
          Eurydice_array_to_subslice_from_mut_5f(&self->buf, self->buf_len),
          Eurydice_slice_subslice_to_shared_72(inputs, consumed), uint8_t);
      self->buf_len += consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_full_08
with const generics
- RATE= 136
*/
size_t libcrux_iot_sha3_keccak_absorb_full_08_b2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_consumed =
      libcrux_iot_sha3_keccak_fill_buffer_08_b2(self, inputs);
  if (input_consumed > (size_t)0U) {
    libcrux_iot_sha3_state_load_block_18_b2(
        &self->inner, Eurydice_array_to_slice_shared_58(&self->buf),
        (size_t)0U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume = inputs.meta - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)136U;
  size_t remainder = input_to_consume % (size_t)136U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_load_block_18_b2(&self->inner, inputs,
                                            input_consumed + i0 * (size_t)136U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_08
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_08_b2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_08_b2(self, inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = inputs.meta;
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d40(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = self->buf_len,
                            .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6d(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
    self->buf_len += input_remainder_len;
  }
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<136usize> for
libcrux_iot_sha3::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_incremental_absorb_e2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_08_b2(self, input);
}

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final_08
with const generics
- RATE= 136
- DELIMITER= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_08_22(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_08_b2(self, inputs);
  size_t input_len = inputs.meta;
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (self->buf_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d4(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = self->buf_len})),
        Eurydice_array_to_subslice_shared_d40(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = (size_t)0U, .end = self->buf_len})),
        uint8_t);
  }
  if (input_remainder_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d4(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = self->buf_len,
                         .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6d(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
  }
  blocks.data[self->buf_len + input_remainder_len] =
      libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)136U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_b2(&self->inner, &blocks,
                                               (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<136usize> for
libcrux_iot_sha3::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_incremental_absorb_final_e2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_final_08_22(self, input);
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.zero_block_08
with const generics
- RATE= 136
*/
Eurydice_arr_ff libcrux_iot_sha3_keccak_zero_block_08_b2(void) {
  return libcrux_secrets_int_public_integers_classify_27_94(
      (KRML_CLITERAL(Eurydice_arr_ff){.data = {0U}}));
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.new_08
with const generics
- RATE= 136
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_bd libcrux_iot_sha3_keccak_new_08_b2(
    void) {
  libcrux_iot_sha3_state_KeccakState uu____0 = libcrux_iot_sha3_state_new_18();
  return (KRML_CLITERAL(libcrux_iot_sha3_keccak_KeccakSpongeState_bd){
      .inner = uu____0,
      .buf = libcrux_iot_sha3_keccak_zero_block_08_b2(),
      .buf_len = (size_t)0U,
      .sponge = false});
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<136usize> for
libcrux_iot_sha3::incremental::Shake256Xof}
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_bd
libcrux_iot_sha3_incremental_new_e2(void) {
  return libcrux_iot_sha3_keccak_new_08_b2();
}

/**
 `out` has the exact size we want here. It must be less than or equal to
 `RATE`.
*/
/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_18
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_18_b2(
    libcrux_iot_sha3_state_KeccakState self, Eurydice_mut_borrow_slice_u8 out) {
  size_t num_full_blocks = out.meta / (size_t)8U;
  size_t last_block_len = out.meta % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = i0 * (size_t)8U + (size_t)4U,
                 .end = i0 * (size_t)8U + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
  if (last_block_len > (size_t)4U) {
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    size_t last_half_block_len = last_block_len - (size_t)4U;
    Eurydice_mut_borrow_slice_u8 uu____2 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____2, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____3 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U + (size_t)4U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(
        uu____3,
        Eurydice_array_to_subslice_shared_d41(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = last_half_block_len})),
        uint8_t);
  } else if (last_block_len > (size_t)0U) {
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____4 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(
        uu____4,
        Eurydice_array_to_subslice_shared_d41(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = last_block_len})),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak._squeeze
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak__squeeze_b2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *keccak_state,
    Eurydice_mut_borrow_slice_u8 out) {
  if (keccak_state->sponge) {
    libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
  }
  size_t out_len = out.meta;
  size_t blocks = out_len / (size_t)136U;
  size_t last = out_len - out_len % (size_t)136U;
  size_t mid;
  if ((size_t)136U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)136U;
  }
  libcrux_iot_sha3_state_store_18_b2(
      keccak_state->inner, Eurydice_slice_subslice_to_mut_72(out, mid));
  size_t offset = mid;
  for (size_t i = (size_t)1U; i < blocks; i++) {
    libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
    libcrux_iot_sha3_state_store_18_b2(
        keccak_state->inner,
        Eurydice_slice_subslice_mut_c8(
            out, (KRML_CLITERAL(core_ops_range_Range_87){
                     .start = offset, .end = offset + (size_t)136U})));
    offset += (size_t)136U;
  }
  if (last > (size_t)0U) {
    if (last < out_len) {
      libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
      libcrux_iot_sha3_state_store_18_b2(
          keccak_state->inner,
          Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
  keccak_state->sponge = true;
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_08
with const generics
- RATE= 136
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_08_b2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak__squeeze_b2(self, out);
}

/**
 Shake256 squeeze
*/
/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<136usize> for
libcrux_iot_sha3::incremental::Shake256Xof}
*/
void libcrux_iot_sha3_incremental_squeeze_e2(
    libcrux_iot_sha3_keccak_KeccakSpongeState_bd *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_08_b2(self, out);
}

/**
 Consume the internal buffer and the required amount of the input to pad to
 `RATE`.

 Returns the `consumed` bytes from `inputs` if there's enough buffered
 content to consume, and `0` otherwise.
 If `consumed > 0` is returned, `self.buf` contains a full block to be
 loaded.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.fill_buffer_08
with const generics
- RATE= 168
*/
size_t libcrux_iot_sha3_keccak_fill_buffer_08_60(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_len = inputs.meta;
  size_t consumed = (size_t)0U;
  if (self->buf_len > (size_t)0U) {
    if (input_len >= (size_t)168U - self->buf_len) {
      consumed = (size_t)168U - self->buf_len;
      Eurydice_slice_copy(
          Eurydice_array_to_subslice_from_mut_5f0(&self->buf, self->buf_len),
          Eurydice_slice_subslice_to_shared_72(inputs, consumed), uint8_t);
      self->buf_len += consumed;
    }
  }
  return consumed;
}

/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_full_08
with const generics
- RATE= 168
*/
size_t libcrux_iot_sha3_keccak_absorb_full_08_60(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_consumed =
      libcrux_iot_sha3_keccak_fill_buffer_08_60(self, inputs);
  if (input_consumed > (size_t)0U) {
    libcrux_iot_sha3_state_load_block_18_60(
        &self->inner, Eurydice_array_to_slice_shared_2c(&self->buf),
        (size_t)0U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
    self->buf_len = (size_t)0U;
  }
  size_t input_to_consume = inputs.meta - input_consumed;
  size_t num_blocks = input_to_consume / (size_t)168U;
  size_t remainder = input_to_consume % (size_t)168U;
  for (size_t i = (size_t)0U; i < num_blocks; i++) {
    size_t i0 = i;
    libcrux_iot_sha3_state_load_block_18_60(&self->inner, inputs,
                                            input_consumed + i0 * (size_t)168U);
    libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
  }
  return remainder;
}

/**
 Absorb

 This function takes any number of bytes to absorb and buffers if it's not
 enough. The function assumes that all input slices in `blocks` have the same
 length.

 Only a multiple of `RATE` blocks are absorbed.
 For the remaining bytes [`absorb_final`] needs to be called.

 This works best with relatively small `inputs`.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_08
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_08_60(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_08_60(self, inputs);
  if (input_remainder_len > (size_t)0U) {
    size_t input_len = inputs.meta;
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d41(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = self->buf_len,
                            .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6d(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
    self->buf_len += input_remainder_len;
  }
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<168usize> for
libcrux_iot_sha3::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_incremental_absorb_f3(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_08_60(self, input);
}

/**
 Absorb a final block.

 The `inputs` block may be empty. Everything in the `inputs` block beyond
 `RATE` bytes is ignored.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final_08
with const generics
- RATE= 168
- DELIMITER= 31
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_absorb_final_08_37(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 inputs) {
  size_t input_remainder_len =
      libcrux_iot_sha3_keccak_absorb_full_08_60(self, inputs);
  size_t input_len = inputs.meta;
  Eurydice_arr_5c blocks = libcrux_secrets_int_public_integers_classify_27_df0(
      (KRML_CLITERAL(Eurydice_arr_5c){.data = {0U}}));
  if (self->buf_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d4(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = self->buf_len})),
        Eurydice_array_to_subslice_shared_d42(
            &self->buf, (KRML_CLITERAL(core_ops_range_Range_87){
                            .start = (size_t)0U, .end = self->buf_len})),
        uint8_t);
  }
  if (input_remainder_len > (size_t)0U) {
    Eurydice_slice_copy(
        Eurydice_array_to_subslice_mut_d4(
            &blocks, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = self->buf_len,
                         .end = self->buf_len + input_remainder_len})),
        Eurydice_slice_subslice_from_shared_6d(inputs,
                                               input_len - input_remainder_len),
        uint8_t);
  }
  blocks.data[self->buf_len + input_remainder_len] =
      libcrux_secrets_int_public_integers_classify_27_90(31U);
  size_t uu____0 = (size_t)168U - (size_t)1U;
  blocks.data[uu____0] = (uint32_t)blocks.data[uu____0] | 128U;
  libcrux_iot_sha3_state_load_block_full_18_60(&self->inner, &blocks,
                                               (size_t)0U);
  libcrux_iot_sha3_keccak_keccakf1600(&self->inner);
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<168usize> for
libcrux_iot_sha3::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_incremental_absorb_final_f3(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_borrow_slice_u8 input) {
  libcrux_iot_sha3_keccak_absorb_final_08_37(self, input);
}

/**
 An all zero block
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.zero_block_08
with const generics
- RATE= 168
*/
Eurydice_arr_c5 libcrux_iot_sha3_keccak_zero_block_08_60(void) {
  return libcrux_secrets_int_public_integers_classify_27_33(
      (KRML_CLITERAL(Eurydice_arr_c5){.data = {0U}}));
}

/**
 Generate a new keccak xof state.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.new_08
with const generics
- RATE= 168
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_31 libcrux_iot_sha3_keccak_new_08_60(
    void) {
  libcrux_iot_sha3_state_KeccakState uu____0 = libcrux_iot_sha3_state_new_18();
  return (KRML_CLITERAL(libcrux_iot_sha3_keccak_KeccakSpongeState_31){
      .inner = uu____0,
      .buf = libcrux_iot_sha3_keccak_zero_block_08_60(),
      .buf_len = (size_t)0U,
      .sponge = false});
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<168usize> for
libcrux_iot_sha3::incremental::Shake128Xof}
*/
libcrux_iot_sha3_keccak_KeccakSpongeState_31
libcrux_iot_sha3_incremental_new_f3(void) {
  return libcrux_iot_sha3_keccak_new_08_60();
}

/**
 `out` has the exact size we want here. It must be less than or equal to
 `RATE`.
*/
/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_18
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_state_store_18_60(
    libcrux_iot_sha3_state_KeccakState self, Eurydice_mut_borrow_slice_u8 out) {
  size_t num_full_blocks = out.meta / (size_t)8U;
  size_t last_block_len = out.meta % (size_t)8U;
  for (size_t i = (size_t)0U; i < num_full_blocks; i++) {
    size_t i0 = i;
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, i0 / (size_t)5U,
                                           i0 % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____0 = Eurydice_slice_subslice_mut_c8(
        out,
        (KRML_CLITERAL(core_ops_range_Range_87){
            .start = i0 * (size_t)8U, .end = i0 * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____0, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____1 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = i0 * (size_t)8U + (size_t)4U,
                 .end = i0 * (size_t)8U + (size_t)8U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(uu____1, Eurydice_array_to_slice_shared_98(&lvalue),
                        uint8_t);
  }
  if (last_block_len > (size_t)4U) {
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    size_t last_half_block_len = last_block_len - (size_t)4U;
    Eurydice_mut_borrow_slice_u8 uu____2 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + (size_t)4U}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue0 = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(uu____2, Eurydice_array_to_slice_shared_98(&lvalue0),
                        uint8_t);
    Eurydice_mut_borrow_slice_u8 uu____3 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U + (size_t)4U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)1U)[0U]);
    Eurydice_slice_copy(
        uu____3,
        Eurydice_array_to_subslice_shared_d41(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = last_half_block_len})),
        uint8_t);
  } else if (last_block_len > (size_t)0U) {
    Eurydice_arr_a0 keccak_lane = libcrux_iot_sha3_lane_deinterleave_8d(
        libcrux_iot_sha3_state_get_lane_18(&self, num_full_blocks / (size_t)5U,
                                           num_full_blocks % (size_t)5U));
    Eurydice_mut_borrow_slice_u8 uu____4 = Eurydice_slice_subslice_mut_c8(
        out, (KRML_CLITERAL(core_ops_range_Range_87){
                 .start = num_full_blocks * (size_t)8U,
                 .end = num_full_blocks * (size_t)8U + last_block_len}));
    /* original Rust expression is not an lvalue in C */
    Eurydice_array_u8x4 lvalue = core_num__u32__to_le_bytes(
        libcrux_iot_sha3_lane_index_cc(&keccak_lane, (size_t)0U)[0U]);
    Eurydice_slice_copy(
        uu____4,
        Eurydice_array_to_subslice_shared_d41(
            &lvalue, (KRML_CLITERAL(core_ops_range_Range_87){
                         .start = (size_t)0U, .end = last_block_len})),
        uint8_t);
  }
}

/**
A monomorphic instance of libcrux_iot_sha3.keccak._squeeze
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak__squeeze_60(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *keccak_state,
    Eurydice_mut_borrow_slice_u8 out) {
  if (keccak_state->sponge) {
    libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
  }
  size_t out_len = out.meta;
  size_t blocks = out_len / (size_t)168U;
  size_t last = out_len - out_len % (size_t)168U;
  size_t mid;
  if ((size_t)168U >= out_len) {
    mid = out_len;
  } else {
    mid = (size_t)168U;
  }
  libcrux_iot_sha3_state_store_18_60(
      keccak_state->inner, Eurydice_slice_subslice_to_mut_72(out, mid));
  size_t offset = mid;
  for (size_t i = (size_t)1U; i < blocks; i++) {
    libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
    libcrux_iot_sha3_state_store_18_60(
        keccak_state->inner,
        Eurydice_slice_subslice_mut_c8(
            out, (KRML_CLITERAL(core_ops_range_Range_87){
                     .start = offset, .end = offset + (size_t)168U})));
    offset += (size_t)168U;
  }
  if (last > (size_t)0U) {
    if (last < out_len) {
      libcrux_iot_sha3_keccak_keccakf1600(&keccak_state->inner);
      libcrux_iot_sha3_state_store_18_60(
          keccak_state->inner,
          Eurydice_slice_subslice_from_mut_6d(out, offset));
    }
  }
  keccak_state->sponge = true;
}

/**
 Squeeze `N` x `LEN` bytes.
*/
/**
This function found in impl {libcrux_iot_sha3::keccak::KeccakSpongeState<RATE>}
*/
/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_08
with const generics
- RATE= 168
*/
KRML_MUSTINLINE void libcrux_iot_sha3_keccak_squeeze_08_60(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak__squeeze_60(self, out);
}

/**
This function found in impl {libcrux_iot_sha3::incremental::Xof<168usize> for
libcrux_iot_sha3::incremental::Shake128Xof}
*/
void libcrux_iot_sha3_incremental_squeeze_f3(
    libcrux_iot_sha3_keccak_KeccakSpongeState_31 *self,
    Eurydice_mut_borrow_slice_u8 out) {
  libcrux_iot_sha3_keccak_squeeze_08_60(self, out);
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_sha3::lane::Lane2U32}
*/
inline Eurydice_arr_a0 libcrux_iot_sha3_lane_clone_f6(
    const Eurydice_arr_a0 *self) {
  return self[0U];
}

/**
This function found in impl {core::clone::Clone for
libcrux_iot_sha3::state::KeccakState}
*/
inline libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_state_clone_0f(
    const libcrux_iot_sha3_state_KeccakState *self) {
  return self[0U];
}

/**
This function found in impl {core::convert::From<libcrux_iot_sha3::Algorithm>
for u32}
*/
uint32_t from_c3(Algorithm v) {
  switch (v) {
    case libcrux_iot_sha3_Algorithm_Sha224: {
      break;
    }
    case libcrux_iot_sha3_Algorithm_Sha256: {
      return 2U;
    }
    case libcrux_iot_sha3_Algorithm_Sha384: {
      return 3U;
    }
    case libcrux_iot_sha3_Algorithm_Sha512: {
      return 4U;
    }
    default: {
      KRML_HOST_EPRINTF("KaRaMeL incomplete match at %s:%d\n", __FILE__,
                        __LINE__);
      KRML_HOST_EXIT(253U);
    }
  }
  return 1U;
}

/**
This function found in impl {core::convert::TryFrom<u32,
libcrux_iot_sha3::UnknownAlgorithm> for libcrux_iot_sha3::Algorithm}
*/
core_result_Result_20 try_from_72(uint32_t v) {
  switch (v) {
    case 1U: {
      break;
    }
    case 2U: {
      return (KRML_CLITERAL(core_result_Result_20){
          .tag = core_result_Ok, .f0 = libcrux_iot_sha3_Algorithm_Sha256});
    }
    case 3U: {
      return (KRML_CLITERAL(core_result_Result_20){
          .tag = core_result_Ok, .f0 = libcrux_iot_sha3_Algorithm_Sha384});
    }
    case 4U: {
      return (KRML_CLITERAL(core_result_Result_20){
          .tag = core_result_Ok, .f0 = libcrux_iot_sha3_Algorithm_Sha512});
    }
    default: {
      return (KRML_CLITERAL(core_result_Result_20){.tag = core_result_Err});
    }
  }
  return (KRML_CLITERAL(core_result_Result_20){
      .tag = core_result_Ok, .f0 = libcrux_iot_sha3_Algorithm_Sha224});
}
