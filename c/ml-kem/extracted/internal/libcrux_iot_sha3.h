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

#ifndef internal_libcrux_iot_sha3_H
#define internal_libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_sha3.h"
#include "internal/libcrux_iot_core.h"
#include "libcrux_iot_core.h"

typedef Eurydice_arr_a0 libcrux_iot_sha3_lane_Lane2U32;

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_a0 libcrux_iot_sha3_lane_from_ints_8d(Eurydice_arr_a0 value);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_a0 libcrux_iot_sha3_lane_zero_8d(void);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_state_new_18(void);

/**
This function found in impl {core::convert::From<[u32; 2usize]> for
libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_a0 libcrux_iot_sha3_lane_from_29(Eurydice_arr_a0 value);

/**
This function found in impl {core::ops::index::Index<usize, u32> for
libcrux_iot_sha3::lane::Lane2U32}
*/
const uint32_t *libcrux_iot_sha3_lane_index_cc(const Eurydice_arr_a0 *self,
                                               size_t index);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_a0 libcrux_iot_sha3_lane_interleave_8d(Eurydice_arr_a0 self);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
Eurydice_arr_a0 libcrux_iot_sha3_state_get_lane_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_lane_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    Eurydice_arr_a0 lane);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
uint32_t libcrux_iot_sha3_state_get_with_zeta_18(
    const libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    size_t zeta);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_lane_value_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j,
    uint32_t value);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta_d(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_theta(
    libcrux_iot_sha3_state_KeccakState *s);

#define LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_0                               \
  ((KRML_CLITERAL(Eurydice_arr_030){                                           \
      .data = {1U, 0U, 0U, 0U, 1U, 1U, 1U, 1U, 0U, 0U, 1U, 0U, 1U, 1U, 1U, 1U, \
               0U, 0U, 0U, 0U, 1U, 0U, 1U, 0U, 0U, 0U, 1U, 1U, 0U, 1U, 0U, 1U, \
               1U, 1U, 1U, 1U, 0U, 0U, 1U, 1U, 1U, 1U, 0U, 1U, 1U, 0U, 0U, 1U, \
               0U, 1U, 0U, 1U, 1U, 1U, 0U, 1U, 0U, 1U, 1U, 0U, 1U, 1U, 1U, 0U, \
               0U, 1U, 1U, 0U, 1U, 0U, 0U, 1U, 1U, 0U, 1U, 1U, 0U, 1U, 0U, 0U, \
               0U, 1U, 0U, 0U, 1U, 1U, 1U, 0U, 1U, 1U, 0U, 1U, 1U, 0U, 0U, 0U, \
               0U, 1U, 1U, 1U, 0U, 1U, 0U, 0U, 1U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, \
               0U, 1U, 0U, 1U, 1U, 0U, 0U, 0U, 1U, 1U, 1U, 0U, 0U, 0U, 0U, 0U, \
               0U, 1U, 1U, 0U, 1U, 1U, 1U, 1U, 0U, 1U, 0U, 0U, 0U, 0U, 0U, 0U, \
               0U, 1U, 0U, 0U, 1U, 0U, 1U, 0U, 0U, 1U, 1U, 1U, 1U, 1U, 1U, 1U, \
               1U, 0U, 0U, 0U, 1U, 1U, 0U, 0U, 0U, 1U, 0U, 1U, 0U, 1U, 0U, 1U, \
               0U, 0U, 0U, 0U, 1U, 0U, 0U, 0U, 0U, 1U, 1U, 0U, 0U, 1U, 1U, 0U, \
               0U, 0U, 0U, 0U, 1U, 1U, 1U, 1U, 1U, 0U, 1U, 1U, 1U, 0U, 1U, 1U, \
               1U, 1U, 1U, 1U, 0U, 1U, 0U, 1U, 0U, 0U, 1U, 0U, 1U, 1U, 0U, 1U, \
               0U, 1U, 0U, 1U, 1U, 0U, 0U, 1U, 1U, 1U, 0U, 0U, 1U, 0U, 0U, 1U, \
               1U, 0U, 0U, 1U, 0U, 0U, 0U, 1U, 0U, 1U, 1U, 1U}}))

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
void libcrux_iot_sha3_state_set_with_zeta_18(
    libcrux_iot_sha3_state_KeccakState *self, size_t i, size_t j, size_t zeta,
    uint32_t v);

#define LIBCRUX_IOT_SHA3_KECCAK_RC_INTERLEAVED_1                           \
  ((KRML_CLITERAL(Eurydice_arr_030){                                       \
      .data = {                                                            \
          0U,          137U,        2147483787U, 2147516544U, 139U,        \
          32768U,      2147516552U, 2147483778U, 11U,         10U,         \
          32898U,      32771U,      32907U,      2147483659U, 2147483786U, \
          2147483777U, 2147483777U, 2147483656U, 131U,        2147516419U, \
          2147516552U, 2147483784U, 32768U,      2147516546U, 2147516553U, \
          2147516547U, 2147483649U, 2147516418U, 2147483785U, 130U,        \
          2147483656U, 137U,        2147483656U, 0U,          131U,        \
          2147516544U, 8U,          2147483776U, 2147516544U, 2U,          \
          2147516555U, 8U,          2147483657U, 32779U,      2147516546U, \
          2147516416U, 32776U,      32897U,      2147516553U, 2147516553U, \
          2147516426U, 138U,        130U,        2147483650U, 32898U,      \
          32896U,      2147483659U, 2147483651U, 10U,         32769U,      \
          2147483779U, 32899U,      139U,        32778U,      2147483779U, \
          32778U,      2147483648U, 2147483786U, 2147483656U, 10U,         \
          32904U,      8U,          2147483651U, 0U,          10U,         \
          32779U,      2147516552U, 2147483659U, 2147483776U, 2147516554U, \
          32777U,      3U,          2147483651U, 137U,        2147483777U, \
          2147483787U, 2147516419U, 2147516427U, 32776U,      32776U,      \
          32770U,      9U,          2147516545U, 32906U,      2147516426U, \
          128U,        32905U,      32906U,      2147516553U, 2147516416U, \
          32897U,      2147516426U, 9U,          2147516418U, 2147483658U, \
          2147516418U, 2147483648U, 2147483657U, 32904U,      2U,          \
          2147516424U, 2147516552U, 2147483649U, 2147516555U, 2U,          \
          2147516418U, 2147483779U, 32905U,      32896U,      2147483778U, \
          136U,        2147516554U, 32906U,      2147516547U, 2147483659U, \
          2147483657U, 32769U,      2147483785U, 136U,        2147516419U, \
          2147516417U, 3U,          2147483776U, 2147516425U, 2147483785U, \
          11U,         131U,        2147516425U, 2147483779U, 32768U,      \
          2147516427U, 32770U,      3U,          2147483786U, 2147483650U, \
          32769U,      2147483648U, 2147483651U, 131U,        2147516554U, \
          32771U,      32776U,      32907U,      2147483778U, 1U,          \
          32769U,      2147483658U, 2147516424U, 2147516427U, 32897U,      \
          2147516547U, 2147483778U, 130U,        2147483777U, 2147483650U, \
          32904U,      139U,        32899U,      8U,          2147483786U, \
          2147483787U, 2147516554U, 32896U,      2147483784U, 32899U,      \
          2U,          2147516545U, 32771U,      32897U,      2147516416U, \
          32770U,      138U,        1U,          32898U,      32906U,      \
          2147516416U, 32907U,      2147483649U, 2147516545U, 32777U,      \
          138U,        136U,        2147516425U, 2147483658U, 2147516555U, \
          139U,        32905U,      32771U,      32770U,      128U,        \
          32778U,      2147483658U, 2147516545U, 32896U,      2147483649U, \
          2147516424U, 2147516546U, 2147516426U, 3U,          2147483657U, \
          32898U,      32777U,      128U,        32899U,      129U,        \
          1U,          32779U,      2147516417U, 128U,        32768U,      \
          2147516417U, 9U,          2147516555U, 129U,        130U,        \
          2147483787U, 2147516425U, 2147483648U, 2147483776U, 2147516419U, \
          2147516546U, 2147516547U, 2147483784U, 32905U,      32777U,      \
          9U,          2147516424U, 2147516417U, 138U,        11U,         \
          137U,        2147483650U, 32779U,      2147516427U, 32907U,      \
          2147483784U, 32778U,      2147483785U, 1U,          32904U,      \
          129U,        136U,        2147516544U, 129U,        11U}}))

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta_d(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_theta(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta_d(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_theta(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x0_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x1_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x2_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x3_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_c_x4_z1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta_d(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_theta(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y1_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y2_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y3_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta0(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y4_zeta1(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_2(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 0
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_56(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 4
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_23(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 8
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_70(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 12
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_60(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 16
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_18(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta0_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_y0_zeta1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round0_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round0_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta0_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_y0_zeta1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round1_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round1_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta0_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_y0_zeta1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round2_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round2_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta0_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1 with const
generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_y0_zeta1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of
libcrux_iot_sha3.keccak.keccakf1600_round3_pi_rho_chi_1 with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_round3_pi_rho_chi_1_fc(
    libcrux_iot_sha3_state_KeccakState *s);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccakf1600_4rounds
with const generics
- BASE_ROUND= 20
*/
void libcrux_iot_sha3_keccak_keccakf1600_4rounds_fc(
    libcrux_iot_sha3_state_KeccakState *s);

void libcrux_iot_sha3_keccak_keccakf1600(libcrux_iot_sha3_state_KeccakState *s);

/**
This function found in impl {libcrux_iot_sha3::lane::Lane2U32}
*/
Eurydice_arr_a0 libcrux_iot_sha3_lane_deinterleave_8d(Eurydice_arr_a0 self);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_2u32_c6(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_full_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_dc(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_2u32_c6(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_full_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_store_block_18_c6(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_c6(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_squeeze_last_c6(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_state_load_block_18_c6(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 72
*/
void libcrux_iot_sha3_keccak_absorb_block_c6(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 72
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_dc(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 72
- DELIM= 6
*/
void keccakx1_dc(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_2u32_b2(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_full_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_22(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_2u32_b2(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_full_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_store_block_18_b2(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_b2(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_squeeze_last_b2(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_state_load_block_18_b2(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 136
*/
void libcrux_iot_sha3_keccak_absorb_block_b2(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_22(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 6
*/
void keccakx1_22(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_220(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 136
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_220(Eurydice_borrow_slice_u8 data,
                                        Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 136
- DELIM= 31
*/
void keccakx1_220(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out);

typedef libcrux_iot_sha3_state_KeccakState
    libcrux_iot_sha3_incremental_UnbufferedXofState;

/**
 Create a new SHAKE-128 state object.
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_incremental_shake128_init(
    void);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_2u32_60(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_2u32_60(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_full_18_60(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_absorb_final_37(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
 Absorb
*/
void libcrux_iot_sha3_incremental_shake128_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data0);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_18_60(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_three_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_three_blocks_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze three blocks
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_first_three_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

/**
 Squeeze another block
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

#define libcrux_iot_sha3_Algorithm_Sha224 1
#define libcrux_iot_sha3_Algorithm_Sha256 2
#define libcrux_iot_sha3_Algorithm_Sha384 3
#define libcrux_iot_sha3_Algorithm_Sha512 4

typedef uint8_t Algorithm;

#define SHA3_224_DIGEST_SIZE ((size_t)28U)

#define SHA3_256_DIGEST_SIZE ((size_t)32U)

#define SHA3_384_DIGEST_SIZE ((size_t)48U)

#define SHA3_512_DIGEST_SIZE ((size_t)64U)

/**
 Returns the size of a digest in bytes for a given [`Algorithm`].
*/
size_t digest_size(Algorithm mode);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_2u32_9e(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_full_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_3a(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_2u32_9e(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_full_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_store_block_18_9e(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_9e(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_squeeze_last_9e(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_state_load_block_18_9e(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 144
*/
void libcrux_iot_sha3_keccak_absorb_block_9e(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 144
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_3a(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 144
- DELIM= 6
*/
void keccakx1_3a(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_2u32_53(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    Eurydice_borrow_slice_u8 blocks, size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_2u32_53(
    libcrux_iot_sha3_state_KeccakState *keccak_state,
    const Eurydice_arr_5c *blocks, size_t start);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_full_18_53(
    libcrux_iot_sha3_state_KeccakState *self, const Eurydice_arr_5c *blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_final
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_absorb_final_dc0(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 last,
    size_t start, size_t len);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_2u32_53(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_full_18_53(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_store_block_18_53(
    const libcrux_iot_sha3_state_KeccakState *self,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_first_block_53(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_next_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_next_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_squeeze_last_53(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_state_load_block_18_53(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 104
*/
void libcrux_iot_sha3_keccak_absorb_block_53(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 104
- DELIM= 6
*/
void libcrux_iot_sha3_keccak_keccak_dc0(Eurydice_borrow_slice_u8 data,
                                        Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 104
- DELIM= 6
*/
void keccakx1_dc0(Eurydice_borrow_slice_u8 data,
                  Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_2u32
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_2u32_60(
    const libcrux_iot_sha3_state_KeccakState *s, Eurydice_arr_5c *out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.store_block_full_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_store_block_full_18_60(
    const libcrux_iot_sha3_state_KeccakState *self, Eurydice_arr_5c *out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_and_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_and_last_60(
    const libcrux_iot_sha3_state_KeccakState *s,
    Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_last
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_last_60(
    libcrux_iot_sha3_state_KeccakState s, Eurydice_mut_borrow_slice_u8 out);

/**
This function found in impl {libcrux_iot_sha3::state::KeccakState}
*/
/**
A monomorphic instance of libcrux_iot_sha3.state.load_block_18
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_state_load_block_18_60(
    libcrux_iot_sha3_state_KeccakState *self, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.absorb_block
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_absorb_block_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 blocks,
    size_t start);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.keccak
with const generics
- RATE= 168
- DELIM= 31
*/
void libcrux_iot_sha3_keccak_keccak_37(Eurydice_borrow_slice_u8 data,
                                       Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccakx1
with const generics
- RATE= 168
- DELIM= 31
*/
void keccakx1_37(Eurydice_borrow_slice_u8 data,
                 Eurydice_mut_borrow_slice_u8 out);

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakSpongeState
with const generics
- $168size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakSpongeState_31_s {
  libcrux_iot_sha3_state_KeccakState inner;
  Eurydice_arr_c5 buf;
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakSpongeState_31;

typedef libcrux_iot_sha3_keccak_KeccakSpongeState_31
    libcrux_iot_sha3_incremental_Shake128Xof;

/**
A monomorphic instance of libcrux_iot_sha3.keccak.KeccakSpongeState
with const generics
- $136size_t
*/
typedef struct libcrux_iot_sha3_keccak_KeccakSpongeState_bd_s {
  libcrux_iot_sha3_state_KeccakState inner;
  Eurydice_arr_ff buf;
  size_t buf_len;
  bool sponge;
} libcrux_iot_sha3_keccak_KeccakSpongeState_bd;

typedef libcrux_iot_sha3_keccak_KeccakSpongeState_bd
    libcrux_iot_sha3_incremental_Shake256Xof;

/**
A monomorphic instance of libcrux_iot_sha3.keccak.squeeze_first_five_blocks
with const generics
- RATE= 168
*/
void libcrux_iot_sha3_keccak_squeeze_first_five_blocks_60(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze five blocks
*/
void libcrux_iot_sha3_incremental_shake128_squeeze_first_five_blocks(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out0);

/**
 Absorb some data for SHAKE-256 for the last time
*/
void libcrux_iot_sha3_incremental_shake256_absorb_final(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_borrow_slice_u8 data);

/**
 Create a new SHAKE-256 state object.
*/
libcrux_iot_sha3_state_KeccakState libcrux_iot_sha3_incremental_shake256_init(
    void);

/**
 Squeeze the first SHAKE-256 block
*/
void libcrux_iot_sha3_incremental_shake256_squeeze_first_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

/**
 Squeeze the next SHAKE-256 block
*/
void libcrux_iot_sha3_incremental_shake256_squeeze_next_block(
    libcrux_iot_sha3_state_KeccakState *s, Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_SHA3_KECCAK_WIDTH ((size_t)200U)

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_sha3_H_DEFINED
#endif /* internal_libcrux_iot_sha3_H */
