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

#ifndef libcrux_iot_core_H
#define libcrux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_COEFFICIENT ((size_t)12U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT ((size_t)256U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_COEFFICIENTS_IN_RING_ELEMENT * (size_t)12U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE ((size_t)32U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_SHARED_SECRET_SIZE ((size_t)32U)

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3168size_t
*/
typedef struct Eurydice_arr_a8_s {
  uint8_t data[3168U];
} Eurydice_arr_a8;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1568size_t
*/
typedef struct Eurydice_arr_d1_s {
  uint8_t data[1568U];
} Eurydice_arr_d1;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemKeyPair
with const generics
- $3168size_t
- $1568size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemKeyPair_3f_s {
  Eurydice_arr_a8 sk;
  Eurydice_arr_d1 pk;
} libcrux_iot_ml_kem_types_MlKemKeyPair_3f;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $34size_t
*/
typedef struct Eurydice_arr_31_s {
  uint8_t data[34U];
} Eurydice_arr_31;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_31, size_t

*/
typedef struct Eurydice_dst_ref_shared_cf_s {
  const Eurydice_arr_31 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_cf;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $168size_t
*/
typedef struct Eurydice_arr_c5_s {
  uint8_t data[168U];
} Eurydice_arr_c5;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_c5, size_t

*/
typedef struct Eurydice_dst_ref_mut_c3_s {
  Eurydice_arr_c5 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_c3;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $504size_t
*/
typedef struct Eurydice_arr_79_s {
  uint8_t data[504U];
} Eurydice_arr_79;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_79, size_t

*/
typedef struct Eurydice_dst_ref_mut_8c_s {
  Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_8c;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_ec_s {
  uint8_t data[32U];
} Eurydice_arr_ec;

/**
A monomorphic instance of n-tuple
with types libcrux_iot_ml_kem_types_MlKemCiphertext_a3, Eurydice_arr_ec

*/
typedef struct tuple_97_s {
  Eurydice_arr_d1 fst;
  Eurydice_arr_ec snd;
} tuple_97;

typedef struct Eurydice_arr_fa_s Eurydice_arr_fa;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_fa, size_t

*/
typedef struct Eurydice_dst_ref_shared_b4_s {
  const Eurydice_arr_fa *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_b4;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $33size_t
*/
typedef struct Eurydice_arr_fa_s {
  uint8_t data[33U];
} Eurydice_arr_fa;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1184size_t
*/
typedef struct Eurydice_arr_5f_s {
  uint8_t data[1184U];
} Eurydice_arr_5f;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2400size_t
*/
typedef struct Eurydice_arr_7d_s {
  uint8_t data[2400U];
} Eurydice_arr_7d;

/**
A monomorphic instance of libcrux_iot_ml_kem.types.MlKemKeyPair
with const generics
- $2400size_t
- $1184size_t
*/
typedef struct libcrux_iot_ml_kem_types_MlKemKeyPair_e2_s {
  Eurydice_arr_7d sk;
  Eurydice_arr_5f pk;
} libcrux_iot_ml_kem_types_MlKemKeyPair_e2;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1088size_t
*/
typedef struct Eurydice_arr_2b_s {
  uint8_t data[1088U];
} Eurydice_arr_2b;

/**
A monomorphic instance of n-tuple
with types libcrux_iot_ml_kem_types_MlKemCiphertext_d8, Eurydice_arr_ec

*/
typedef struct tuple_bf_s {
  Eurydice_arr_2b fst;
  Eurydice_arr_ec snd;
} tuple_bf;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $64size_t
*/
typedef struct Eurydice_arr_c7_s {
  uint8_t data[64U];
} Eurydice_arr_c7;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_83_s {
  const int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_83;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_83_s {
  int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_83;

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $16size_t
*/
typedef struct Eurydice_arr_d6_s {
  int16_t data[16U];
} Eurydice_arr_d6;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $48size_t
*/
typedef struct Eurydice_arr_65_s {
  uint8_t data[48U];
} Eurydice_arr_65;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $28size_t
*/
typedef struct Eurydice_arr_a2_s {
  uint8_t data[28U];
} Eurydice_arr_a2;

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_a0_s {
  uint32_t data[2U];
} Eurydice_arr_a0;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_core_H_DEFINED
#endif /* libcrux_iot_core_H */
