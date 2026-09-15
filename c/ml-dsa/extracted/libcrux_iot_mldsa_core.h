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

#ifndef libcrux_iot_mldsa_core_H
#define libcrux_iot_mldsa_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#define None 0
#define Some 1

typedef uint8_t Option_87_tags;

#define libcrux_iot_ml_dsa_types_VerificationError_MalformedHintError 0
#define libcrux_iot_ml_dsa_types_VerificationError_SignerResponseExceedsBoundError \
  1
#define libcrux_iot_ml_dsa_types_VerificationError_CommitmentHashesDontMatchError \
  2
#define libcrux_iot_ml_dsa_types_VerificationError_VerificationContextTooLongError \
  3

typedef uint8_t libcrux_iot_ml_dsa_types_VerificationError;

#define libcrux_iot_ml_dsa_types_SigningError_RejectionSamplingError 0
#define libcrux_iot_ml_dsa_types_SigningError_ContextTooLongError 1

typedef uint8_t libcrux_iot_ml_dsa_types_SigningError;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4627size_t
*/
typedef struct Eurydice_arr_930_s {
  uint8_t data[4627U];
} Eurydice_arr_930;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2592size_t
*/
typedef struct Eurydice_arr_43_s {
  uint8_t data[2592U];
} Eurydice_arr_43;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $4896size_t
*/
typedef struct Eurydice_arr_e2_s {
  uint8_t data[4896U];
} Eurydice_arr_e2;

typedef struct Eurydice_arr_6c_s Eurydice_arr_6c;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_6c, size_t

*/
typedef struct Eurydice_dst_ref_shared_20_s {
  const Eurydice_arr_6c *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_20;

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_6c_s {
  int32_t data[256U];
} Eurydice_arr_6c;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_6c, size_t

*/
typedef struct Eurydice_dst_ref_mut_20_s {
  Eurydice_arr_6c *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_20;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $2592size_t
- $4896size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_850_s {
  Eurydice_arr_e2 signing_key;
  Eurydice_arr_43 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_850;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $3309size_t
*/
typedef struct Eurydice_arr_0c_s {
  uint8_t data[3309U];
} Eurydice_arr_0c;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1952size_t
*/
typedef struct Eurydice_arr_29_s {
  uint8_t data[1952U];
} Eurydice_arr_29;

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
- $4032size_t
*/
typedef struct Eurydice_arr_24_s {
  uint8_t data[4032U];
} Eurydice_arr_24;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1952size_t
- $4032size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5_s {
  Eurydice_arr_24 signing_key;
  Eurydice_arr_29 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_d5;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2420size_t
*/
typedef struct Eurydice_arr_85_s {
  uint8_t data[2420U];
} Eurydice_arr_85;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1312size_t
*/
typedef struct Eurydice_arr_02_s {
  uint8_t data[1312U];
} Eurydice_arr_02;

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types int32_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_83_s {
  const int32_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_83;

/**
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $263size_t
*/
typedef struct Eurydice_arr_d0_s {
  int32_t data[263U];
} Eurydice_arr_d0;

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $32size_t
*/
typedef struct Eurydice_arr_ec_s {
  uint8_t data[32U];
} Eurydice_arr_ec;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $2560size_t
*/
typedef struct Eurydice_arr_10_s {
  uint8_t data[2560U];
} Eurydice_arr_10;

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
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_ff_s {
  uint8_t data[136U];
} Eurydice_arr_ff;

#define Ok 0
#define Err 1

typedef uint8_t Result_8e_tags;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $640size_t
*/
typedef struct Eurydice_arr_20_s {
  uint8_t data[640U];
} Eurydice_arr_20;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $576size_t
*/
typedef struct Eurydice_arr_22_s {
  uint8_t data[576U];
} Eurydice_arr_22;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $11size_t
*/
typedef struct Eurydice_arr_c9_s {
  uint8_t data[11U];
} Eurydice_arr_c9;

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSAKeyPair
with const generics
- $1312size_t
- $2560size_t
*/
typedef struct libcrux_iot_ml_dsa_types_MLDSAKeyPair_85_s {
  Eurydice_arr_10 signing_key;
  Eurydice_arr_02 verification_key;
} libcrux_iot_ml_dsa_types_MLDSAKeyPair_85;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $66size_t
*/
typedef struct Eurydice_arr_91_s {
  uint8_t data[66U];
} Eurydice_arr_91;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_d0, size_t

*/
typedef struct Eurydice_dst_ref_mut_33_s {
  Eurydice_arr_d0 *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_33;

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
A monomorphic instance of Eurydice.arr
with types int32_t
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_4d_s {
  int32_t data[8U];
} Eurydice_arr_4d;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $840size_t
*/
typedef struct Eurydice_arr_d1_s {
  uint8_t data[840U];
} Eurydice_arr_d1;

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

#define libcrux_iot_mldsa_core_H_DEFINED
#endif /* libcrux_iot_mldsa_core_H */
