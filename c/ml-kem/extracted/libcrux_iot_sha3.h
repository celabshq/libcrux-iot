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

#ifndef libcrux_iot_sha3_H
#define libcrux_iot_sha3_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "eurydice_glue_additions.h"
#include "libcrux_iot_core.h"

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_lane_Lane2U32
with const generics
- $25size_t
*/
typedef struct Eurydice_arr_c0_s {
  Eurydice_arr_a0 data[25U];
} Eurydice_arr_c0;

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_lane_Lane2U32
with const generics
- $5size_t
*/
typedef struct Eurydice_arr_44_s {
  Eurydice_arr_a0 data[5U];
} Eurydice_arr_44;

typedef struct libcrux_iot_sha3_state_KeccakState_s {
  Eurydice_arr_c0 st;
  Eurydice_arr_44 c;
  Eurydice_arr_44 d;
  size_t i;
} libcrux_iot_sha3_state_KeccakState;

/**
 Writes SHA3-512 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_512_DIGEST_SIZE`] bytes long
*/
void sha512_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 Writes SHA3-256 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_256_DIGEST_SIZE`] bytes long
*/
void sha256_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 Writes SHAKE256 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes.

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake256_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data);

/**
 Writes SHA3-224 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_224_DIGEST_SIZE`] bytes long
*/
void sha224_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 Writes SHA3-384 digest of input payload to externally allocated buffer.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
 - `digest` is exactly [`SHA3_384_DIGEST_SIZE`] bytes long
*/
void sha384_ema(Eurydice_mut_borrow_slice_u8 digest,
                Eurydice_borrow_slice_u8 payload);

/**
 Returns SHA3-224 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_a2 sha224(Eurydice_borrow_slice_u8 payload);

/**
 Returns SHA3-256 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_ec sha256(Eurydice_borrow_slice_u8 payload);

/**
 Returns SHA3-384 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_65 sha384(Eurydice_borrow_slice_u8 payload);

/**
 Returns SHA3-512 digest of input payload.

 Preconditions:
 - `payload` is at most `u32::MAX` bytes long
*/
Eurydice_arr_c7 sha512(Eurydice_borrow_slice_u8 payload);

/**
 Writes SHAKE-128 digest of input payload to externally allocated buffer.

 Writes `out.len()` bytes

 Preconditions:
 - `out` is at most `u32::MAX` bytes long
*/
void shake128_ema(Eurydice_mut_borrow_slice_u8 out,
                  Eurydice_borrow_slice_u8 data);

/**
A monomorphic instance of Eurydice.arr
with types libcrux_iot_sha3_incremental_UnbufferedXofState
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_7b_s {
  libcrux_iot_sha3_state_KeccakState data[4U];
} Eurydice_arr_7b;

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_sha3_H_DEFINED
#endif /* libcrux_iot_sha3_H */
