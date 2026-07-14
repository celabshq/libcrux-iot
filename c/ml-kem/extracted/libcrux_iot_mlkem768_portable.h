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

#ifndef libcrux_iot_mlkem768_portable_H
#define libcrux_iot_mlkem768_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "libcrux_iot_core.h"

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
Eurydice_arr_ec libcrux_iot_ml_kem_mlkem768_portable_decapsulate(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext);

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_bf libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
    const Eurydice_arr_5f *public_key, Eurydice_arr_ec randomness);

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_e2
libcrux_iot_ml_kem_mlkem768_portable_generate_key_pair(
    Eurydice_arr_c7 randomness);

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext);

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key_only(
    const Eurydice_arr_7d *private_key);

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_public_key(
    const Eurydice_arr_5f *public_key);

#if defined(__cplusplus)
}
#endif

#define libcrux_iot_mlkem768_portable_H_DEFINED
#endif /* libcrux_iot_mlkem768_portable_H */
