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

#include "libcrux_iot_mlkem768_portable.h"

#include "internal/libcrux_iot_mlkem_portable.h"
#include "libcrux_iot_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.decapsulate with const
generics
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
static Eurydice_arr_ec decapsulate_64(const Eurydice_arr_7d *private_key,
                                      const Eurydice_arr_2b *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_decapsulate_5d0(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 768

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem768PrivateKey`] and an
 [`MlKem768Ciphertext`].
*/
Eurydice_arr_ec libcrux_iot_ml_kem_mlkem768_portable_decapsulate(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext) {
  return decapsulate_64(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.encapsulate with const
generics
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
static tuple_bf encapsulate_19(const Eurydice_arr_5f *public_key,
                               const Eurydice_arr_ec *randomness) {
  return libcrux_iot_ml_kem_ind_cca_encapsulate_fe0(public_key, randomness);
}

/**
 Encapsulate ML-KEM 768

 Generates an ([`MlKem768Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem768PublicKey`] and [`SHARED_SECRET_SIZE`]
 bytes of `randomness`.
*/
tuple_bf libcrux_iot_ml_kem_mlkem768_portable_encapsulate(
    const Eurydice_arr_5f *public_key, Eurydice_arr_ec randomness) {
  return encapsulate_19(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
static libcrux_iot_ml_kem_types_MlKemKeyPair_e2 generate_keypair_96(
    const Eurydice_arr_c7 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_generate_keypair_de0(randomness);
}

/**
 Generate ML-KEM 768 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_e2
libcrux_iot_ml_kem_mlkem768_portable_generate_key_pair(
    Eurydice_arr_c7 randomness) {
  return generate_keypair_96(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key with
const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
static KRML_MUSTINLINE bool validate_private_key_d3(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_88(private_key,
                                                            ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext) {
  return validate_private_key_d3(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key_only
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
static KRML_MUSTINLINE bool validate_private_key_only_3b(
    const Eurydice_arr_7d *private_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_d3(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_private_key_only(
    const Eurydice_arr_7d *private_key) {
  return validate_private_key_only_3b(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_public_key with
const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
static KRML_MUSTINLINE bool validate_public_key_3b(
    const Eurydice_arr_5f *public_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_public_key_21(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem768_portable_validate_public_key(
    const Eurydice_arr_5f *public_key) {
  return validate_public_key_3b(public_key);
}
