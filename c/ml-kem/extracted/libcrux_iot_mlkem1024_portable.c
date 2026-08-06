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

#include "libcrux_iot_mlkem1024_portable.h"

#include "internal/libcrux_iot_mlkem_portable.h"
#include "libcrux_iot_core.h"

/**
 Portable decapsulate
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.decapsulate with const
generics
- K= 4
- K_SQUARED= 16
- SECRET_KEY_SIZE= 3168
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
- CIPHERTEXT_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
- IMPLICIT_REJECTION_HASH_INPUT_SIZE= 1600
*/
static Eurydice_arr_ec decapsulate_c8(const Eurydice_arr_a8 *private_key,
                                      const Eurydice_arr_d1 *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_decapsulate_5d1(private_key, ciphertext);
}

/**
 Decapsulate ML-KEM 1024

 Generates an [`MlKemSharedSecret`].
 The input is a reference to an [`MlKem1024PrivateKey`] and an
 [`MlKem1024Ciphertext`].
*/
Eurydice_arr_ec libcrux_iot_ml_kem_mlkem1024_portable_decapsulate(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *ciphertext) {
  return decapsulate_c8(private_key, ciphertext);
}

/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.encapsulate with const
generics
- K= 4
- K_SQUARED= 16
- CIPHERTEXT_SIZE= 1568
- PUBLIC_KEY_SIZE= 1568
- T_AS_NTT_ENCODED_SIZE= 1536
- C1_SIZE= 1408
- C2_SIZE= 160
- VECTOR_U_COMPRESSION_FACTOR= 11
- VECTOR_V_COMPRESSION_FACTOR= 5
- C1_BLOCK_SIZE= 352
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- ETA2= 2
- ETA2_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
- PRF_OUTPUT_SIZE2= 512
*/
static tuple_97 encapsulate_85(const Eurydice_arr_d1 *public_key,
                               const Eurydice_arr_ec *randomness) {
  return libcrux_iot_ml_kem_ind_cca_encapsulate_fe1(public_key, randomness);
}

/**
 Encapsulate ML-KEM 1024

 Generates an ([`MlKem1024Ciphertext`], [`MlKemSharedSecret`]) tuple.
 The input is a reference to an [`MlKem1024PublicKey`] and
 [`SHARED_SECRET_SIZE`] bytes of `randomness`.
*/
tuple_97 libcrux_iot_ml_kem_mlkem1024_portable_encapsulate(
    const Eurydice_arr_d1 *public_key, Eurydice_arr_ec randomness) {
  return encapsulate_85(public_key, &randomness);
}

/**
 Portable generate key pair.
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.generate_keypair with const
generics
- K= 4
- K_SQUARED= 16
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
static libcrux_iot_ml_kem_types_MlKemKeyPair_3f generate_keypair_fc(
    const Eurydice_arr_c7 *randomness) {
  return libcrux_iot_ml_kem_ind_cca_generate_keypair_de1(randomness);
}

/**
 Generate ML-KEM 1024 Key Pair
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_3f
libcrux_iot_ml_kem_mlkem1024_portable_generate_key_pair(
    Eurydice_arr_c7 randomness) {
  return generate_keypair_fc(&randomness);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key with
const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_private_key_43(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *ciphertext) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_75(private_key,
                                                            ciphertext);
}

/**
 Validate a private key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *ciphertext) {
  return validate_private_key_43(private_key, ciphertext);
}

/**
 Private key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_private_key_only
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
static KRML_MUSTINLINE bool validate_private_key_only_f5(
    const Eurydice_arr_a8 *private_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_private_key_only_2f(private_key);
}

/**
 Validate the private key only.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_private_key_only(
    const Eurydice_arr_a8 *private_key) {
  return validate_private_key_only_f5(private_key);
}

/**
 Public key validation
*/
/**
A monomorphic instance of
libcrux_iot_ml_kem.ind_cca.instantiations.portable.validate_public_key with
const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
static KRML_MUSTINLINE bool validate_public_key_f5(
    const Eurydice_arr_d1 *public_key) {
  return libcrux_iot_ml_kem_ind_cca_validate_public_key_df(public_key);
}

/**
 Validate a public key.

 Returns `true` if valid, and `false` otherwise.
*/
bool libcrux_iot_ml_kem_mlkem1024_portable_validate_public_key(
    const Eurydice_arr_d1 *public_key) {
  return validate_public_key_f5(public_key);
}
