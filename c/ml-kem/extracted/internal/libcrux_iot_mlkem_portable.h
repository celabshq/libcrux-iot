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

#ifndef internal_libcrux_iot_mlkem_portable_H
#define internal_libcrux_iot_mlkem_portable_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_mlkem_portable.h"
#include "libcrux_iot_core.h"

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 4
- PUBLIC_KEY_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_df(
    const Eurydice_arr_d1 *public_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_2f(
    const Eurydice_arr_a8 *private_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 4
- SECRET_KEY_SIZE= 3168
- CIPHERTEXT_SIZE= 1568
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_75(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *_ciphertext);

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 4
- K_SQUARED= 16
- CPA_PRIVATE_KEY_SIZE= 1536
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 512
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_3f
libcrux_iot_ml_kem_ind_cca_generate_keypair_de1(
    const Eurydice_arr_c7 *randomness);

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
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
tuple_97 libcrux_iot_ml_kem_ind_cca_encapsulate_fe1(
    const Eurydice_arr_d1 *public_key, const Eurydice_arr_ec *randomness);

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
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
Eurydice_arr_ec libcrux_iot_ml_kem_ind_cca_decapsulate_5d1(
    const Eurydice_arr_a8 *private_key, const Eurydice_arr_d1 *ciphertext);

/**
 Validate an ML-KEM public key.

 This implements the Modulus check in 7.2 2.
 Note that the size check in 7.2 1 is covered by the `PUBLIC_KEY_SIZE` in the
 `public_key` type.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_public_key
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector
with const generics
- K= 3
- PUBLIC_KEY_SIZE= 1184
*/
bool libcrux_iot_ml_kem_ind_cca_validate_public_key_21(
    const Eurydice_arr_5f *public_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key_only
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_only_d3(
    const Eurydice_arr_7d *private_key);

/**
 Validate an ML-KEM private key.

 This implements the Hash check in 7.3 3.
 Note that the size checks in 7.2 1 and 2 are covered by the `SECRET_KEY_SIZE`
 and `CIPHERTEXT_SIZE` in the `private_key` and `ciphertext` types.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.validate_private_key
with types libcrux_iot_ml_kem_hash_functions_portable_PortableHash
with const generics
- K= 3
- SECRET_KEY_SIZE= 2400
- CIPHERTEXT_SIZE= 1088
*/
bool libcrux_iot_ml_kem_ind_cca_validate_private_key_88(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *_ciphertext);

/**
 Packed API

 Generate a key pair.

 Depending on the `Vector` and `Hasher` used, this requires different hardware
 features
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.generate_keypair
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
- K= 3
- K_SQUARED= 9
- CPA_PRIVATE_KEY_SIZE= 1152
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
- ETA1= 2
- ETA1_RANDOMNESS_SIZE= 128
- PRF_OUTPUT_SIZE1= 384
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_e2
libcrux_iot_ml_kem_ind_cca_generate_keypair_de0(
    const Eurydice_arr_c7 *randomness);

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.encapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
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
tuple_bf libcrux_iot_ml_kem_ind_cca_encapsulate_fe0(
    const Eurydice_arr_5f *public_key, const Eurydice_arr_ec *randomness);

/**
A monomorphic instance of libcrux_iot_ml_kem.ind_cca.decapsulate
with types libcrux_iot_ml_kem_vector_portable_vector_type_PortableVector,
libcrux_iot_ml_kem_hash_functions_portable_PortableHash,
libcrux_iot_ml_kem_variant_MlKem with const generics
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
Eurydice_arr_ec libcrux_iot_ml_kem_ind_cca_decapsulate_5d0(
    const Eurydice_arr_7d *private_key, const Eurydice_arr_2b *ciphertext);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_mlkem_portable_H_DEFINED
#endif /* internal_libcrux_iot_mlkem_portable_H */
