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

#ifndef internal_libcrux_iot_mldsa_core_H
#define internal_libcrux_iot_mldsa_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_mldsa_core.h"

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct Option_87_s {
  Option_87_tags tag;
  size_t f0;
} Option_87;

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

static inline uint64_t core_num__u64__from_le_bytes(Eurydice_array_u8x8 x0);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_87_s {
  size_t start;
  size_t end;
} core_ops_range_Range_87;

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int64_t

*/
int64_t libcrux_secrets_int_public_integers_classify_27_b8(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_declassify_d8_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int64_t libcrux_secrets_int_as_i64_36(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i64}
*/
uint64_t libcrux_secrets_int_as_u64_60(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
int32_t libcrux_secrets_int_as_i32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i64}
*/
int32_t libcrux_secrets_int_as_i32_60(int64_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int32_t libcrux_secrets_int_as_i32_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
uint8_t libcrux_secrets_int_as_u8_36(int32_t self);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $4627size_t
*/
typedef Eurydice_arr_930 libcrux_iot_ml_dsa_types_MLDSASignature_06;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 4627
*/
const Eurydice_arr_930 *libcrux_iot_ml_dsa_types_as_ref_ad_f1(
    const Eurydice_arr_930 *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 2592
*/
const Eurydice_arr_43 *libcrux_iot_ml_dsa_types_as_ref_e9_c6(
    const Eurydice_arr_43 *self);

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_arr uint8_t[[$64size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_56(const Eurydice_arr_c7 *val);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$64size_t]]

*/
const Eurydice_arr_c7 *libcrux_secrets_int_public_integers_classify_ref_c5_56(
    const Eurydice_arr_c7 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$2592size_t]]

*/
const Eurydice_arr_43 *libcrux_secrets_int_public_integers_classify_ref_c5_81(
    const Eurydice_arr_43 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_11(
    const Eurydice_arr_930 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_fc(
    const Eurydice_arr_43 *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4896
*/
const Eurydice_arr_e2 *libcrux_iot_ml_dsa_types_as_ref_f8_72(
    const Eurydice_arr_e2 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f7(
    const Eurydice_arr_e2 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4627
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_11(
    Eurydice_arr_930 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_6c
with const generics
- $8size_t
*/
typedef struct Eurydice_arr_81_s {
  Eurydice_arr_6c data[8U];
} Eurydice_arr_81;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_20 Eurydice_array_to_slice_shared_861(
    const Eurydice_arr_81 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_20 Eurydice_array_to_slice_mut_861(Eurydice_arr_81 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1024size_t
*/
typedef struct Eurydice_arr_1b_s {
  uint8_t data[1024U];
} Eurydice_arr_1b;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_68(
    const Eurydice_arr_1b *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1024
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_68(Eurydice_arr_1b *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 4627
*/
Eurydice_arr_930 libcrux_iot_ml_dsa_types_zero_ad_f1(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 2592
*/
Eurydice_arr_43 libcrux_iot_ml_dsa_types_new_e9_c6(Eurydice_arr_43 value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4896
*/
Eurydice_arr_e2 libcrux_iot_ml_dsa_types_new_f8_72(Eurydice_arr_e2 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2592
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_fc(Eurydice_arr_43 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4896
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f7(Eurydice_arr_e2 *a);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $3309size_t
*/
typedef Eurydice_arr_0c libcrux_iot_ml_dsa_types_MLDSASignature_aa;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 3309
*/
const Eurydice_arr_0c *libcrux_iot_ml_dsa_types_as_ref_ad_5c(
    const Eurydice_arr_0c *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1952
*/
const Eurydice_arr_29 *libcrux_iot_ml_dsa_types_as_ref_e9_a2(
    const Eurydice_arr_29 *self);

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_arr uint8_t[[$48size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_69(const Eurydice_arr_65 *val);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$48size_t]]

*/
const Eurydice_arr_65 *libcrux_secrets_int_public_integers_classify_ref_c5_69(
    const Eurydice_arr_65 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$1952size_t]]

*/
const Eurydice_arr_29 *libcrux_secrets_int_public_integers_classify_ref_c5_bb(
    const Eurydice_arr_29 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_6b(
    const Eurydice_arr_0c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_37(
    const Eurydice_arr_29 *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 4032
*/
const Eurydice_arr_24 *libcrux_iot_ml_dsa_types_as_ref_f8_e5(
    const Eurydice_arr_24 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_980(
    const Eurydice_arr_24 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 3309
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_6b(Eurydice_arr_0c *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_6c
with const generics
- $6size_t
*/
typedef struct Eurydice_arr_5d_s {
  Eurydice_arr_6c data[6U];
} Eurydice_arr_5d;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_shared_20 Eurydice_array_to_slice_shared_860(
    const Eurydice_arr_5d *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$48size_t]]

*/
const Eurydice_arr_65 *libcrux_secrets_int_public_integers_declassify_ref_ad_69(
    const Eurydice_arr_65 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 6
*/
Eurydice_dst_ref_mut_20 Eurydice_array_to_slice_mut_860(Eurydice_arr_5d *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 48
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_9f0(
    const Eurydice_arr_65 *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 3309
*/
Eurydice_arr_0c libcrux_iot_ml_dsa_types_zero_ad_5c(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1952
*/
Eurydice_arr_29 libcrux_iot_ml_dsa_types_new_e9_a2(Eurydice_arr_29 value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 4032
*/
Eurydice_arr_24 libcrux_iot_ml_dsa_types_new_f8_e5(Eurydice_arr_24 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1952
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_37(Eurydice_arr_29 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 4032
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_98(Eurydice_arr_24 *a);

/**
A monomorphic instance of libcrux_iot_ml_dsa.types.MLDSASignature
with const generics
- $2420size_t
*/
typedef Eurydice_arr_85 libcrux_iot_ml_dsa_types_MLDSASignature_28;

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_ad
with const generics
- SIZE= 2420
*/
const Eurydice_arr_85 *libcrux_iot_ml_dsa_types_as_ref_ad_37(
    const Eurydice_arr_85 *self);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_e9
with const generics
- SIZE= 1312
*/
const Eurydice_arr_02 *libcrux_iot_ml_dsa_types_as_ref_e9_7d(
    const Eurydice_arr_02 *self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int32_t[[$256size_t]]

*/
Eurydice_arr_6c libcrux_secrets_int_public_integers_classify_27_9d(
    Eurydice_arr_6c self);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int32_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_subslice_to_shared_25(
    const Eurydice_arr_d0 *a, size_t r);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a ([T])> for
&'a ([T])}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_6d
with types int32_t

*/
Eurydice_dst_ref_shared_83
libcrux_secrets_int_classify_public_classify_ref_6d_a8(
    Eurydice_dst_ref_shared_83 self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_31 libcrux_secrets_int_public_integers_classify_27_78(
    Eurydice_arr_31 self);

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_arr uint8_t[[$32size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_4b(const Eurydice_arr_ec *val);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$32size_t]]

*/
const Eurydice_arr_ec *libcrux_secrets_int_public_integers_classify_ref_c5_4b(
    const Eurydice_arr_ec *self);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$64size_t]]

*/
const Eurydice_arr_c7 *libcrux_secrets_int_public_integers_declassify_ref_ad_56(
    const Eurydice_arr_c7 *self);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$1312size_t]]

*/
const Eurydice_arr_02 *libcrux_secrets_int_public_integers_classify_ref_c5_8d(
    const Eurydice_arr_02 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_0d(
    const Eurydice_arr_85 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_9f(
    const Eurydice_arr_02 *a);

/**
 A reference to the raw byte array.
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.as_ref_f8
with const generics
- SIZE= 2560
*/
const Eurydice_arr_10 *libcrux_iot_ml_dsa_types_as_ref_f8_ab(
    const Eurydice_arr_10 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_34(
    const Eurydice_arr_10 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2420
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_0d(Eurydice_arr_85 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_6c
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_b7_s {
  Eurydice_arr_6c data[4U];
} Eurydice_arr_b7;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_20 Eurydice_array_to_slice_shared_86(
    const Eurydice_arr_b7 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$32size_t]]

*/
const Eurydice_arr_ec *libcrux_secrets_int_public_integers_declassify_ref_ad_4b(
    const Eurydice_arr_ec *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$256size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_20 Eurydice_array_to_slice_mut_86(Eurydice_arr_b7 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_83 Eurydice_array_to_subslice_mut_44(
    Eurydice_arr_6c *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_slice_shared_af(
    const Eurydice_arr_6c *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f(
    const Eurydice_arr_ff *a, size_t r);

/**
A monomorphic instance of core.result.Result
with types Eurydice_array_u8x8, core_array_TryFromSliceError

*/
typedef struct Result_8e_s {
  Result_8e_tags tag;
  union {
    Eurydice_array_u8x8 case_Ok;
    TryFromSliceError case_Err;
  } val;
} Result_8e;

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $768size_t
*/
typedef struct Eurydice_arr_d2_s {
  uint8_t data[768U];
} Eurydice_arr_d2;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 768
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_27(
    const Eurydice_arr_d2 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 768
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_27(Eurydice_arr_d2 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 640
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_4f(
    const Eurydice_arr_20 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 640
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_4f(Eurydice_arr_20 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 576
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_8a(
    const Eurydice_arr_22 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 576
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_8a(Eurydice_arr_22 *a);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$11size_t]]

*/
const Eurydice_arr_c9 *libcrux_secrets_int_public_integers_classify_ref_c5_95(
    const Eurydice_arr_c9 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 11
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_2f(
    const Eurydice_arr_c9 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_82_s {
  uint8_t data[1U];
} Eurydice_arr_82;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_79(
    const Eurydice_arr_82 *a);

/**
 Init with zero
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASignature<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.zero_ad
with const generics
- SIZE= 2420
*/
Eurydice_arr_85 libcrux_iot_ml_dsa_types_zero_ad_37(void);

/**
 Build
*/
/**
This function found in impl
{libcrux_iot_ml_dsa::types::MLDSAVerificationKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_e9
with const generics
- SIZE= 1312
*/
Eurydice_arr_02 libcrux_iot_ml_dsa_types_new_e9_7d(Eurydice_arr_02 value);

/**
 Build
*/
/**
This function found in impl {libcrux_iot_ml_dsa::types::MLDSASigningKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_dsa.types.new_f8
with const generics
- SIZE= 2560
*/
Eurydice_arr_10 libcrux_iot_ml_dsa_types_new_f8_ab(Eurydice_arr_10 value);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1312
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_9f0(
    Eurydice_arr_02 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 2560
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_34(Eurydice_arr_10 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_17(
    const Eurydice_arr_c7 *a);

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice uint8_t

*/
void libcrux_secrets_mem_requests_ct_declassify_45(const uint8_t (*val)[]);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a ([T])> for
&'a ([T])}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_6d
with types uint8_t

*/
Eurydice_borrow_slice_u8 libcrux_secrets_int_classify_public_classify_ref_6d_90(
    Eurydice_borrow_slice_u8 self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 66
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f1(
    const Eurydice_arr_91 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_d0
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_93_s {
  Eurydice_arr_d0 data[4U];
} Eurydice_arr_93;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int32_t[[$263size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_33 Eurydice_array_to_slice_mut_7e(Eurydice_arr_93 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_d0, size_t

*/
typedef struct Eurydice_dst_ref_shared_33_s {
  const Eurydice_arr_d0 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_33;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 263
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_slice_shared_2c0(
    const Eurydice_arr_d0 *a);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr int32_t[[$263size_t]]

*/
const Eurydice_arr_d0 *libcrux_secrets_int_public_integers_classify_ref_c5_72(
    const Eurydice_arr_d0 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_2c(
    const Eurydice_arr_c5 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr uint8_t[[$168size_t]]

*/
const Eurydice_arr_c5 *libcrux_secrets_int_public_integers_declassify_ref_ad_33(
    const Eurydice_arr_c5 *self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types int32_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
int32_t with const generics
- N= 263
*/
Eurydice_dst_ref_mut_83 Eurydice_array_to_subslice_from_mut_11(
    Eurydice_arr_d0 *a, size_t r);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_ref_c5
with types Eurydice_arr uint8_t[[$34size_t]]

*/
const Eurydice_arr_31 *libcrux_secrets_int_public_integers_classify_ref_c5_78(
    const Eurydice_arr_31 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e9(
    const Eurydice_arr_31 *a);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a ([T])>
for &'a ([T])}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.declassify_ref_5c
with types uint8_t

*/
Eurydice_borrow_slice_u8
libcrux_secrets_int_classify_public_declassify_ref_5c_90(
    Eurydice_borrow_slice_u8 self);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_89_s {
  uint8_t data[128U];
} Eurydice_arr_89;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 128
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_78(
    const Eurydice_arr_89 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 128
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_78(Eurydice_arr_89 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_82(
    const Eurydice_array_u8x2 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_01(
    const Eurydice_arr_ec *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_subslice_shared_44(
    const Eurydice_arr_4d *a, core_ops_range_Range_87 r);

/**
This function found in impl {libcrux_secrets::traits::DeclassifyRef<&'a (T)> for
&'a (T)}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_ref_ad
with types Eurydice_arr int32_t[[$8size_t]]

*/
const Eurydice_arr_4d *libcrux_secrets_int_public_integers_declassify_ref_ad_70(
    const Eurydice_arr_4d *self);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_slice_shared_fd(
    const Eurydice_arr_4d *a);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_83 Eurydice_slice_subslice_shared_47(
    Eurydice_dst_ref_shared_83 s, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int32_t
with const generics
- N= 8
*/
Eurydice_dst_ref_mut_83 Eurydice_array_to_slice_mut_fd(Eurydice_arr_4d *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 66
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d42(
    Eurydice_arr_91 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d41(
    Eurydice_arr_31 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_58(Eurydice_arr_ff *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_2c(Eurydice_arr_c5 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 840
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_4c(Eurydice_arr_d1 *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_17(Eurydice_arr_c7 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$64size_t]]

*/
Eurydice_arr_c7 libcrux_secrets_int_public_integers_classify_27_56(
    Eurydice_arr_c7 self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_9f(Eurydice_arr_65 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$48size_t]]

*/
Eurydice_arr_65 libcrux_secrets_int_public_integers_classify_27_69(
    Eurydice_arr_65 self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_01(Eurydice_arr_ec *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_ec libcrux_secrets_int_public_integers_classify_27_4b(
    Eurydice_arr_ec self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_5e(Eurydice_arr_a2 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$28size_t]]

*/
Eurydice_arr_a2 libcrux_secrets_int_public_integers_classify_27_96(
    Eurydice_arr_a2 self);

/**
A monomorphic instance of Eurydice.slice_subslice_to_mut
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_to_mut_72(
    Eurydice_mut_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d41(
    const Eurydice_array_u8x4 *a, core_ops_range_Range_87 r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$136size_t]]

*/
Eurydice_arr_ff libcrux_secrets_int_public_integers_classify_27_94(
    Eurydice_arr_ff self);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d40(
    const Eurydice_arr_ff *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6d(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d40(
    Eurydice_arr_ff *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 136
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_58(
    const Eurydice_arr_ff *a);

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_72(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 136
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f(
    Eurydice_arr_ff *a, size_t r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_from_mut_6d(
    Eurydice_mut_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $200size_t
*/
typedef struct Eurydice_arr_5c_s {
  uint8_t data[200U];
} Eurydice_arr_5c;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d4(
    const Eurydice_arr_5c *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_15(Eurydice_arr_5c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_98(
    const Eurydice_array_u8x4 *a);

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_c8(
    Eurydice_mut_borrow_slice_u8 s, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_15(
    const Eurydice_arr_5c *a);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_c8(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d4(
    Eurydice_arr_5c *a, core_ops_range_Range_87 r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$200size_t]]

*/
Eurydice_arr_5c libcrux_secrets_int_public_integers_classify_27_df0(
    Eurydice_arr_5c self);

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $255size_t
*/
typedef struct Eurydice_arr_03_s {
  uint32_t data[255U];
} Eurydice_arr_03;

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint32_t[[$2size_t]]

*/
Eurydice_arr_a0 libcrux_secrets_int_public_integers_classify_27_aa(
    Eurydice_arr_a0 self);

#if defined(__cplusplus)
}
#endif

#define internal_libcrux_iot_mldsa_core_H_DEFINED
#endif /* internal_libcrux_iot_mldsa_core_H */
