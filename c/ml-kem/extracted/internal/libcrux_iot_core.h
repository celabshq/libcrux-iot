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

#ifndef internal_libcrux_iot_core_H
#define internal_libcrux_iot_core_H

#include "eurydice_glue.h"

#if defined(__cplusplus)
extern "C" {
#endif

#include "../libcrux_iot_core.h"

#define core_option_None 0
#define core_option_Some 1

typedef uint8_t core_option_Option_87_tags;

/**
A monomorphic instance of core.option.Option
with types size_t

*/
typedef struct core_option_Option_87_s {
  core_option_Option_87_tags tag;
  size_t f0;
} core_option_Option_87;

static inline int16_t core_num__i16__wrapping_add(int16_t x0, int16_t x1);

static inline int16_t core_num__i16__wrapping_mul(int16_t x0, int16_t x1);

static inline int16_t core_num__i16__wrapping_neg(int16_t x0);

static inline int16_t core_num__i16__wrapping_sub(int16_t x0, int16_t x1);

static inline int32_t core_num__i32__wrapping_add(int32_t x0, int32_t x1);

static inline int32_t core_num__i32__wrapping_mul(int32_t x0, int32_t x1);

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

static inline uint32_t core_num__u32__wrapping_add(uint32_t x0, uint32_t x1);

static inline uint32_t core_num__u32__wrapping_sub(uint32_t x0, uint32_t x1);

static inline uint64_t core_num__u64__wrapping_add(uint64_t x0, uint64_t x1);

static inline uint64_t core_num__u64__wrapping_mul(uint64_t x0, uint64_t x1);

static inline size_t core_num__usize__wrapping_add(size_t x0, size_t x1);

/**
A monomorphic instance of core.ops.range.Range
with types size_t

*/
typedef struct core_ops_range_Range_87_s {
  size_t start;
  size_t end;
} core_ops_range_Range_87;

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

void libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs_c, Eurydice_borrow_slice_u8 rhs_c,
    Eurydice_borrow_slice_u8 lhs_s, Eurydice_borrow_slice_u8 rhs_s,
    Eurydice_mut_borrow_slice_u8 out);

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_BYTES_PER_RING_ELEMENT \
  (LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U)

#define LIBCRUX_IOT_ML_KEM_CONSTANTS_CPA_PKE_KEY_GENERATION_SEED_SIZE \
  ((size_t)32U)

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_27_df(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
uint32_t libcrux_secrets_int_as_u32_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_27_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int16_t libcrux_secrets_int_as_i16_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int16_t libcrux_secrets_int_as_i16_36(int32_t self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int32_t libcrux_secrets_int_as_i32_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int32_t libcrux_secrets_int_as_i32_b8(uint32_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint16_t libcrux_secrets_int_as_u16_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
int16_t libcrux_secrets_int_as_i16_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint8_t libcrux_secrets_int_as_u8_f5(int16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int16_t libcrux_secrets_int_as_i16_59(uint8_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self);

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d49(
    const Eurydice_arr_a8 *a, core_ops_range_Range_87 r);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_08
with const generics
- SIZE= 1568
*/
Eurydice_arr_d1 libcrux_iot_ml_kem_types_from_08_d9(Eurydice_arr_d1 value);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_iot_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_d9
with const generics
- PRIVATE_KEY_SIZE= 3168
- PUBLIC_KEY_SIZE= 1568
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_3f libcrux_iot_ml_kem_types_from_d9_70(
    Eurydice_arr_a8 sk, Eurydice_arr_d1 pk);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_c2
with const generics
- SIZE= 3168
*/
Eurydice_arr_a8 libcrux_iot_ml_kem_types_from_c2_0e(Eurydice_arr_a8 value);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1536size_t
*/
typedef struct Eurydice_arr_df_s {
  uint8_t data[1536U];
} Eurydice_arr_df;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_2f(
    const Eurydice_arr_df *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d48(
    Eurydice_arr_a8 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_2f(Eurydice_arr_df *a);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $272size_t
*/
typedef struct Eurydice_arr_5b_s {
  int16_t data[272U];
} Eurydice_arr_5b;

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types Eurydice_arr_5b, size_t

*/
typedef struct Eurydice_dst_ref_mut_df_s {
  Eurydice_arr_5b *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_df;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_5b
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_24_s {
  Eurydice_arr_5b data[4U];
} Eurydice_arr_24;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f22(Eurydice_arr_24 *a);

/**
A monomorphic instance of Eurydice.dst_ref_mut
with types size_t, size_t

*/
typedef struct Eurydice_dst_ref_mut_c30_s {
  size_t *ptr;
  size_t meta;
} Eurydice_dst_ref_mut_c30;

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_cc_s {
  size_t data[4U];
} Eurydice_arr_cc;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_4e(Eurydice_arr_cc *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_31
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_560_s {
  Eurydice_arr_31 data[4U];
} Eurydice_arr_560;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e2(
    const Eurydice_arr_560 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_c5, size_t

*/
typedef struct Eurydice_dst_ref_shared_c3_s {
  const Eurydice_arr_c5 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_c3;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c5
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_9c_s {
  Eurydice_arr_c5 data[4U];
} Eurydice_arr_9c;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b2(
    const Eurydice_arr_9c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b2(Eurydice_arr_9c *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types Eurydice_arr_79, size_t

*/
typedef struct Eurydice_dst_ref_shared_8c_s {
  const Eurydice_arr_79 *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_8c;

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_79
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_7c_s {
  Eurydice_arr_79 data[4U];
} Eurydice_arr_7c;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb2(
    const Eurydice_arr_7c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb2(Eurydice_arr_7c *a);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_cf
with const generics
- SIZE= 1568
*/
Eurydice_arr_d1 libcrux_iot_ml_kem_types_from_cf_d9(Eurydice_arr_d1 value);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_b50(
    const Eurydice_arr_d1 *a);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1568
*/
const Eurydice_arr_d1 *libcrux_iot_ml_kem_types_as_slice_63_d9(
    const Eurydice_arr_d1 *self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_b5(Eurydice_arr_d1 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $512size_t
*/
typedef struct Eurydice_arr_56_s {
  uint8_t data[512U];
} Eurydice_arr_56;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 512
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d48(
    const Eurydice_arr_56 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 512
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_92(Eurydice_arr_56 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_fa
with const generics
- $4size_t
*/
typedef struct Eurydice_arr_890_s {
  Eurydice_arr_fa data[4U];
} Eurydice_arr_890;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_b4 Eurydice_array_to_slice_shared_041(
    const Eurydice_arr_890 *a);

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_23(Eurydice_arr_890 *prf_inputs,
                                                  uint8_t domain_separator);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1600size_t
*/
typedef struct Eurydice_arr_140_s {
  uint8_t data[1600U];
} Eurydice_arr_140;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1600
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_72(
    const Eurydice_arr_140 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1568size_t]]

*/
Eurydice_arr_d1 libcrux_secrets_int_public_integers_classify_27_ac(
    Eurydice_arr_d1 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1600
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f2(
    Eurydice_arr_140 *a, size_t r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
Eurydice_arr_140 libcrux_iot_ml_kem_utils_into_padded_array_49(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f4(
    const Eurydice_arr_d1 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_213(
    const Eurydice_arr_d1 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_68(
    const Eurydice_arr_a8 *a);

typedef struct Eurydice_borrow_slice_u8_x4_s {
  Eurydice_borrow_slice_u8 fst;
  Eurydice_borrow_slice_u8 snd;
  Eurydice_borrow_slice_u8 thd;
  Eurydice_borrow_slice_u8 f3;
} Eurydice_borrow_slice_u8_x4;

typedef struct Eurydice_borrow_slice_u8_x2_s {
  Eurydice_borrow_slice_u8 fst;
  Eurydice_borrow_slice_u8 snd;
} Eurydice_borrow_slice_u8_x2;

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
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1536
- PUBLIC_KEY_SIZE= 1568
*/
Eurydice_borrow_slice_u8_x4 libcrux_iot_ml_kem_types_unpack_private_key_e3(
    Eurydice_borrow_slice_u8 private_key);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f3(
    const Eurydice_arr_5f *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_212(
    const Eurydice_arr_5f *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d47(
    const Eurydice_arr_7d *a, core_ops_range_Range_87 r);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_08
with const generics
- SIZE= 1184
*/
Eurydice_arr_5f libcrux_iot_ml_kem_types_from_08_3d(Eurydice_arr_5f value);

/**
 Create a new [`MlKemKeyPair`] from the secret and public key.
*/
/**
This function found in impl
{libcrux_iot_ml_kem::types::MlKemKeyPair<PRIVATE_KEY_SIZE, PUBLIC_KEY_SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_d9
with const generics
- PRIVATE_KEY_SIZE= 2400
- PUBLIC_KEY_SIZE= 1184
*/
libcrux_iot_ml_kem_types_MlKemKeyPair_e2 libcrux_iot_ml_kem_types_from_d9_bc(
    Eurydice_arr_7d sk, Eurydice_arr_5f pk);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_c2
with const generics
- SIZE= 2400
*/
Eurydice_arr_7d libcrux_iot_ml_kem_types_from_c2_79(Eurydice_arr_7d value);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1152size_t
*/
typedef struct Eurydice_arr_0e_s {
  uint8_t data[1152U];
} Eurydice_arr_0e;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f4(
    const Eurydice_arr_0e *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d46(
    Eurydice_arr_7d *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ff(Eurydice_arr_5f *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f4(Eurydice_arr_0e *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_5b
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_b1_s {
  Eurydice_arr_5b data[3U];
} Eurydice_arr_b1;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f21(Eurydice_arr_b1 *a);

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_eb_s {
  size_t data[3U];
} Eurydice_arr_eb;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_20(Eurydice_arr_eb *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_31
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_81_s {
  Eurydice_arr_31 data[3U];
} Eurydice_arr_81;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e1(
    const Eurydice_arr_81 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c5
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_2c_s {
  Eurydice_arr_c5 data[3U];
} Eurydice_arr_2c;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b1(
    const Eurydice_arr_2c *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b1(Eurydice_arr_2c *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_79
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_7e_s {
  Eurydice_arr_79 data[3U];
} Eurydice_arr_7e;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb1(
    const Eurydice_arr_7e *a);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb1(Eurydice_arr_7e *a);

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_cf
with const generics
- SIZE= 1088
*/
Eurydice_arr_2b libcrux_iot_ml_kem_types_from_cf_52(Eurydice_arr_2b value);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ff(
    const Eurydice_arr_5f *a);

/**
 A reference to the raw byte slice.
*/
/**
This function found in impl {libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.as_slice_63
with const generics
- SIZE= 1184
*/
const Eurydice_arr_5f *libcrux_iot_ml_kem_types_as_slice_63_3d(
    const Eurydice_arr_5f *self);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1184size_t]]

*/
Eurydice_arr_5f libcrux_secrets_int_public_integers_classify_27_c20(
    Eurydice_arr_5f self);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1088
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_06(Eurydice_arr_2b *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_fa
with const generics
- $3size_t
*/
typedef struct Eurydice_arr_801_s {
  Eurydice_arr_fa data[3U];
} Eurydice_arr_801;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_b4 Eurydice_array_to_slice_shared_040(
    const Eurydice_arr_801 *a);

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_78(Eurydice_arr_801 *prf_inputs,
                                                  uint8_t domain_separator);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $1120size_t
*/
typedef struct Eurydice_arr_af_s {
  uint8_t data[1120U];
} Eurydice_arr_af;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1120
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_81(
    const Eurydice_arr_af *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1088size_t]]

*/
Eurydice_arr_2b libcrux_secrets_int_public_integers_classify_27_53(
    Eurydice_arr_2b self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1120
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f1(
    Eurydice_arr_af *a, size_t r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
Eurydice_arr_af libcrux_iot_ml_kem_utils_into_padded_array_66(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f2(
    const Eurydice_arr_2b *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_211(
    const Eurydice_arr_2b *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_51(
    const Eurydice_arr_7d *a);

/**
 Unpack an incoming private key into it's different parts.

 We have this here in types to extract into a common core for C.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.unpack_private_key
with const generics
- CPA_SECRET_KEY_SIZE= 1152
- PUBLIC_KEY_SIZE= 1184
*/
Eurydice_borrow_slice_u8_x4 libcrux_iot_ml_kem_types_unpack_private_key_64(
    Eurydice_borrow_slice_u8 private_key);

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
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d43(
    Eurydice_arr_31 *a, core_ops_range_Range_87 r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
Eurydice_arr_31 libcrux_iot_ml_kem_utils_into_padded_array_de(
    Eurydice_borrow_slice_u8 slice);

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_31 libcrux_secrets_int_public_integers_declassify_d8_78(
    Eurydice_arr_31 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int16_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int16_t with const generics
- N= 272
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_to_shared_a9(
    const Eurydice_arr_5b *a, size_t r);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a ([T])> for
&'a ([T])}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_6d
with types int16_t

*/
Eurydice_borrow_slice_i16
libcrux_secrets_int_classify_public_classify_ref_6d_39(
    Eurydice_borrow_slice_i16 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f0(
    const Eurydice_arr_c7 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d45(
    const Eurydice_arr_c7 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_72(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d44(
    const Eurydice_arr_ec *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6d(
    Eurydice_borrow_slice_u8 s, size_t r);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$272size_t]]

*/
Eurydice_arr_5b libcrux_secrets_int_public_integers_classify_27_19(
    Eurydice_arr_5b self);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_5b
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_28_s {
  Eurydice_arr_5b data[1U];
} Eurydice_arr_28;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f2(Eurydice_arr_28 *a);

/**
A monomorphic instance of Eurydice.arr
with types size_t
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_58_s {
  size_t data[1U];
} Eurydice_arr_58;

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_31(Eurydice_arr_58 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_31
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_f4_s {
  Eurydice_arr_31 data[1U];
} Eurydice_arr_f4;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_f4 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_c5
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_88_s {
  Eurydice_arr_c5 data[1U];
} Eurydice_arr_88;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b(
    const Eurydice_arr_88 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d43(
    const Eurydice_arr_c5 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b(Eurydice_arr_88 *a);

/**
A monomorphic instance of Eurydice.arr
with types Eurydice_arr_79
with const generics
- $1size_t
*/
typedef struct Eurydice_arr_d8_s {
  Eurydice_arr_79 data[1U];
} Eurydice_arr_d8;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb(
    const Eurydice_arr_d8 *a);

/**
A monomorphic instance of Eurydice.dst_ref_shared
with types size_t, size_t

*/
typedef struct Eurydice_dst_ref_shared_c30_s {
  const size_t *ptr;
  size_t meta;
} Eurydice_dst_ref_shared_c30;

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 272
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_subslice_mut_e7(
    Eurydice_arr_5b *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 504
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d42(
    const Eurydice_arr_79 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb(Eurydice_arr_d8 *a);

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
- N= 33
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_b5(
    const Eurydice_arr_fa *a);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $256size_t
*/
typedef struct Eurydice_arr_04_s {
  int16_t data[256U];
} Eurydice_arr_04;

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 256
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_990(
    const Eurydice_arr_04 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $384size_t
*/
typedef struct Eurydice_arr_b2_s {
  uint8_t data[384U];
} Eurydice_arr_b2;

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 384
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d40(
    const Eurydice_arr_b2 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 384
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_a9(Eurydice_arr_b2 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 33
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d42(
    Eurydice_arr_fa *a, core_ops_range_Range_87 r);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
Eurydice_arr_fa libcrux_iot_ml_kem_utils_into_padded_array_29(
    Eurydice_borrow_slice_u8 slice);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_17(
    const Eurydice_arr_c7 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f(
    Eurydice_arr_c7 *a, size_t r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_01(
    const Eurydice_arr_ec *a);

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
Eurydice_arr_c7 libcrux_iot_ml_kem_utils_into_padded_array_c9(
    Eurydice_borrow_slice_u8 slice);

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
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_slice_shared_af(
    const Eurydice_arr_6c *a);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_83 Eurydice_slice_subslice_shared_47(
    Eurydice_dst_ref_shared_83 s, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_83 Eurydice_array_to_subslice_mut_44(
    Eurydice_arr_6c *a, core_ops_range_Range_87 r);

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
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_shared_e7(
    const Eurydice_arr_d6 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_borrow_slice_i16 Eurydice_slice_subslice_shared_a6(
    Eurydice_borrow_slice_i16 s, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 16
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_8a(
    Eurydice_arr_d6 *a);

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_d6 libcrux_secrets_int_public_integers_classify_27_4b0(
    Eurydice_arr_d6 self);

/**
A monomorphic instance of Eurydice.arr
with types int16_t
with const generics
- $128size_t
*/
typedef struct Eurydice_arr_34_s {
  int16_t data[128U];
} Eurydice_arr_34;

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice Eurydice_arr uint8_t[[$168size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_e40(
    const Eurydice_arr_c5 (*val)[]);

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice Eurydice_arr uint8_t[[$504size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_e4(
    const Eurydice_arr_79 (*val)[]);

/**
This function found in impl {libcrux_secrets::traits::ClassifyRefMut<&'a mut
(T)> for &'a mut (T)}
*/
/**
A monomorphic instance of
libcrux_secrets.int.classify_public.classify_ref_mut_a1 with types
Eurydice_dst_ref_mut uint8_t size_t

*/
Eurydice_mut_borrow_slice_u8 *
libcrux_secrets_int_classify_public_classify_ref_mut_a1_75(
    Eurydice_mut_borrow_slice_u8 *self);

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
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e9(
    const Eurydice_arr_31 *a);

/**
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_ff_s {
  uint8_t data[136U];
} Eurydice_arr_ff;

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

#define core_result_Ok 0
#define core_result_Err 1

typedef uint8_t core_result_Result_c7_tags;

/**
A monomorphic instance of core.result.Result
with types Eurydice_array_u8x4, core_array_TryFromSliceError

*/
typedef struct core_result_Result_c7_s {
  core_result_Result_c7_tags tag;
  union {
    Eurydice_array_u8x4 case_Ok;
    core_array_TryFromSliceError case_Err;
  } val;
} core_result_Result_c7;

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x4 core_result_unwrap_26_cc(core_result_Result_c7 self);

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
typedef struct Eurydice_arr_030_s {
  uint32_t data[255U];
} Eurydice_arr_030;

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

#define internal_libcrux_iot_core_H_DEFINED
#endif /* internal_libcrux_iot_core_H */
