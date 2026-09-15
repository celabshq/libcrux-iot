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

static inline uint32_t core_num__u32__from_le_bytes(Eurydice_array_u8x4 x0);

static inline uint32_t core_num__u32__rotate_left(uint32_t x0, uint32_t x1);

static inline Eurydice_array_u8x4 core_num__u32__to_le_bytes(uint32_t x0);

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
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self);

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
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$168size_t]]

*/
Eurydice_arr_c5 libcrux_secrets_int_public_integers_classify_27_33(
    Eurydice_arr_c5 self);

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d42(
    const Eurydice_arr_c5 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d41(
    Eurydice_arr_c5 *a, core_ops_range_Range_87 r);

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_2c(
    const Eurydice_arr_c5 *a);

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f0(
    Eurydice_arr_c5 *a, size_t r);

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
A monomorphic instance of Eurydice.arr
with types uint8_t
with const generics
- $136size_t
*/
typedef struct Eurydice_arr_ff_s {
  uint8_t data[136U];
} Eurydice_arr_ff;

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
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_c8(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_87 r);

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
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $255size_t
*/
typedef struct Eurydice_arr_03_s {
  uint32_t data[255U];
} Eurydice_arr_03;

/**
A monomorphic instance of Eurydice.arr
with types uint32_t
with const generics
- $2size_t
*/
typedef struct Eurydice_arr_a0_s {
  uint32_t data[2U];
} Eurydice_arr_a0;

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
