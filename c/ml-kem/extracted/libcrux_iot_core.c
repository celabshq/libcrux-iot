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

#include "internal/libcrux_iot_core.h"

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t classify_27_de(uint16_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_declassify_d8_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
static KRML_MUSTINLINE uint16_t as_u16_59(uint8_t self) {
  return classify_27_de(
      (uint16_t)(uint32_t)libcrux_secrets_int_public_integers_declassify_d8_90(
          self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint8_t

*/
uint8_t libcrux_secrets_int_public_integers_classify_27_90(uint8_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint16_t

*/
static KRML_MUSTINLINE uint16_t declassify_d8_de(uint16_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
static KRML_MUSTINLINE uint8_t as_u8_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)(uint32_t)declassify_d8_de(self));
}

/**
 Return 1 if `value` is not zero and 0 otherwise.
*/
static KRML_NOINLINE uint8_t inz(uint8_t value) {
  uint16_t value0 = as_u16_59(value);
  uint8_t result =
      as_u8_ca((uint32_t)core_num__u16__wrapping_add(~value0, 1U) >> 8U);
  return (uint32_t)result & 1U;
}

static KRML_NOINLINE uint8_t is_non_zero(uint8_t value) { return inz(value); }

/**
 Return 1 if the bytes of `lhs` and `rhs` do not exactly
 match and 0 otherwise.
*/
static KRML_NOINLINE uint8_t compare(Eurydice_borrow_slice_u8 lhs,
                                     Eurydice_borrow_slice_u8 rhs) {
  uint8_t r = libcrux_secrets_int_public_integers_classify_27_90(0U);
  for (size_t i = (size_t)0U; i < lhs.meta; i++) {
    size_t i0 = i;
    uint8_t nr = (uint32_t)r | ((uint32_t)lhs.ptr[i0] ^ (uint32_t)rhs.ptr[i0]);
    r = nr;
  }
  return is_non_zero(r);
}

static KRML_NOINLINE uint8_t compare_ciphertexts_in_constant_time(
    Eurydice_borrow_slice_u8 lhs, Eurydice_borrow_slice_u8 rhs) {
  return compare(lhs, rhs);
}

/**
 If `selector` is not zero, return the bytes in `rhs`; return the bytes in
 `lhs` otherwise.
*/
static KRML_NOINLINE void select_ct(Eurydice_borrow_slice_u8 lhs,
                                    Eurydice_borrow_slice_u8 rhs,
                                    uint8_t selector,
                                    Eurydice_mut_borrow_slice_u8 out) {
  uint8_t mask = core_num__u8__wrapping_sub(is_non_zero(selector), 1U);
  for (size_t i = (size_t)0U; i < lhs.meta; i++) {
    size_t i0 = i;
    uint8_t outi = ((uint32_t)lhs.ptr[i0] & (uint32_t)mask) |
                   ((uint32_t)rhs.ptr[i0] & (~(uint32_t)mask & 0xFFU));
    out.ptr[i0] = outi;
  }
}

static KRML_NOINLINE void select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs, Eurydice_borrow_slice_u8 rhs,
    uint8_t selector, Eurydice_mut_borrow_slice_u8 out) {
  select_ct(lhs, rhs, selector, out);
}

KRML_NOINLINE void
libcrux_iot_ml_kem_constant_time_ops_compare_ciphertexts_select_shared_secret_in_constant_time(
    Eurydice_borrow_slice_u8 lhs_c, Eurydice_borrow_slice_u8 rhs_c,
    Eurydice_borrow_slice_u8 lhs_s, Eurydice_borrow_slice_u8 rhs_s,
    Eurydice_mut_borrow_slice_u8 out) {
  uint8_t selector = compare_ciphertexts_in_constant_time(lhs_c, rhs_c);
  select_shared_secret_in_constant_time(lhs_s, rhs_s, selector, out);
}

/**
 K * BITS_PER_RING_ELEMENT / 8

 [eurydice] Note that we can't use const generics here because that breaks
            C extraction with eurydice.
*/
size_t libcrux_iot_ml_kem_constants_ranked_bytes_per_ring_element(size_t rank) {
  return rank * LIBCRUX_IOT_ML_KEM_CONSTANTS_BITS_PER_RING_ELEMENT / (size_t)8U;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t classify_27_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint32_t

*/
static KRML_MUSTINLINE uint32_t declassify_d8_df(uint32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
uint64_t libcrux_secrets_int_as_u64_b8(uint32_t self) {
  return classify_27_49((uint64_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types uint32_t

*/
uint32_t libcrux_secrets_int_public_integers_classify_27_df(uint32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types uint64_t

*/
static KRML_MUSTINLINE uint64_t declassify_d8_49(uint64_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for u64}
*/
uint32_t libcrux_secrets_int_as_u32_a3(uint64_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)declassify_d8_49(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
uint32_t libcrux_secrets_int_as_u32_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_df(
      (uint32_t)libcrux_secrets_int_public_integers_declassify_d8_90(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_classify_27_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int16_t libcrux_secrets_int_as_i16_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int32_t

*/
static KRML_MUSTINLINE int32_t declassify_d8_a8(int32_t self) { return self; }

/**
This function found in impl {libcrux_secrets::int::CastOps for i32}
*/
int16_t libcrux_secrets_int_as_i16_36(int32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)declassify_d8_a8(self));
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types int32_t

*/
int32_t libcrux_secrets_int_public_integers_classify_27_a8(int32_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types int16_t

*/
int16_t libcrux_secrets_int_public_integers_declassify_d8_39(int16_t self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int32_t libcrux_secrets_int_as_i32_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u32}
*/
int32_t libcrux_secrets_int_as_i32_b8(uint32_t self) {
  return libcrux_secrets_int_public_integers_classify_27_a8(
      (int32_t)declassify_d8_df(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint16_t libcrux_secrets_int_as_u16_f5(int16_t self) {
  return classify_27_de(
      (uint16_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
int16_t libcrux_secrets_int_as_i16_ca(uint16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)(uint32_t)declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
uint8_t libcrux_secrets_int_as_u8_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_90(
      (uint8_t)libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u8}
*/
int16_t libcrux_secrets_int_as_i16_59(uint8_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      (int16_t)(uint32_t)libcrux_secrets_int_public_integers_declassify_d8_90(
          self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for u16}
*/
uint64_t libcrux_secrets_int_as_u64_ca(uint16_t self) {
  return classify_27_49((uint64_t)(uint32_t)declassify_d8_de(self));
}

/**
This function found in impl {libcrux_secrets::int::CastOps for i16}
*/
int16_t libcrux_secrets_int_as_i16_f5(int16_t self) {
  return libcrux_secrets_int_public_integers_classify_27_39(
      libcrux_secrets_int_public_integers_declassify_d8_39(self));
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d49(
    const Eurydice_arr_a8 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_08
with const generics
- SIZE= 1568
*/
Eurydice_arr_d1 libcrux_iot_ml_kem_types_from_08_d9(Eurydice_arr_d1 value) {
  return value;
}

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
    Eurydice_arr_a8 sk, Eurydice_arr_d1 pk) {
  return (KRML_CLITERAL(libcrux_iot_ml_kem_types_MlKemKeyPair_3f){.sk = sk,
                                                                  .pk = pk});
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_c2
with const generics
- SIZE= 3168
*/
Eurydice_arr_a8 libcrux_iot_ml_kem_types_from_c2_0e(Eurydice_arr_a8 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_2f(
    const Eurydice_arr_df *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1536U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 3168
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d48(
    Eurydice_arr_a8 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1536
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_2f(
    Eurydice_arr_df *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1536U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f22(Eurydice_arr_24 *a) {
  Eurydice_dst_ref_mut_df lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_4e(Eurydice_arr_cc *a) {
  Eurydice_dst_ref_mut_c30 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e2(
    const Eurydice_arr_560 *a) {
  Eurydice_dst_ref_shared_cf lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b2(
    const Eurydice_arr_9c *a) {
  Eurydice_dst_ref_shared_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b2(Eurydice_arr_9c *a) {
  Eurydice_dst_ref_mut_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb2(
    const Eurydice_arr_7c *a) {
  Eurydice_dst_ref_shared_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb2(Eurydice_arr_7c *a) {
  Eurydice_dst_ref_mut_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_cf
with const generics
- SIZE= 1568
*/
Eurydice_arr_d1 libcrux_iot_ml_kem_types_from_cf_d9(Eurydice_arr_d1 value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_b50(
    const Eurydice_arr_d1 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1568U;
  return lit;
}

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
    const Eurydice_arr_d1 *self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1568
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_b5(
    Eurydice_arr_d1 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1568U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 512
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d48(
    const Eurydice_arr_56 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 512
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_92(
    Eurydice_arr_56 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)512U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 4
*/
Eurydice_dst_ref_shared_b4 Eurydice_array_to_slice_shared_041(
    const Eurydice_arr_890 *a) {
  Eurydice_dst_ref_shared_b4 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 4
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_23(Eurydice_arr_890 *prf_inputs,
                                                  uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)4U; i++) {
    size_t i0 = i;
    prf_inputs->data[i0].data[32U] =
        libcrux_secrets_int_public_integers_classify_27_90(domain_separator);
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1600
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_72(
    const Eurydice_arr_140 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1600U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1568size_t]]

*/
Eurydice_arr_d1 libcrux_secrets_int_public_integers_classify_27_ac(
    Eurydice_arr_d1 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1600
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f2(
    Eurydice_arr_140 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)1600U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1600
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_d47(
    Eurydice_arr_140 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1600
*/
Eurydice_arr_140 libcrux_iot_ml_kem_utils_into_padded_array_49(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_140 out;
  uint8_t repeat_expression[1600U];
  for (size_t i = (size_t)0U; i < (size_t)1600U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)1600U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_d47(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f4(
    const Eurydice_arr_d1 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1568U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1568
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_213(
    const Eurydice_arr_d1 *a, size_t r) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 3168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_68(
    const Eurydice_arr_a8 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3168U;
  return lit;
}

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
    Eurydice_borrow_slice_u8 self) {
  return self;
}

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
    Eurydice_borrow_slice_u8 private_key) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1536U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 secret_key0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1568U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____1.fst;
  Eurydice_borrow_slice_u8 secret_key = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____2.snd;
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8_x4){
      .fst = ind_cpa_secret_key,
      .snd = libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          ind_cpa_public_key),
      .thd = libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          ind_cpa_public_key_hash),
      .f3 = implicit_rejection_value});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f3(
    const Eurydice_arr_5f *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1184U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_212(
    const Eurydice_arr_5f *a, size_t r) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d47(
    const Eurydice_arr_7d *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPublicKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_08
with const generics
- SIZE= 1184
*/
Eurydice_arr_5f libcrux_iot_ml_kem_types_from_08_3d(Eurydice_arr_5f value) {
  return value;
}

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
    Eurydice_arr_7d sk, Eurydice_arr_5f pk) {
  return (KRML_CLITERAL(libcrux_iot_ml_kem_types_MlKemKeyPair_e2){.sk = sk,
                                                                  .pk = pk});
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemPrivateKey<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_c2
with const generics
- SIZE= 2400
*/
Eurydice_arr_7d libcrux_iot_ml_kem_types_from_c2_79(Eurydice_arr_7d value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_f4(
    const Eurydice_arr_0e *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1152U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 2400
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d46(
    Eurydice_arr_7d *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_ff(
    Eurydice_arr_5f *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1184U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1152
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_f4(
    Eurydice_arr_0e *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1152U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f21(Eurydice_arr_b1 *a) {
  Eurydice_dst_ref_mut_df lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_20(Eurydice_arr_eb *a) {
  Eurydice_dst_ref_mut_c30 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e1(
    const Eurydice_arr_81 *a) {
  Eurydice_dst_ref_shared_cf lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b1(
    const Eurydice_arr_2c *a) {
  Eurydice_dst_ref_shared_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b1(Eurydice_arr_2c *a) {
  Eurydice_dst_ref_mut_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb1(
    const Eurydice_arr_7e *a) {
  Eurydice_dst_ref_shared_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb1(Eurydice_arr_7e *a) {
  Eurydice_dst_ref_mut_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
This function found in impl {core::convert::From<[u8; SIZE]> for
libcrux_iot_ml_kem::types::MlKemCiphertext<SIZE>}
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.types.from_cf
with const generics
- SIZE= 1088
*/
Eurydice_arr_2b libcrux_iot_ml_kem_types_from_cf_52(Eurydice_arr_2b value) {
  return value;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1184
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_ff(
    const Eurydice_arr_5f *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1184U;
  return lit;
}

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
    const Eurydice_arr_5f *self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1184size_t]]

*/
Eurydice_arr_5f libcrux_secrets_int_public_integers_classify_27_c20(
    Eurydice_arr_5f self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 1088
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_06(
    Eurydice_arr_2b *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1088U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$33size_t]]
with const generics
- N= 3
*/
Eurydice_dst_ref_shared_b4 Eurydice_array_to_slice_shared_040(
    const Eurydice_arr_801 *a) {
  Eurydice_dst_ref_shared_b4 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)3U;
  return lit;
}

/**
A monomorphic instance of libcrux_iot_ml_kem.utils.prf_input_inc
with const generics
- K= 3
*/
uint8_t libcrux_iot_ml_kem_utils_prf_input_inc_78(Eurydice_arr_801 *prf_inputs,
                                                  uint8_t domain_separator) {
  for (size_t i = (size_t)0U; i < (size_t)3U; i++) {
    size_t i0 = i;
    prf_inputs->data[i0].data[32U] =
        libcrux_secrets_int_public_integers_classify_27_90(domain_separator);
    domain_separator = (uint32_t)domain_separator + 1U;
  }
  return domain_separator;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 1120
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_81(
    const Eurydice_arr_af *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1120U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$1088size_t]]

*/
Eurydice_arr_2b libcrux_secrets_int_public_integers_classify_27_53(
    Eurydice_arr_2b self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1120
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f1(
    Eurydice_arr_af *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){
      .ptr = a->data + r, .meta = (size_t)1120U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 1120
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_d45(
    Eurydice_arr_af *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 1120
*/
Eurydice_arr_af libcrux_iot_ml_kem_utils_into_padded_array_66(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_af out;
  uint8_t repeat_expression[1120U];
  for (size_t i = (size_t)0U; i < (size_t)1120U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)1120U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_d45(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f2(
    const Eurydice_arr_2b *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)1088U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 1088
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_to_shared_211(
    const Eurydice_arr_2b *a, size_t r) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 2400
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_51(
    const Eurydice_arr_7d *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)2400U;
  return lit;
}

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
    Eurydice_borrow_slice_u8 private_key) {
  Eurydice_borrow_slice_u8_x2 uu____0 = Eurydice_slice_split_at(
      private_key, (size_t)1152U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_secret_key = uu____0.fst;
  Eurydice_borrow_slice_u8 secret_key0 = uu____0.snd;
  Eurydice_borrow_slice_u8_x2 uu____1 = Eurydice_slice_split_at(
      secret_key0, (size_t)1184U, uint8_t, Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key = uu____1.fst;
  Eurydice_borrow_slice_u8 secret_key = uu____1.snd;
  Eurydice_borrow_slice_u8_x2 uu____2 = Eurydice_slice_split_at(
      secret_key, LIBCRUX_IOT_ML_KEM_CONSTANTS_H_DIGEST_SIZE, uint8_t,
      Eurydice_borrow_slice_u8_x2);
  Eurydice_borrow_slice_u8 ind_cpa_public_key_hash = uu____2.fst;
  Eurydice_borrow_slice_u8 implicit_rejection_value = uu____2.snd;
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8_x4){
      .fst = ind_cpa_secret_key,
      .snd = libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          ind_cpa_public_key),
      .thd = libcrux_secrets_int_classify_public_declassify_ref_5c_90(
          ind_cpa_public_key_hash),
      .f3 = implicit_rejection_value});
}

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice uint8_t

*/
void libcrux_secrets_mem_requests_ct_declassify_45(const uint8_t (*val)[]) {}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 34
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d43(
    Eurydice_arr_31 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 34
*/
Eurydice_arr_31 libcrux_iot_ml_kem_utils_into_padded_array_de(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_31 out;
  uint8_t repeat_expression[34U];
  for (size_t i = (size_t)0U; i < (size_t)34U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)34U * sizeof(uint8_t));
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d43(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
This function found in impl {libcrux_secrets::traits::Declassify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.declassify_d8
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_31 libcrux_secrets_int_public_integers_declassify_d8_78(
    Eurydice_arr_31 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_to_shared
with types int16_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
int16_t with const generics
- N= 272
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_to_shared_a9(
    const Eurydice_arr_5b *a, size_t r) {
  Eurydice_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = r;
  return lit;
}

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
    Eurydice_borrow_slice_i16 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_from_shared_5f0(
    const Eurydice_arr_c7 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r,
                                                  .meta = (size_t)64U - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d45(
    const Eurydice_arr_c7 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_to_shared
with types uint8_t, core_ops_range_RangeTo size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_to_shared_72(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr, .meta = r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d44(
    const Eurydice_arr_ec *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_shared
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_from_shared_6d(
    Eurydice_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r,
                                                  .meta = s.meta - r});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$272size_t]]

*/
Eurydice_arr_5b libcrux_secrets_int_public_integers_classify_27_19(
    Eurydice_arr_5b self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr int16_t[[$272size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_df Eurydice_array_to_slice_mut_f2(Eurydice_arr_28 *a) {
  Eurydice_dst_ref_mut_df lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types size_t
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_c30 Eurydice_array_to_slice_mut_31(Eurydice_arr_58 *a) {
  Eurydice_dst_ref_mut_c30 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$34size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_cf Eurydice_array_to_slice_shared_6e(
    const Eurydice_arr_f4 *a) {
  Eurydice_dst_ref_shared_cf lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_c3 Eurydice_array_to_slice_shared_1b(
    const Eurydice_arr_88 *a) {
  Eurydice_dst_ref_shared_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 168
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d43(
    const Eurydice_arr_c5 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$168size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_c3 Eurydice_array_to_slice_mut_1b(Eurydice_arr_88 *a) {
  Eurydice_dst_ref_mut_c3 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_shared_8c Eurydice_array_to_slice_shared_eb(
    const Eurydice_arr_d8 *a) {
  Eurydice_dst_ref_shared_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 272
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_subslice_mut_e7(
    Eurydice_arr_5b *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_i16){
      .ptr = a->data + r.start, .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 504
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d42(
    const Eurydice_arr_79 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types Eurydice_arr uint8_t[[$504size_t]]
with const generics
- N= 1
*/
Eurydice_dst_ref_mut_8c Eurydice_array_to_slice_mut_eb(Eurydice_arr_d8 *a) {
  Eurydice_dst_ref_mut_8c lit;
  lit.ptr = a->data;
  lit.meta = (size_t)1U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 128
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_78(
    const Eurydice_arr_89 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 128
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_78(
    Eurydice_arr_89 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)128U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 33
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_b5(
    const Eurydice_arr_fa *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)33U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int16_t
with const generics
- N= 256
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_slice_shared_990(
    const Eurydice_arr_04 *a) {
  Eurydice_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 384
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d40(
    const Eurydice_arr_b2 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 384
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_a9(
    Eurydice_arr_b2 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)384U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 33
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d42(
    Eurydice_arr_fa *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 33
*/
Eurydice_arr_fa libcrux_iot_ml_kem_utils_into_padded_array_29(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_fa out;
  uint8_t repeat_expression[33U];
  for (size_t i = (size_t)0U; i < (size_t)33U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)33U * sizeof(uint8_t));
  Eurydice_slice_copy(Eurydice_array_to_subslice_mut_d42(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 64
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_17(
    const Eurydice_arr_c7 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_from_mut_5f(
    Eurydice_arr_c7 *a, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r,
                                                      .meta = (size_t)64U - r});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 32
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_01(
    const Eurydice_arr_ec *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 64
*/
static Eurydice_mut_borrow_slice_u8 array_to_subslice_mut_d40(
    Eurydice_arr_c7 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
 Pad the `slice` with `0`s at the end.
*/
/**
A monomorphic instance of libcrux_iot_ml_kem.utils.into_padded_array
with const generics
- LEN= 64
*/
Eurydice_arr_c7 libcrux_iot_ml_kem_utils_into_padded_array_c9(
    Eurydice_borrow_slice_u8 slice) {
  Eurydice_arr_c7 out;
  uint8_t repeat_expression[64U];
  for (size_t i = (size_t)0U; i < (size_t)64U; i++) {
    repeat_expression[i] =
        libcrux_secrets_int_public_integers_classify_27_90(0U);
  }
  memcpy(out.data, repeat_expression, (size_t)64U * sizeof(uint8_t));
  Eurydice_slice_copy(array_to_subslice_mut_d40(
                          &out, (KRML_CLITERAL(core_ops_range_Range_87){
                                    .start = (size_t)0U, .end = slice.meta})),
                      slice, uint8_t);
  return out;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_shared_83 Eurydice_array_to_slice_shared_af(
    const Eurydice_arr_6c *a) {
  Eurydice_dst_ref_shared_83 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)256U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t

*/
Eurydice_dst_ref_shared_83 Eurydice_slice_subslice_shared_47(
    Eurydice_dst_ref_shared_83 s, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_shared_83){.ptr = s.ptr + r.start,
                                                    .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types int32_t, core_ops_range_Range size_t, Eurydice_derefed_slice int32_t
with const generics
- N= 256
*/
Eurydice_dst_ref_mut_83 Eurydice_array_to_subslice_mut_44(
    Eurydice_arr_6c *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_dst_ref_mut_83){.ptr = a->data + r.start,
                                                 .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::ClassifyRef<&'a ([T])> for
&'a ([T])}
*/
/**
A monomorphic instance of libcrux_secrets.int.classify_public.classify_ref_6d
with types uint8_t

*/
Eurydice_borrow_slice_u8 libcrux_secrets_int_classify_public_classify_ref_6d_90(
    Eurydice_borrow_slice_u8 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t
with const generics
- N= 16
*/
Eurydice_borrow_slice_i16 Eurydice_array_to_subslice_shared_e7(
    const Eurydice_arr_d6 *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_i16){.ptr = a->data + r.start,
                                                   .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types int16_t, core_ops_range_Range size_t, Eurydice_derefed_slice int16_t

*/
Eurydice_borrow_slice_i16 Eurydice_slice_subslice_shared_a6(
    Eurydice_borrow_slice_i16 s, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_i16){.ptr = s.ptr + r.start,
                                                   .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types int16_t
with const generics
- N= 16
*/
Eurydice_mut_borrow_slice_i16 Eurydice_array_to_slice_mut_8a(
    Eurydice_arr_d6 *a) {
  Eurydice_mut_borrow_slice_i16 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)16U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr int16_t[[$16size_t]]

*/
Eurydice_arr_d6 libcrux_secrets_int_public_integers_classify_27_4b0(
    Eurydice_arr_d6 self) {
  return self;
}

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice Eurydice_arr uint8_t[[$168size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_e40(
    const Eurydice_arr_c5 (*val)[]) {}

/**
 Declassify secret memory.

 No-op if `valgrind_ct_test` cfg is not enabled.
*/
/**
A monomorphic instance of libcrux_secrets.mem_requests.ct_declassify
with types Eurydice_derefed_slice Eurydice_arr uint8_t[[$504size_t]]

*/
void libcrux_secrets_mem_requests_ct_declassify_e4(
    const Eurydice_arr_79 (*val)[]) {}

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
    Eurydice_mut_borrow_slice_u8 *self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$34size_t]]

*/
Eurydice_arr_31 libcrux_secrets_int_public_integers_classify_27_78(
    Eurydice_arr_31 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 34
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_e9(
    const Eurydice_arr_31 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)34U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 64
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_17(
    Eurydice_arr_c7 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)64U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$64size_t]]

*/
Eurydice_arr_c7 libcrux_secrets_int_public_integers_classify_27_56(
    Eurydice_arr_c7 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 48
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_9f(
    Eurydice_arr_65 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)48U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$48size_t]]

*/
Eurydice_arr_65 libcrux_secrets_int_public_integers_classify_27_69(
    Eurydice_arr_65 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 32
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_01(
    Eurydice_arr_ec *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)32U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$32size_t]]

*/
Eurydice_arr_ec libcrux_secrets_int_public_integers_classify_27_4b(
    Eurydice_arr_ec self) {
  return self;
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 28
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_5e(
    Eurydice_arr_a2 *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)28U;
  return lit;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$28size_t]]

*/
Eurydice_arr_a2 libcrux_secrets_int_public_integers_classify_27_96(
    Eurydice_arr_a2 self) {
  return self;
}

/**
A monomorphic instance of Eurydice.slice_subslice_from_mut
with types uint8_t, core_ops_range_RangeFrom size_t, Eurydice_derefed_slice
uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_from_mut_6d(
    Eurydice_mut_borrow_slice_u8 s, size_t r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = s.ptr + r,
                                                      .meta = s.meta - r});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_subslice_shared_d4(
    const Eurydice_arr_5c *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = a->data + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_mut
with types uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_slice_mut_15(
    Eurydice_arr_5c *a) {
  Eurydice_mut_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 4
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_98(
    const Eurydice_array_u8x4 *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)4U;
  return lit;
}

/**
A monomorphic instance of Eurydice.slice_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_mut_borrow_slice_u8 Eurydice_slice_subslice_mut_c8(
    Eurydice_mut_borrow_slice_u8 s, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                      .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_slice_shared
with types uint8_t
with const generics
- N= 200
*/
Eurydice_borrow_slice_u8 Eurydice_array_to_slice_shared_15(
    const Eurydice_arr_5c *a) {
  Eurydice_borrow_slice_u8 lit;
  lit.ptr = a->data;
  lit.meta = (size_t)200U;
  return lit;
}

/**
This function found in impl {core::result::Result<T, E>[TraitClause@0,
TraitClause@1]}
*/
/**
A monomorphic instance of core.result.unwrap_26
with types Eurydice_arr uint8_t[[$4size_t]], core_array_TryFromSliceError

*/
Eurydice_array_u8x4 core_result_unwrap_26_cc(core_result_Result_c7 self) {
  if (self.tag == core_result_Ok) {
    return self.val.case_Ok;
  } else {
    KRML_HOST_EPRINTF("KaRaMeL abort at %s:%d\n%s\n", __FILE__, __LINE__,
                      "unwrap not Ok");
    KRML_HOST_EXIT(255U);
  }
}

/**
A monomorphic instance of Eurydice.slice_subslice_shared
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t

*/
Eurydice_borrow_slice_u8 Eurydice_slice_subslice_shared_c8(
    Eurydice_borrow_slice_u8 s, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_borrow_slice_u8){.ptr = s.ptr + r.start,
                                                  .meta = r.end - r.start});
}

/**
A monomorphic instance of Eurydice.array_to_subslice_mut
with types uint8_t, core_ops_range_Range size_t, Eurydice_derefed_slice uint8_t
with const generics
- N= 200
*/
Eurydice_mut_borrow_slice_u8 Eurydice_array_to_subslice_mut_d4(
    Eurydice_arr_5c *a, core_ops_range_Range_87 r) {
  return (KRML_CLITERAL(Eurydice_mut_borrow_slice_u8){.ptr = a->data + r.start,
                                                      .meta = r.end - r.start});
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint8_t[[$200size_t]]

*/
Eurydice_arr_5c libcrux_secrets_int_public_integers_classify_27_df0(
    Eurydice_arr_5c self) {
  return self;
}

/**
This function found in impl {libcrux_secrets::traits::Classify<T> for T}
*/
/**
A monomorphic instance of libcrux_secrets.int.public_integers.classify_27
with types Eurydice_arr uint32_t[[$2size_t]]

*/
Eurydice_arr_a0 libcrux_secrets_int_public_integers_classify_27_aa(
    Eurydice_arr_a0 self) {
  return self;
}
