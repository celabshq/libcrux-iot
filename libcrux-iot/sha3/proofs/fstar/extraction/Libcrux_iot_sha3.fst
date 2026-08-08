module Libcrux_iot_sha3
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// Size in bytes of a SHA3 244 digest
let v_SHA3_224_DIGEST_SIZE: usize = mk_usize 28

/// Size in bytes of a SHA3 256 digest
let v_SHA3_256_DIGEST_SIZE: usize = mk_usize 32

/// Size in bytes of a SHA3 384 digest
let v_SHA3_384_DIGEST_SIZE: usize = mk_usize 48

/// Size in bytes of a SHA3 512 digest
let v_SHA3_512_DIGEST_SIZE: usize = mk_usize 64

/// The Digest Algorithm.
type t_Algorithm =
  | Algorithm_Sha224 : t_Algorithm
  | Algorithm_Sha256 : t_Algorithm
  | Algorithm_Sha384 : t_Algorithm
  | Algorithm_Sha512 : t_Algorithm

let anon_const_Algorithm_Sha224__anon_const_0: u32 = mk_u32 1

let anon_const_Algorithm_Sha256__anon_const_0: u32 = mk_u32 2

let anon_const_Algorithm_Sha384__anon_const_0: u32 = mk_u32 3

let anon_const_Algorithm_Sha512__anon_const_0: u32 = mk_u32 4

let t_Algorithm_cast_to_repr (x: t_Algorithm) : u32 =
  match x <: t_Algorithm with
  | Algorithm_Sha224  -> anon_const_Algorithm_Sha224__anon_const_0
  | Algorithm_Sha256  -> anon_const_Algorithm_Sha256__anon_const_0
  | Algorithm_Sha384  -> anon_const_Algorithm_Sha384__anon_const_0
  | Algorithm_Sha512  -> anon_const_Algorithm_Sha512__anon_const_0

let impl_3: Core_models.Clone.t_Clone t_Algorithm =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Marker.t_Copy t_Algorithm

unfold
let impl_2 = impl_2'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core_models.Fmt.t_Debug t_Algorithm

unfold
let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core_models.Marker.t_StructuralPartialEq t_Algorithm

unfold
let impl_5 = impl_5'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_6': Core_models.Cmp.t_PartialEq t_Algorithm t_Algorithm

unfold
let impl_6 = impl_6'

/// Error returned when a `u32` does not correspond to an [`Algorithm`].
type t_UnknownAlgorithm = | UnknownAlgorithm : t_UnknownAlgorithm

let impl_8: Core_models.Clone.t_Clone t_UnknownAlgorithm =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core_models.Marker.t_Copy t_UnknownAlgorithm

unfold
let impl_7 = impl_7'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core_models.Fmt.t_Debug t_UnknownAlgorithm

unfold
let impl_9 = impl_9'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_10': Core_models.Marker.t_StructuralPartialEq t_UnknownAlgorithm

unfold
let impl_10 = impl_10'

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_11': Core_models.Cmp.t_PartialEq t_UnknownAlgorithm t_UnknownAlgorithm

unfold
let impl_11 = impl_11'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core_models.Convert.t_TryFrom t_Algorithm u32 =
  {
    f_Error = t_UnknownAlgorithm;
    f_try_from_pre = (fun (v: u32) -> true);
    f_try_from_post
    =
    (fun (v: u32) (out: Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm) -> true);
    f_try_from
    =
    fun (v: u32) ->
      match v <: u32 with
      | Rust_primitives.Integers.MkInt 1 ->
        Core_models.Result.Result_Ok (Algorithm_Sha224 <: t_Algorithm)
        <:
        Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm
      | Rust_primitives.Integers.MkInt 2 ->
        Core_models.Result.Result_Ok (Algorithm_Sha256 <: t_Algorithm)
        <:
        Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm
      | Rust_primitives.Integers.MkInt 3 ->
        Core_models.Result.Result_Ok (Algorithm_Sha384 <: t_Algorithm)
        <:
        Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm
      | Rust_primitives.Integers.MkInt 4 ->
        Core_models.Result.Result_Ok (Algorithm_Sha512 <: t_Algorithm)
        <:
        Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm
      | _ ->
        Core_models.Result.Result_Err (UnknownAlgorithm <: t_UnknownAlgorithm)
        <:
        Core_models.Result.t_Result t_Algorithm t_UnknownAlgorithm
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core_models.Convert.t_From u32 t_Algorithm =
  {
    f_from_pre = (fun (v: t_Algorithm) -> true);
    f_from_post = (fun (v: t_Algorithm) (out: u32) -> true);
    f_from
    =
    fun (v: t_Algorithm) ->
      match v <: t_Algorithm with
      | Algorithm_Sha224  -> mk_u32 1
      | Algorithm_Sha256  -> mk_u32 2
      | Algorithm_Sha384  -> mk_u32 3
      | Algorithm_Sha512  -> mk_u32 4
  }

/// Returns the size of a digest in bytes for a given [`Algorithm`].
let digest_size (mode: t_Algorithm) : usize =
  match mode <: t_Algorithm with
  | Algorithm_Sha224  -> v_SHA3_224_DIGEST_SIZE
  | Algorithm_Sha256  -> v_SHA3_256_DIGEST_SIZE
  | Algorithm_Sha384  -> v_SHA3_384_DIGEST_SIZE
  | Algorithm_Sha512  -> v_SHA3_512_DIGEST_SIZE

let keccakx1 (v_RATE: usize) (v_DELIM: u8) (data out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = Libcrux_iot_sha3.Keccak.keccak v_RATE v_DELIM data out in
  out

/// Writes SHA3-224 digest of input payload to externally allocated buffer.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_224_DIGEST_SIZE`] bytes long
let sha224_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 digest <: usize) =. v_SHA3_224_DIGEST_SIZE)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 digest <: usize) =.
            v_SHA3_224_DIGEST_SIZE
            <:
            bool)
      in
      ()
  in
  let digest:t_Slice u8 = keccakx1 (mk_usize 144) (mk_u8 6) payload digest in
  digest

/// Returns SHA3-224 digest of input payload.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
let sha224 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 28))
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 28) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 28))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 28) <: t_Array u8 (mk_usize 28))
  in
  let out:t_Array u8 (mk_usize 28) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (sha224_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
          payload
        <:
        t_Slice u8)
  in
  out

/// Writes SHA3-256 digest of input payload to externally allocated buffer.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_256_DIGEST_SIZE`] bytes long
let sha256_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 digest <: usize) =. v_SHA3_256_DIGEST_SIZE)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 digest <: usize) =.
            v_SHA3_256_DIGEST_SIZE
            <:
            bool)
      in
      ()
  in
  let digest:t_Slice u8 = keccakx1 (mk_usize 136) (mk_u8 6) payload digest in
  digest

/// Returns SHA3-256 digest of input payload.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
let sha256 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 32))
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 32) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 32))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 32) <: t_Array u8 (mk_usize 32))
  in
  let out:t_Array u8 (mk_usize 32) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (sha256_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
          payload
        <:
        t_Slice u8)
  in
  out

/// Writes SHA3-384 digest of input payload to externally allocated buffer.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_384_DIGEST_SIZE`] bytes long
let sha384_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 digest <: usize) =. v_SHA3_384_DIGEST_SIZE)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 digest <: usize) =.
            v_SHA3_384_DIGEST_SIZE
            <:
            bool)
      in
      ()
  in
  let digest:t_Slice u8 = keccakx1 (mk_usize 104) (mk_u8 6) payload digest in
  digest

/// Returns SHA3-384 digest of input payload.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
let sha384 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 48))
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 48) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 48))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 48) <: t_Array u8 (mk_usize 48))
  in
  let out:t_Array u8 (mk_usize 48) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (sha384_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
          payload
        <:
        t_Slice u8)
  in
  out

/// Writes SHA3-512 digest of input payload to externally allocated buffer.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
/// - `digest` is exactly [`SHA3_512_DIGEST_SIZE`] bytes long
let sha512_ema (digest payload: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        (Core_models.Slice.impl__len #u8 digest <: usize) =. v_SHA3_512_DIGEST_SIZE)
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 digest <: usize) =.
            v_SHA3_512_DIGEST_SIZE
            <:
            bool)
      in
      ()
  in
  let digest:t_Slice u8 = keccakx1 (mk_usize 72) (mk_u8 6) payload digest in
  digest

/// Hashes using a particular [`Algorithm`] of the SHA3 family.
/// # Examples
///```rust
/// use libcrux_iot_sha3::{digest_size, hash, Algorithm};
/// let payload = b\"Kecak is a Balinese dance.\";
/// let digest: [u8; digest_size(Algorithm::Sha256)] = hash(Algorithm::Sha256, payload);
/// ```
let hash (v_LEN: usize) (algorithm: t_Algorithm) (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 v_LEN)
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize) &&
        v_LEN =. (digest_size algorithm <: usize))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((Core_models.Slice.impl__len #u8 payload <: usize) <=.
            (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize)
            <:
            bool)
      in
      ()
  in
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match v_LEN, digest_size algorithm <: (usize & usize) with
        | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
      in
      ()
  in
  let out:t_Array u8 v_LEN =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 v_LEN)
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) v_LEN <: t_Array u8 v_LEN)
  in
  let out:t_Array u8 v_LEN =
    match algorithm <: t_Algorithm with
    | Algorithm_Sha224  ->
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
        (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
        (sha224_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
              <:
              t_Slice u8)
            payload
          <:
          t_Slice u8)
    | Algorithm_Sha256  ->
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
        (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
        (sha256_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
              <:
              t_Slice u8)
            payload
          <:
          t_Slice u8)
    | Algorithm_Sha384  ->
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
        (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
        (sha384_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
              <:
              t_Slice u8)
            payload
          <:
          t_Slice u8)
    | Algorithm_Sha512  ->
      Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
        (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
        (sha512_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
              <:
              t_Slice u8)
            payload
          <:
          t_Slice u8)
  in
  out

/// Returns SHA3-512 digest of input payload.
/// Preconditions:
/// - `payload` is at most `u32::MAX` bytes long
let sha512 (payload: t_Slice u8)
    : Prims.Pure (t_Array u8 (mk_usize 64))
      (requires
        (Core_models.Slice.impl__len #u8 payload <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 64) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 64))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) <: t_Array u8 (mk_usize 64))
  in
  let out:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (sha512_ema (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
          payload
        <:
        t_Slice u8)
  in
  out

/// Returns SHAKE-128 digest of input payload.
/// Preconditions:
/// - `BYTES` is at most `u32::MAX as usize`
let shake128 (v_BYTES: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_BYTES)
      (requires v_BYTES <=. (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 v_BYTES =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 v_BYTES)
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) v_BYTES <: t_Array u8 v_BYTES)
  in
  let out:t_Array u8 v_BYTES =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (keccakx1 (mk_usize 168)
          (mk_u8 31)
          data
          (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  out

/// Writes SHAKE-128 digest of input payload to externally allocated buffer.
/// Writes `out.len()` bytes
/// Preconditions:
/// - `out` is at most `u32::MAX` bytes long
let shake128_ema (out data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 out <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = keccakx1 (mk_usize 168) (mk_u8 31) data out in
  out

/// Returns SHAKE256 digest of input payload.
/// Preconditions:
/// - `BYTES` is at most `u32::MAX as usize`
let shake256 (v_BYTES: usize) (data: t_Slice u8)
    : Prims.Pure (t_Array u8 v_BYTES)
      (requires v_BYTES <=. (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 v_BYTES =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 v_BYTES)
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) v_BYTES <: t_Array u8 v_BYTES)
  in
  let out:t_Array u8 v_BYTES =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (keccakx1 (mk_usize 136)
          (mk_u8 31)
          data
          (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  out

/// Writes SHAKE256 digest of input payload to externally allocated buffer.
/// Writes `out.len()` bytes.
/// Preconditions:
/// - `out` is at most `u32::MAX` bytes long
let shake256_ema (out data: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 out <: usize) <=.
        (cast (Core_models.Num.impl_u32__MAX <: u32) <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = keccakx1 (mk_usize 136) (mk_u8 31) data out in
  out
