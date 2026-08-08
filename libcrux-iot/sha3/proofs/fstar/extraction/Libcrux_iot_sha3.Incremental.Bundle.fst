module Libcrux_iot_sha3.Incremental.Bundle
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

/// An unbuffered XOF state.
type t_UnbufferedXofState = { f_state:Libcrux_iot_sha3.State.t_KeccakState }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_UnbufferedXofState

unfold
let impl_2 = impl_2'

let impl: Core_models.Clone.t_Clone t_UnbufferedXofState =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_Copy t_UnbufferedXofState

unfold
let impl_1 = impl_1'

/// Input-buffering SHAKE128 state
type t_Shake128Xof = { f_state:Libcrux_iot_sha3.Keccak.t_KeccakXofState (mk_usize 168) }

/// Input-buffering SHAKE256 state
type t_Shake256Xof = { f_state:Libcrux_iot_sha3.Keccak.t_KeccakXofState (mk_usize 136) }

/// Create a new SHAKE-128 state object.
let shake128_init (_: Prims.unit) : t_UnbufferedXofState =
  { f_state = Libcrux_iot_sha3.State.impl_KeccakState__new () } <: t_UnbufferedXofState

/// Absorb
let shake128_absorb_final (s: t_UnbufferedXofState) (data0: t_Slice u8)
    : Prims.Pure t_UnbufferedXofState
      (requires (Core_models.Slice.impl__len #u8 data0 <: usize) <. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let s:t_UnbufferedXofState =
    {
      s with
      f_state
      =
      Libcrux_iot_sha3.Keccak.absorb_final (mk_usize 168)
        (mk_u8 31)
        s.f_state
        data0
        (mk_usize 0)
        (Core_models.Slice.impl__len #u8 data0 <: usize)
    }
    <:
    t_UnbufferedXofState
  in
  s

/// Squeeze three blocks
let shake128_squeeze_first_three_blocks (s: t_UnbufferedXofState) (out0: t_Slice u8)
    : Prims.Pure (t_UnbufferedXofState & t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 out0 <: usize) >=. (mk_usize 3 *! mk_usize 168 <: usize))
      (fun _ -> Prims.l_True) =
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    Libcrux_iot_sha3.Keccak.squeeze_first_three_blocks (mk_usize 168) s.f_state out0
  in
  let s:t_UnbufferedXofState = { s with f_state = tmp0 } <: t_UnbufferedXofState in
  let out0:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  s, out0 <: (t_UnbufferedXofState & t_Slice u8)

/// Squeeze five blocks
let shake128_squeeze_first_five_blocks (s: t_UnbufferedXofState) (out0: t_Slice u8)
    : Prims.Pure (t_UnbufferedXofState & t_Slice u8)
      (requires
        (Core_models.Slice.impl__len #u8 out0 <: usize) >=. (mk_usize 5 *! mk_usize 168 <: usize))
      (fun _ -> Prims.l_True) =
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    Libcrux_iot_sha3.Keccak.squeeze_first_five_blocks (mk_usize 168) s.f_state out0
  in
  let s:t_UnbufferedXofState = { s with f_state = tmp0 } <: t_UnbufferedXofState in
  let out0:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  s, out0 <: (t_UnbufferedXofState & t_Slice u8)

/// Squeeze another block
let shake128_squeeze_next_block (s: t_UnbufferedXofState) (out0: t_Slice u8)
    : Prims.Pure (t_UnbufferedXofState & t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 out0 <: usize) >=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    Libcrux_iot_sha3.Keccak.squeeze_next_block (mk_usize 168) s.f_state out0
  in
  let s:t_UnbufferedXofState = { s with f_state = tmp0 } <: t_UnbufferedXofState in
  let out0:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  s, out0 <: (t_UnbufferedXofState & t_Slice u8)

/// Create a new SHAKE-256 state object.
let shake256_init (_: Prims.unit) : t_UnbufferedXofState =
  { f_state = Libcrux_iot_sha3.State.impl_KeccakState__new () } <: t_UnbufferedXofState

/// Absorb some data for SHAKE-256 for the last time
let shake256_absorb_final (s: t_UnbufferedXofState) (data: t_Slice u8)
    : Prims.Pure t_UnbufferedXofState
      (requires (Core_models.Slice.impl__len #u8 data <: usize) <. mk_usize 136)
      (fun _ -> Prims.l_True) =
  let s:t_UnbufferedXofState =
    {
      s with
      f_state
      =
      Libcrux_iot_sha3.Keccak.absorb_final (mk_usize 136)
        (mk_u8 31)
        s.f_state
        data
        (mk_usize 0)
        (Core_models.Slice.impl__len #u8 data <: usize)
    }
    <:
    t_UnbufferedXofState
  in
  s

/// Squeeze the first SHAKE-256 block
let shake256_squeeze_first_block (s: t_UnbufferedXofState) (out: t_Slice u8)
    : Prims.Pure (t_UnbufferedXofState & t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 out <: usize) >=. mk_usize 136)
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = Libcrux_iot_sha3.Keccak.squeeze_first_block (mk_usize 136) s.f_state out in
  s, out <: (t_UnbufferedXofState & t_Slice u8)

/// Squeeze the next SHAKE-256 block
let shake256_squeeze_next_block (s: t_UnbufferedXofState) (out: t_Slice u8)
    : Prims.Pure (t_UnbufferedXofState & t_Slice u8)
      (requires (Core_models.Slice.impl__len #u8 out <: usize) >=. mk_usize 136)
      (fun _ -> Prims.l_True) =
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    Libcrux_iot_sha3.Keccak.squeeze_next_block (mk_usize 136) s.f_state out
  in
  let s:t_UnbufferedXofState = { s with f_state = tmp0 } <: t_UnbufferedXofState in
  let out:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  s, out <: (t_UnbufferedXofState & t_Slice u8)

class t_Sealed (v_Self: Type0) = { __marker_trait_t_Sealed:Prims.unit }

/// Interface for an input-buffering Extendable Output Function
/// (XOF)
class t_Xof (v_Self: Type0) (v_RATE: usize) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Sealed v_Self;
  f_new_pre:Prims.unit -> Type0;
  f_new_post:Prims.unit -> v_Self -> Type0;
  f_new:x0: Prims.unit -> Prims.Pure v_Self (f_new_pre x0) (fun result -> f_new_post x0 result);
  f_absorb_pre:v_Self -> t_Slice u8 -> Type0;
  f_absorb_post:v_Self -> t_Slice u8 -> v_Self -> Type0;
  f_absorb:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure v_Self (f_absorb_pre x0 x1) (fun result -> f_absorb_post x0 x1 result);
  f_absorb_final_pre:v_Self -> t_Slice u8 -> Type0;
  f_absorb_final_post:v_Self -> t_Slice u8 -> v_Self -> Type0;
  f_absorb_final:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure v_Self (f_absorb_final_pre x0 x1) (fun result -> f_absorb_final_post x0 x1 result);
  f_squeeze_pre:v_Self -> t_Slice u8 -> Type0;
  f_squeeze_post:v_Self -> t_Slice u8 -> (v_Self & t_Slice u8) -> Type0;
  f_squeeze:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure (v_Self & t_Slice u8)
        (f_squeeze_pre x0 x1)
        (fun result -> f_squeeze_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) (v_RATE:usize) {|i: t_Xof v_Self v_RATE|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl__from__private: t_Sealed t_Shake128Xof = { __marker_trait_t_Sealed = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: t_Xof t_Shake128Xof (mk_usize 168) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_new_pre = (fun (_: Prims.unit) -> true);
    f_new_post = (fun (_: Prims.unit) (out: t_Shake128Xof) -> true);
    f_new
    =
    (fun (_: Prims.unit) ->
        { f_state = Libcrux_iot_sha3.Keccak.impl__new (mk_usize 168) () } <: t_Shake128Xof);
    f_absorb_pre
    =
    (fun (self_: t_Shake128Xof) (input: t_Slice u8) ->
        self_.f_state.Libcrux_iot_sha3.Keccak.f_buf_len <. mk_usize 168);
    f_absorb_post = (fun (self: t_Shake128Xof) (input: t_Slice u8) (out: t_Shake128Xof) -> true);
    f_absorb
    =
    (fun (self: t_Shake128Xof) (input: t_Slice u8) ->
        let self:t_Shake128Xof =
          {
            self with
            f_state = Libcrux_iot_sha3.Keccak.impl__absorb (mk_usize 168) self.f_state input
          }
          <:
          t_Shake128Xof
        in
        self);
    f_absorb_final_pre
    =
    (fun (self_: t_Shake128Xof) (input: t_Slice u8) ->
        self_.f_state.Libcrux_iot_sha3.Keccak.f_buf_len <. mk_usize 168);
    f_absorb_final_post
    =
    (fun (self: t_Shake128Xof) (input: t_Slice u8) (out: t_Shake128Xof) -> true);
    f_absorb_final
    =
    (fun (self: t_Shake128Xof) (input: t_Slice u8) ->
        let self:t_Shake128Xof =
          {
            self with
            f_state
            =
            Libcrux_iot_sha3.Keccak.impl__absorb_final (mk_usize 168) (mk_u8 31) self.f_state input
          }
          <:
          t_Shake128Xof
        in
        self);
    f_squeeze_pre = (fun (self: t_Shake128Xof) (out: t_Slice u8) -> true);
    f_squeeze_post
    =
    (fun (self: t_Shake128Xof) (out: t_Slice u8) (out1: (t_Shake128Xof & t_Slice u8)) -> true);
    f_squeeze
    =
    fun (self: t_Shake128Xof) (out: t_Slice u8) ->
      let (tmp0: Libcrux_iot_sha3.Keccak.t_KeccakXofState (mk_usize 168)), (tmp1: t_Slice u8) =
        Libcrux_iot_sha3.Keccak.impl__squeeze (mk_usize 168) self.f_state out
      in
      let self:t_Shake128Xof = { self with f_state = tmp0 } <: t_Shake128Xof in
      let out:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      self, out <: (t_Shake128Xof & t_Slice u8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1__from__private: t_Sealed t_Shake256Xof = { __marker_trait_t_Sealed = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_Xof t_Shake256Xof (mk_usize 136) =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_new_pre = (fun (_: Prims.unit) -> true);
    f_new_post = (fun (_: Prims.unit) (out: t_Shake256Xof) -> true);
    f_new
    =
    (fun (_: Prims.unit) ->
        { f_state = Libcrux_iot_sha3.Keccak.impl__new (mk_usize 136) () } <: t_Shake256Xof);
    f_absorb_pre
    =
    (fun (self_: t_Shake256Xof) (input: t_Slice u8) ->
        self_.f_state.Libcrux_iot_sha3.Keccak.f_buf_len <. mk_usize 136);
    f_absorb_post = (fun (self: t_Shake256Xof) (input: t_Slice u8) (out: t_Shake256Xof) -> true);
    f_absorb
    =
    (fun (self: t_Shake256Xof) (input: t_Slice u8) ->
        let self:t_Shake256Xof =
          {
            self with
            f_state = Libcrux_iot_sha3.Keccak.impl__absorb (mk_usize 136) self.f_state input
          }
          <:
          t_Shake256Xof
        in
        self);
    f_absorb_final_pre
    =
    (fun (self_: t_Shake256Xof) (input: t_Slice u8) ->
        self_.f_state.Libcrux_iot_sha3.Keccak.f_buf_len <. mk_usize 136);
    f_absorb_final_post
    =
    (fun (self: t_Shake256Xof) (input: t_Slice u8) (out: t_Shake256Xof) -> true);
    f_absorb_final
    =
    (fun (self: t_Shake256Xof) (input: t_Slice u8) ->
        let self:t_Shake256Xof =
          {
            self with
            f_state
            =
            Libcrux_iot_sha3.Keccak.impl__absorb_final (mk_usize 136) (mk_u8 31) self.f_state input
          }
          <:
          t_Shake256Xof
        in
        self);
    f_squeeze_pre = (fun (self: t_Shake256Xof) (out: t_Slice u8) -> true);
    f_squeeze_post
    =
    (fun (self: t_Shake256Xof) (out: t_Slice u8) (out1: (t_Shake256Xof & t_Slice u8)) -> true);
    f_squeeze
    =
    fun (self: t_Shake256Xof) (out: t_Slice u8) ->
      let (tmp0: Libcrux_iot_sha3.Keccak.t_KeccakXofState (mk_usize 136)), (tmp1: t_Slice u8) =
        Libcrux_iot_sha3.Keccak.impl__squeeze (mk_usize 136) self.f_state out
      in
      let self:t_Shake256Xof = { self with f_state = tmp0 } <: t_Shake256Xof in
      let out:t_Slice u8 = tmp1 in
      let _:Prims.unit = () in
      self, out <: (t_Shake256Xof & t_Slice u8)
  }
