module Libcrux_iot_sha3.State
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_iot_sha3.Lane in
  ()

type t_KeccakState = {
  f_st:t_Array Libcrux_iot_sha3.Lane.t_Lane2U32 (mk_usize 25);
  f_c:t_Array Libcrux_iot_sha3.Lane.t_Lane2U32 (mk_usize 5);
  f_d:t_Array Libcrux_iot_sha3.Lane.t_Lane2U32 (mk_usize 5);
  f_i:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_2': Core_models.Fmt.t_Debug t_KeccakState

unfold
let impl_2 = impl_2'

let impl: Core_models.Clone.t_Clone t_KeccakState =
  { f_clone = (fun x -> x); f_clone_pre = (fun _ -> True); f_clone_post = (fun _ _ -> True) }

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core_models.Marker.t_Copy t_KeccakState

unfold
let impl_1 = impl_1'

let impl_KeccakState__new (_: Prims.unit) : t_KeccakState =
  {
    f_st
    =
    Rust_primitives.Hax.repeat (Libcrux_iot_sha3.Lane.impl_Lane2U32__zero ()
        <:
        Libcrux_iot_sha3.Lane.t_Lane2U32)
      (mk_usize 25);
    f_c
    =
    Rust_primitives.Hax.repeat (Libcrux_iot_sha3.Lane.impl_Lane2U32__zero ()
        <:
        Libcrux_iot_sha3.Lane.t_Lane2U32)
      (mk_usize 5);
    f_d
    =
    Rust_primitives.Hax.repeat (Libcrux_iot_sha3.Lane.impl_Lane2U32__zero ()
        <:
        Libcrux_iot_sha3.Lane.t_Lane2U32)
      (mk_usize 5);
    f_i = mk_usize 0
  }
  <:
  t_KeccakState

let impl_KeccakState__get_with_zeta (self: t_KeccakState) (i j zeta: usize)
    : Prims.Pure u32
      (requires i <. mk_usize 5 && j <. mk_usize 5 && zeta <. mk_usize 2)
      (fun _ -> Prims.l_True) =
  (self.f_st.[ (mk_usize 5 *! j <: usize) +! i <: usize ] <: Libcrux_iot_sha3.Lane.t_Lane2U32).[ zeta
  ]

let impl_KeccakState__set_with_zeta (self: t_KeccakState) (i j zeta: usize) (v: u32)
    : Prims.Pure t_KeccakState
      (requires i <. mk_usize 5 && j <. mk_usize 5 && zeta <. mk_usize 2)
      (fun _ -> Prims.l_True) =
  let self:t_KeccakState =
    {
      self with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_st
        ((mk_usize 5 *! j <: usize) +! i <: usize)
        ({
            (self.f_st.[ (mk_usize 5 *! j <: usize) +! i <: usize ]
              <:
              Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (self.f_st.[ (mk_usize 5 *!
                    j
                    <:
                    usize) +!
                  i
                  <:
                  usize ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              zeta
              v
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    t_KeccakState
  in
  self

let impl_KeccakState__get_lane (self: t_KeccakState) (i j: usize)
    : Prims.Pure Libcrux_iot_sha3.Lane.t_Lane2U32
      (requires i <. mk_usize 5 && j <. mk_usize 5)
      (fun _ -> Prims.l_True) = self.f_st.[ (mk_usize 5 *! j <: usize) +! i <: usize ]

let impl_KeccakState__set_lane
      (self: t_KeccakState)
      (i j: usize)
      (lane: Libcrux_iot_sha3.Lane.t_Lane2U32)
    : Prims.Pure t_KeccakState (requires i <. mk_usize 5 && j <. mk_usize 5) (fun _ -> Prims.l_True) =
  let self:t_KeccakState =
    {
      self with
      f_st
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_st
        ((mk_usize 5 *! j <: usize) +! i <: usize)
        lane
    }
    <:
    t_KeccakState
  in
  self

let impl_KeccakState__set_lane_value (self: t_KeccakState) (i j: usize) (value: u32)
    : Prims.Pure t_KeccakState (requires i <. mk_usize 5 && j <. mk_usize 2) (fun _ -> Prims.l_True) =
  let self:t_KeccakState =
    {
      self with
      f_c
      =
      Rust_primitives.Hax.Monomorphized_update_at.update_at_usize self.f_c
        i
        ({
            (self.f_c.[ i ] <: Libcrux_iot_sha3.Lane.t_Lane2U32) with
            Libcrux_iot_sha3.Lane._0
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize (self.f_c.[ i ]
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
                .Libcrux_iot_sha3.Lane._0
              j
              value
            <:
            t_Array u32 (mk_usize 2)
          }
          <:
          Libcrux_iot_sha3.Lane.t_Lane2U32)
    }
    <:
    t_KeccakState
  in
  self

/// `out` has the exact size we want here. It must be less than or equal to
/// `RATE`.
let impl_KeccakState__store (v_RATE: usize) (self: t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (Core_models.Slice.impl__len #u8 out <: usize) <=. v_RATE)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let e_out_len:usize = Core_models.Slice.impl__len #u8 out in
  let num_full_blocks:usize = (Core_models.Slice.impl__len #u8 out <: usize) /! mk_usize 8 in
  let last_block_len:usize = (Core_models.Slice.impl__len #u8 out <: usize) %! mk_usize 8 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      num_full_blocks
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 out <: usize) =. e_out_len <: bool)
      out
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          let keccak_lane:Libcrux_iot_sha3.Lane.t_Lane2U32 =
            Libcrux_iot_sha3.Lane.impl_Lane2U32__deinterleave (impl_KeccakState__get_lane self
                  (i /! mk_usize 5 <: usize)
                  (i %! mk_usize 5 <: usize)
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = i *! mk_usize 8 <: usize;
                  Core_models.Ops.Range.f_end = (i *! mk_usize 8 <: usize) +! mk_usize 4 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core_models.Ops.Range.f_start = i *! mk_usize 8 <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (i *! mk_usize 8 <: usize) +! mk_usize 4 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 0 ] <: u32)
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = (i *! mk_usize 8 <: usize) +! mk_usize 4 <: usize;
                  Core_models.Ops.Range.f_end = (i *! mk_usize 8 <: usize) +! mk_usize 8 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core_models.Ops.Range.f_start
                        =
                        (i *! mk_usize 8 <: usize) +! mk_usize 4 <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (i *! mk_usize 8 <: usize) +! mk_usize 8 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 1 ] <: u32)
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          out)
  in
  let out:t_Slice u8 =
    if last_block_len >. mk_usize 4
    then
      let keccak_lane:Libcrux_iot_sha3.Lane.t_Lane2U32 =
        Libcrux_iot_sha3.Lane.impl_Lane2U32__deinterleave (impl_KeccakState__get_lane self
              (num_full_blocks /! mk_usize 5 <: usize)
              (num_full_blocks %! mk_usize 5 <: usize)
            <:
            Libcrux_iot_sha3.Lane.t_Lane2U32)
      in
      let last_half_block_len:usize = last_block_len -! mk_usize 4 in
      let out:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
          ({
              Core_models.Ops.Range.f_start = num_full_blocks *! mk_usize 8 <: usize;
              Core_models.Ops.Range.f_end
              =
              (num_full_blocks *! mk_usize 8 <: usize) +! mk_usize 4 <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (out.[ {
                    Core_models.Ops.Range.f_start = num_full_blocks *! mk_usize 8 <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (num_full_blocks *! mk_usize 8 <: usize) +! mk_usize 4 <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 0 ] <: u32)
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      let out:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
          ({
              Core_models.Ops.Range.f_start
              =
              (num_full_blocks *! mk_usize 8 <: usize) +! mk_usize 4 <: usize;
              Core_models.Ops.Range.f_end
              =
              (num_full_blocks *! mk_usize 8 <: usize) +! last_block_len <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (out.[ {
                    Core_models.Ops.Range.f_start
                    =
                    (num_full_blocks *! mk_usize 8 <: usize) +! mk_usize 4 <: usize;
                    Core_models.Ops.Range.f_end
                    =
                    (num_full_blocks *! mk_usize 8 <: usize) +! last_block_len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              ((Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 1 ] <: u32)
                  <:
                  t_Array u8 (mk_usize 4)).[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = last_half_block_len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      out
    else
      if last_block_len >. mk_usize 0
      then
        let keccak_lane:Libcrux_iot_sha3.Lane.t_Lane2U32 =
          Libcrux_iot_sha3.Lane.impl_Lane2U32__deinterleave (impl_KeccakState__get_lane self
                (num_full_blocks /! mk_usize 5 <: usize)
                (num_full_blocks %! mk_usize 5 <: usize)
              <:
              Libcrux_iot_sha3.Lane.t_Lane2U32)
        in
        let out:t_Slice u8 =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
            ({
                Core_models.Ops.Range.f_start = num_full_blocks *! mk_usize 8 <: usize;
                Core_models.Ops.Range.f_end
                =
                (num_full_blocks *! mk_usize 8 <: usize) +! last_block_len <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Core_models.Slice.impl__copy_from_slice #u8
                (out.[ {
                      Core_models.Ops.Range.f_start = num_full_blocks *! mk_usize 8 <: usize;
                      Core_models.Ops.Range.f_end
                      =
                      (num_full_blocks *! mk_usize 8 <: usize) +! last_block_len <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                ((Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 0 ] <: u32)
                    <:
                    t_Array u8 (mk_usize 4)).[ {
                      Core_models.Ops.Range.f_start = mk_usize 0;
                      Core_models.Ops.Range.f_end = last_block_len
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        in
        out
      else out
  in
  out

let load_block_2u32
      (v_RATE: usize)
      (keccak_state: t_KeccakState)
      (blocks: t_Slice u8)
      (start: usize)
    : Prims.Pure t_KeccakState
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 blocks <: usize)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        Hax_lib.v_assert ((v_RATE <=. (Core_models.Slice.impl__len #u8 blocks <: usize) <: bool) &&
            ((v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 <: bool))
      in
      ()
  in
  let keccak_state:t_KeccakState =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (v_RATE /! mk_usize 8 <: usize)
      (fun keccak_state temp_1_ ->
          let keccak_state:t_KeccakState = keccak_state in
          let _:usize = temp_1_ in
          true)
      keccak_state
      (fun keccak_state i ->
          let keccak_state:t_KeccakState = keccak_state in
          let i:usize = i in
          let offset:usize = start +! (mk_usize 8 *! i <: usize) in
          let a:u32 =
            Core_models.Num.impl_u32__from_le_bytes (Core_models.Result.impl__unwrap #(t_Array u8
                      (mk_usize 4))
                  #Core_models.Array.t_TryFromSliceError
                  (Core_models.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      (blocks.[ {
                            Core_models.Ops.Range.f_start = offset;
                            Core_models.Ops.Range.f_end = offset +! mk_usize 4 <: usize
                          }
                          <:
                          Core_models.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core_models.Result.t_Result (t_Array u8 (mk_usize 4))
                      Core_models.Array.t_TryFromSliceError)
                <:
                t_Array u8 (mk_usize 4))
          in
          let b:u32 =
            Core_models.Num.impl_u32__from_le_bytes (Core_models.Result.impl__unwrap #(t_Array u8
                      (mk_usize 4))
                  #Core_models.Array.t_TryFromSliceError
                  (Core_models.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (mk_usize 4))
                      #FStar.Tactics.Typeclasses.solve
                      (blocks.[ {
                            Core_models.Ops.Range.f_start = offset +! mk_usize 4 <: usize;
                            Core_models.Ops.Range.f_end = offset +! mk_usize 8 <: usize
                          }
                          <:
                          Core_models.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core_models.Result.t_Result (t_Array u8 (mk_usize 4))
                      Core_models.Array.t_TryFromSliceError)
                <:
                t_Array u8 (mk_usize 4))
          in
          let lane:Libcrux_iot_sha3.Lane.t_Lane2U32 =
            Libcrux_iot_sha3.Lane.impl_Lane2U32__interleave (Core_models.Convert.f_from #Libcrux_iot_sha3.Lane.t_Lane2U32
                  #(t_Array u32 (mk_usize 2))
                  #FStar.Tactics.Typeclasses.solve
                  (let list = [a; b] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list 2 list)
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
          in
          let got:Libcrux_iot_sha3.Lane.t_Lane2U32 =
            impl_KeccakState__get_lane keccak_state
              (i /! mk_usize 5 <: usize)
              (i %! mk_usize 5 <: usize)
          in
          let keccak_state:t_KeccakState =
            impl_KeccakState__set_lane keccak_state
              (i /! mk_usize 5 <: usize)
              (i %! mk_usize 5 <: usize)
              (Libcrux_iot_sha3.Lane.impl_Lane2U32__from_ints (let list =
                      [
                        (got.[ mk_usize 0 ] <: u32) ^. (lane.[ mk_usize 0 ] <: u32) <: u32;
                        (got.[ mk_usize 1 ] <: u32) ^. (lane.[ mk_usize 1 ] <: u32) <: u32
                      ]
                    in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
                    Rust_primitives.Hax.array_of_list 2 list)
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
          in
          keccak_state)
  in
  keccak_state

let impl_KeccakState__load_block
      (v_RATE: usize)
      (self: t_KeccakState)
      (blocks: t_Slice u8)
      (start: usize)
    : Prims.Pure t_KeccakState
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 blocks <: usize)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let self:t_KeccakState = load_block_2u32 v_RATE self blocks start in
  self

let load_block_full_2u32
      (v_RATE: usize)
      (keccak_state: t_KeccakState)
      (blocks: t_Array u8 (mk_usize 200))
      (start: usize)
    : Prims.Pure t_KeccakState
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (mk_i32 200) <: Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let keccak_state:t_KeccakState =
    load_block_2u32 v_RATE keccak_state (blocks <: t_Slice u8) start
  in
  keccak_state

let impl_KeccakState__load_block_full
      (v_RATE: usize)
      (self: t_KeccakState)
      (blocks: t_Array u8 (mk_usize 200))
      (start: usize)
    : Prims.Pure t_KeccakState
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        start <=. mk_usize 200 &&
        (start +! v_RATE <: usize) <=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let self:t_KeccakState = load_block_full_2u32 v_RATE self blocks start in
  self

let store_block_2u32 (v_RATE: usize) (s: t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (fun _ -> Prims.l_True) =
  let e_out_len:usize = Core_models.Slice.impl__len #u8 out in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (v_RATE /! mk_usize 8 <: usize)
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          (Core_models.Slice.impl__len #u8 out <: usize) =. e_out_len <: bool)
      out
      (fun out i ->
          let out:t_Slice u8 = out in
          let i:usize = i in
          let keccak_lane:Libcrux_iot_sha3.Lane.t_Lane2U32 =
            Libcrux_iot_sha3.Lane.impl_Lane2U32__deinterleave (impl_KeccakState__get_lane s
                  (i /! mk_usize 5 <: usize)
                  (i %! mk_usize 5 <: usize)
                <:
                Libcrux_iot_sha3.Lane.t_Lane2U32)
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = mk_usize 8 *! i <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 8 *! i <: usize) +! mk_usize 4 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core_models.Ops.Range.f_start = mk_usize 8 *! i <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 8 *! i <: usize) +! mk_usize 4 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 0 ] <: u32)
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = (mk_usize 8 *! i <: usize) +! mk_usize 4 <: usize;
                  Core_models.Ops.Range.f_end = (mk_usize 8 *! i <: usize) +! mk_usize 8 <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (out.[ {
                        Core_models.Ops.Range.f_start
                        =
                        (mk_usize 8 *! i <: usize) +! mk_usize 4 <: usize;
                        Core_models.Ops.Range.f_end
                        =
                        (mk_usize 8 *! i <: usize) +! mk_usize 8 <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                  (Core_models.Num.impl_u32__to_le_bytes (keccak_lane.[ mk_usize 1 ] <: u32)
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          out)
  in
  out

let impl_KeccakState__store_block (v_RATE: usize) (self: t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = store_block_2u32 v_RATE self out in
  out

let store_block_full_2u32 (v_RATE: usize) (s: t_KeccakState) (out: t_Array u8 (mk_usize 200))
    : Prims.Pure (t_Array u8 (mk_usize 200))
      (requires (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_full out
      (Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull)
      (store_block_2u32 v_RATE
          s
          (out.[ Core_models.Ops.Range.RangeFull <: Core_models.Ops.Range.t_RangeFull ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  out

let impl_KeccakState__store_block_full
      (v_RATE: usize)
      (self: t_KeccakState)
      (out: t_Array u8 (mk_usize 200))
    : Prims.Pure (t_Array u8 (mk_usize 200))
      (requires (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168)
      (fun _ -> Prims.l_True) =
  let out:t_Array u8 (mk_usize 200) = store_block_full_2u32 v_RATE self out in
  out
