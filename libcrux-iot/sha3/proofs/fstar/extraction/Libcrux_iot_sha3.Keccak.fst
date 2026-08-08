module Libcrux_iot_sha3.Keccak
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Libcrux_secrets.Int.Public_integers in
  let open Libcrux_secrets.Traits in
  ()

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs.
type t_KeccakXofState (v_RATE: usize) = {
  f_inner:Libcrux_iot_sha3.State.t_KeccakState;
  f_buf:t_Array u8 v_RATE;
  f_buf_len:usize;
  f_sponge:bool
}

/// An all zero block
let impl__zero_block (v_RATE: usize) (_: Prims.unit) : t_Array u8 v_RATE =
  Libcrux_secrets.Traits.f_classify #(t_Array u8 v_RATE)
    #FStar.Tactics.Typeclasses.solve
    (Rust_primitives.Hax.repeat (mk_u8 0) v_RATE <: t_Array u8 v_RATE)

/// Generate a new keccak xof state.
let impl__new (v_RATE: usize) (_: Prims.unit) : t_KeccakXofState v_RATE =
  {
    f_inner = Libcrux_iot_sha3.State.impl_KeccakState__new ();
    f_buf = impl__zero_block v_RATE ();
    f_buf_len = mk_usize 0;
    f_sponge = false
  }
  <:
  t_KeccakXofState v_RATE

/// Consume the internal buffer and the required amount of the input to pad to
/// `RATE`.
/// Returns the `consumed` bytes from `inputs` if there\'s enough buffered
/// content to consume, and `0` otherwise.
/// If `consumed > 0` is returned, `self.buf` contains a full block to be
/// loaded.
let impl__fill_buffer (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & usize)
      (requires self.f_buf_len <. v_RATE)
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_KeccakXofState v_RATE), (res: usize) = temp_0_ in
          res <=. v_RATE && self_e_future.f_buf_len <=. v_RATE) =
  let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
  let consumed:usize = mk_usize 0 in
  let (consumed: usize), (self: t_KeccakXofState v_RATE) =
    if self.f_buf_len >. mk_usize 0
    then
      if input_len >=. (v_RATE -! self.f_buf_len <: usize)
      then
        let consumed:usize = v_RATE -! self.f_buf_len in
        let self:t_KeccakXofState v_RATE =
          {
            self with
            f_buf
            =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from self.f_buf
              ({ Core_models.Ops.Range.f_start = self.f_buf_len }
                <:
                Core_models.Ops.Range.t_RangeFrom usize)
              (Core_models.Slice.impl__copy_from_slice #u8
                  (self.f_buf.[ { Core_models.Ops.Range.f_start = self.f_buf_len }
                      <:
                      Core_models.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
                  (inputs.[ { Core_models.Ops.Range.f_end = consumed }
                      <:
                      Core_models.Ops.Range.t_RangeTo usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          }
          <:
          t_KeccakXofState v_RATE
        in
        let self:t_KeccakXofState v_RATE =
          { self with f_buf_len = self.f_buf_len +! consumed } <: t_KeccakXofState v_RATE
        in
        consumed, self <: (usize & t_KeccakXofState v_RATE)
      else consumed, self <: (usize & t_KeccakXofState v_RATE)
    else consumed, self <: (usize & t_KeccakXofState v_RATE)
  in
  let hax_temp_output:usize = consumed in
  self, hax_temp_output <: (t_KeccakXofState v_RATE & usize)

assume
val v_RC_INTERLEAVED_0_': t_Array u32 (mk_usize 255)

unfold
let v_RC_INTERLEAVED_0_ = v_RC_INTERLEAVED_0_'

assume
val v_RC_INTERLEAVED_1_': t_Array u32 (mk_usize 255)

unfold
let v_RC_INTERLEAVED_1_ = v_RC_INTERLEAVED_1_'

assume
val keccakf1600_round0_theta_c_x0_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x0_z0 = keccakf1600_round0_theta_c_x0_z0'

assume
val keccakf1600_round0_theta_c_x0_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x0_z1 = keccakf1600_round0_theta_c_x0_z1'

assume
val keccakf1600_round0_theta_c_x1_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x1_z0 = keccakf1600_round0_theta_c_x1_z0'

assume
val keccakf1600_round0_theta_c_x1_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x1_z1 = keccakf1600_round0_theta_c_x1_z1'

assume
val keccakf1600_round0_theta_c_x2_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x2_z0 = keccakf1600_round0_theta_c_x2_z0'

assume
val keccakf1600_round0_theta_c_x2_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x2_z1 = keccakf1600_round0_theta_c_x2_z1'

assume
val keccakf1600_round0_theta_c_x3_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x3_z0 = keccakf1600_round0_theta_c_x3_z0'

assume
val keccakf1600_round0_theta_c_x3_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x3_z1 = keccakf1600_round0_theta_c_x3_z1'

assume
val keccakf1600_round0_theta_c_x4_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x4_z0 = keccakf1600_round0_theta_c_x4_z0'

assume
val keccakf1600_round0_theta_c_x4_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_c_x4_z1 = keccakf1600_round0_theta_c_x4_z1'

assume
val keccakf1600_round0_theta_d': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta_d = keccakf1600_round0_theta_d'

assume
val keccakf1600_round0_theta': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_theta = keccakf1600_round0_theta'

assume
val keccakf1600_round0_pi_rho_chi_y0_zeta0':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y0_zeta0 (v_BASE_ROUND: usize) =
  keccakf1600_round0_pi_rho_chi_y0_zeta0' v_BASE_ROUND

assume
val keccakf1600_round0_pi_rho_chi_y0_zeta1':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y0_zeta1 (v_BASE_ROUND: usize) =
  keccakf1600_round0_pi_rho_chi_y0_zeta1' v_BASE_ROUND

assume
val keccakf1600_round0_pi_rho_chi_y1_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y1_zeta0 = keccakf1600_round0_pi_rho_chi_y1_zeta0'

assume
val keccakf1600_round0_pi_rho_chi_y1_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y1_zeta1 = keccakf1600_round0_pi_rho_chi_y1_zeta1'

assume
val keccakf1600_round0_pi_rho_chi_1_':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_1_ (v_BASE_ROUND: usize) =
  keccakf1600_round0_pi_rho_chi_1_' v_BASE_ROUND

assume
val keccakf1600_round0_pi_rho_chi_y2_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y2_zeta0 = keccakf1600_round0_pi_rho_chi_y2_zeta0'

assume
val keccakf1600_round0_pi_rho_chi_y2_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y2_zeta1 = keccakf1600_round0_pi_rho_chi_y2_zeta1'

assume
val keccakf1600_round0_pi_rho_chi_y3_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y3_zeta0 = keccakf1600_round0_pi_rho_chi_y3_zeta0'

assume
val keccakf1600_round0_pi_rho_chi_y3_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y3_zeta1 = keccakf1600_round0_pi_rho_chi_y3_zeta1'

assume
val keccakf1600_round0_pi_rho_chi_y4_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y4_zeta0 = keccakf1600_round0_pi_rho_chi_y4_zeta0'

assume
val keccakf1600_round0_pi_rho_chi_y4_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_y4_zeta1 = keccakf1600_round0_pi_rho_chi_y4_zeta1'

assume
val keccakf1600_round0_pi_rho_chi_2_': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round0_pi_rho_chi_2_ = keccakf1600_round0_pi_rho_chi_2_'

assume
val keccakf1600_round1_theta_c_x0_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x0_z0 = keccakf1600_round1_theta_c_x0_z0'

assume
val keccakf1600_round1_theta_c_x0_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x0_z1 = keccakf1600_round1_theta_c_x0_z1'

assume
val keccakf1600_round1_theta_c_x1_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x1_z0 = keccakf1600_round1_theta_c_x1_z0'

assume
val keccakf1600_round1_theta_c_x1_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x1_z1 = keccakf1600_round1_theta_c_x1_z1'

assume
val keccakf1600_round1_theta_c_x2_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x2_z0 = keccakf1600_round1_theta_c_x2_z0'

assume
val keccakf1600_round1_theta_c_x2_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x2_z1 = keccakf1600_round1_theta_c_x2_z1'

assume
val keccakf1600_round1_theta_c_x3_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x3_z0 = keccakf1600_round1_theta_c_x3_z0'

assume
val keccakf1600_round1_theta_c_x3_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x3_z1 = keccakf1600_round1_theta_c_x3_z1'

assume
val keccakf1600_round1_theta_c_x4_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x4_z0 = keccakf1600_round1_theta_c_x4_z0'

assume
val keccakf1600_round1_theta_c_x4_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_c_x4_z1 = keccakf1600_round1_theta_c_x4_z1'

assume
val keccakf1600_round1_theta_d': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta_d = keccakf1600_round1_theta_d'

assume
val keccakf1600_round1_theta': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_theta = keccakf1600_round1_theta'

assume
val keccakf1600_round1_pi_rho_chi_y0_zeta0':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y0_zeta0 (v_BASE_ROUND: usize) =
  keccakf1600_round1_pi_rho_chi_y0_zeta0' v_BASE_ROUND

assume
val keccakf1600_round1_pi_rho_chi_y0_zeta1':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y0_zeta1 (v_BASE_ROUND: usize) =
  keccakf1600_round1_pi_rho_chi_y0_zeta1' v_BASE_ROUND

assume
val keccakf1600_round1_pi_rho_chi_y1_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y1_zeta0 = keccakf1600_round1_pi_rho_chi_y1_zeta0'

assume
val keccakf1600_round1_pi_rho_chi_y1_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y1_zeta1 = keccakf1600_round1_pi_rho_chi_y1_zeta1'

assume
val keccakf1600_round1_pi_rho_chi_1_':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_1_ (v_BASE_ROUND: usize) =
  keccakf1600_round1_pi_rho_chi_1_' v_BASE_ROUND

assume
val keccakf1600_round1_pi_rho_chi_y2_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y2_zeta0 = keccakf1600_round1_pi_rho_chi_y2_zeta0'

assume
val keccakf1600_round1_pi_rho_chi_y2_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y2_zeta1 = keccakf1600_round1_pi_rho_chi_y2_zeta1'

assume
val keccakf1600_round1_pi_rho_chi_y3_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y3_zeta0 = keccakf1600_round1_pi_rho_chi_y3_zeta0'

assume
val keccakf1600_round1_pi_rho_chi_y3_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y3_zeta1 = keccakf1600_round1_pi_rho_chi_y3_zeta1'

assume
val keccakf1600_round1_pi_rho_chi_y4_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y4_zeta0 = keccakf1600_round1_pi_rho_chi_y4_zeta0'

assume
val keccakf1600_round1_pi_rho_chi_y4_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_y4_zeta1 = keccakf1600_round1_pi_rho_chi_y4_zeta1'

assume
val keccakf1600_round1_pi_rho_chi_2_': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round1_pi_rho_chi_2_ = keccakf1600_round1_pi_rho_chi_2_'

assume
val keccakf1600_round2_theta_c_x0_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x0_z0 = keccakf1600_round2_theta_c_x0_z0'

assume
val keccakf1600_round2_theta_c_x0_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x0_z1 = keccakf1600_round2_theta_c_x0_z1'

assume
val keccakf1600_round2_theta_c_x1_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x1_z0 = keccakf1600_round2_theta_c_x1_z0'

assume
val keccakf1600_round2_theta_c_x1_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x1_z1 = keccakf1600_round2_theta_c_x1_z1'

assume
val keccakf1600_round2_theta_c_x2_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x2_z0 = keccakf1600_round2_theta_c_x2_z0'

assume
val keccakf1600_round2_theta_c_x2_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x2_z1 = keccakf1600_round2_theta_c_x2_z1'

assume
val keccakf1600_round2_theta_c_x3_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x3_z0 = keccakf1600_round2_theta_c_x3_z0'

assume
val keccakf1600_round2_theta_c_x3_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x3_z1 = keccakf1600_round2_theta_c_x3_z1'

assume
val keccakf1600_round2_theta_c_x4_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x4_z0 = keccakf1600_round2_theta_c_x4_z0'

assume
val keccakf1600_round2_theta_c_x4_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_c_x4_z1 = keccakf1600_round2_theta_c_x4_z1'

assume
val keccakf1600_round2_theta_d': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta_d = keccakf1600_round2_theta_d'

assume
val keccakf1600_round2_theta': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_theta = keccakf1600_round2_theta'

assume
val keccakf1600_round2_pi_rho_chi_y0_zeta0':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y0_zeta0 (v_BASE_ROUND: usize) =
  keccakf1600_round2_pi_rho_chi_y0_zeta0' v_BASE_ROUND

assume
val keccakf1600_round2_pi_rho_chi_y0_zeta1':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y0_zeta1 (v_BASE_ROUND: usize) =
  keccakf1600_round2_pi_rho_chi_y0_zeta1' v_BASE_ROUND

assume
val keccakf1600_round2_pi_rho_chi_y1_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y1_zeta0 = keccakf1600_round2_pi_rho_chi_y1_zeta0'

assume
val keccakf1600_round2_pi_rho_chi_y1_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y1_zeta1 = keccakf1600_round2_pi_rho_chi_y1_zeta1'

assume
val keccakf1600_round2_pi_rho_chi_1_':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_1_ (v_BASE_ROUND: usize) =
  keccakf1600_round2_pi_rho_chi_1_' v_BASE_ROUND

assume
val keccakf1600_round2_pi_rho_chi_y2_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y2_zeta0 = keccakf1600_round2_pi_rho_chi_y2_zeta0'

assume
val keccakf1600_round2_pi_rho_chi_y2_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y2_zeta1 = keccakf1600_round2_pi_rho_chi_y2_zeta1'

assume
val keccakf1600_round2_pi_rho_chi_y3_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y3_zeta0 = keccakf1600_round2_pi_rho_chi_y3_zeta0'

assume
val keccakf1600_round2_pi_rho_chi_y3_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y3_zeta1 = keccakf1600_round2_pi_rho_chi_y3_zeta1'

assume
val keccakf1600_round2_pi_rho_chi_y4_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y4_zeta0 = keccakf1600_round2_pi_rho_chi_y4_zeta0'

assume
val keccakf1600_round2_pi_rho_chi_y4_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_y4_zeta1 = keccakf1600_round2_pi_rho_chi_y4_zeta1'

assume
val keccakf1600_round2_pi_rho_chi_2_': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round2_pi_rho_chi_2_ = keccakf1600_round2_pi_rho_chi_2_'

assume
val keccakf1600_round3_theta_c_x0_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x0_z0 = keccakf1600_round3_theta_c_x0_z0'

assume
val keccakf1600_round3_theta_c_x0_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x0_z1 = keccakf1600_round3_theta_c_x0_z1'

assume
val keccakf1600_round3_theta_c_x1_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x1_z0 = keccakf1600_round3_theta_c_x1_z0'

assume
val keccakf1600_round3_theta_c_x1_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x1_z1 = keccakf1600_round3_theta_c_x1_z1'

assume
val keccakf1600_round3_theta_c_x2_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x2_z0 = keccakf1600_round3_theta_c_x2_z0'

assume
val keccakf1600_round3_theta_c_x2_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x2_z1 = keccakf1600_round3_theta_c_x2_z1'

assume
val keccakf1600_round3_theta_c_x3_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x3_z0 = keccakf1600_round3_theta_c_x3_z0'

assume
val keccakf1600_round3_theta_c_x3_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x3_z1 = keccakf1600_round3_theta_c_x3_z1'

assume
val keccakf1600_round3_theta_c_x4_z0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x4_z0 = keccakf1600_round3_theta_c_x4_z0'

assume
val keccakf1600_round3_theta_c_x4_z1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_c_x4_z1 = keccakf1600_round3_theta_c_x4_z1'

assume
val keccakf1600_round3_theta_d': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta_d = keccakf1600_round3_theta_d'

assume
val keccakf1600_round3_theta': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_theta = keccakf1600_round3_theta'

assume
val keccakf1600_round3_pi_rho_chi_y0_zeta0':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y0_zeta0 (v_BASE_ROUND: usize) =
  keccakf1600_round3_pi_rho_chi_y0_zeta0' v_BASE_ROUND

assume
val keccakf1600_round3_pi_rho_chi_y0_zeta1':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y0_zeta1 (v_BASE_ROUND: usize) =
  keccakf1600_round3_pi_rho_chi_y0_zeta1' v_BASE_ROUND

assume
val keccakf1600_round3_pi_rho_chi_y1_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y1_zeta0 = keccakf1600_round3_pi_rho_chi_y1_zeta0'

assume
val keccakf1600_round3_pi_rho_chi_y1_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y1_zeta1 = keccakf1600_round3_pi_rho_chi_y1_zeta1'

assume
val keccakf1600_round3_pi_rho_chi_1_':
    v_BASE_ROUND: usize ->
    s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_1_ (v_BASE_ROUND: usize) =
  keccakf1600_round3_pi_rho_chi_1_' v_BASE_ROUND

assume
val keccakf1600_round3_pi_rho_chi_y2_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y2_zeta0 = keccakf1600_round3_pi_rho_chi_y2_zeta0'

assume
val keccakf1600_round3_pi_rho_chi_y2_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y2_zeta1 = keccakf1600_round3_pi_rho_chi_y2_zeta1'

assume
val keccakf1600_round3_pi_rho_chi_y3_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y3_zeta0 = keccakf1600_round3_pi_rho_chi_y3_zeta0'

assume
val keccakf1600_round3_pi_rho_chi_y3_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y3_zeta1 = keccakf1600_round3_pi_rho_chi_y3_zeta1'

assume
val keccakf1600_round3_pi_rho_chi_y4_zeta0': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y4_zeta0 = keccakf1600_round3_pi_rho_chi_y4_zeta0'

assume
val keccakf1600_round3_pi_rho_chi_y4_zeta1': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_y4_zeta1 = keccakf1600_round3_pi_rho_chi_y4_zeta1'

assume
val keccakf1600_round3_pi_rho_chi_2_': s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_round3_pi_rho_chi_2_ = keccakf1600_round3_pi_rho_chi_2_'

assume
val keccakf1600_4rounds': v_BASE_ROUND: usize -> s: Libcrux_iot_sha3.State.t_KeccakState
  -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600_4rounds (v_BASE_ROUND: usize) = keccakf1600_4rounds' v_BASE_ROUND

assume
val keccakf1600': s: Libcrux_iot_sha3.State.t_KeccakState -> Libcrux_iot_sha3.State.t_KeccakState

unfold
let keccakf1600 = keccakf1600'

let impl__absorb_full (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & usize)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE)
      (ensures
        fun temp_0_ ->
          let (self_e_future: t_KeccakXofState v_RATE), (remainder: usize) = temp_0_ in
          remainder <. v_RATE && remainder <=. (Core_models.Slice.impl__len #u8 inputs <: usize) &&
          self_e_future.f_buf_len <. v_RATE) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (self.f_buf_len <. v_RATE <: bool) in
      ()
  in
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__fill_buffer v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let input_consumed:usize = out in
  let self:t_KeccakXofState v_RATE =
    if input_consumed >. mk_usize 0
    then
      let self:t_KeccakXofState v_RATE =
        {
          self with
          f_inner
          =
          Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE
            self.f_inner
            (self.f_buf <: t_Slice u8)
            (mk_usize 0)
        }
        <:
        t_KeccakXofState v_RATE
      in
      let self:t_KeccakXofState v_RATE =
        { self with f_inner = keccakf1600 self.f_inner } <: t_KeccakXofState v_RATE
      in
      let self:t_KeccakXofState v_RATE =
        { self with f_buf_len = mk_usize 0 } <: t_KeccakXofState v_RATE
      in
      self
    else self
  in
  let input_to_consume:usize =
    (Core_models.Slice.impl__len #u8 inputs <: usize) -! input_consumed
  in
  let num_blocks:usize = input_to_consume /! v_RATE in
  let remainder:usize = input_to_consume %! v_RATE in
  let e_buf_len:usize = self.f_buf_len in
  let self:t_KeccakXofState v_RATE =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      num_blocks
      (fun self e_i ->
          let self:t_KeccakXofState v_RATE = self in
          let e_i:usize = e_i in
          self.f_buf_len =. e_buf_len <: bool)
      self
      (fun self i ->
          let self:t_KeccakXofState v_RATE = self in
          let i:usize = i in
          let self:t_KeccakXofState v_RATE =
            {
              self with
              f_inner
              =
              Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE
                self.f_inner
                inputs
                (input_consumed +! (i *! v_RATE <: usize) <: usize)
            }
            <:
            t_KeccakXofState v_RATE
          in
          let self:t_KeccakXofState v_RATE =
            { self with f_inner = keccakf1600 self.f_inner } <: t_KeccakXofState v_RATE
          in
          self)
  in
  let hax_temp_output:usize = remainder in
  self, hax_temp_output <: (t_KeccakXofState v_RATE & usize)

/// Absorb
/// This function takes any number of bytes to absorb and buffers if it\'s not enough.
/// The function assumes that all input slices in `blocks` have the same length.
/// Only a multiple of `RATE` blocks are absorbed.
/// For the remaining bytes [`absorb_final`] needs to be called.
/// This works best with relatively small `inputs`.
let impl__absorb (v_RATE: usize) (self: t_KeccakXofState v_RATE) (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE)
      (fun _ -> Prims.l_True) =
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__absorb_full v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let input_remainder_len:usize = out in
  let self:t_KeccakXofState v_RATE =
    if input_remainder_len >. mk_usize 0
    then
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            Hax_lib.v_assert ((self.f_buf_len =. mk_usize 0 <: bool) ||
                ((self.f_buf_len +! input_remainder_len <: usize) <=. v_RATE <: bool))
          in
          ()
      in
      let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
      let self:t_KeccakXofState v_RATE =
        {
          self with
          f_buf
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range self.f_buf
            ({
                Core_models.Ops.Range.f_start = self.f_buf_len;
                Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
              }
              <:
              Core_models.Ops.Range.t_Range usize)
            (Core_models.Slice.impl__copy_from_slice #u8
                (self.f_buf.[ {
                      Core_models.Ops.Range.f_start = self.f_buf_len;
                      Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (inputs.[ {
                      Core_models.Ops.Range.f_start = input_len -! input_remainder_len <: usize
                    }
                    <:
                    Core_models.Ops.Range.t_RangeFrom usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        }
        <:
        t_KeccakXofState v_RATE
      in
      let self:t_KeccakXofState v_RATE =
        { self with f_buf_len = self.f_buf_len +! input_remainder_len } <: t_KeccakXofState v_RATE
      in
      self
    else self
  in
  self

/// Absorb a final block.
/// The `inputs` block may be empty. Everything in the `inputs` block beyond
/// `RATE` bytes is ignored.
let impl__absorb_final
      (v_RATE: usize)
      (v_DELIMITER: u8)
      (self: t_KeccakXofState v_RATE)
      (inputs: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        self.f_buf_len <. v_RATE)
      (fun _ -> Prims.l_True) =
  let (tmp0: t_KeccakXofState v_RATE), (out: usize) = impl__absorb_full v_RATE self inputs in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let input_remainder_len:usize = out in
  let input_len:usize = Core_models.Slice.impl__len #u8 inputs in
  let blocks:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if self.f_buf_len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({
              Core_models.Ops.Range.f_start = mk_usize 0;
              Core_models.Ops.Range.f_end = self.f_buf_len
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = self.f_buf_len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (self.f_buf.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = self.f_buf_len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if input_remainder_len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({
              Core_models.Ops.Range.f_start = self.f_buf_len;
              Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
            }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = self.f_buf_len;
                    Core_models.Ops.Range.f_end = self.f_buf_len +! input_remainder_len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (inputs.[ {
                    Core_models.Ops.Range.f_start = input_len -! input_remainder_len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (self.f_buf_len +! input_remainder_len <: usize)
      (Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve v_DELIMITER <: u8)
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (v_RATE -! mk_usize 1 <: usize)
      ((blocks.[ v_RATE -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let self:t_KeccakXofState v_RATE =
    {
      self with
      f_inner
      =
      Libcrux_iot_sha3.State.impl_KeccakState__load_block_full v_RATE
        self.f_inner
        blocks
        (mk_usize 0)
    }
    <:
    t_KeccakXofState v_RATE
  in
  let self:t_KeccakXofState v_RATE =
    { self with f_inner = keccakf1600 self.f_inner } <: t_KeccakXofState v_RATE
  in
  self

#push-options "--z3rlimit 60"

let e_squeeze (v_RATE: usize) (keccak_state: t_KeccakXofState v_RATE) (out: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & t_Slice u8)
      (requires
        v_RATE =. mk_usize 168 || v_RATE =. mk_usize 144 || v_RATE =. mk_usize 136 ||
        v_RATE =. mk_usize 104 ||
        v_RATE =. mk_usize 72)
      (fun _ -> Prims.l_True) =
  let keccak_state:t_KeccakXofState v_RATE =
    if keccak_state.f_sponge
    then
      let keccak_state:t_KeccakXofState v_RATE =
        { keccak_state with f_inner = keccakf1600 keccak_state.f_inner } <: t_KeccakXofState v_RATE
      in
      keccak_state
    else keccak_state
  in
  let out_len:usize = Core_models.Slice.impl__len #u8 out in
  let blocks:usize = out_len /! v_RATE in
  let last:usize = out_len -! (out_len %! v_RATE <: usize) in
  let mid:usize = if v_RATE >=. out_len then out_len else v_RATE in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_to out
      ({ Core_models.Ops.Range.f_end = mid } <: Core_models.Ops.Range.t_RangeTo usize)
      (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
          keccak_state.f_inner
          (out.[ { Core_models.Ops.Range.f_end = mid } <: Core_models.Ops.Range.t_RangeTo usize ]
            <:
            t_Slice u8)
        <:
        t_Slice u8)
  in
  let offset:usize = mid in
  let (keccak_state: t_KeccakXofState v_RATE), (offset: usize), (out: t_Slice u8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
      blocks
      (fun temp_0_ e_k ->
          let (keccak_state: t_KeccakXofState v_RATE), (offset: usize), (out: t_Slice u8) =
            temp_0_
          in
          let e_k:usize = e_k in
          ((Core_models.Slice.impl__len #u8 out <: usize) =. out_len <: bool) &&
          ((Rust_primitives.Hax.Int.from_machine offset <: Hax_lib.Int.t_Int) =
            ((Rust_primitives.Hax.Int.from_machine e_k <: Hax_lib.Int.t_Int) *
              (Rust_primitives.Hax.Int.from_machine v_RATE <: Hax_lib.Int.t_Int)
              <:
              Hax_lib.Int.t_Int)
            <:
            bool))
      (keccak_state, offset, out <: (t_KeccakXofState v_RATE & usize & t_Slice u8))
      (fun temp_0_ e_k ->
          let (keccak_state: t_KeccakXofState v_RATE), (offset: usize), (out: t_Slice u8) =
            temp_0_
          in
          let e_k:usize = e_k in
          let keccak_state:t_KeccakXofState v_RATE =
            { keccak_state with f_inner = keccakf1600 keccak_state.f_inner }
            <:
            t_KeccakXofState v_RATE
          in
          let out:t_Slice u8 =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_range out
              ({
                  Core_models.Ops.Range.f_start = offset;
                  Core_models.Ops.Range.f_end = offset +! v_RATE <: usize
                }
                <:
                Core_models.Ops.Range.t_Range usize)
              (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
                  keccak_state.f_inner
                  (out.[ {
                        Core_models.Ops.Range.f_start = offset;
                        Core_models.Ops.Range.f_end = offset +! v_RATE <: usize
                      }
                      <:
                      Core_models.Ops.Range.t_Range usize ]
                    <:
                    t_Slice u8)
                <:
                t_Slice u8)
          in
          let offset:usize = offset +! v_RATE in
          keccak_state, offset, out <: (t_KeccakXofState v_RATE & usize & t_Slice u8))
  in
  let (keccak_state: t_KeccakXofState v_RATE), (out: t_Slice u8) =
    if last >. mk_usize 0 && last <. out_len
    then
      let _:Prims.unit =
        if true
        then
          let _:Prims.unit =
            match last, offset <: (usize & usize) with
            | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
          in
          ()
      in
      let keccak_state:t_KeccakXofState v_RATE =
        { keccak_state with f_inner = keccakf1600 keccak_state.f_inner } <: t_KeccakXofState v_RATE
      in
      let out:t_Slice u8 =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
          ({ Core_models.Ops.Range.f_start = offset } <: Core_models.Ops.Range.t_RangeFrom usize)
          (Libcrux_iot_sha3.State.impl_KeccakState__store v_RATE
              keccak_state.f_inner
              (out.[ { Core_models.Ops.Range.f_start = offset }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      keccak_state, out <: (t_KeccakXofState v_RATE & t_Slice u8)
    else keccak_state, out <: (t_KeccakXofState v_RATE & t_Slice u8)
  in
  let keccak_state:t_KeccakXofState v_RATE =
    { keccak_state with f_sponge = true } <: t_KeccakXofState v_RATE
  in
  keccak_state, out <: (t_KeccakXofState v_RATE & t_Slice u8)

#pop-options

/// Squeeze `N` x `LEN` bytes.
let impl__squeeze (v_RATE: usize) (self: t_KeccakXofState v_RATE) (out: t_Slice u8)
    : Prims.Pure (t_KeccakXofState v_RATE & t_Slice u8)
      (requires
        v_RATE =. mk_usize 168 || v_RATE =. mk_usize 144 || v_RATE =. mk_usize 136 ||
        v_RATE =. mk_usize 104 ||
        v_RATE =. mk_usize 72)
      (fun _ -> Prims.l_True) =
  let (tmp0: t_KeccakXofState v_RATE), (tmp1: t_Slice u8) = e_squeeze v_RATE self out in
  let self:t_KeccakXofState v_RATE = tmp0 in
  let out:t_Slice u8 = tmp1 in
  let _:Prims.unit = () in
  self, out <: (t_KeccakXofState v_RATE & t_Slice u8)

let absorb_block
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (blocks: t_Slice u8)
      (start: usize)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
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
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__load_block v_RATE s blocks start
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  s

let absorb_final
      (v_RATE: usize)
      (v_DELIM: u8)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (last: t_Slice u8)
      (start len: usize)
    : Prims.Pure Libcrux_iot_sha3.State.t_KeccakState
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168 &&
        len <. v_RATE &&
        ((Rust_primitives.Hax.Int.from_machine start <: Hax_lib.Int.t_Int) +
          (Rust_primitives.Hax.Int.from_machine len <: Hax_lib.Int.t_Int)
          <:
          Hax_lib.Int.t_Int) <=
        (Rust_primitives.Hax.Int.from_machine (Core_models.Slice.impl__len #u8 last <: usize)
          <:
          Hax_lib.Int.t_Int))
      (fun _ -> Prims.l_True) =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit = Hax_lib.v_assert (len <. v_RATE <: bool) in
      ()
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let blocks:t_Array u8 (mk_usize 200) =
    if len >. mk_usize 0
    then
      let blocks:t_Array u8 (mk_usize 200) =
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range blocks
          ({ Core_models.Ops.Range.f_start = mk_usize 0; Core_models.Ops.Range.f_end = len }
            <:
            Core_models.Ops.Range.t_Range usize)
          (Core_models.Slice.impl__copy_from_slice #u8
              (blocks.[ {
                    Core_models.Ops.Range.f_start = mk_usize 0;
                    Core_models.Ops.Range.f_end = len
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
              (last.[ {
                    Core_models.Ops.Range.f_start = start;
                    Core_models.Ops.Range.f_end = start +! len <: usize
                  }
                  <:
                  Core_models.Ops.Range.t_Range usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8)
      in
      blocks
    else blocks
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      len
      (Libcrux_secrets.Traits.f_classify #u8 #FStar.Tactics.Typeclasses.solve v_DELIM <: u8)
  in
  let blocks:t_Array u8 (mk_usize 200) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize blocks
      (v_RATE -! mk_usize 1 <: usize)
      ((blocks.[ v_RATE -! mk_usize 1 <: usize ] <: u8) |. mk_u8 128 <: u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    Libcrux_iot_sha3.State.impl_KeccakState__load_block_full v_RATE s blocks (mk_usize 0)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  s

let squeeze_first_block (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let out:t_Slice u8 = Libcrux_iot_sha3.State.impl_KeccakState__store_block v_RATE s out in
  out

let squeeze_next_block (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        v_RATE <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (ensures
        fun temp_0_ ->
          let (s_future: Libcrux_iot_sha3.State.t_KeccakState), (out_future: t_Slice u8) =
            temp_0_
          in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  let out:t_Slice u8 = Libcrux_iot_sha3.State.impl_KeccakState__store_block v_RATE s out in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_first_three_blocks
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (mk_usize 3 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = squeeze_first_block v_RATE s out in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_first_five_blocks
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (mk_usize 5 *! v_RATE <: usize) <=. (Core_models.Slice.impl__len #u8 out <: usize))
      (fun _ -> Prims.l_True) =
  let out:t_Slice u8 = squeeze_first_block v_RATE s out in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = v_RATE } <: Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 2 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 3 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 3 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
    squeeze_next_block v_RATE
      s
      (out.[ { Core_models.Ops.Range.f_start = mk_usize 4 *! v_RATE <: usize }
          <:
          Core_models.Ops.Range.t_RangeFrom usize ]
        <:
        t_Slice u8)
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
  let out:t_Slice u8 =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
      ({ Core_models.Ops.Range.f_start = mk_usize 4 *! v_RATE <: usize }
        <:
        Core_models.Ops.Range.t_RangeFrom usize)
      tmp1
  in
  let _:Prims.unit = () in
  s, out <: (Libcrux_iot_sha3.State.t_KeccakState & t_Slice u8)

let squeeze_last (v_RATE: usize) (s: Libcrux_iot_sha3.State.t_KeccakState) (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (Core_models.Slice.impl__len #u8 out <: usize) <=. mk_usize 200)
      (fun _ -> Prims.l_True) =
  let s:Libcrux_iot_sha3.State.t_KeccakState = keccakf1600 s in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_iot_sha3.State.impl_KeccakState__store_block_full v_RATE s b
  in
  let out:t_Slice u8 =
    Core_models.Slice.impl__copy_from_slice #u8
      out
      (b.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 out <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let squeeze_first_and_last
      (v_RATE: usize)
      (s: Libcrux_iot_sha3.State.t_KeccakState)
      (out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 && v_RATE <=. mk_usize 168 &&
        (Core_models.Slice.impl__len #u8 out <: usize) <=. mk_usize 200)
      (fun _ -> Prims.l_True) =
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_secrets.Traits.f_classify #(t_Array u8 (mk_usize 200))
      #FStar.Tactics.Typeclasses.solve
      (Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 200) <: t_Array u8 (mk_usize 200))
  in
  let b:t_Array u8 (mk_usize 200) =
    Libcrux_iot_sha3.State.impl_KeccakState__store_block_full v_RATE s b
  in
  let out:t_Slice u8 =
    Core_models.Slice.impl__copy_from_slice #u8
      out
      (b.[ {
            Core_models.Ops.Range.f_start = mk_usize 0;
            Core_models.Ops.Range.f_end = Core_models.Slice.impl__len #u8 out <: usize
          }
          <:
          Core_models.Ops.Range.t_Range usize ]
        <:
        t_Slice u8)
  in
  out

let v_WIDTH: usize = mk_usize 200

let keccak (v_RATE: usize) (v_DELIM: u8) (data out: t_Slice u8)
    : Prims.Pure (t_Slice u8)
      (requires
        v_RATE >. mk_usize 0 && (v_RATE %! mk_usize 8 <: usize) =. mk_usize 0 &&
        v_RATE <=. mk_usize 168)
      (ensures
        fun out_future ->
          let out_future:t_Slice u8 = out_future in
          (Core_models.Slice.impl__len #u8 out_future <: usize) =.
          (Core_models.Slice.impl__len #u8 out <: usize)) =
  let n:usize = (Core_models.Slice.impl__len #u8 data <: usize) /! v_RATE in
  let rem:usize = (Core_models.Slice.impl__len #u8 data <: usize) %! v_RATE in
  let outlen:usize = Core_models.Slice.impl__len #u8 out in
  let blocks:usize = outlen /! v_RATE in
  let last:usize = outlen -! (outlen %! v_RATE <: usize) in
  let s:Libcrux_iot_sha3.State.t_KeccakState = Libcrux_iot_sha3.State.impl_KeccakState__new () in
  let start:usize = mk_usize 0 in
  let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      n
      (fun temp_0_ e_i ->
          let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) = temp_0_ in
          let e_i:usize = e_i in
          start =. (e_i *! v_RATE <: usize) <: bool)
      (s, start <: (Libcrux_iot_sha3.State.t_KeccakState & usize))
      (fun temp_0_ e_i ->
          let (s: Libcrux_iot_sha3.State.t_KeccakState), (start: usize) = temp_0_ in
          let e_i:usize = e_i in
          let s:Libcrux_iot_sha3.State.t_KeccakState = absorb_block v_RATE s data start in
          let start:usize = start +! v_RATE in
          s, start <: (Libcrux_iot_sha3.State.t_KeccakState & usize))
  in
  let s:Libcrux_iot_sha3.State.t_KeccakState =
    absorb_final v_RATE
      v_DELIM
      s
      data
      ((Core_models.Slice.impl__len #u8 data <: usize) -! rem <: usize)
      rem
  in
  let (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
    if blocks =. mk_usize 0
    then
      squeeze_first_and_last v_RATE s out, s <: (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
    else
      let out:t_Slice u8 = squeeze_first_block v_RATE s out in
      let offset:usize = v_RATE in
      let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 1)
          blocks
          (fun temp_0_ e_i ->
              let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
                temp_0_
              in
              let e_i:usize = e_i in
              ((Core_models.Slice.impl__len #u8 out <: usize) =. outlen <: bool) &&
              (offset =. (e_i *! v_RATE <: usize) <: bool))
          (offset, out, s <: (usize & t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState))
          (fun temp_0_ e_i ->
              let (offset: usize), (out: t_Slice u8), (s: Libcrux_iot_sha3.State.t_KeccakState) =
                temp_0_
              in
              let e_i:usize = e_i in
              let (tmp0: Libcrux_iot_sha3.State.t_KeccakState), (tmp1: t_Slice u8) =
                squeeze_next_block v_RATE
                  s
                  (out.[ { Core_models.Ops.Range.f_start = offset }
                      <:
                      Core_models.Ops.Range.t_RangeFrom usize ]
                    <:
                    t_Slice u8)
              in
              let s:Libcrux_iot_sha3.State.t_KeccakState = tmp0 in
              let out:t_Slice u8 =
                Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
                  ({ Core_models.Ops.Range.f_start = offset }
                    <:
                    Core_models.Ops.Range.t_RangeFrom usize)
                  tmp1
              in
              let _:Prims.unit = () in
              let offset:usize = offset +! v_RATE in
              offset, out, s <: (usize & t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState))
      in
      if last <. outlen
      then
        let _:Prims.unit =
          if true
          then
            let _:Prims.unit =
              match last, offset <: (usize & usize) with
              | left_val, right_val -> Hax_lib.v_assert (left_val =. right_val <: bool)
            in
            ()
        in
        Rust_primitives.Hax.Monomorphized_update_at.update_at_range_from out
          ({ Core_models.Ops.Range.f_start = offset } <: Core_models.Ops.Range.t_RangeFrom usize)
          (squeeze_last v_RATE
              s
              (out.[ { Core_models.Ops.Range.f_start = offset }
                  <:
                  Core_models.Ops.Range.t_RangeFrom usize ]
                <:
                t_Slice u8)
            <:
            t_Slice u8),
        s
        <:
        (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
      else out, s <: (t_Slice u8 & Libcrux_iot_sha3.State.t_KeccakState)
  in
  out
