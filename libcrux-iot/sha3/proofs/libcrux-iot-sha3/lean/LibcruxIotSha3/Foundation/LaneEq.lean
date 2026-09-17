import LibcruxIotSha3.Foundation.SpecChain
import LibcruxIotSha3.LaneModel
/-!
# `Foundation/`'s pure step semantics are the lane model

`Foundation/` names the five step mappings `theta_applied`, `rho_applied`,
`pi_applied`, `chi_applied` and `iota_applied`: twenty-five cells written out
one by one, which is the shape the implementation-side `mvcgen` proofs need to
see.  `LibcruxIotSha3/LaneModel.lean` names the same five as indexed functions,
which is the shape the FIPS-202 bit-level proofs need.

They are the same functions, and this file says so.  That is what joins the two
halves of the proof once `hacspec_sha3` -- which used to sit between them --
is gone.
-/

open Aeneas Aeneas.Std
open LibcruxIotSha3.LaneModel

namespace libcrux_iot_sha3.Foundation

theorem theta_applied_eq (s : Lanes) : theta_applied s = thetaLanes s := by
  apply Subtype.ext
  unfold theta_applied thetaLanes mkArr cLane dLane
  rfl

theorem rho_applied_eq (s : Lanes) : rho_applied s = rhoLanes s := by
  apply Subtype.ext
  unfold rho_applied rhoLanes mkArr rot64 libcrux_iot_sha3.rhoOffsets
  rfl

theorem pi_applied_eq (s : Lanes) : pi_applied s = piLanes s := by
  apply Subtype.ext
  unfold pi_applied piLanes mkArr
  rfl

theorem chi_applied_eq (s : Lanes) : chi_applied s = chiLanes s := by
  apply Subtype.ext
  unfold chi_applied chiLanes mkArr
  rfl

theorem iota_applied_eq (s : Lanes) (r : Std.Usize) :
    iota_applied s r = iotaLanes s r.val := by
  unfold iota_applied iotaLanes
  rfl

/-- One round: `Foundation/`'s `prc_spec ∘ theta_applied` is `roundLanes`. -/
theorem prc_spec_theta_eq (s : Lanes) (r : Std.Usize) :
    prc_spec (theta_applied s) r = roundLanes s r.val := by
  rw [← prc_spec_eq_composed, theta_applied_eq, rho_applied_eq, pi_applied_eq,
    chi_applied_eq, iota_applied_eq]
  rfl

/-! ### The 24-round chain

`spec_chain` is the `Nat.fold` of `spec_round_step` that
`keccakf1600_post_canonical` is phrased with; `roundsUpTo` is the lane
model's.  They agree as far as the round constants reach. -/

theorem spec_round_step_at_eq (i : Nat) (hi : i < 24) (st : Lanes) :
    spec_round_step_at i st = .ok (roundLanes st i) := by
  unfold spec_round_step_at
  rw [dif_pos hi]
  unfold spec_round_step
  rw [prc_spec_theta_eq]
  rfl

theorem spec_chain_eq_roundsUpTo (s : Lanes) (n : Nat) (hn : n ≤ 24) :
    spec_chain s n = .ok (roundsUpTo s n) := by
  induction n with
  | zero => rw [spec_chain_zero]; rfl
  | succ k ih =>
    rw [spec_chain_succ, ih (by omega), bind_tc_ok,
      spec_round_step_at_eq k (by omega)]
    rfl

/-- The lane model's `Keccak-f[1600]` is the 24-fold `spec_chain` the
    implementation-side proof produces. -/
theorem spec_chain_24 (s : Lanes) : spec_chain s 24 = .ok (keccakFLanes s) :=
  spec_chain_eq_roundsUpTo s 24 (le_refl _)

end libcrux_iot_sha3.Foundation
