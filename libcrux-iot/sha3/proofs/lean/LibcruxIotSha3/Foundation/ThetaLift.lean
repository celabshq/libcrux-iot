/-
  θ-step impl/spec lifting — the public spec-coupling theorem.

  Helper definitions (`lift_theta_applied`, per-sub-function `@[spec]`s,
  `theta_comp_spec_local`, and the 25 `lift_getElem_bv_*` peel lemmas)
  live in `ThetaLiftDefs.lean`. This file only contains the final
  spec-coupling theorem `theta_lift_spec`, so editing its proof body
  does not invalidate downstream caches (`PrcLift` etc.) that only need
  the definitions.
-/
import LibcruxIotSha3.Foundation.ThetaLiftDefs

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false

attribute [local irreducible] spread_to_even lift_lane_bv

/-! Spec-coupling Triple for round-0 θ, in `.holds`-in-post form so it can
    be tagged `@[spec]` and used by `hax_mvcgen` whenever a downstream
    function calls `keccakf1600_round0_theta`. The post says: for the
    `r_impl` produced by impl-θ, the spec computation
    `keccak_f.theta (lift s)` succeeds with result equal to
    `lift_theta_applied r_impl`. The `r_impl.i = s.i` conjunct lets
    downstream consumers (`prc_lift_spec`, `round0_equiv_spec`) discharge
    their `s.i.val < 24` preconditions on the θ output. -/
set_option maxHeartbeats 16000000 in
@[spec]
theorem theta_lift_spec (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round0_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta (lift s)
        pure (r_spec = lift_theta_applied r_impl)).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local s)
  rw [PostCond.entails_noThrow]
  intro r_impl hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  refine ⟨hpost.2.1, ?_⟩
  -- Reduce `keccak_f.theta (lift s)` to `.ok (theta_applied (lift s))` via
  -- the @[spec] proven in `ThetaLiftDefs`.
  show (do let r_spec ← keccak_f.theta (lift s)
           pure (r_spec = lift_theta_applied r_impl)).holds
  rw [show keccak_f.theta (lift s) = .ok (theta_applied (lift s)) from
        result_eq_of_triple (theta_spec (lift s))]
  -- Goal: (do let r_spec ← .ok (theta_applied (lift s)); pure (...)).holds
  -- which reduces to: theta_applied (lift s) = lift_theta_applied r_impl.
  show ⦃⌜True⌝⦄ Result.ok (theta_applied (lift s) = lift_theta_applied r_impl) ⦃PostCond.noThrow fun p => ⌜p⌝⦄
  simp [Std.Do.Triple, Std.Do.WP.wp]
  show theta_applied (lift s) = lift_theta_applied r_impl
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold theta_applied lift_theta_applied
  simp only [Std.Array.make, hst,
             hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
             hd3z0, hd3z1, hd4z0, hd4z1]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  all_goals
    simp_all only [Std.UScalar.bv_xor, rot32]
  all_goals
    simp only [lift_getElem_bv_0, lift_getElem_bv_1, lift_getElem_bv_2,
      lift_getElem_bv_3, lift_getElem_bv_4, lift_getElem_bv_5,
      lift_getElem_bv_6, lift_getElem_bv_7, lift_getElem_bv_8,
      lift_getElem_bv_9, lift_getElem_bv_10, lift_getElem_bv_11,
      lift_getElem_bv_12, lift_getElem_bv_13, lift_getElem_bv_14,
      lift_getElem_bv_15, lift_getElem_bv_16, lift_getElem_bv_17,
      lift_getElem_bv_18, lift_getElem_bv_19, lift_getElem_bv_20,
      lift_getElem_bv_21, lift_getElem_bv_22, lift_getElem_bv_23,
      lift_getElem_bv_24]
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]

end libcrux_iot_sha3.Foundation
