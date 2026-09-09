/-
  Composition of the structural and algebraic equivalences.

  Combines
  - `Structural.keccakf1600_eq`         (impl ≡ bit_keccak_spec on the pure-Lean side, via mvcgen),
  - `Algebraic.bit_keccak_spec_alg_eq`  (24-fold spec on `lift s` equals `lift` of the
                                         pure-Lean bit_keccak_spec output, via algebra),
  to retarget the impl-level post `keccakf1600_post_canonical`. The canonical
  `lift r_impl` shape (no `lift_perm`) follows from the time-varying
  `impl_swap_k` cycle reaching `swZero` at round 24; no `BalancedAt`
  precondition is required.
-/
import LibcruxIotSha3.AlgebraicEquiv

namespace libcrux_iot_sha3.Composition

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3
open libcrux_iot_sha3.Foundation
open libcrux_iot_sha3.BitSpec
open libcrux_iot_sha3.Structural
open libcrux_iot_sha3.Algebraic

theorem keccakf1600_equiv_via_bit (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakf1600_post_canonical s r_impl ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_eq s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_fromAeneas
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_fromAeneas ⊢
  unfold keccakf1600_post_canonical
  -- Bridge: the Nat.fold IS `spec_chain` (just inlined).
  have h_post_eq :
      (do let lifted_final ← Nat.fold 24
            (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
            (pure (Foundation.lift s))
          pure (lifted_final = Foundation.lift r)).holds
      = (do let lifted_final ← spec_chain (Foundation.lift s) 24
            pure (lifted_final = Foundation.lift r)).holds := by
    unfold spec_chain spec_round_step_at
    congr 1
  rw [h_post_eq]
  -- Bridge lift s → lift (toAeneas (fromAeneas s)) via toAeneas_fromAeneas round-trip.
  rw [show (Foundation.lift s : Array Std.U64 25#usize)
        = Foundation.lift (KState.toAeneas (KState.fromAeneas s)) from by
        rw [KState.toAeneas_fromAeneas]]
  -- Apply the algebraic equivalence (unconditional).
  have h_i' : (KState.fromAeneas s).i = 0#usize := by
    show (KState.fromAeneas s).i = 0#usize
    unfold KState.fromAeneas
    exact h_i
  rw [bit_keccak_spec_alg_eq (KState.fromAeneas s) h_i']
  unfold bit_keccak_spec at h_fromAeneas
  -- Bridge: r.st = (toAeneas (iter^[6] (fromAeneas s))).st (since `lift`
  -- reads only .st, and `with i := 0` preserves `.st` on both sides).
  have h_lift_st_only :
      ∀ (a b : state.KeccakState), a.st = b.st →
        Foundation.lift a = Foundation.lift b := by
    intro a b hab
    unfold Foundation.lift
    apply Subtype.ext
    show List.ofFn (fun i : Fin 25 => lift_lane (a.st.val[(transpose_perm i).val]!))
       = List.ofFn (fun i : Fin 25 => lift_lane (b.st.val[(transpose_perm i).val]!))
    rw [hab]
  have h_r_eq_iter_st :
      r.st = (KState.toAeneas
                (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s))).st := by
    have hrt : r.st = stateArray25ToAeneas (KState.fromAeneas r).st :=
      (stateArray25_toAeneas_fromAeneas r.st).symm
    rw [hrt]
    have h_from_st : (KState.fromAeneas r).st
                   = (Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 (KState.fromAeneas s)).st := by
      rw [h_fromAeneas]
    rw [h_from_st]
    rfl
  apply pure_prop_holds
  exact h_lift_st_only _ _ h_r_eq_iter_st.symm

end libcrux_iot_sha3.Composition
