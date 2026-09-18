import LibcruxIotSha3.Composition.LoopSpecUsize
import LibcruxIotSha3.Foundation.LaneEq
/-!
# The implementation computes the lane model's `Keccak-f[1600]`

`Composition/ViaBit.lean` proves the implementation's `keccakf1600` satisfies
`keccakf1600_post_canonical`, the 24-fold of `spec_round_step`.  This file reads
that as the lane model's `keccakFLanes`, which `Composition/Pedantic/Lanes.lean`
ties to FIPS 202.  It is what `Sponge/` is sealed on.
-/

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3
open LibcruxIotSha3.LaneModel

namespace libcrux_iot_sha3.Composition

open libcrux_iot_sha3.Foundation

/-- The implementation's `keccakf1600` computes `keccakFLanes` on the lifted
    state.  Composes `keccakf1600_equiv_via_bit`'s canonical post with
    `spec_chain_24`. -/
theorem keccakf1600_equiv_lanes (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakFLanes (Foundation.lift s) = Foundation.lift r_impl ⌝ ⦄ := by
  apply Std.Do.Triple.of_entails_right _ (keccakf1600_equiv_via_bit s h_i)
  rw [PostCond.entails_noThrow]
  intro r h_post
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure] at h_post ⊢
  unfold keccakf1600_post_canonical at h_post
  have h_chain :
      (do let lifted_final ← spec_chain (Foundation.lift s) 24
          pure (lifted_final = Foundation.lift r)).holds := by
    have h_eq :
        (do let lifted_final ← Nat.fold 24
              (fun i h acc => acc >>= fun st => spec_round_step st (roundOfNat i (by omega)))
              (pure (Foundation.lift s))
            pure (lifted_final = Foundation.lift r)).holds
        = (do let lifted_final ← spec_chain (Foundation.lift s) 24
              pure (lifted_final = Foundation.lift r)).holds := by
      unfold spec_chain spec_round_step_at
      congr 1
    rw [h_eq] at h_post
    exact h_post
  have h_spec_chain : spec_chain (Foundation.lift s) 24 = .ok (Foundation.lift r) :=
    holds_chain_eq_ok h_chain
  rw [spec_chain_24] at h_spec_chain
  exact (RustM.ok.injEq _ _).mp h_spec_chain

end libcrux_iot_sha3.Composition
