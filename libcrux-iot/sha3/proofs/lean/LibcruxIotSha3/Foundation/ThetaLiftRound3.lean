/-
  Round-3 θ lift spec.

  Round 3's theta operates on a state in round-2 layout, i.e.
  `lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)`.
-/
import LibcruxIotSha3.Foundation.ThetaLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false

attribute [local spec] Aeneas.Std.uncurry

attribute [local irreducible] spread_to_even lift_lane_bv

/-! ## Round-3 per-c-cell sub-function specs

XOR chain order matches the impl: `ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4`
in canonical position order 5*x, 5*x+1, ..., 5*x+4. Zetas follow
`impl_swap_k 3` (true iff position ∈ {1,4,6,7,10,11,13,15,17,19,23,24})
for c[x][0] reads. -/

@[spec]
private theorem theta_c_x0_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 0#usize
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x0_z0

@[spec]
private theorem theta_c_x0_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x0_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 0#usize ((s.c.val[0]!).set 1#usize
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x0_z1

@[spec]
private theorem theta_c_x1_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 0#usize
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x1_z0

@[spec]
private theorem theta_c_x1_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x1_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 1#usize ((s.c.val[1]!).set 1#usize
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x1_z1

@[spec]
private theorem theta_c_x2_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 0#usize
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x2_z0

@[spec]
private theorem theta_c_x2_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x2_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 2#usize ((s.c.val[2]!).set 1#usize
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x2_z1

@[spec]
private theorem theta_c_x3_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 0#usize
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x3_z0

@[spec]
private theorem theta_c_x3_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x3_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 3#usize ((s.c.val[3]!).set 1#usize
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x3_z1

@[spec]
private theorem theta_c_x4_z0_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z0 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 0#usize
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x4_z0

@[spec]
private theorem theta_c_x4_z1_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_c_x4_z1 s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.d = s.d ∧
        r.c = s.c.set 4#usize ((s.c.val[4]!).set 1#usize
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!)) ⌝ ⦄ := by
  theta_c_proof keccak.keccakf1600_round3_theta_c_x4_z1

set_option maxHeartbeats 1600000 in
@[spec]
private theorem theta_d_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round3_theta_d s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧ r.c = s.c ∧
        r.d.val[0]!.val[0]! =
          s.c.val[4]!.val[0]! ^^^ rot32 s.c.val[1]!.val[1]! 1 ∧
        r.d.val[0]!.val[1]! =
          s.c.val[4]!.val[1]! ^^^ s.c.val[1]!.val[0]! ∧
        r.d.val[1]!.val[0]! =
          s.c.val[0]!.val[0]! ^^^ rot32 s.c.val[2]!.val[1]! 1 ∧
        r.d.val[1]!.val[1]! =
          s.c.val[0]!.val[1]! ^^^ s.c.val[2]!.val[0]! ∧
        r.d.val[2]!.val[0]! =
          s.c.val[1]!.val[0]! ^^^ rot32 s.c.val[3]!.val[1]! 1 ∧
        r.d.val[2]!.val[1]! =
          s.c.val[1]!.val[1]! ^^^ s.c.val[3]!.val[0]! ∧
        r.d.val[3]!.val[0]! =
          s.c.val[2]!.val[0]! ^^^ rot32 s.c.val[4]!.val[1]! 1 ∧
        r.d.val[3]!.val[1]! =
          s.c.val[2]!.val[1]! ^^^ s.c.val[4]!.val[0]! ∧
        r.d.val[4]!.val[0]! =
          s.c.val[3]!.val[0]! ^^^ rot32 s.c.val[0]!.val[1]! 1 ∧
        r.d.val[4]!.val[1]! =
          s.c.val[3]!.val[1]! ^^^ s.c.val[0]!.val[0]! ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta_d
  mvcgen
  all_goals first
    | scalar_tac
    | (refine ⟨trivial, trivial, trivial, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
       (apply Std.U32.bv_eq_imp_eq
        simp_all [WP.uncurry', Std.Array.set_val_eq,
                  Std.UScalar.bv_xor, rot32]))

set_option maxHeartbeats 4000000 in
theorem theta_comp_spec_local_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r => ⌜ r.st = s.st ∧ r.i = s.i ∧
        r.d.val[0]!.val[0]! =
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ^^^
          rot32 (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
                 s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
                 s.st.val[9]!.val[1]!) 1 ∧
        r.d.val[0]!.val[1]! =
          (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
           s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
           s.st.val[24]!.val[0]!) ^^^
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ∧
        r.d.val[1]!.val[0]! =
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ^^^
          rot32 (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
                 s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
                 s.st.val[14]!.val[1]!) 1 ∧
        r.d.val[1]!.val[1]! =
          (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
           s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
           s.st.val[4]!.val[0]!) ^^^
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!) ∧
        r.d.val[2]!.val[0]! =
          (s.st.val[5]!.val[0]! ^^^ s.st.val[6]!.val[1]! ^^^
           s.st.val[7]!.val[1]! ^^^ s.st.val[8]!.val[0]! ^^^
           s.st.val[9]!.val[0]!) ^^^
          rot32 (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
                 s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
                 s.st.val[19]!.val[0]!) 1 ∧
        r.d.val[2]!.val[1]! =
          (s.st.val[5]!.val[1]! ^^^ s.st.val[6]!.val[0]! ^^^
           s.st.val[7]!.val[0]! ^^^ s.st.val[8]!.val[1]! ^^^
           s.st.val[9]!.val[1]!) ^^^
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ∧
        r.d.val[3]!.val[0]! =
          (s.st.val[10]!.val[1]! ^^^ s.st.val[11]!.val[1]! ^^^
           s.st.val[12]!.val[0]! ^^^ s.st.val[13]!.val[1]! ^^^
           s.st.val[14]!.val[0]!) ^^^
          rot32 (s.st.val[20]!.val[1]! ^^^ s.st.val[21]!.val[1]! ^^^
                 s.st.val[22]!.val[1]! ^^^ s.st.val[23]!.val[0]! ^^^
                 s.st.val[24]!.val[0]!) 1 ∧
        r.d.val[3]!.val[1]! =
          (s.st.val[10]!.val[0]! ^^^ s.st.val[11]!.val[0]! ^^^
           s.st.val[12]!.val[1]! ^^^ s.st.val[13]!.val[0]! ^^^
           s.st.val[14]!.val[1]!) ^^^
          (s.st.val[20]!.val[0]! ^^^ s.st.val[21]!.val[0]! ^^^
           s.st.val[22]!.val[0]! ^^^ s.st.val[23]!.val[1]! ^^^
           s.st.val[24]!.val[1]!) ∧
        r.d.val[4]!.val[0]! =
          (s.st.val[15]!.val[1]! ^^^ s.st.val[16]!.val[0]! ^^^
           s.st.val[17]!.val[1]! ^^^ s.st.val[18]!.val[0]! ^^^
           s.st.val[19]!.val[1]!) ^^^
          rot32 (s.st.val[0]!.val[1]! ^^^ s.st.val[1]!.val[0]! ^^^
                 s.st.val[2]!.val[1]! ^^^ s.st.val[3]!.val[1]! ^^^
                 s.st.val[4]!.val[0]!) 1 ∧
        r.d.val[4]!.val[1]! =
          (s.st.val[15]!.val[0]! ^^^ s.st.val[16]!.val[1]! ^^^
           s.st.val[17]!.val[0]! ^^^ s.st.val[18]!.val[1]! ^^^
           s.st.val[19]!.val[0]!) ^^^
          (s.st.val[0]!.val[0]! ^^^ s.st.val[1]!.val[1]! ^^^
           s.st.val[2]!.val[0]! ^^^ s.st.val[3]!.val[0]! ^^^
           s.st.val[4]!.val[1]!) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round3_theta
  hax_mvcgen
  all_goals first
    | trivial
    | grind
    | simp_all

/-! ## Round-3 spec-input lane peel infrastructure

Mirrors the round-1 structure with `impl_perm ∘ impl_perm ∘ impl_perm` for
`p` and `impl_swap_k 3` for `sw`. The mapping `(impl_perm³ K).val = L` and
`impl_swap_k 3 L` polarity per K ∈ {0..24} is fixed and decidable. -/

/-! ## RHS-side rewriting: `lift_theta_applied_perm`'s `lift_lane_maybe_swap`
    cells at concrete `Fin 25` indices, for round 3 (perm³ + impl_swap_k 3). -/

private theorem lta_perm_bv_0_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 0))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 0))))).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 0))).val = 0 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 0))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_1_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 1))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 1))))).bv =
      lift_lane_bv ((s.st.val[3]!).val[0]!.bv) ((s.st.val[3]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 1))).val = 3 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 1))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_2_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 2))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 2))))).bv =
      lift_lane_bv ((s.st.val[1]!).val[1]!.bv) ((s.st.val[1]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 2))).val = 1 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 2))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_3_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 3))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 3))))).bv =
      lift_lane_bv ((s.st.val[4]!).val[1]!.bv) ((s.st.val[4]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 3))).val = 4 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 3))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_4_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 4))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 4))))).bv =
      lift_lane_bv ((s.st.val[2]!).val[0]!.bv) ((s.st.val[2]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 4))).val = 2 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 4))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_5_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 5))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 5))))).bv =
      lift_lane_bv ((s.st.val[7]!).val[1]!.bv) ((s.st.val[7]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 5))).val = 7 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 5))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_6_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 6))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 6))))).bv =
      lift_lane_bv ((s.st.val[5]!).val[0]!.bv) ((s.st.val[5]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 6))).val = 5 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 6))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_7_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 7))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 7))))).bv =
      lift_lane_bv ((s.st.val[8]!).val[0]!.bv) ((s.st.val[8]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 7))).val = 8 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 7))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_8_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 8))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 8))))).bv =
      lift_lane_bv ((s.st.val[6]!).val[1]!.bv) ((s.st.val[6]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 8))).val = 6 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 8))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_9_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 9))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 9))))).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 9))).val = 9 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 9))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_10_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 10))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 10))))).bv =
      lift_lane_bv ((s.st.val[14]!).val[0]!.bv) ((s.st.val[14]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 10))).val = 14 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 10))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_11_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 11))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 11))))).bv =
      lift_lane_bv ((s.st.val[12]!).val[0]!.bv) ((s.st.val[12]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 11))).val = 12 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 11))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_12_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 12))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 12))))).bv =
      lift_lane_bv ((s.st.val[10]!).val[1]!.bv) ((s.st.val[10]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 12))).val = 10 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 12))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_13_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 13))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 13))))).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 13))).val = 13 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 13))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_14_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 14))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 14))))).bv =
      lift_lane_bv ((s.st.val[11]!).val[1]!.bv) ((s.st.val[11]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 14))).val = 11 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 14))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_15_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 15))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 15))))).bv =
      lift_lane_bv ((s.st.val[16]!).val[0]!.bv) ((s.st.val[16]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 15))).val = 16 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 15))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_16_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 16))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 16))))).bv =
      lift_lane_bv ((s.st.val[19]!).val[1]!.bv) ((s.st.val[19]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 16))).val = 19 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 16))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_17_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 17))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 17))))).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 17))).val = 17 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 17))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_18_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 18))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 18))))).bv =
      lift_lane_bv ((s.st.val[15]!).val[1]!.bv) ((s.st.val[15]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 18))).val = 15 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 18))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_19_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 19))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 19))))).bv =
      lift_lane_bv ((s.st.val[18]!).val[0]!.bv) ((s.st.val[18]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 19))).val = 18 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 19))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_20_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 20))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 20))))).bv =
      lift_lane_bv ((s.st.val[23]!).val[1]!.bv) ((s.st.val[23]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 20))).val = 23 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 20))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_21_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 21))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 21))))).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 21))).val = 21 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 21))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_22_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 22))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 22))))).bv =
      lift_lane_bv ((s.st.val[24]!).val[1]!.bv) ((s.st.val[24]!).val[0]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 22))).val = 24 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 22))) = true := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_true_bv]
private theorem lta_perm_bv_23_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 23))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 23))))).bv =
      lift_lane_bv ((s.st.val[22]!).val[0]!.bv) ((s.st.val[22]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 23))).val = 22 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 23))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]
private theorem lta_perm_bv_24_3 (s : state.KeccakState) :
    (lift_lane_maybe_swap
        (s.st.val[(impl_perm (impl_perm (impl_perm 24))).val]!)
        (impl_swap_k 3 (impl_perm (impl_perm (impl_perm 24))))).bv =
      lift_lane_bv ((s.st.val[20]!).val[0]!.bv) ((s.st.val[20]!).val[1]!.bv) := by
  have hp : (impl_perm (impl_perm (impl_perm 24))).val = 20 := by decide
  have hsw : impl_swap_k 3 (impl_perm (impl_perm (impl_perm 24))) = false := by rw [impl_swap_k_three]; decide
  rw [hp, hsw, lift_lane_maybe_swap_false_bv]

/-- 25 LHS-peel lemmas: each `lift_perm_getElem_bv_K_3` exposes the spec-side
    input lane `K` (post-perm³, post-swap-k-3) as `lift_lane_bv ...halves...`. -/
private theorem lift_perm_getElem_bv_0_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(0 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]!.bv) ((s.st.val[0]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨0, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨0, by decide⟩)).val = 0 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨0, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_1_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(1 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[1]!.bv) ((s.st.val[7]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨1, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨1, by decide⟩)).val = 7 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨1, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_2_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(2 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[0]!.bv) ((s.st.val[14]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨2, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨2, by decide⟩)).val = 14 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨2, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_3_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(3 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[0]!.bv) ((s.st.val[16]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨3, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨3, by decide⟩)).val = 16 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨3, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_4_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(4 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[1]!.bv) ((s.st.val[23]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨4, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨4, by decide⟩)).val = 23 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨4, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_5_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(5 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[0]!.bv) ((s.st.val[3]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨5, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨5, by decide⟩)).val = 3 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨5, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_6_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(6 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[0]!.bv) ((s.st.val[5]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨6, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨6, by decide⟩)).val = 5 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨6, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_7_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(7 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[0]!.bv) ((s.st.val[12]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨7, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨7, by decide⟩)).val = 12 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨7, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_8_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(8 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[1]!.bv) ((s.st.val[19]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨8, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨8, by decide⟩)).val = 19 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨8, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_9_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(9 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]!.bv) ((s.st.val[21]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨9, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨9, by decide⟩)).val = 21 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨9, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_10_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(10 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[1]!.bv) ((s.st.val[1]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨10, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨10, by decide⟩)).val = 1 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨10, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_11_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(11 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[0]!.bv) ((s.st.val[8]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨11, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨11, by decide⟩)).val = 8 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨11, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_12_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(12 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[1]!.bv) ((s.st.val[10]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨12, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨12, by decide⟩)).val = 10 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨12, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_13_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(13 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]!.bv) ((s.st.val[17]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨13, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨13, by decide⟩)).val = 17 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨13, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_14_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(14 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[1]!.bv) ((s.st.val[24]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨14, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨14, by decide⟩)).val = 24 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨14, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_15_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(15 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[1]!.bv) ((s.st.val[4]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨15, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨15, by decide⟩)).val = 4 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨15, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_16_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(16 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[1]!.bv) ((s.st.val[6]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨16, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨16, by decide⟩)).val = 6 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨16, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_17_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(17 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]!.bv) ((s.st.val[13]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨17, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨17, by decide⟩)).val = 13 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨17, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_18_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(18 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[1]!.bv) ((s.st.val[15]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨18, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨18, by decide⟩)).val = 15 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨18, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_19_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(19 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[0]!.bv) ((s.st.val[22]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨19, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨19, by decide⟩)).val = 22 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨19, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_20_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(20 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[0]!.bv) ((s.st.val[2]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨20, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨20, by decide⟩)).val = 2 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨20, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_21_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(21 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]!.bv) ((s.st.val[9]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨21, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨21, by decide⟩)).val = 9 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨21, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_22_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(22 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[1]!.bv) ((s.st.val[11]!).val[0]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨22, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨22, by decide⟩)).val = 11 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨22, by decide⟩)) = true := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_true_bv]

private theorem lift_perm_getElem_bv_23_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(23 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[0]!.bv) ((s.st.val[18]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨23, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨23, by decide⟩)).val = 18 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨23, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

private theorem lift_perm_getElem_bv_24_3 (s : state.KeccakState) :
    ((↑(lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3)) : List Std.U64)[(24 : Nat)]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[0]!.bv) ((s.st.val[20]!).val[1]!.bv) := by
  have h := lift_perm_getElem_bv_aux s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3) ⟨24, by decide⟩
  have hp : ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨24, by decide⟩)).val = 20 := by decide
  have hsw : impl_swap_k 3 ((impl_perm ∘ impl_perm ∘ impl_perm) (transpose_perm ⟨24, by decide⟩)) = false := by
    rw [impl_swap_k_three]; decide
  rw [h, hp, hsw, lift_lane_maybe_swap_false_bv]

set_option maxHeartbeats 2000000 in
@[spec]
theorem theta_lift_spec_3 (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600_round3_theta s
    ⦃ ⇓ r_impl => ⌜
      r_impl.i = s.i ∧
      (do
        let r_spec ← keccak_f.theta
          (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
        pure (r_spec = lift_theta_applied_perm r_impl
          (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))).holds ⌝ ⦄ := by
  apply Triple.of_entails_right _ (theta_comp_spec_local_3 s)
  rw [PostCond.entails_noThrow]
  intro r_impl hpost
  dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
  refine ⟨hpost.2.1, ?_⟩
  rw [show keccak_f.theta (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))
          = .ok (theta_applied
                  (lift_perm s (impl_perm ∘ impl_perm ∘ impl_perm) (impl_swap_k 3))) from
        result_eq_of_triple (theta_spec _)]
  show ⦃⌜True⌝⦄ Result.ok _ ⦃PostCond.noThrow fun p => ⌜p⌝⦄
  simp [Std.Do.Triple, Std.Do.WP.wp]
  obtain ⟨hst, _, hd0z0, hd0z1, hd1z0, hd1z1, hd2z0, hd2z1,
          hd3z0, hd3z1, hd4z0, hd4z1⟩ := hpost
  apply Subtype.ext
  unfold theta_applied lift_theta_applied_perm
  show _ = List.ofFn _
  simp only [Std.Array.make, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ,
             Nat.zero_add, Nat.reduceAdd, hst]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (apply Std.U64.bv_eq_imp_eq)
  -- Rewrite `impl_swap_k 3` to a decidable membership form so reduceIte can fire.
  all_goals simp only [impl_swap_k_three]
  -- Unfold `lift_lane_maybe_swap` and `lift_lane` to expose `s.st[(impl_perm³ K).val]!`.
  all_goals
    simp (config := { decide := true }) only [
      lift_lane_maybe_swap, lift_lane,
      Std.UScalar.bv_xor,
      reduceIte,
      Function.comp_apply]
  all_goals
    simp_all only [Std.UScalar.bv_xor, rot32]
  all_goals
    simp only [lift_perm_getElem_bv_0_3, lift_perm_getElem_bv_1_3, lift_perm_getElem_bv_2_3,
      lift_perm_getElem_bv_3_3, lift_perm_getElem_bv_4_3, lift_perm_getElem_bv_5_3,
      lift_perm_getElem_bv_6_3, lift_perm_getElem_bv_7_3, lift_perm_getElem_bv_8_3,
      lift_perm_getElem_bv_9_3, lift_perm_getElem_bv_10_3, lift_perm_getElem_bv_11_3,
      lift_perm_getElem_bv_12_3, lift_perm_getElem_bv_13_3, lift_perm_getElem_bv_14_3,
      lift_perm_getElem_bv_15_3, lift_perm_getElem_bv_16_3, lift_perm_getElem_bv_17_3,
      lift_perm_getElem_bv_18_3, lift_perm_getElem_bv_19_3, lift_perm_getElem_bv_20_3,
      lift_perm_getElem_bv_21_3, lift_perm_getElem_bv_22_3, lift_perm_getElem_bv_23_3,
      lift_perm_getElem_bv_24_3]
  all_goals simp only [Std.UScalarTy.U64_numBits_eq, ← lift_xor, ← lift_td]
  all_goals first
    | rfl
    | apply congrArg₂ lift_lane_bv
  all_goals try simp only [rotateLeft1_xor_bv32]
  all_goals
    first | ac_rfl
          | (apply congrArg (HXor.hXor (α := BitVec 32) _); ac_rfl)
          | (apply congrArg (HXor.hXor (α := BitVec 32) _);
             try simp only [← rotateLeft1_xor_bv32]; ac_rfl)

end libcrux_iot_sha3.Foundation
