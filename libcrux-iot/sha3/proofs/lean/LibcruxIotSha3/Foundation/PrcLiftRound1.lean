/-
  Round-1 ρ∘π∘χ∘ι lift spec.

  Same shape as `prc_lift_spec` (round 0) but on the round-1 impl chain.
  The output `lift_perm` uses `impl_perm` composed with itself
  (`impl_perm ∘ impl_perm`), because the input state is already in the
  round-0 layout and round 1 advances by one more `impl_perm`.

  Structure:
  - 10 per-FC `@[spec]` lemmas `pi_rho_chi_y{0..4}_zeta{0,1}_spec_fc_1`.
  - 25 input access lemmas `lift_theta_applied_perm_bv_K_1`.
  - 25 output access lemmas via `lift_perm (impl_perm ∘ impl_perm) (impl_swap_k 2)`.
  - The intermediate `prc_spec_1` mirroring impl's fused per-cell structure.
  - Main composition `prc_lift_spec_1`.
-/
import LibcruxIotSha3.Foundation.PrcLift

open Aeneas Aeneas.Std Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Foundation

set_option mvcgen.warning false

/-! ### FC proof macros (round-1 versions)

`prc_y_zeta_no_rc_proof` and `prc_y_zeta_with_rc_proof_1` are the
round-1 analogues of the round-0 macros in `PrcLift.lean`. They have
the same `hax_mvcgen` hyp-name layout because the impl FC bodies have
the same shape (5 reads, 5 rotates, 5 chi steps, 5 writes). -/

set_option maxHeartbeats 16000000

/-! ## Per-FC spec lemmas for round-1 -/

/-! y0_zeta0 FC (round 1): writes lanes 0/8/11/19/22 at halves 0/1/1/1/1;
    RC_INTERLEAVED_0[s.i] XORed into lane 0 half 0; preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y0_zeta0_spec_fc_1
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[8]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx2 := rot32 (s.st.val[11]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 22
      let bx3 := rot32 (s.st.val[19]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 11
      let bx4 := rot32 (s.st.val[22]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        0#usize 1#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_0.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · exact h_59.trans (h_52.trans (h_45.trans (h_38.trans h_31)))
  · exact h_58.trans (h_51.trans (h_44.trans (h_37.trans h_30)))
  · have hb : s.i.val < keccak.RC_INTERLEAVED_0.val.length := by
      have hl : keccak.RC_INTERLEAVED_0.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_0.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_0.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_61, h_54, h_47, h_40, h_33]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_36.2, h_35.2, h_34,
        h_43.2, h_42.2, h_41,
        h_50.2, h_49.2, h_48,
        h_57.2, h_56.2, h_55,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

/-! y0_zeta1 FC (round 1): writes lanes 0/8/11/19/22 at halves 1/0/0/0/0;
    RC_INTERLEAVED_1[s.i] XORed into lane 0 half 1; INCREMENTS `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y0_zeta1_spec_fc_1
    (BR : Std.Usize) (s : state.KeccakState) (hi : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1 BR s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[0]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 0
      let bx1 := rot32 (s.st.val[8]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 22
      let bx2 := rot32 (s.st.val[11]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 21
      let bx3 := rot32 (s.st.val[19]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 10
      let bx4 := rot32 (s.st.val[22]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 7
      r.d = s.d ∧ r.c = s.c ∧ r.i.val = s.i.val + 1 ∧
      r.st.val = apply_5_writes s.st.val
        0 8 11 19 22
        1#usize 0#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2) ^^^ keccak.RC_INTERLEAVED_1.val[s.i.val]!)
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1
  hax_mvcgen
  all_goals try scalar_tac
  expose_names
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_61.trans (h_54.trans (h_47.trans (h_40.trans h_33)))
  · exact h_60.trans (h_53.trans (h_46.trans (h_39.trans h_32)))
  · rw [h_59, h_52, h_45, h_38, h_31, h_30]
    rfl
  · have hb : s.i.val < keccak.RC_INTERLEAVED_1.val.length := by
      have hl : keccak.RC_INTERLEAVED_1.val.length = 255 := Array.length_eq _
      omega
    have hRC : keccak.RC_INTERLEAVED_1.val[s.i.val]?.getD default
             = keccak.RC_INTERLEAVED_1.val[s.i.val]'hb := by
      rw [List.getElem?_eq_getElem hb]; rfl
    rw [h_62, h_55, h_48, h_41, h_34]
    norm_num [apply_5_writes]
    congr 6
    all_goals apply Std.U32.bv_eq_imp_eq
    all_goals (
      simp only [
        hRC,
        h_29.2, h_27.2, h_26.2, h_25,
        h_37.2, h_36.2, h_35,
        h_44.2, h_43.2, h_42,
        h_51.2, h_50.2, h_49,
        h_58.2, h_57.2, h_56,
        h_7, h_9, h_20, h_22, h_24,
        h_6.2, h_8.2, h_19.2, h_21.2, h_23.2,
        h_28,
        h, h_1, h_2, h_3, h_4, h_5, h_10, h_11, h_12, h_13, h_14, h_15, h_16, h_17, h_18,
        Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32]
      norm_num)

/-! y1_zeta0 FC (round 1): writes lanes 4/7/10/18/21 at halves 1/1/1/1/0;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta0_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[18]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 10
      let bx2 := rot32 (s.st.val[4]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 2
      let bx3 := rot32 (s.st.val[7]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 23
      let bx4 := rot32 (s.st.val[10]!.val[1]! ^^^ s.d.val[2]!.val[1]!) 31
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        1#usize 1#usize 1#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0

/-! y1_zeta1 FC (round 1): writes lanes 4/7/10/18/21 at halves 0/0/0/0/1;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y1_zeta1_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[18]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[21]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 10
      let bx2 := rot32 (s.st.val[4]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 1
      let bx3 := rot32 (s.st.val[7]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 22
      let bx4 := rot32 (s.st.val[10]!.val[0]! ^^^ s.d.val[2]!.val[0]!) 30
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        4 7 10 18 21
        0#usize 0#usize 0#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1

/-! y2_zeta0 FC (round 1): writes lanes 3/6/14/17/20 at halves 1/1/1/0/1;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta0_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[6]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      let bx1 := rot32 (s.st.val[14]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 13
      let bx3 := rot32 (s.st.val[20]!.val[1]! ^^^ s.d.val[4]!.val[0]!) 4
      let bx4 := rot32 (s.st.val[3]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        1#usize 1#usize 1#usize 0#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0

/-! y2_zeta1 FC (round 1): writes lanes 3/6/14/17/20 at halves 0/0/0/1/0;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y2_zeta1_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[6]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 0
      let bx1 := rot32 (s.st.val[14]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 3
      let bx2 := rot32 (s.st.val[17]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 12
      let bx3 := rot32 (s.st.val[20]!.val[0]! ^^^ s.d.val[4]!.val[1]!) 4
      let bx4 := rot32 (s.st.val[3]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 9
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        3 6 14 17 20
        0#usize 0#usize 0#usize 1#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1

/-! y3_zeta0 FC (round 1): writes lanes 2/5/13/16/24 at halves 1/1/0/1/1;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta0_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[24]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 14
      let bx1 := rot32 (s.st.val[2]!.val[1]! ^^^ s.d.val[0]!.val[0]!) 18
      let bx2 := rot32 (s.st.val[5]!.val[1]! ^^^ s.d.val[1]!.val[0]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 8
      let bx4 := rot32 (s.st.val[16]!.val[1]! ^^^ s.d.val[3]!.val[0]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        1#usize 1#usize 0#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0

/-! y3_zeta1 FC (round 1): writes lanes 2/5/13/16/24 at halves 0/0/1/0/0;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y3_zeta1_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[24]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 13
      let bx1 := rot32 (s.st.val[2]!.val[0]! ^^^ s.d.val[0]!.val[1]!) 18
      let bx2 := rot32 (s.st.val[5]!.val[0]! ^^^ s.d.val[1]!.val[1]!) 5
      let bx3 := rot32 (s.st.val[13]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 7
      let bx4 := rot32 (s.st.val[16]!.val[0]! ^^^ s.d.val[3]!.val[1]!) 28
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        2 5 13 16 24
        0#usize 0#usize 1#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1

/-! y4_zeta0 FC (round 1): writes lanes 1/9/12/15/23 at halves 1/0/1/1/1;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta0_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[12]!.val[1]! ^^^ s.d.val[2]!.val[0]!) 31
      let bx1 := rot32 (s.st.val[15]!.val[1]! ^^^ s.d.val[3]!.val[1]!) 28
      let bx2 := rot32 (s.st.val[23]!.val[1]! ^^^ s.d.val[4]!.val[1]!) 20
      let bx3 := rot32 (s.st.val[1]!.val[1]! ^^^ s.d.val[0]!.val[1]!) 21
      let bx4 := rot32 (s.st.val[9]!.val[0]! ^^^ s.d.val[1]!.val[0]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        1#usize 0#usize 1#usize 1#usize 1#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0

/-! y4_zeta1 FC (round 1): writes lanes 1/9/12/15/23 at halves 0/1/0/0/0;
    preserves `s.i`. -/
set_option maxHeartbeats 16000000 in
@[spec]
private theorem pi_rho_chi_y4_zeta1_spec_fc_1
    (s : state.KeccakState) :
    ⦃ ⌜ True ⌝ ⦄ keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1 s
    ⦃ ⇓ r => ⌜
      let bx0 := rot32 (s.st.val[12]!.val[0]! ^^^ s.d.val[2]!.val[1]!) 31
      let bx1 := rot32 (s.st.val[15]!.val[0]! ^^^ s.d.val[3]!.val[0]!) 27
      let bx2 := rot32 (s.st.val[23]!.val[0]! ^^^ s.d.val[4]!.val[0]!) 19
      let bx3 := rot32 (s.st.val[1]!.val[0]! ^^^ s.d.val[0]!.val[0]!) 20
      let bx4 := rot32 (s.st.val[9]!.val[1]! ^^^ s.d.val[1]!.val[1]!) 1
      r.d = s.d ∧ r.c = s.c ∧ r.i = s.i ∧
      r.st.val = apply_5_writes s.st.val
        1 9 12 15 23
        0#usize 1#usize 0#usize 0#usize 0#usize
        (bx0 ^^^ ((~~~bx1) &&& bx2))
        (bx1 ^^^ ((~~~bx2) &&& bx3))
        (bx2 ^^^ ((~~~bx3) &&& bx4))
        (bx3 ^^^ ((~~~bx4) &&& bx0))
        (bx4 ^^^ ((~~~bx0) &&& bx1)) ⌝ ⦄ := by
  prc_y_zeta_no_rc_proof keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1

/-! ## Input cell access lemmas

For each `K = 0..24`, `(lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[K]!.bv`
is `lift_lane_bv` over the swap-aware halves of `s.st[impl_perm K]` XOR'd with
`s.d[K/5]`. -/

private theorem lta_perm_getElem (s : state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    (lift_theta_applied_perm s p sw).val[k.val]! =
      lift_lane_maybe_swap (s.st.val[(p (transpose_perm k)).val]!)
                           (sw (p (transpose_perm k))) ^^^
        lift_lane (s.d.val[k.val % 5]!) := by
  unfold lift_theta_applied_perm
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simp), List.getElem_ofFn]

theorem lift_theta_applied_perm_bv_0_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[0]!).bv =
      lift_lane_bv ((s.st.val[0]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[0]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨0, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨0, by decide⟩)).val = 0 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨0, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_1_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[1]!).bv =
      lift_lane_bv ((s.st.val[6]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[6]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨1, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨1, by decide⟩)).val = 6 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨1, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_2_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[2]!).bv =
      lift_lane_bv ((s.st.val[12]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[12]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨2, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨2, by decide⟩)).val = 12 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨2, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_3_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[3]!).bv =
      lift_lane_bv ((s.st.val[18]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[18]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨3, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨3, by decide⟩)).val = 18 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨3, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_4_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[4]!).bv =
      lift_lane_bv ((s.st.val[24]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[24]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨4, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨4, by decide⟩)).val = 24 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨4, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_5_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[5]!).bv =
      lift_lane_bv ((s.st.val[2]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[2]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨5, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨5, by decide⟩)).val = 2 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨5, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_6_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[6]!).bv =
      lift_lane_bv ((s.st.val[8]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[8]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨6, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨6, by decide⟩)).val = 8 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨6, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_7_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[7]!).bv =
      lift_lane_bv ((s.st.val[14]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[14]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨7, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨7, by decide⟩)).val = 14 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨7, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_8_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[8]!).bv =
      lift_lane_bv ((s.st.val[15]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[15]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨8, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨8, by decide⟩)).val = 15 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨8, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_9_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[9]!).bv =
      lift_lane_bv ((s.st.val[21]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[21]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨9, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨9, by decide⟩)).val = 21 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨9, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_10_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[10]!).bv =
      lift_lane_bv ((s.st.val[4]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[4]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨10, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨10, by decide⟩)).val = 4 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨10, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_11_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[11]!).bv =
      lift_lane_bv ((s.st.val[5]!).val[1]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[5]!).val[0]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨11, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨11, by decide⟩)).val = 5 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨11, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_12_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[12]!).bv =
      lift_lane_bv ((s.st.val[11]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[11]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨12, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨12, by decide⟩)).val = 11 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨12, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_13_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[13]!).bv =
      lift_lane_bv ((s.st.val[17]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[17]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨13, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨13, by decide⟩)).val = 17 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨13, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_14_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[14]!).bv =
      lift_lane_bv ((s.st.val[23]!).val[0]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[23]!).val[1]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨14, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨14, by decide⟩)).val = 23 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨14, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_15_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[15]!).bv =
      lift_lane_bv ((s.st.val[1]!).val[0]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[1]!).val[1]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨15, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨15, by decide⟩)).val = 1 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨15, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_16_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[16]!).bv =
      lift_lane_bv ((s.st.val[7]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[7]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨16, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨16, by decide⟩)).val = 7 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨16, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_17_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[17]!).bv =
      lift_lane_bv ((s.st.val[13]!).val[1]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[13]!).val[0]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨17, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨17, by decide⟩)).val = 13 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨17, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_18_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[18]!).bv =
      lift_lane_bv ((s.st.val[19]!).val[0]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[19]!).val[1]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨18, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨18, by decide⟩)).val = 19 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨18, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_19_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[19]!).bv =
      lift_lane_bv ((s.st.val[20]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[20]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨19, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨19, by decide⟩)).val = 20 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨19, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_20_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[20]!).bv =
      lift_lane_bv ((s.st.val[3]!).val[1]! ^^^ (s.d.val[0]!).val[0]!).bv
                   ((s.st.val[3]!).val[0]! ^^^ (s.d.val[0]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨20, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨20, by decide⟩)).val = 3 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨20, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_21_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[21]!).bv =
      lift_lane_bv ((s.st.val[9]!).val[0]! ^^^ (s.d.val[1]!).val[0]!).bv
                   ((s.st.val[9]!).val[1]! ^^^ (s.d.val[1]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨21, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨21, by decide⟩)).val = 9 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨21, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_22_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[22]!).bv =
      lift_lane_bv ((s.st.val[10]!).val[0]! ^^^ (s.d.val[2]!).val[0]!).bv
                   ((s.st.val[10]!).val[1]! ^^^ (s.d.val[2]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨22, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨22, by decide⟩)).val = 10 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨22, by decide⟩)) = false := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_23_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[23]!).bv =
      lift_lane_bv ((s.st.val[16]!).val[1]! ^^^ (s.d.val[3]!).val[0]!).bv
                   ((s.st.val[16]!).val[0]! ^^^ (s.d.val[3]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨23, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨23, by decide⟩)).val = 16 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨23, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

theorem lift_theta_applied_perm_bv_24_1 (s : state.KeccakState) :
    ((lift_theta_applied_perm s impl_perm (impl_swap_k 1)).val[24]!).bv =
      lift_lane_bv ((s.st.val[22]!).val[1]! ^^^ (s.d.val[4]!).val[0]!).bv
                   ((s.st.val[22]!).val[0]! ^^^ (s.d.val[4]!).val[1]!).bv := by
  rw [lta_perm_getElem s impl_perm (impl_swap_k 1) ⟨24, by decide⟩]
  have hp : (impl_perm (transpose_perm ⟨24, by decide⟩)).val = 22 := by decide
  have hsw : impl_swap_k 1 (impl_perm (transpose_perm ⟨24, by decide⟩)) = true := by rw [impl_swap_k_one]; decide
  show (lift_lane_maybe_swap _ _ ^^^ lift_lane _).bv = _
  simp only [hp, hsw, lift_lane_maybe_swap, lift_lane, Std.UScalar.bv_xor]
  rw [lift_xor]; rfl

/-! ### Set-peeling lemmas (`getElem!` over `List.set`), local copies. -/
private theorem list_getElem!_set_ne {α} [Inhabited α] {l : List α} {i j : Nat}
    {a : α} (h : i ≠ j) : (l.set i a)[j]! = l[j]! := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, if_neg h]

private theorem list_getElem!_set_eq {α} [Inhabited α] {l : List α} {i : Nat}
    {a : α} (h : i < l.length) : (l.set i a)[i]! = a := by
  simp only [List.getElem!_eq_getElem?_getD, List.getElem?_set, h,
    if_true, Option.getD_some]

/-! ## Main composition: `prc_lift_spec_1`

   Infrastructure: 10 per-FC specs + 25 input cell access lemmas. The proof
   mirrors `prc_lift_spec` (round 0) but characterises the output as
   `lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2)` rather than the
   plain canonical lift. The output side is handled by a `conv_rhs` scoping
   block that unfolds `impl_swap_k 2` (rewriting it to its concrete polarity
   indicator on `Fin 25`) and `impl_perm`/`lift_lane_maybe_swap` only on the
   RHS — this avoids accidentally normalising the LHS, which would defeat the
   per-cell `simp` cascade. Runs at 256M heartbeats. -/

set_option maxHeartbeats 32000000 in
theorem prc_lift_spec_1 (s : state.KeccakState) (hi_lt : s.i.val < 24) :
    ⦃ ⌜ True ⌝ ⦄
    (do let r1 ← keccak.keccakf1600_round1_pi_rho_chi_1 0#usize s
        keccak.keccakf1600_round1_pi_rho_chi_2 r1)
    ⦃ ⇓ r_impl => ⌜
      (do let a1 ← keccak_f.rho
            (lift_theta_applied_perm s impl_perm (impl_swap_k 1))
          let a2 ← keccak_f.pi a1
          let a3 ← keccak_f.chi a2
          let r_spec ← keccak_f.iota a3 s.i
          pure (r_spec = lift_perm r_impl (impl_perm ∘ impl_perm) (impl_swap_k 2))).holds ⌝ ⦄ := by
  unfold keccak.keccakf1600_round1_pi_rho_chi_1
  unfold keccak.keccakf1600_round1_pi_rho_chi_2
  hax_mvcgen
  all_goals try scalar_tac
  subst_vars
  rw [prc_spec_eq_composed]
  casesm* _ ∧ _
  have hlane : ∀ (L : lane.Lane2U32), L.val.length = 2 := fun L => L.2
  have hss : (↑s.st : List lane.Lane2U32).length = 25 := s.st.2
  apply Subtype.ext
  unfold prc_spec lift_perm transpose_perm
  conv_rhs =>
    rw [show (impl_swap_k 2) = (fun L : Fin 25 =>
      decide (L.val ∉ ([0, 9, 13, 17, 21] : List Nat))) from by
      funext L; rw [impl_swap_k]]
    unfold impl_perm lift_lane_maybe_swap
  simp (config := { decide := true }) only [Std.Array.make, List.ofFn_succ, List.ofFn_zero,
    Function.comp_apply, Fin.val_succ, Fin.val_zero, Nat.zero_add,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, reduceIte]
  repeat' (first | rfl | (apply List.cons_eq_cons.mpr; refine ⟨?_, ?_⟩))
  all_goals (
    apply Std.U64.bv_eq_imp_eq
    simp (config := { decide := true }) only
      [*, apply_5_writes, lift_lane,
       list_getElem!_set_ne, list_getElem!_set_eq, List.length_set,
       Std.Array.set_val_eq, show ((0#usize : Std.Usize) : Nat) = 0 from rfl,
       show ((1#usize : Std.Usize) : Nat) = 1 from rfl]
    simp only [lift_theta_applied_perm_bv_0_1, lift_theta_applied_perm_bv_1_1,
      lift_theta_applied_perm_bv_2_1, lift_theta_applied_perm_bv_3_1,
      lift_theta_applied_perm_bv_4_1, lift_theta_applied_perm_bv_5_1,
      lift_theta_applied_perm_bv_6_1, lift_theta_applied_perm_bv_7_1,
      lift_theta_applied_perm_bv_8_1, lift_theta_applied_perm_bv_9_1,
      lift_theta_applied_perm_bv_10_1, lift_theta_applied_perm_bv_11_1,
      lift_theta_applied_perm_bv_12_1, lift_theta_applied_perm_bv_13_1,
      lift_theta_applied_perm_bv_14_1, lift_theta_applied_perm_bv_15_1,
      lift_theta_applied_perm_bv_16_1, lift_theta_applied_perm_bv_17_1,
      lift_theta_applied_perm_bv_18_1, lift_theta_applied_perm_bv_19_1,
      lift_theta_applied_perm_bv_20_1, lift_theta_applied_perm_bv_21_1,
      lift_theta_applied_perm_bv_22_1, lift_theta_applied_perm_bv_23_1,
      lift_theta_applied_perm_bv_24_1,
      Std.UScalar.bv_xor, Std.UScalar.bv_and, Std.UScalar.bv_not, rot32, rot64]
    simp only [Std.UScalarTy.U64_numBits_eq,
      rot_0, rot_1, rot_2, rot_3, rot_6, rot_8, rot_10,
      rot_14, rot_15, rot_18, rot_20, rot_21, rot_25, rot_27,
      rot_28, rot_36, rot_39, rot_41, rot_43, rot_44, rot_45,
      rot_55, rot_56, rot_61, rot_62,
      ← lift_xor, ← lift_and, ← lift_not, ← rc_equiv _ hi_lt])

end libcrux_iot_sha3.Foundation
