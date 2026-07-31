/-
  # `Vector/Portable/NttMaster.lean` — forward NTT master (ML-DSA)

  Composes the 8 proven layer-driver FCs (`ntt_at_layer_7 … ntt_at_layer_0`,
  all in `NttDriver`) into the straight-line `simd.portable.ntt.ntt` body, giving
  the full forward NTT impl↔spec equivalence on the lifted flat 256-array:
  `lift_units r = Pure.ntt (lift_units re)`.

  The running coefficient bound is threaded `B → B + 34·2^24` through the 8 layers
  (cumulative increments `1,2,4,8,16,1,1,1` × `2^24`). Each running bound is made an
  OPAQUE Nat fvar via `generalize`-per-call (the `ntt_at_layer_3_fc` idiom) to dodge
  the kernel deep-recursion trap from nesting literal `B + k·2^24` numerals across
  chained FC calls.
-/
import LibcruxIotMlDsa.Vector.Portable.NttDriver

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.NttDriver
open Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper; the original is `private` in `NttDriver`). -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v` (file-scoped §13.5 copy). -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## Forward NTT master `ntt_inner_fc`.

`simd.portable.ntt.ntt` is the straight-line `do let re1 ← ntt_at_layer_7 re; …;
ntt_at_layer_0 re7` (layers 7,6,5,4,3,2,1,0). Composing the 8 proven layer drivers
gives `lift_units r = Pure.ntt (lift_units re)`, with the running coefficient bound
threaded `B → B + 34·2^24` (per-layer increments `1,2,4,8,16,1,1,1` × `2^24`). -/

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_inner_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 34 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt re
    ⦃ ⇓ r => ⌜ Lift.lift_units r = Pure.ntt (Lift.lift_units re)
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 34 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  -- Layer 7 (INCR = 2^24): input bound B.
  have hB7 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, hr1_lift, hr1_bd⟩ := triple_exists_ok (ntt_at_layer_7_fc re B hB7 hin)
  -- Layer 6 (INCR = 2·2^24): input bound C7 := B + 2^24.
  have hB6raw : ((B + 2 ^ 24 : Nat) : Int) + 2 * 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB7def : B + 2 ^ 24 = C7 at hr1_bd hB6raw
  obtain ⟨r2, hr2_eq, hr2_lift, hr2_bd⟩ := triple_exists_ok (ntt_at_layer_6_fc r1 C7 hB6raw hr1_bd)
  -- Layer 5 (INCR = 4·2^24): input bound C6 := C7 + 2·2^24.
  have hB5raw : ((C7 + 2 * 2 ^ 24 : Nat) : Int) + 4 * 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    push_cast; omega
  generalize hB6def : C7 + 2 * 2 ^ 24 = C6 at hr2_bd hB5raw
  obtain ⟨r3, hr3_eq, hr3_lift, hr3_bd⟩ := triple_exists_ok (ntt_at_layer_5_fc r2 C6 hB5raw hr2_bd)
  -- Layer 4 (INCR = 8·2^24): input bound C5 := C6 + 4·2^24.
  have hB4raw : ((C6 + 4 * 2 ^ 24 : Nat) : Int) + 8 * 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    have e6 : C6 = C7 + 2 * 2 ^ 24 := hB6def.symm
    push_cast; omega
  generalize hB5def : C6 + 4 * 2 ^ 24 = C5 at hr3_bd hB4raw
  obtain ⟨r4, hr4_eq, hr4_lift, hr4_bd⟩ := triple_exists_ok (ntt_at_layer_4_fc r3 C5 hB4raw hr3_bd)
  -- Layer 3 (INCR = 16·2^24): input bound C4 := C5 + 8·2^24.
  have hB3raw : ((C5 + 8 * 2 ^ 24 : Nat) : Int) + 16 * 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    have e6 : C6 = C7 + 2 * 2 ^ 24 := hB6def.symm
    have e5 : C5 = C6 + 4 * 2 ^ 24 := hB5def.symm
    push_cast; omega
  generalize hB4def : C5 + 8 * 2 ^ 24 = C4 at hr4_bd hB3raw
  obtain ⟨r5, hr5_eq, hr5_lift, hr5_bd⟩ := triple_exists_ok (ntt_at_layer_3_fc r4 C4 hB3raw hr4_bd)
  -- Layer 2 (INCR = 2^24): input bound C3 := C4 + 16·2^24.
  have hB2raw : ((C4 + 16 * 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    have e6 : C6 = C7 + 2 * 2 ^ 24 := hB6def.symm
    have e5 : C5 = C6 + 4 * 2 ^ 24 := hB5def.symm
    have e4 : C4 = C5 + 8 * 2 ^ 24 := hB4def.symm
    push_cast; omega
  generalize hB3def : C4 + 16 * 2 ^ 24 = C3 at hr5_bd hB2raw
  obtain ⟨r6, hr6_eq, hr6_lift, hr6_bd⟩ := triple_exists_ok (ntt_at_layer_2_fc r5 C3 hB2raw hr5_bd)
  -- Layer 1 (INCR = 2^24): input bound C2 := C3 + 2^24.
  have hB1raw : ((C3 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    have e6 : C6 = C7 + 2 * 2 ^ 24 := hB6def.symm
    have e5 : C5 = C6 + 4 * 2 ^ 24 := hB5def.symm
    have e4 : C4 = C5 + 8 * 2 ^ 24 := hB4def.symm
    have e3 : C3 = C4 + 16 * 2 ^ 24 := hB3def.symm
    push_cast; omega
  generalize hB2def : C3 + 2 ^ 24 = C2 at hr6_bd hB1raw
  obtain ⟨r7, hr7_eq, hr7_lift, hr7_bd⟩ := triple_exists_ok (ntt_at_layer_1_fc r6 C2 hB1raw hr6_bd)
  -- Layer 0 (INCR = 2^24): input bound C1 := C2 + 2^24.
  have hB0raw : ((C2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e7 : C7 = B + 2 ^ 24 := hB7def.symm
    have e6 : C6 = C7 + 2 * 2 ^ 24 := hB6def.symm
    have e5 : C5 = C6 + 4 * 2 ^ 24 := hB5def.symm
    have e4 : C4 = C5 + 8 * 2 ^ 24 := hB4def.symm
    have e3 : C3 = C4 + 16 * 2 ^ 24 := hB3def.symm
    have e2 : C2 = C3 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB1def : C2 + 2 ^ 24 = C1 at hr7_bd hB0raw
  obtain ⟨r8, hr8_eq, hr8_lift, hr8_bd⟩ := triple_exists_ok (ntt_at_layer_0_fc r7 C1 hB0raw hr7_bd)
  -- Collapse the 8 `.ok` binds.
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr8_eq
  refine ⟨?_, ?_⟩
  · -- Equality conjunct: chain the 8 `lift_units` facts through `Pure.ntt`.
    show Lift.lift_units r8 = Pure.ntt (Lift.lift_units re)
    simp only [Pure.ntt, List.foldl]
    rw [hr8_lift, hr7_lift, hr6_lift, hr5_lift, hr4_lift, hr3_lift, hr2_lift, hr1_lift]
  · -- Bound conjunct: recover `B + 34·2^24` from the chained `generalize`s.
    have heq : C1 + 2 ^ 24 = B + 34 * 2 ^ 24 := by
      rw [← hB1def, ← hB2def, ← hB3def, ← hB4def, ← hB5def, ← hB6def, ← hB7def]
      ring
    intro u hu l hl
    have := hr8_bd u hu l hl
    rw [heq] at this
    exact this

end libcrux_iot_ml_dsa.Vector.Portable.NttDriver
