/-
  # `Vector/Portable/Ntt.lean` — Layer-0 within-SIMD-unit butterflies (ML-DSA)

  ML-DSA analogue of ml-kem's `LibcruxIotMlKem/Vector/Portable/Ntt.lean`
  (`ntt_step_spec`). The keystone butterfly FC that sets the proof template for
  the within-`Coefficients` Cooley–Tukey layers.

  - **`simd_unit_ntt_at_layer_0_fc`** — `simd.portable.ntt.simd_unit_ntt_at_layer_0`
    is a straight-line (no loop) sequence of 4 Cooley–Tukey pairs over the lanes
    `(0,1)/(2,3)/(4,5)/(6,7)`, each with its own zeta. For a pair `(lo, hi)` with
    zeta `z`:
    ```
    t        ← montgomery_multiply_fe_by_fer values[hi] z   -- t = hi·z·R⁻¹
    out[hi]  ← values[lo] - t                               -- CHECKED i32 sub
    out[lo]  ← values[lo] + t                               -- CHECKED i32 add
    ```
    Under the per-lane input bound `|values[j]| ≤ B` and `B + 2^24 ≤ 2^31 - 1`,
    the checked `±` never overflow, and each output lane lifts (Montgomery-strip)
    to the clean butterfly:
    `liftZ out[lo] = liftZ values[lo] + liftZ values[hi] · liftZ z` and
    `liftZ out[hi] = liftZ values[lo] - liftZ values[hi] · liftZ z`,
    matching the spec `ntt_layer` step at `len = 1`. The multiplied lane is the
    ODD/HIGH lane of each pair.

  Composition seams (all from `Spec/Lift.lean`):
  * **mont-mul seam** `liftZ_of_mont` — turns the leaf's
    `(t : Z_q) = (hi)(z)·R⁻¹` into `liftZ t = liftZ hi · liftZ z`.
  * **additive seams** `liftZ_add` / `liftZ_sub` — push `liftZ` across the
    checked `±` value equations.
-/
import LibcruxIotMlDsa.Vector.Portable.Element

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_dsa.Util.LoopHelper libcrux_iot_ml_dsa.Util.LoopSpecs
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters

/-! ## Local Triple ↔ Result.ok bridges (file-scoped copies of the §13.5 helpers). -/

/-- `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post. -/
private theorem triple_exists_ok
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- `classify` is the identity (`ok a`). -/
private theorem classify_ok (z : Std.I32) :
    libcrux_secrets.traits.Classify.Blanket.classify z = .ok z := rfl

/-! ## Checked `i32` `±` no-overflow bridges.

The layer-0 body uses the CHECKED `Std.I32` `Sub`/`Add` (monadic, can panic),
NOT the wrapping ops of `Coefficients` `add`/`subtract`. Under
`|x| ≤ B`, `|t| ≤ 2^24`, `B + 2^24 ≤ 2^31 - 1`, the result is in bounds, so the
op is `.ok` with the exact integer value and `|x ± t| ≤ B + 2^24`. -/

/-- `|x ± t| ≤ B + 2^24` from `|x| ≤ B`, `|t| ≤ 2^24` (triangle ineq.). -/
private theorem sum_abs_bound (x t : Int) (B : Nat)
    (hx : x.natAbs ≤ B) (ht : t.natAbs ≤ 2 ^ 24) :
    (x + t).natAbs ≤ B + 2 ^ 24 ∧ (x - t).natAbs ≤ B + 2 ^ 24 := by
  have h_tri_add : (x + t).natAbs ≤ x.natAbs + t.natAbs := Int.natAbs_add_le _ _
  have h_eq : x - t = x + (-t) := by ring
  have h_tri_sub : (x - t).natAbs ≤ x.natAbs + t.natAbs := by
    rw [h_eq]
    have := Int.natAbs_add_le x (-t)
    rw [Int.natAbs_neg] at this
    exact this
  exact ⟨by omega, by omega⟩

/-- Checked i32 subtraction is `.ok` with value `x - t` under the bound. -/
private theorem checked_sub_ok (x t : Std.I32) (B : Nat)
    (hx : x.val.natAbs ≤ B) (ht : t.val.natAbs ≤ 2 ^ 24)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1) :
    ∃ z : Std.I32, (x - t : Result Std.I32) = .ok z ∧ z.val = x.val - t.val
      ∧ z.val.natAbs ≤ B + 2 ^ 24 := by
  have h_abs := (sum_abs_bound x.val t.val B hx ht).2
  have h_in : Aeneas.Std.IScalar.inBounds Aeneas.Std.IScalarTy.I32 (x.val - t.val) := by
    simp only [Aeneas.Std.IScalar.inBounds, Aeneas.Std.IScalarTy.I32_numBits_eq]
    have h_nat : (x.val - t.val).natAbs ≤ B + 2 ^ 24 := h_abs
    constructor
    · have : -(2 ^ 31 - 1 : Int) ≤ x.val - t.val := by omega
      have h31 : (-(2 : Int) ^ 31) ≤ -(2 ^ 31 - 1) := by norm_num
      omega
    · omega
  have h := Aeneas.Std.IScalar.sub_equiv x t
  cases hz : (x - t : Result Std.I32) with
  | ok z =>
    rw [hz] at h
    refine ⟨z, rfl, h.2.1, ?_⟩
    rw [h.2.1]; exact h_abs
  | fail e =>
    rw [hz] at h
    exact absurd h_in h
  | div =>
    rw [hz] at h
    exact h.elim

/-- Checked i32 addition is `.ok` with value `x + t` under the bound. -/
private theorem checked_add_ok (x t : Std.I32) (B : Nat)
    (hx : x.val.natAbs ≤ B) (ht : t.val.natAbs ≤ 2 ^ 24)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1) :
    ∃ z : Std.I32, (x + t : Result Std.I32) = .ok z ∧ z.val = x.val + t.val
      ∧ z.val.natAbs ≤ B + 2 ^ 24 := by
  have h_abs := (sum_abs_bound x.val t.val B hx ht).1
  have h_in : Aeneas.Std.IScalar.inBounds Aeneas.Std.IScalarTy.I32 (x.val + t.val) := by
    simp only [Aeneas.Std.IScalar.inBounds, Aeneas.Std.IScalarTy.I32_numBits_eq]
    have h_nat : (x.val + t.val).natAbs ≤ B + 2 ^ 24 := h_abs
    constructor
    · have : -(2 ^ 31 - 1 : Int) ≤ x.val + t.val := by omega
      have h31 : (-(2 : Int) ^ 31) ≤ -(2 ^ 31 - 1) := by norm_num
      omega
    · omega
  have h := Aeneas.Std.IScalar.add_equiv x t
  cases hz : (x + t : Result Std.I32) with
  | ok z =>
    rw [hz] at h
    refine ⟨z, rfl, h.2.1, ?_⟩
    rw [h.2.1]; exact h_abs
  | fail e =>
    rw [hz] at h
    exact absurd h_in h
  | div =>
    rw [hz] at h
    exact h.elim

/-! ## The keystone butterfly FC. -/

@[spec]
theorem simd_unit_ntt_at_layer_0_fc
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (zeta0 zeta1 zeta2 zeta3 : Std.I32) (B : Nat)
    (hz0 : zeta0.val.natAbs ≤ 8380416) (hz1 : zeta1.val.natAbs ≤ 8380416)
    (hz2 : zeta2.val.natAbs ≤ 8380416) (hz3 : zeta3.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ j : Nat, j < 8 → (simd_unit.values.val[j]!).val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_0 simd_unit zeta0 zeta1 zeta2 zeta3
    ⦃ ⇓ r => ⌜ (liftZ (r.values.val[0]!).val = liftZ (simd_unit.values.val[0]!).val + liftZ (simd_unit.values.val[1]!).val * liftZ zeta0.val
              ∧ liftZ (r.values.val[1]!).val = liftZ (simd_unit.values.val[0]!).val - liftZ (simd_unit.values.val[1]!).val * liftZ zeta0.val
              ∧ liftZ (r.values.val[2]!).val = liftZ (simd_unit.values.val[2]!).val + liftZ (simd_unit.values.val[3]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[3]!).val = liftZ (simd_unit.values.val[2]!).val - liftZ (simd_unit.values.val[3]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[4]!).val = liftZ (simd_unit.values.val[4]!).val + liftZ (simd_unit.values.val[5]!).val * liftZ zeta2.val
              ∧ liftZ (r.values.val[5]!).val = liftZ (simd_unit.values.val[4]!).val - liftZ (simd_unit.values.val[5]!).val * liftZ zeta2.val
              ∧ liftZ (r.values.val[6]!).val = liftZ (simd_unit.values.val[6]!).val + liftZ (simd_unit.values.val[7]!).val * liftZ zeta3.val
              ∧ liftZ (r.values.val[7]!).val = liftZ (simd_unit.values.val[6]!).val - liftZ (simd_unit.values.val[7]!).val * liftZ zeta3.val)
            ∧ (∀ j : Nat, j < 8 → (r.values.val[j]!).val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  have h_len : simd_unit.values.length = 8 := Coefficients_values_length simd_unit
  -- Abbreviate the 8 input lanes.
  set v0 : Std.I32 := simd_unit.values.val[0]! with hv0
  set v1 : Std.I32 := simd_unit.values.val[1]! with hv1
  set v2 : Std.I32 := simd_unit.values.val[2]! with hv2
  set v3 : Std.I32 := simd_unit.values.val[3]! with hv3
  set v4 : Std.I32 := simd_unit.values.val[4]! with hv4
  set v5 : Std.I32 := simd_unit.values.val[5]! with hv5
  set v6 : Std.I32 := simd_unit.values.val[6]! with hv6
  set v7 : Std.I32 := simd_unit.values.val[7]! with hv7
  -- Per-lane input bounds.
  have hb0 : v0.val.natAbs ≤ B := hin 0 (by norm_num)
  have hb1 : v1.val.natAbs ≤ B := hin 1 (by norm_num)
  have hb2 : v2.val.natAbs ≤ B := hin 2 (by norm_num)
  have hb3 : v3.val.natAbs ≤ B := hin 3 (by norm_num)
  have hb4 : v4.val.natAbs ≤ B := hin 4 (by norm_num)
  have hb5 : v5.val.natAbs ≤ B := hin 5 (by norm_num)
  have hb6 : v6.val.natAbs ≤ B := hin 6 (by norm_num)
  have hb7 : v7.val.natAbs ≤ B := hin 7 (by norm_num)
  -- mont-mul leaves: t_p = mmfbf v[hi] zeta_p (the second arg is classify zeta_p = zeta_p).
  obtain ⟨t0, ht0_eq, ht0_lift, ht0_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v1 zeta0 hz0)
  obtain ⟨t1, ht1_eq, ht1_lift, ht1_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v3 zeta1 hz1)
  obtain ⟨t2, ht2_eq, ht2_lift, ht2_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v5 zeta2 hz2)
  obtain ⟨t3, ht3_eq, ht3_lift, ht3_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v7 zeta3 hz3)
  -- Checked subtractions/additions (the four butterflies).
  obtain ⟨s0, hs0_eq, hs0_val, hs0_bd⟩ := checked_sub_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨p0, hp0_eq, hp0_val, hp0_bd⟩ := checked_add_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨s1, hs1_eq, hs1_val, hs1_bd⟩ := checked_sub_ok v2 t1 B hb2 ht1_bd hB
  obtain ⟨p1, hp1_eq, hp1_val, hp1_bd⟩ := checked_add_ok v2 t1 B hb2 ht1_bd hB
  obtain ⟨s2, hs2_eq, hs2_val, hs2_bd⟩ := checked_sub_ok v4 t2 B hb4 ht2_bd hB
  obtain ⟨p2, hp2_eq, hp2_val, hp2_bd⟩ := checked_add_ok v4 t2 B hb4 ht2_bd hB
  obtain ⟨s3, hs3_eq, hs3_val, hs3_bd⟩ := checked_sub_ok v6 t3 B hb6 ht3_bd hB
  obtain ⟨p3, hp3_eq, hp3_val, hp3_bd⟩ := checked_add_ok v6 t3 B hb6 ht3_bd hB
  -- ===== Index/update bridges (read the EXACT lane each step touches). =====
  -- Helper: any `.set`-chain has length 8 (used for the index bound on updates).
  -- Pair 0: hi=1, lo=0.
  have hi_v1 : Array.index_usize simd_unit.values 1#usize = .ok v1 :=
    array_index_usize_ok_eq simd_unit.values 1#usize (by rw [h_len]; decide)
  have hi_v0 : Array.index_usize simd_unit.values 0#usize = .ok v0 :=
    array_index_usize_ok_eq simd_unit.values 0#usize (by rw [h_len]; decide)
  have hu_a : Array.update simd_unit.values 1#usize s0
      = .ok (simd_unit.values.set 1#usize s0) :=
    array_update_ok_eq simd_unit.values 1#usize s0 (by rw [h_len]; decide)
  set a : CoeffArray := simd_unit.values.set 1#usize s0 with ha
  have ha_len : a.length = 8 := by rw [ha, Std.Array.set_length]; exact h_len
  -- a[0] = v0 (set at 1 ≠ 0).
  have ha_0 : a.val[0]! = v0 := by
    rw [ha, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide)]
    rw [Std.Array.getElem!_Nat_eq]
  have hi_a0 : Array.index_usize a 0#usize = .ok v0 :=
    (array_index_usize_ok_eq a 0#usize (by rw [ha_len]; decide)).trans (congrArg Result.ok ha_0)
  have hu_a1 : Array.update a 0#usize p0 = .ok (a.set 0#usize p0) :=
    array_update_ok_eq a 0#usize p0 (by rw [ha_len]; decide)
  set a1 : CoeffArray := a.set 0#usize p0 with ha1
  have ha1_len : a1.length = 8 := by rw [ha1, Std.Array.set_length]; exact ha_len
  -- Pair 1: hi=3, lo=2.  a1[3] = v3, a1[2] = v2.
  have ha1_3 : a1.val[3]! = v3 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha1_2 : a1.val[2]! = v2 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a13 : Array.index_usize a1 3#usize = .ok v3 :=
    (array_index_usize_ok_eq a1 3#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_3)
  have hi_a12 : Array.index_usize a1 2#usize = .ok v2 :=
    (array_index_usize_ok_eq a1 2#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_2)
  have hu_a2 : Array.update a1 3#usize s1 = .ok (a1.set 3#usize s1) :=
    array_update_ok_eq a1 3#usize s1 (by rw [ha1_len]; decide)
  set a2 : CoeffArray := a1.set 3#usize s1 with ha2
  have ha2_len : a2.length = 8 := by rw [ha2, Std.Array.set_length]; exact ha1_len
  have ha2_2 : a2.val[2]! = v2 := by
    rw [ha2, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha1_2]
  have hi_a22 : Array.index_usize a2 2#usize = .ok v2 :=
    (array_index_usize_ok_eq a2 2#usize (by rw [ha2_len]; decide)).trans (congrArg Result.ok ha2_2)
  have hu_a3 : Array.update a2 2#usize p1 = .ok (a2.set 2#usize p1) :=
    array_update_ok_eq a2 2#usize p1 (by rw [ha2_len]; decide)
  set a3 : CoeffArray := a2.set 2#usize p1 with ha3
  have ha3_len : a3.length = 8 := by rw [ha3, Std.Array.set_length]; exact ha2_len
  -- Pair 2: hi=5, lo=4.  a3[5] = v5, a3[4] = v4.
  have ha3_5 : a3.val[5]! = v5 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha3_4 : a3.val[4]! = v4 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a35 : Array.index_usize a3 5#usize = .ok v5 :=
    (array_index_usize_ok_eq a3 5#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_5)
  have hi_a34 : Array.index_usize a3 4#usize = .ok v4 :=
    (array_index_usize_ok_eq a3 4#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_4)
  have hu_a4 : Array.update a3 5#usize s2 = .ok (a3.set 5#usize s2) :=
    array_update_ok_eq a3 5#usize s2 (by rw [ha3_len]; decide)
  set a4 : CoeffArray := a3.set 5#usize s2 with ha4
  have ha4_len : a4.length = 8 := by rw [ha4, Std.Array.set_length]; exact ha3_len
  have ha4_4 : a4.val[4]! = v4 := by
    rw [ha4, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha3_4]
  have hi_a44 : Array.index_usize a4 4#usize = .ok v4 :=
    (array_index_usize_ok_eq a4 4#usize (by rw [ha4_len]; decide)).trans (congrArg Result.ok ha4_4)
  have hu_a5 : Array.update a4 4#usize p2 = .ok (a4.set 4#usize p2) :=
    array_update_ok_eq a4 4#usize p2 (by rw [ha4_len]; decide)
  set a5 : CoeffArray := a4.set 4#usize p2 with ha5
  have ha5_len : a5.length = 8 := by rw [ha5, Std.Array.set_length]; exact ha4_len
  -- Pair 3: hi=7, lo=6.  a5[7] = v7, a5[6] = v6.
  have ha5_7 : a5.val[7]! = v7 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha5_6 : a5.val[6]! = v6 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a57 : Array.index_usize a5 7#usize = .ok v7 :=
    (array_index_usize_ok_eq a5 7#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_7)
  have hi_a56 : Array.index_usize a5 6#usize = .ok v6 :=
    (array_index_usize_ok_eq a5 6#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_6)
  have hu_a6 : Array.update a5 7#usize s3 = .ok (a5.set 7#usize s3) :=
    array_update_ok_eq a5 7#usize s3 (by rw [ha5_len]; decide)
  set a6 : CoeffArray := a5.set 7#usize s3 with ha6
  have ha6_len : a6.length = 8 := by rw [ha6, Std.Array.set_length]; exact ha5_len
  have ha6_6 : a6.val[6]! = v6 := by
    rw [ha6, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha5_6]
  have hi_a66 : Array.index_usize a6 6#usize = .ok v6 :=
    (array_index_usize_ok_eq a6 6#usize (by rw [ha6_len]; decide)).trans (congrArg Result.ok ha6_6)
  have hu_a7 : Array.update a6 6#usize p3 = .ok (a6.set 6#usize p3) :=
    array_update_ok_eq a6 6#usize p3 (by rw [ha6_len]; decide)
  set a7 : CoeffArray := a6.set 6#usize p3 with ha7
  have ha7_len : a7.length = 8 := by rw [ha7, Std.Array.set_length]; exact ha6_len
  -- ===== Compose the whole do-block into one `.ok { values := a7 }`. =====
  set final_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    { values := a7 } with hfu
  have h_body :
      libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_0
        simd_unit zeta0 zeta1 zeta2 zeta3 = .ok final_unit := by
    unfold libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_0
    rw [hi_v1]; simp only [bind_tc_ok]
    rw [classify_ok zeta0]; simp only [bind_tc_ok]
    rw [ht0_eq]; simp only [bind_tc_ok]
    rw [hi_v0]; simp only [bind_tc_ok]
    rw [hs0_eq]; simp only [bind_tc_ok]
    rw [hu_a]; simp only [bind_tc_ok]
    rw [hi_a0]; simp only [bind_tc_ok]
    rw [hp0_eq]; simp only [bind_tc_ok]
    rw [hu_a1]; simp only [bind_tc_ok]
    rw [hi_a13]; simp only [bind_tc_ok]
    rw [classify_ok zeta1]; simp only [bind_tc_ok]
    rw [ht1_eq]; simp only [bind_tc_ok]
    rw [hi_a12]; simp only [bind_tc_ok]
    rw [hs1_eq]; simp only [bind_tc_ok]
    rw [hu_a2]; simp only [bind_tc_ok]
    rw [hi_a22]; simp only [bind_tc_ok]
    rw [hp1_eq]; simp only [bind_tc_ok]
    rw [hu_a3]; simp only [bind_tc_ok]
    rw [hi_a35]; simp only [bind_tc_ok]
    rw [classify_ok zeta2]; simp only [bind_tc_ok]
    rw [ht2_eq]; simp only [bind_tc_ok]
    rw [hi_a34]; simp only [bind_tc_ok]
    rw [hs2_eq]; simp only [bind_tc_ok]
    rw [hu_a4]; simp only [bind_tc_ok]
    rw [hi_a44]; simp only [bind_tc_ok]
    rw [hp2_eq]; simp only [bind_tc_ok]
    rw [hu_a5]; simp only [bind_tc_ok]
    rw [hi_a57]; simp only [bind_tc_ok]
    rw [classify_ok zeta3]; simp only [bind_tc_ok]
    rw [ht3_eq]; simp only [bind_tc_ok]
    rw [hi_a56]; simp only [bind_tc_ok]
    rw [hs3_eq]; simp only [bind_tc_ok]
    rw [hu_a6]; simp only [bind_tc_ok]
    rw [hi_a66]; simp only [bind_tc_ok]
    rw [hp3_eq]; simp only [bind_tc_ok]
    rw [hu_a7]; simp only [bind_tc_ok]
    rfl
  -- ===== Final lane values of a7 (track through the set chain). =====
  -- a7 = a6.set 6 p3; reads: 0→p0, 1→s0, 2→p1, 3→s1, 4→p2, 5→s2, 6→p3, 7→s3.
  have hr0 : a7.val[0]! = p0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_eq _ _ 0 _ ⟨rfl, by rw [ha_len]; decide⟩]
  have hr1 : a7.val[1]! = s0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_eq _ _ 1 _ ⟨rfl, by rw [h_len]; decide⟩]
  have hr2 : a7.val[2]! = p1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_eq _ _ 2 _ ⟨rfl, by rw [ha2_len]; decide⟩]
  have hr3 : a7.val[3]! = s1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_eq _ _ 3 _ ⟨rfl, by rw [ha1_len]; decide⟩]
  have hr4 : a7.val[4]! = p2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_eq _ _ 4 _ ⟨rfl, by rw [ha4_len]; decide⟩]
  have hr5 : a7.val[5]! = s2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_eq _ _ 5 _ ⟨rfl, by rw [ha3_len]; decide⟩]
  have hr6 : a7.val[6]! = p3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq,
        Std.Array.getElem!_Nat_set_eq _ _ 6 _ ⟨rfl, by rw [ha6_len]; decide⟩]
  have hr7 : a7.val[7]! = s3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_eq _ _ 7 _ ⟨rfl, by rw [ha5_len]; decide⟩]
  -- ===== Lift seams: lift each t_p to clean (hi)·(z). =====
  have hlift0 : liftZ t0.val = liftZ v1.val * liftZ zeta0.val := liftZ_of_mont _ _ _ ht0_lift
  have hlift1 : liftZ t1.val = liftZ v3.val * liftZ zeta1.val := liftZ_of_mont _ _ _ ht1_lift
  have hlift2 : liftZ t2.val = liftZ v5.val * liftZ zeta2.val := liftZ_of_mont _ _ _ ht2_lift
  have hlift3 : liftZ t3.val = liftZ v7.val * liftZ zeta3.val := liftZ_of_mont _ _ _ ht3_lift
  -- ===== Close the Triple. =====
  apply triple_of_ok h_body
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- r[0] = v0 + v1·z0
    show liftZ (final_unit.values.val[0]!).val = _
    rw [show final_unit.values = a7 from rfl, hr0, hp0_val, liftZ_add, hlift0]
  · show liftZ (final_unit.values.val[1]!).val = _
    rw [show final_unit.values = a7 from rfl, hr1, hs0_val, liftZ_sub, hlift0]
  · show liftZ (final_unit.values.val[2]!).val = _
    rw [show final_unit.values = a7 from rfl, hr2, hp1_val, liftZ_add, hlift1]
  · show liftZ (final_unit.values.val[3]!).val = _
    rw [show final_unit.values = a7 from rfl, hr3, hs1_val, liftZ_sub, hlift1]
  · show liftZ (final_unit.values.val[4]!).val = _
    rw [show final_unit.values = a7 from rfl, hr4, hp2_val, liftZ_add, hlift2]
  · show liftZ (final_unit.values.val[5]!).val = _
    rw [show final_unit.values = a7 from rfl, hr5, hs2_val, liftZ_sub, hlift2]
  · show liftZ (final_unit.values.val[6]!).val = _
    rw [show final_unit.values = a7 from rfl, hr6, hp3_val, liftZ_add, hlift3]
  · show liftZ (final_unit.values.val[7]!).val = _
    rw [show final_unit.values = a7 from rfl, hr7, hs3_val, liftZ_sub, hlift3]
  · -- Output bounds on all 8 lanes (case-split `j < 8` explicitly).
    intro j hj
    show (final_unit.values.val[j]!).val.natAbs ≤ B + 2 ^ 24
    rw [show final_unit.values = a7 from rfl]
    match j, hj with
    | 0, _ => rw [hr0]; exact hp0_bd
    | 1, _ => rw [hr1]; exact hs0_bd
    | 2, _ => rw [hr2]; exact hp1_bd
    | 3, _ => rw [hr3]; exact hs1_bd
    | 4, _ => rw [hr4]; exact hp2_bd
    | 5, _ => rw [hr5]; exact hs2_bd
    | 6, _ => rw [hr6]; exact hp3_bd
    | 7, _ => rw [hr7]; exact hs3_bd
    | (n + 8), h => exact absurd h (by omega)

/-! ## Layer-1 butterfly FC (zeta reused across pairs 0/1 and 2/3). -/

@[spec]
theorem simd_unit_ntt_at_layer_1_fc
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (zeta1 zeta2 : Std.I32) (B : Nat)
    (hz1 : zeta1.val.natAbs ≤ 8380416) (hz2 : zeta2.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ j : Nat, j < 8 → (simd_unit.values.val[j]!).val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_1 simd_unit zeta1 zeta2
    ⦃ ⇓ r => ⌜ (liftZ (r.values.val[0]!).val = liftZ (simd_unit.values.val[0]!).val + liftZ (simd_unit.values.val[2]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[1]!).val = liftZ (simd_unit.values.val[1]!).val + liftZ (simd_unit.values.val[3]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[2]!).val = liftZ (simd_unit.values.val[0]!).val - liftZ (simd_unit.values.val[2]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[3]!).val = liftZ (simd_unit.values.val[1]!).val - liftZ (simd_unit.values.val[3]!).val * liftZ zeta1.val
              ∧ liftZ (r.values.val[4]!).val = liftZ (simd_unit.values.val[4]!).val + liftZ (simd_unit.values.val[6]!).val * liftZ zeta2.val
              ∧ liftZ (r.values.val[5]!).val = liftZ (simd_unit.values.val[5]!).val + liftZ (simd_unit.values.val[7]!).val * liftZ zeta2.val
              ∧ liftZ (r.values.val[6]!).val = liftZ (simd_unit.values.val[4]!).val - liftZ (simd_unit.values.val[6]!).val * liftZ zeta2.val
              ∧ liftZ (r.values.val[7]!).val = liftZ (simd_unit.values.val[5]!).val - liftZ (simd_unit.values.val[7]!).val * liftZ zeta2.val)
            ∧ (∀ j : Nat, j < 8 → (r.values.val[j]!).val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  have h_len : simd_unit.values.length = 8 := Coefficients_values_length simd_unit
  -- Abbreviate the 8 input lanes.
  set v0 : Std.I32 := simd_unit.values.val[0]! with hv0
  set v1 : Std.I32 := simd_unit.values.val[1]! with hv1
  set v2 : Std.I32 := simd_unit.values.val[2]! with hv2
  set v3 : Std.I32 := simd_unit.values.val[3]! with hv3
  set v4 : Std.I32 := simd_unit.values.val[4]! with hv4
  set v5 : Std.I32 := simd_unit.values.val[5]! with hv5
  set v6 : Std.I32 := simd_unit.values.val[6]! with hv6
  set v7 : Std.I32 := simd_unit.values.val[7]! with hv7
  -- Per-lane input bounds.
  have hb0 : v0.val.natAbs ≤ B := hin 0 (by norm_num)
  have hb1 : v1.val.natAbs ≤ B := hin 1 (by norm_num)
  have hb2 : v2.val.natAbs ≤ B := hin 2 (by norm_num)
  have hb3 : v3.val.natAbs ≤ B := hin 3 (by norm_num)
  have hb4 : v4.val.natAbs ≤ B := hin 4 (by norm_num)
  have hb5 : v5.val.natAbs ≤ B := hin 5 (by norm_num)
  have hb6 : v6.val.natAbs ≤ B := hin 6 (by norm_num)
  have hb7 : v7.val.natAbs ≤ B := hin 7 (by norm_num)
  -- mont-mul leaves: t_p = mmfbf v[hi] zeta_p.  Pairs 0/1 use zeta1, pairs 2/3 use zeta2.
  obtain ⟨t0, ht0_eq, ht0_lift, ht0_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v2 zeta1 hz1)
  obtain ⟨t1, ht1_eq, ht1_lift, ht1_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v3 zeta1 hz1)
  obtain ⟨t2, ht2_eq, ht2_lift, ht2_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v6 zeta2 hz2)
  obtain ⟨t3, ht3_eq, ht3_lift, ht3_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v7 zeta2 hz2)
  -- Checked subtractions/additions.  s_p lands on the HI lane, p_p on the LO lane.
  obtain ⟨s0, hs0_eq, hs0_val, hs0_bd⟩ := checked_sub_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨p0, hp0_eq, hp0_val, hp0_bd⟩ := checked_add_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨s1, hs1_eq, hs1_val, hs1_bd⟩ := checked_sub_ok v1 t1 B hb1 ht1_bd hB
  obtain ⟨p1, hp1_eq, hp1_val, hp1_bd⟩ := checked_add_ok v1 t1 B hb1 ht1_bd hB
  obtain ⟨s2, hs2_eq, hs2_val, hs2_bd⟩ := checked_sub_ok v4 t2 B hb4 ht2_bd hB
  obtain ⟨p2, hp2_eq, hp2_val, hp2_bd⟩ := checked_add_ok v4 t2 B hb4 ht2_bd hB
  obtain ⟨s3, hs3_eq, hs3_val, hs3_bd⟩ := checked_sub_ok v5 t3 B hb5 ht3_bd hB
  obtain ⟨p3, hp3_eq, hp3_val, hp3_bd⟩ := checked_add_ok v5 t3 B hb5 ht3_bd hB
  -- ===== Index/update bridges. =====
  -- Pair 0: hi=2, lo=0.  Update 2 (s0) then update 0 (p0).
  have hi_v2 : Array.index_usize simd_unit.values 2#usize = .ok v2 :=
    array_index_usize_ok_eq simd_unit.values 2#usize (by rw [h_len]; decide)
  have hi_v0 : Array.index_usize simd_unit.values 0#usize = .ok v0 :=
    array_index_usize_ok_eq simd_unit.values 0#usize (by rw [h_len]; decide)
  have hu_a : Array.update simd_unit.values 2#usize s0
      = .ok (simd_unit.values.set 2#usize s0) :=
    array_update_ok_eq simd_unit.values 2#usize s0 (by rw [h_len]; decide)
  set a : CoeffArray := simd_unit.values.set 2#usize s0 with ha
  have ha_len : a.length = 8 := by rw [ha, Std.Array.set_length]; exact h_len
  have ha_0 : a.val[0]! = v0 := by
    rw [ha, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide)]
    rw [Std.Array.getElem!_Nat_eq]
  have hi_a0 : Array.index_usize a 0#usize = .ok v0 :=
    (array_index_usize_ok_eq a 0#usize (by rw [ha_len]; decide)).trans (congrArg Result.ok ha_0)
  have hu_a1 : Array.update a 0#usize p0 = .ok (a.set 0#usize p0) :=
    array_update_ok_eq a 0#usize p0 (by rw [ha_len]; decide)
  set a1 : CoeffArray := a.set 0#usize p0 with ha1
  have ha1_len : a1.length = 8 := by rw [ha1, Std.Array.set_length]; exact ha_len
  -- Pair 1: hi=3, lo=1.  a1[3] = v3, a1[1] = v1.
  have ha1_3 : a1.val[3]! = v3 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha1_1 : a1.val[1]! = v1 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a13 : Array.index_usize a1 3#usize = .ok v3 :=
    (array_index_usize_ok_eq a1 3#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_3)
  have hi_a11 : Array.index_usize a1 1#usize = .ok v1 :=
    (array_index_usize_ok_eq a1 1#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_1)
  have hu_a2 : Array.update a1 3#usize s1 = .ok (a1.set 3#usize s1) :=
    array_update_ok_eq a1 3#usize s1 (by rw [ha1_len]; decide)
  set a2 : CoeffArray := a1.set 3#usize s1 with ha2
  have ha2_len : a2.length = 8 := by rw [ha2, Std.Array.set_length]; exact ha1_len
  have ha2_1 : a2.val[1]! = v1 := by
    rw [ha2, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha1_1]
  have hi_a21 : Array.index_usize a2 1#usize = .ok v1 :=
    (array_index_usize_ok_eq a2 1#usize (by rw [ha2_len]; decide)).trans (congrArg Result.ok ha2_1)
  have hu_a3 : Array.update a2 1#usize p1 = .ok (a2.set 1#usize p1) :=
    array_update_ok_eq a2 1#usize p1 (by rw [ha2_len]; decide)
  set a3 : CoeffArray := a2.set 1#usize p1 with ha3
  have ha3_len : a3.length = 8 := by rw [ha3, Std.Array.set_length]; exact ha2_len
  -- Pair 2: hi=6, lo=4.  a3[6] = v6, a3[4] = v4.
  have ha3_6 : a3.val[6]! = v6 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha3_4 : a3.val[4]! = v4 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a36 : Array.index_usize a3 6#usize = .ok v6 :=
    (array_index_usize_ok_eq a3 6#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_6)
  have hi_a34 : Array.index_usize a3 4#usize = .ok v4 :=
    (array_index_usize_ok_eq a3 4#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_4)
  have hu_a4 : Array.update a3 6#usize s2 = .ok (a3.set 6#usize s2) :=
    array_update_ok_eq a3 6#usize s2 (by rw [ha3_len]; decide)
  set a4 : CoeffArray := a3.set 6#usize s2 with ha4
  have ha4_len : a4.length = 8 := by rw [ha4, Std.Array.set_length]; exact ha3_len
  have ha4_4 : a4.val[4]! = v4 := by
    rw [ha4, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha3_4]
  have hi_a44 : Array.index_usize a4 4#usize = .ok v4 :=
    (array_index_usize_ok_eq a4 4#usize (by rw [ha4_len]; decide)).trans (congrArg Result.ok ha4_4)
  have hu_a5 : Array.update a4 4#usize p2 = .ok (a4.set 4#usize p2) :=
    array_update_ok_eq a4 4#usize p2 (by rw [ha4_len]; decide)
  set a5 : CoeffArray := a4.set 4#usize p2 with ha5
  have ha5_len : a5.length = 8 := by rw [ha5, Std.Array.set_length]; exact ha4_len
  -- Pair 3: hi=7, lo=5.  a5[7] = v7, a5[5] = v5.
  have ha5_7 : a5.val[7]! = v7 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha5_5 : a5.val[5]! = v5 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a57 : Array.index_usize a5 7#usize = .ok v7 :=
    (array_index_usize_ok_eq a5 7#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_7)
  have hi_a55 : Array.index_usize a5 5#usize = .ok v5 :=
    (array_index_usize_ok_eq a5 5#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_5)
  have hu_a6 : Array.update a5 7#usize s3 = .ok (a5.set 7#usize s3) :=
    array_update_ok_eq a5 7#usize s3 (by rw [ha5_len]; decide)
  set a6 : CoeffArray := a5.set 7#usize s3 with ha6
  have ha6_len : a6.length = 8 := by rw [ha6, Std.Array.set_length]; exact ha5_len
  have ha6_5 : a6.val[5]! = v5 := by
    rw [ha6, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha5_5]
  have hi_a65 : Array.index_usize a6 5#usize = .ok v5 :=
    (array_index_usize_ok_eq a6 5#usize (by rw [ha6_len]; decide)).trans (congrArg Result.ok ha6_5)
  have hu_a7 : Array.update a6 5#usize p3 = .ok (a6.set 5#usize p3) :=
    array_update_ok_eq a6 5#usize p3 (by rw [ha6_len]; decide)
  set a7 : CoeffArray := a6.set 5#usize p3 with ha7
  have ha7_len : a7.length = 8 := by rw [ha7, Std.Array.set_length]; exact ha6_len
  -- ===== Compose the whole do-block into one `.ok { values := a7 }`. =====
  set final_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    { values := a7 } with hfu
  have h_body :
      libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_1
        simd_unit zeta1 zeta2 = .ok final_unit := by
    unfold libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_1
    rw [hi_v2]; simp only [bind_tc_ok]
    rw [classify_ok zeta1]; simp only [bind_tc_ok]
    rw [ht0_eq]; simp only [bind_tc_ok]
    rw [hi_v0]; simp only [bind_tc_ok]
    rw [hs0_eq]; simp only [bind_tc_ok]
    rw [hu_a]; simp only [bind_tc_ok]
    rw [hi_a0]; simp only [bind_tc_ok]
    rw [hp0_eq]; simp only [bind_tc_ok]
    rw [hu_a1]; simp only [bind_tc_ok]
    rw [hi_a13]; simp only [bind_tc_ok]
    rw [ht1_eq]; simp only [bind_tc_ok]
    rw [hi_a11]; simp only [bind_tc_ok]
    rw [hs1_eq]; simp only [bind_tc_ok]
    rw [hu_a2]; simp only [bind_tc_ok]
    rw [hi_a21]; simp only [bind_tc_ok]
    rw [hp1_eq]; simp only [bind_tc_ok]
    rw [hu_a3]; simp only [bind_tc_ok]
    rw [hi_a36]; simp only [bind_tc_ok]
    rw [classify_ok zeta2]; simp only [bind_tc_ok]
    rw [ht2_eq]; simp only [bind_tc_ok]
    rw [hi_a34]; simp only [bind_tc_ok]
    rw [hs2_eq]; simp only [bind_tc_ok]
    rw [hu_a4]; simp only [bind_tc_ok]
    rw [hi_a44]; simp only [bind_tc_ok]
    rw [hp2_eq]; simp only [bind_tc_ok]
    rw [hu_a5]; simp only [bind_tc_ok]
    rw [hi_a57]; simp only [bind_tc_ok]
    rw [ht3_eq]; simp only [bind_tc_ok]
    rw [hi_a55]; simp only [bind_tc_ok]
    rw [hs3_eq]; simp only [bind_tc_ok]
    rw [hu_a6]; simp only [bind_tc_ok]
    rw [hi_a65]; simp only [bind_tc_ok]
    rw [hp3_eq]; simp only [bind_tc_ok]
    rw [hu_a7]; simp only [bind_tc_ok]
    rfl
  -- ===== Final lane values of a7. =====
  -- a7 = a6.set 5 p3; reads: 0→p0, 1→p1, 2→s0, 3→s1, 4→p2, 5→p3, 6→s2, 7→s3.
  have hr0 : a7.val[0]! = p0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_eq _ _ 0 _ ⟨rfl, by rw [ha_len]; decide⟩]
  have hr1 : a7.val[1]! = p1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_eq _ _ 1 _ ⟨rfl, by rw [ha2_len]; decide⟩]
  have hr2 : a7.val[2]! = s0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_eq _ _ 2 _ ⟨rfl, by rw [h_len]; decide⟩]
  have hr3 : a7.val[3]! = s1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_eq _ _ 3 _ ⟨rfl, by rw [ha1_len]; decide⟩]
  have hr4 : a7.val[4]! = p2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_eq _ _ 4 _ ⟨rfl, by rw [ha4_len]; decide⟩]
  have hr5 : a7.val[5]! = p3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq,
        Std.Array.getElem!_Nat_set_eq _ _ 5 _ ⟨rfl, by rw [ha6_len]; decide⟩]
  have hr6 : a7.val[6]! = s2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_eq _ _ 6 _ ⟨rfl, by rw [ha3_len]; decide⟩]
  have hr7 : a7.val[7]! = s3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_eq _ _ 7 _ ⟨rfl, by rw [ha5_len]; decide⟩]
  -- ===== Lift seams. =====
  have hlift0 : liftZ t0.val = liftZ v2.val * liftZ zeta1.val := liftZ_of_mont _ _ _ ht0_lift
  have hlift1 : liftZ t1.val = liftZ v3.val * liftZ zeta1.val := liftZ_of_mont _ _ _ ht1_lift
  have hlift2 : liftZ t2.val = liftZ v6.val * liftZ zeta2.val := liftZ_of_mont _ _ _ ht2_lift
  have hlift3 : liftZ t3.val = liftZ v7.val * liftZ zeta2.val := liftZ_of_mont _ _ _ ht3_lift
  -- ===== Close the Triple. =====
  apply triple_of_ok h_body
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- r[0] = v0 + v2·z1
    show liftZ (final_unit.values.val[0]!).val = _
    rw [show final_unit.values = a7 from rfl, hr0, hp0_val, liftZ_add, hlift0]
  · show liftZ (final_unit.values.val[1]!).val = _
    rw [show final_unit.values = a7 from rfl, hr1, hp1_val, liftZ_add, hlift1]
  · show liftZ (final_unit.values.val[2]!).val = _
    rw [show final_unit.values = a7 from rfl, hr2, hs0_val, liftZ_sub, hlift0]
  · show liftZ (final_unit.values.val[3]!).val = _
    rw [show final_unit.values = a7 from rfl, hr3, hs1_val, liftZ_sub, hlift1]
  · show liftZ (final_unit.values.val[4]!).val = _
    rw [show final_unit.values = a7 from rfl, hr4, hp2_val, liftZ_add, hlift2]
  · show liftZ (final_unit.values.val[5]!).val = _
    rw [show final_unit.values = a7 from rfl, hr5, hp3_val, liftZ_add, hlift3]
  · show liftZ (final_unit.values.val[6]!).val = _
    rw [show final_unit.values = a7 from rfl, hr6, hs2_val, liftZ_sub, hlift2]
  · show liftZ (final_unit.values.val[7]!).val = _
    rw [show final_unit.values = a7 from rfl, hr7, hs3_val, liftZ_sub, hlift3]
  · -- Output bounds on all 8 lanes.
    intro j hj
    show (final_unit.values.val[j]!).val.natAbs ≤ B + 2 ^ 24
    rw [show final_unit.values = a7 from rfl]
    match j, hj with
    | 0, _ => rw [hr0]; exact hp0_bd
    | 1, _ => rw [hr1]; exact hp1_bd
    | 2, _ => rw [hr2]; exact hs0_bd
    | 3, _ => rw [hr3]; exact hs1_bd
    | 4, _ => rw [hr4]; exact hp2_bd
    | 5, _ => rw [hr5]; exact hp3_bd
    | 6, _ => rw [hr6]; exact hs2_bd
    | 7, _ => rw [hr7]; exact hs3_bd
    | (n + 8), h => exact absurd h (by omega)

/-! ## Layer-2 butterfly FC (single zeta reused across all 4 pairs). -/

@[spec]
theorem simd_unit_ntt_at_layer_2_fc
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (zeta : Std.I32) (B : Nat)
    (hz : zeta.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ j : Nat, j < 8 → (simd_unit.values.val[j]!).val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_2 simd_unit zeta
    ⦃ ⇓ r => ⌜ (liftZ (r.values.val[0]!).val = liftZ (simd_unit.values.val[0]!).val + liftZ (simd_unit.values.val[4]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[1]!).val = liftZ (simd_unit.values.val[1]!).val + liftZ (simd_unit.values.val[5]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[2]!).val = liftZ (simd_unit.values.val[2]!).val + liftZ (simd_unit.values.val[6]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[3]!).val = liftZ (simd_unit.values.val[3]!).val + liftZ (simd_unit.values.val[7]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[4]!).val = liftZ (simd_unit.values.val[0]!).val - liftZ (simd_unit.values.val[4]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[5]!).val = liftZ (simd_unit.values.val[1]!).val - liftZ (simd_unit.values.val[5]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[6]!).val = liftZ (simd_unit.values.val[2]!).val - liftZ (simd_unit.values.val[6]!).val * liftZ zeta.val
              ∧ liftZ (r.values.val[7]!).val = liftZ (simd_unit.values.val[3]!).val - liftZ (simd_unit.values.val[7]!).val * liftZ zeta.val)
            ∧ (∀ j : Nat, j < 8 → (r.values.val[j]!).val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  have h_len : simd_unit.values.length = 8 := Coefficients_values_length simd_unit
  -- Abbreviate the 8 input lanes.
  set v0 : Std.I32 := simd_unit.values.val[0]! with hv0
  set v1 : Std.I32 := simd_unit.values.val[1]! with hv1
  set v2 : Std.I32 := simd_unit.values.val[2]! with hv2
  set v3 : Std.I32 := simd_unit.values.val[3]! with hv3
  set v4 : Std.I32 := simd_unit.values.val[4]! with hv4
  set v5 : Std.I32 := simd_unit.values.val[5]! with hv5
  set v6 : Std.I32 := simd_unit.values.val[6]! with hv6
  set v7 : Std.I32 := simd_unit.values.val[7]! with hv7
  -- Per-lane input bounds.
  have hb0 : v0.val.natAbs ≤ B := hin 0 (by norm_num)
  have hb1 : v1.val.natAbs ≤ B := hin 1 (by norm_num)
  have hb2 : v2.val.natAbs ≤ B := hin 2 (by norm_num)
  have hb3 : v3.val.natAbs ≤ B := hin 3 (by norm_num)
  have hb4 : v4.val.natAbs ≤ B := hin 4 (by norm_num)
  have hb5 : v5.val.natAbs ≤ B := hin 5 (by norm_num)
  have hb6 : v6.val.natAbs ≤ B := hin 6 (by norm_num)
  have hb7 : v7.val.natAbs ≤ B := hin 7 (by norm_num)
  -- mont-mul leaves: t_p = mmfbf v[hi] zeta.  All 4 pairs use the SAME zeta.
  obtain ⟨t0, ht0_eq, ht0_lift, ht0_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v4 zeta hz)
  obtain ⟨t1, ht1_eq, ht1_lift, ht1_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v5 zeta hz)
  obtain ⟨t2, ht2_eq, ht2_lift, ht2_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v6 zeta hz)
  obtain ⟨t3, ht3_eq, ht3_lift, ht3_bd⟩ :=
    triple_exists_ok (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
      v7 zeta hz)
  -- Checked subtractions/additions.  s_p lands on the HI lane, p_p on the LO lane.
  obtain ⟨s0, hs0_eq, hs0_val, hs0_bd⟩ := checked_sub_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨p0, hp0_eq, hp0_val, hp0_bd⟩ := checked_add_ok v0 t0 B hb0 ht0_bd hB
  obtain ⟨s1, hs1_eq, hs1_val, hs1_bd⟩ := checked_sub_ok v1 t1 B hb1 ht1_bd hB
  obtain ⟨p1, hp1_eq, hp1_val, hp1_bd⟩ := checked_add_ok v1 t1 B hb1 ht1_bd hB
  obtain ⟨s2, hs2_eq, hs2_val, hs2_bd⟩ := checked_sub_ok v2 t2 B hb2 ht2_bd hB
  obtain ⟨p2, hp2_eq, hp2_val, hp2_bd⟩ := checked_add_ok v2 t2 B hb2 ht2_bd hB
  obtain ⟨s3, hs3_eq, hs3_val, hs3_bd⟩ := checked_sub_ok v3 t3 B hb3 ht3_bd hB
  obtain ⟨p3, hp3_eq, hp3_val, hp3_bd⟩ := checked_add_ok v3 t3 B hb3 ht3_bd hB
  -- ===== Index/update bridges. =====
  -- Pair 0: hi=4, lo=0.  Update 4 (s0) then update 0 (p0).
  have hi_v4 : Array.index_usize simd_unit.values 4#usize = .ok v4 :=
    array_index_usize_ok_eq simd_unit.values 4#usize (by rw [h_len]; decide)
  have hi_v0 : Array.index_usize simd_unit.values 0#usize = .ok v0 :=
    array_index_usize_ok_eq simd_unit.values 0#usize (by rw [h_len]; decide)
  have hu_a : Array.update simd_unit.values 4#usize s0
      = .ok (simd_unit.values.set 4#usize s0) :=
    array_update_ok_eq simd_unit.values 4#usize s0 (by rw [h_len]; decide)
  set a : CoeffArray := simd_unit.values.set 4#usize s0 with ha
  have ha_len : a.length = 8 := by rw [ha, Std.Array.set_length]; exact h_len
  have ha_0 : a.val[0]! = v0 := by
    rw [ha, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide)]
    rw [Std.Array.getElem!_Nat_eq]
  have hi_a0 : Array.index_usize a 0#usize = .ok v0 :=
    (array_index_usize_ok_eq a 0#usize (by rw [ha_len]; decide)).trans (congrArg Result.ok ha_0)
  have hu_a1 : Array.update a 0#usize p0 = .ok (a.set 0#usize p0) :=
    array_update_ok_eq a 0#usize p0 (by rw [ha_len]; decide)
  set a1 : CoeffArray := a.set 0#usize p0 with ha1
  have ha1_len : a1.length = 8 := by rw [ha1, Std.Array.set_length]; exact ha_len
  -- Pair 1: hi=5, lo=1.  a1[5] = v5, a1[1] = v1.
  have ha1_5 : a1.val[5]! = v5 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha1_1 : a1.val[1]! = v1 := by
    rw [ha1, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a15 : Array.index_usize a1 5#usize = .ok v5 :=
    (array_index_usize_ok_eq a1 5#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_5)
  have hi_a11 : Array.index_usize a1 1#usize = .ok v1 :=
    (array_index_usize_ok_eq a1 1#usize (by rw [ha1_len]; decide)).trans (congrArg Result.ok ha1_1)
  have hu_a2 : Array.update a1 5#usize s1 = .ok (a1.set 5#usize s1) :=
    array_update_ok_eq a1 5#usize s1 (by rw [ha1_len]; decide)
  set a2 : CoeffArray := a1.set 5#usize s1 with ha2
  have ha2_len : a2.length = 8 := by rw [ha2, Std.Array.set_length]; exact ha1_len
  have ha2_1 : a2.val[1]! = v1 := by
    rw [ha2, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha1_1]
  have hi_a21 : Array.index_usize a2 1#usize = .ok v1 :=
    (array_index_usize_ok_eq a2 1#usize (by rw [ha2_len]; decide)).trans (congrArg Result.ok ha2_1)
  have hu_a3 : Array.update a2 1#usize p1 = .ok (a2.set 1#usize p1) :=
    array_update_ok_eq a2 1#usize p1 (by rw [ha2_len]; decide)
  set a3 : CoeffArray := a2.set 1#usize p1 with ha3
  have ha3_len : a3.length = 8 := by rw [ha3, Std.Array.set_length]; exact ha2_len
  -- Pair 2: hi=6, lo=2.  a3[6] = v6, a3[2] = v2.
  have ha3_6 : a3.val[6]! = v6 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha3_2 : a3.val[2]! = v2 := by
    rw [ha3, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a36 : Array.index_usize a3 6#usize = .ok v6 :=
    (array_index_usize_ok_eq a3 6#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_6)
  have hi_a32 : Array.index_usize a3 2#usize = .ok v2 :=
    (array_index_usize_ok_eq a3 2#usize (by rw [ha3_len]; decide)).trans (congrArg Result.ok ha3_2)
  have hu_a4 : Array.update a3 6#usize s2 = .ok (a3.set 6#usize s2) :=
    array_update_ok_eq a3 6#usize s2 (by rw [ha3_len]; decide)
  set a4 : CoeffArray := a3.set 6#usize s2 with ha4
  have ha4_len : a4.length = 8 := by rw [ha4, Std.Array.set_length]; exact ha3_len
  have ha4_2 : a4.val[2]! = v2 := by
    rw [ha4, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha3_2]
  have hi_a42 : Array.index_usize a4 2#usize = .ok v2 :=
    (array_index_usize_ok_eq a4 2#usize (by rw [ha4_len]; decide)).trans (congrArg Result.ok ha4_2)
  have hu_a5 : Array.update a4 2#usize p2 = .ok (a4.set 2#usize p2) :=
    array_update_ok_eq a4 2#usize p2 (by rw [ha4_len]; decide)
  set a5 : CoeffArray := a4.set 2#usize p2 with ha5
  have ha5_len : a5.length = 8 := by rw [ha5, Std.Array.set_length]; exact ha4_len
  -- Pair 3: hi=7, lo=3.  a5[7] = v7, a5[3] = v3.
  have ha5_7 : a5.val[7]! = v7 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have ha5_3 : a5.val[3]! = v3 := by
    rw [ha5, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide), Std.Array.getElem!_Nat_eq]
  have hi_a57 : Array.index_usize a5 7#usize = .ok v7 :=
    (array_index_usize_ok_eq a5 7#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_7)
  have hi_a53 : Array.index_usize a5 3#usize = .ok v3 :=
    (array_index_usize_ok_eq a5 3#usize (by rw [ha5_len]; decide)).trans (congrArg Result.ok ha5_3)
  have hu_a6 : Array.update a5 7#usize s3 = .ok (a5.set 7#usize s3) :=
    array_update_ok_eq a5 7#usize s3 (by rw [ha5_len]; decide)
  set a6 : CoeffArray := a5.set 7#usize s3 with ha6
  have ha6_len : a6.length = 8 := by rw [ha6, Std.Array.set_length]; exact ha5_len
  have ha6_3 : a6.val[3]! = v3 := by
    rw [ha6, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        Std.Array.getElem!_Nat_eq, ha5_3]
  have hi_a63 : Array.index_usize a6 3#usize = .ok v3 :=
    (array_index_usize_ok_eq a6 3#usize (by rw [ha6_len]; decide)).trans (congrArg Result.ok ha6_3)
  have hu_a7 : Array.update a6 3#usize p3 = .ok (a6.set 3#usize p3) :=
    array_update_ok_eq a6 3#usize p3 (by rw [ha6_len]; decide)
  set a7 : CoeffArray := a6.set 3#usize p3 with ha7
  have ha7_len : a7.length = 8 := by rw [ha7, Std.Array.set_length]; exact ha6_len
  -- ===== Compose the whole do-block into one `.ok { values := a7 }`. =====
  set final_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    { values := a7 } with hfu
  have h_body :
      libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_2
        simd_unit zeta = .ok final_unit := by
    unfold libcrux_iot_ml_dsa.simd.portable.ntt.simd_unit_ntt_at_layer_2
    rw [hi_v4]; simp only [bind_tc_ok]
    rw [classify_ok zeta]; simp only [bind_tc_ok]
    rw [ht0_eq]; simp only [bind_tc_ok]
    rw [hi_v0]; simp only [bind_tc_ok]
    rw [hs0_eq]; simp only [bind_tc_ok]
    rw [hu_a]; simp only [bind_tc_ok]
    rw [hi_a0]; simp only [bind_tc_ok]
    rw [hp0_eq]; simp only [bind_tc_ok]
    rw [hu_a1]; simp only [bind_tc_ok]
    rw [hi_a15]; simp only [bind_tc_ok]
    rw [ht1_eq]; simp only [bind_tc_ok]
    rw [hi_a11]; simp only [bind_tc_ok]
    rw [hs1_eq]; simp only [bind_tc_ok]
    rw [hu_a2]; simp only [bind_tc_ok]
    rw [hi_a21]; simp only [bind_tc_ok]
    rw [hp1_eq]; simp only [bind_tc_ok]
    rw [hu_a3]; simp only [bind_tc_ok]
    rw [hi_a36]; simp only [bind_tc_ok]
    rw [ht2_eq]; simp only [bind_tc_ok]
    rw [hi_a32]; simp only [bind_tc_ok]
    rw [hs2_eq]; simp only [bind_tc_ok]
    rw [hu_a4]; simp only [bind_tc_ok]
    rw [hi_a42]; simp only [bind_tc_ok]
    rw [hp2_eq]; simp only [bind_tc_ok]
    rw [hu_a5]; simp only [bind_tc_ok]
    rw [hi_a57]; simp only [bind_tc_ok]
    rw [ht3_eq]; simp only [bind_tc_ok]
    rw [hi_a53]; simp only [bind_tc_ok]
    rw [hs3_eq]; simp only [bind_tc_ok]
    rw [hu_a6]; simp only [bind_tc_ok]
    rw [hi_a63]; simp only [bind_tc_ok]
    rw [hp3_eq]; simp only [bind_tc_ok]
    rw [hu_a7]; simp only [bind_tc_ok]
    rfl
  -- ===== Final lane values of a7. =====
  -- a7 = a6.set 3 p3; reads: 0→p0, 1→p1, 2→p2, 3→p3, 4→s0, 5→s1, 6→s2, 7→s3.
  have hr0 : a7.val[0]! = p0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_eq _ _ 0 _ ⟨rfl, by rw [ha_len]; decide⟩]
  have hr1 : a7.val[1]! = p1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_eq _ _ 1 _ ⟨rfl, by rw [ha2_len]; decide⟩]
  have hr2 : a7.val[2]! = p2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_eq _ _ 2 _ ⟨rfl, by rw [ha4_len]; decide⟩]
  have hr3 : a7.val[3]! = p3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq,
        Std.Array.getElem!_Nat_set_eq _ _ 3 _ ⟨rfl, by rw [ha6_len]; decide⟩]
  have hr4 : a7.val[4]! = s0 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha1, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha, Std.Array.getElem!_Nat_set_eq _ _ 4 _ ⟨rfl, by rw [h_len]; decide⟩]
  have hr5 : a7.val[5]! = s1 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha3, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha2, Std.Array.getElem!_Nat_set_eq _ _ 5 _ ⟨rfl, by rw [ha1_len]; decide⟩]
  have hr6 : a7.val[6]! = s2 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha5, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha4, Std.Array.getElem!_Nat_set_eq _ _ 6 _ ⟨rfl, by rw [ha3_len]; decide⟩]
  have hr7 : a7.val[7]! = s3 := by
    rw [ha7, ← Std.Array.getElem!_Nat_eq, Std.Array.getElem!_Nat_set_ne _ _ _ _ (by decide),
        ha6, Std.Array.getElem!_Nat_set_eq _ _ 7 _ ⟨rfl, by rw [ha5_len]; decide⟩]
  -- ===== Lift seams. =====
  have hlift0 : liftZ t0.val = liftZ v4.val * liftZ zeta.val := liftZ_of_mont _ _ _ ht0_lift
  have hlift1 : liftZ t1.val = liftZ v5.val * liftZ zeta.val := liftZ_of_mont _ _ _ ht1_lift
  have hlift2 : liftZ t2.val = liftZ v6.val * liftZ zeta.val := liftZ_of_mont _ _ _ ht2_lift
  have hlift3 : liftZ t3.val = liftZ v7.val * liftZ zeta.val := liftZ_of_mont _ _ _ ht3_lift
  -- ===== Close the Triple. =====
  apply triple_of_ok h_body
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- r[0] = v0 + v4·z
    show liftZ (final_unit.values.val[0]!).val = _
    rw [show final_unit.values = a7 from rfl, hr0, hp0_val, liftZ_add, hlift0]
  · show liftZ (final_unit.values.val[1]!).val = _
    rw [show final_unit.values = a7 from rfl, hr1, hp1_val, liftZ_add, hlift1]
  · show liftZ (final_unit.values.val[2]!).val = _
    rw [show final_unit.values = a7 from rfl, hr2, hp2_val, liftZ_add, hlift2]
  · show liftZ (final_unit.values.val[3]!).val = _
    rw [show final_unit.values = a7 from rfl, hr3, hp3_val, liftZ_add, hlift3]
  · show liftZ (final_unit.values.val[4]!).val = _
    rw [show final_unit.values = a7 from rfl, hr4, hs0_val, liftZ_sub, hlift0]
  · show liftZ (final_unit.values.val[5]!).val = _
    rw [show final_unit.values = a7 from rfl, hr5, hs1_val, liftZ_sub, hlift1]
  · show liftZ (final_unit.values.val[6]!).val = _
    rw [show final_unit.values = a7 from rfl, hr6, hs2_val, liftZ_sub, hlift2]
  · show liftZ (final_unit.values.val[7]!).val = _
    rw [show final_unit.values = a7 from rfl, hr7, hs3_val, liftZ_sub, hlift3]
  · -- Output bounds on all 8 lanes.
    intro j hj
    show (final_unit.values.val[j]!).val.natAbs ≤ B + 2 ^ 24
    rw [show final_unit.values = a7 from rfl]
    match j, hj with
    | 0, _ => rw [hr0]; exact hp0_bd
    | 1, _ => rw [hr1]; exact hp1_bd
    | 2, _ => rw [hr2]; exact hp2_bd
    | 3, _ => rw [hr3]; exact hp3_bd
    | 4, _ => rw [hr4]; exact hs0_bd
    | 5, _ => rw [hr5]; exact hs1_bd
    | 6, _ => rw [hr6]; exact hs2_bd
    | 7, _ => rw [hr7]; exact hs3_bd
    | (n + 8), h => exact absurd h (by omega)


/-! ## Cross-unit forward NTT layer op `outer_3_plus` FC (KEYSTONE).

  `simd.portable.ntt.outer_3_plus OFFSET STEP_BY ZETA re` loops `j` over the
  `Range Usize` `[OFFSET, OFFSET+STEP_BY)`, applying a Cooley–Tukey butterfly to
  the pair of WHOLE `Coefficients` SIMD units `(j, i=j+STEP_BY)`:
  ```
  tmp1 = montgomery_multiply_by_constant(re[i], ZETA)   -- |tmp1[l]| ≤ 2^24
  out[j] = re[j] + tmp1     out[i] = re[j] - tmp1
  ```
  Lifting (Montgomery-strip) each output lane gives the clean butterfly
  `liftZ out[j][l] = liftZ re[j][l] + liftZ re[i][l]·liftZ ZETA` and
  `liftZ out[i][l] = liftZ re[j][l] - liftZ re[i][l]·liftZ ZETA`.

  Structurally mirrors ml-kem's `Layer1FC` (Range-Usize loop via
  `loop_range_spec_usize`), but updates TWO units per iteration, so the
  invariant tracks two swept sub-ranges and the step re-establishes it with
  `getElem!_Nat_set_ne`/`_set_eq` applied twice (final array is
  `re.set i c2 |>.set j c4`; the double-set at `i` is harmless: `j ≠ i`). -/

namespace Layer3OuterFC

open Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_dsa.Util.LoopSpecs

/-- The cross-unit accumulator: the whole 32-unit array. -/
abbrev Acc := Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize

/-- Local `usize_add_ok_eq` helper. -/
theorem usize_add_ok_eq (x y : Std.Usize) (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- FC loop invariant for `outer_3_plus_fc`.  `S = STEP_BY.val`.
    `acc` agrees with the clean butterfly on the lower swept range `[OFFSET, k)`,
    is unchanged outside the touched window, and stays `≤ B + 2^24`. -/
def inv
    (OFFSET STEP_BY : Std.Usize) (ZETA : Std.I32)
    (re : Acc) (B : Nat) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, OFFSET.val ≤ j → j < k.val →
        (∀ l : Nat, l < 8 →
          liftZ (acc.val[j]!).values.val[l]!.val
            = liftZ (re.val[j]!).values.val[l]!.val
              + liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val)
      ∧ (∀ l : Nat, l < 8 →
          liftZ (acc.val[j + STEP_BY.val]!).values.val[l]!.val
            = liftZ (re.val[j]!).values.val[l]!.val
              - liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val))
    ∧ (∀ u : Nat, u < 32 → (u < OFFSET.val ∨ k.val ≤ u) →
          (u < OFFSET.val + STEP_BY.val ∨ k.val + STEP_BY.val ≤ u) →
          acc.val[u]! = re.val[u]!)
    ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
          (acc.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (OFFSET STEP_BY : Std.Usize) (ZETA : Std.I32)
    (re : Acc) (B : Nat) (e : Std.Usize) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < e.val ∧ iter'.«end» = e ∧ iter'.start.val = k.val + 1
        ∧ (inv OFFSET STEP_BY ZETA re B iter'.start acc').holds
  | .done y => (inv OFFSET STEP_BY ZETA re B e y).holds

end Layer3OuterFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `outer_3_plus_fc`. At cursor `j = k` with
    `OFFSET ≤ k < OFFSET+STEP_BY`, applies the butterfly to the pair
    `(k, k+STEP_BY)`, extending the lower swept range and preserving the
    unchanged window + bound. -/
theorem outer_3_plus_step_lemma_fc
    (OFFSET STEP_BY : Std.Usize) (ZETA : Std.I32)
    (re : Layer3OuterFC.Acc) (B : Nat)
    (hzeta : ZETA.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hstep : 1 ≤ STEP_BY.val)
    (hbound : OFFSET.val + 2 * STEP_BY.val ≤ 32)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 → (re.val[u]!).values.val[l]!.val.natAbs ≤ B)
    (acc : Layer3OuterFC.Acc) (k : Std.Usize) (e : Std.Usize)
    (h_ge : OFFSET.val ≤ k.val)
    (h_le : k.val ≤ e.val)
    (h_e : e.val = OFFSET.val + STEP_BY.val)
    (h_inv : (Layer3OuterFC.inv OFFSET STEP_BY ZETA re B k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body STEP_BY ZETA
      { start := k, «end» := e } acc
    ⦃ ⇓ r => ⌜ Layer3OuterFC.step_post OFFSET STEP_BY ZETA re B e k r ⌝ ⦄ := by
  have h_acc_len : acc.length = 32 := Std.Array.length_eq _
  obtain ⟨h_done, h_undone, h_bd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body
  by_cases h_lt : k.val < e.val
  · -- `Some j = k` branch.
    have hk_lt_oS : k.val < OFFSET.val + STEP_BY.val := by rw [← h_e]; exact h_lt
    have hk_lt_32 : k.val < 32 := by omega
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k e h_lt
    -- i = k + STEP_BY.
    have hi_max : k.val + STEP_BY.val ≤ Std.Usize.max := by
      have h_kS_le_32 : k.val + STEP_BY.val ≤ 32 := by omega
      have h_32_le_max : (32 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i, hi_eq, hi_val⟩ := Layer3OuterFC.usize_add_ok_eq k STEP_BY hi_max
    have hi_val' : i.val = k.val + STEP_BY.val := hi_val
    have hi_lt_32 : i.val < 32 := by rw [hi_val']; omega
    have h_ne_ki : k.val ≠ i.val := by rw [hi_val']; omega
    -- No-hazard: acc[k] = re[k], acc[i] = re[k+S] = re[i].
    have h_acc_k : acc.val[k.val]! = re.val[k.val]! :=
      h_undone k.val hk_lt_32 (Or.inr (Nat.le_refl _)) (Or.inl hk_lt_oS)
    have h_acc_i : acc.val[i.val]! = re.val[i.val]! :=
      h_undone i.val hi_lt_32 (Or.inr (by omega)) (Or.inr (by omega))
    -- (1) tmp = acc[i].
    -- Opaque names for the two read units (prevents `simp` index renormalization).
    set ai : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients := acc.val[i.val]! with hai_def
    set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients := acc.val[k.val]! with hak_def
    have h_idx_i :
        Aeneas.Std.Array.index_usize acc i = .ok ai :=
      array_index_usize_ok_eq acc i (by rw [h_acc_len]; exact hi_lt_32)
    -- (2) classify ZETA = ZETA.
    -- (3) tmp1 = montgomery_multiply_by_constant acc[i] ZETA.
    obtain ⟨tmp1, h_tmp1_eq, h_tmp1_P⟩ :=
      triple_exists_ok
        (libcrux_iot_ml_dsa.Vector.Portable.Element.montgomery_multiply_by_constant_spec
          ai ZETA hzeta)
    -- (4) c = acc[j] = acc[k].
    have h_idx_k :
        Aeneas.Std.Array.index_usize acc k = .ok ak :=
      array_index_usize_ok_eq acc k (by rw [h_acc_len]; exact hk_lt_32)
    -- (5) re1 = update acc i (acc[k]) = acc.set i acc[k].
    have h_upd_re1 :
        Aeneas.Std.Array.update acc i ak = .ok (acc.set i ak) :=
      array_update_ok_eq acc i ak (by rw [h_acc_len]; exact hi_lt_32)
    set re1 : Layer3OuterFC.Acc := acc.set i ak with hre1_def
    have hre1_len : re1.length = 32 := by rw [hre1_def, Std.Array.set_length]; exact h_acc_len
    -- re1[i] = ak.
    have hre1_i : re1.val[i.val]! = ak := by
      rw [hre1_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc i i.val ak
          ⟨rfl, by rw [h_acc_len]; exact hi_lt_32⟩
    -- (6) (c1, mb) = index_mut_usize re1 i; c1 = re1[i] = ak, mb = re1.set i.
    have h_idx_re1_i :
        Aeneas.Std.Array.index_usize re1 i = .ok ak :=
      (array_index_usize_ok_eq re1 i (by rw [hre1_len]; exact hi_lt_32)).trans
        (congrArg Result.ok hre1_i)
    have h_imt_i :
        Aeneas.Std.Array.index_mut_usize re1 i = .ok (ak, re1.set i) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_re1_i]; rfl
    -- (7) c2 = subtract c1 tmp1 = subtract ak tmp1.
    have h_bd_rek : ∀ l : Nat, l < 8 → (re.val[k.val]!).values.val[l]!.val.natAbs ≤ B :=
      fun l hl => hin k.val hk_lt_32 l hl
    have h_bd_ak : ∀ l : Nat, l < 8 → (ak.values.val[l]!).val.natAbs ≤ B := by
      intro l hl; rw [h_acc_k]; exact h_bd_rek l hl
    have h_tmp1_bd : ∀ l : Nat, l < 8 → (tmp1.values.val[l]!).val.natAbs ≤ 2 ^ 24 :=
      fun l hl => (h_tmp1_P l hl).2
    have h_sub_pre : ∀ l : Nat, l < 8 →
        ((ak.values.val[l]!).val - (tmp1.values.val[l]!).val : Int).natAbs ≤ 2 ^ 31 - 1 := by
      intro l hl
      have hb := h_bd_ak l hl
      have ht := h_tmp1_bd l hl
      have := (sum_abs_bound (ak.values.val[l]!).val (tmp1.values.val[l]!).val B hb ht).2
      omega
    obtain ⟨c2, h_c2_eq, h_c2_P⟩ :=
      triple_exists_ok
        (libcrux_iot_ml_dsa.Vector.Portable.Element.subtract_spec ak tmp1 h_sub_pre)
    -- re2 = mb c2 = re1.set i c2 = acc.set i c2 (double-set at i, last wins).
    set re2 : Layer3OuterFC.Acc := re1.set i c2 with hre2_def
    have hre2_eq : re2 = acc.set i c2 := by
      rw [hre2_def, hre1_def]
      apply Subtype.ext
      simp only [Aeneas.Std.Array.set_val_eq, List.set_set]
    have hre2_len : re2.length = 32 := by rw [hre2_def, Std.Array.set_length]; exact hre1_len
    -- re2[k] = ak (k ≠ i).
    have hre2_k : re2.val[k.val]! = ak := by
      rw [hre2_eq, hak_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne acc i k.val c2 (Ne.symm h_ne_ki)
    -- (8) (c3, mb1) = index_mut_usize re2 k; c3 = re2[k] = ak, mb1 = re2.set k.
    have h_idx_re2_k :
        Aeneas.Std.Array.index_usize re2 k = .ok ak :=
      (array_index_usize_ok_eq re2 k (by rw [hre2_len]; exact hk_lt_32)).trans
        (congrArg Result.ok hre2_k)
    have h_imt_k :
        Aeneas.Std.Array.index_mut_usize re2 k = .ok (ak, re2.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_re2_k]; rfl
    -- Body-shaped variant: the writeback `index_mut_back c2` is the literal
    -- `re1.set i c2`, which is `re2` by definition.
    have h_imt_k_body :
        Aeneas.Std.Array.index_mut_usize (re1.set i c2) k
          = .ok (ak, re2.set k) := by
      rw [show re1.set i c2 = re2 from hre2_def.symm]; exact h_imt_k
    -- (9) c4 = add c3 tmp1 = add ak tmp1.
    have h_add_pre : ∀ l : Nat, l < 8 →
        ((ak.values.val[l]!).val + (tmp1.values.val[l]!).val : Int).natAbs ≤ 2 ^ 31 - 1 := by
      intro l hl
      have hb := h_bd_ak l hl
      have ht := h_tmp1_bd l hl
      have := (sum_abs_bound (ak.values.val[l]!).val (tmp1.values.val[l]!).val B hb ht).1
      omega
    obtain ⟨c4, h_c4_eq, h_c4_P⟩ :=
      triple_exists_ok
        (libcrux_iot_ml_dsa.Vector.Portable.Element.add_spec ak tmp1 h_add_pre)
    -- a = mb1 c4 = re2.set k c4 = (acc.set i c2).set k c4.
    set a : Layer3OuterFC.Acc := re2.set k c4 with ha_def
    have ha_eq : a = (acc.set i c2).set k c4 := by rw [ha_def, hre2_eq]
    have ha_len : a.length = 32 := by rw [ha_def, Std.Array.set_length]; exact hre2_len
    -- Compose the body to .ok (cont (iter', a)).
    have h_body :
        libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body STEP_BY ZETA
          { start := k, «end» := e } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize), a)) := by
      unfold libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := e } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [Aeneas.Std.bind_tc_ok, hi_eq, h_idx_i, classify_ok, h_tmp1_eq, h_idx_k,
        h_upd_re1, h_imt_i, h_c2_eq, h_imt_k_body, h_c4_eq]
      exact ha_def.symm
    apply triple_of_ok h_body
    -- step_post: cont branch.
    show Layer3OuterFC.step_post OFFSET STEP_BY ZETA re B e k
      (.cont (({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize), a))
    unfold Layer3OuterFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Invariant at (s, a).  s.val = k.val + 1.
    show (Layer3OuterFC.inv OFFSET STEP_BY ZETA re B s a).holds
    -- The butterfly lift seam (in `re[k+STEP_BY]` form, matching the post).
    have h_lift_tmp1 : ∀ l : Nat, l < 8 →
        liftZ (tmp1.values.val[l]!).val
          = liftZ (re.val[k.val + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val := by
      intro l hl
      have h := (h_tmp1_P l hl).1
      have hseam := liftZ_of_mont (tmp1.values.val[l]!).val (ai.values.val[l]!).val ZETA.val h
      rw [h_acc_i, show i.val = k.val + STEP_BY.val from hi_val'] at hseam
      exact hseam
    -- a[k][l] = c4[l] = acc[k][l] + tmp1[l]  (the ADD lane = j = k).
    have ha_k : a.val[k.val]! = c4 := by
      rw [ha_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq re2 k k.val c4
          ⟨rfl, by rw [hre2_len]; exact hk_lt_32⟩
    -- a[i][l] = c2[l] = acc[k][l] - tmp1[l]  (the SUB lane = i = k+S).
    have ha_i : a.val[i.val]! = c2 := by
      rw [ha_eq]
      rw [show ((acc.set i c2).set k c4).val[i.val]! = (acc.set i c2).val[i.val]! from by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne (acc.set i c2) k i.val c4 h_ne_ki]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc i i.val c2
          ⟨rfl, by rw [h_acc_len]; exact hi_lt_32⟩
    have ha_kS : a.val[k.val + STEP_BY.val]! = c2 := by
      rw [show k.val + STEP_BY.val = i.val from hi_val'.symm]; exact ha_i
    have h_inv_pure :
        (∀ j : Nat, OFFSET.val ≤ j → j < s.val →
            (∀ l : Nat, l < 8 →
              liftZ (a.val[j]!).values.val[l]!.val
                = liftZ (re.val[j]!).values.val[l]!.val
                  + liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val)
          ∧ (∀ l : Nat, l < 8 →
              liftZ (a.val[j + STEP_BY.val]!).values.val[l]!.val
                = liftZ (re.val[j]!).values.val[l]!.val
                  - liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val))
        ∧ (∀ u : Nat, u < 32 → (u < OFFSET.val ∨ s.val ≤ u) →
              (u < OFFSET.val + STEP_BY.val ∨ s.val + STEP_BY.val ≤ u) →
              a.val[u]! = re.val[u]!)
        ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
              (a.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) := by
      refine ⟨?_, ?_, ?_⟩
      · -- Butterfly equations for j < s.val = k.val + 1.
        intro j hj_ge hj_lt
        rw [hs_val] at hj_lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hj_lt_k | hj_eq_k
        · -- j < k.val: unchanged by both sets (j ≠ k, j+S ≠ k and j+S ≠ i need care).
          -- a = (acc.set i c2).set k c4.  j and j+S differ from k and i.
          have h_j_ne_k : j ≠ k.val := Nat.ne_of_lt hj_lt_k
          have h_j_ne_i : j ≠ i.val := by rw [hi_val']; omega
          have h_jS_ne_k : j + STEP_BY.val ≠ k.val := by omega
          have h_jS_ne_i : j + STEP_BY.val ≠ i.val := by rw [hi_val']; omega
          have h_a_j : a.val[j]! = acc.val[j]! := by
            rw [ha_eq]
            rw [show ((acc.set i c2).set k c4).val[j]! = (acc.set i c2).val[j]! from by
              simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
                Aeneas.Std.Array.getElem!_Nat_set_ne (acc.set i c2) k j c4 (Ne.symm h_j_ne_k)]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc i j c2 (Ne.symm h_j_ne_i)
          have h_a_jS : a.val[j + STEP_BY.val]! = acc.val[j + STEP_BY.val]! := by
            rw [ha_eq]
            rw [show ((acc.set i c2).set k c4).val[j + STEP_BY.val]!
                = (acc.set i c2).val[j + STEP_BY.val]! from by
              simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
                Aeneas.Std.Array.getElem!_Nat_set_ne (acc.set i c2) k (j + STEP_BY.val) c4
                  (Ne.symm h_jS_ne_k)]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc i (j + STEP_BY.val) c2 (Ne.symm h_jS_ne_i)
          rw [h_a_j, h_a_jS]
          exact h_done j hj_ge hj_lt_k
        · -- j = k.val: the freshly-written pair.
          subst hj_eq_k
          refine ⟨?_, ?_⟩
          · -- a[k] = c4 = add ak tmp1.
            intro l hl
            rw [ha_k]
            have hval := (h_c4_P l hl).1
            rw [hval, liftZ_add, h_lift_tmp1 l hl, h_acc_k]
          · -- a[k+S] = a[i] = c2 = subtract ak tmp1.
            intro l hl
            rw [ha_kS]
            have hval := (h_c2_P l hl).1
            rw [hval, liftZ_sub, h_lift_tmp1 l hl, h_acc_k]
      · -- Unchanged window for the new cursor s.val = k.val + 1.
        intro u hu_lt hu_disj1 hu_disj2
        rw [hs_val] at hu_disj1 hu_disj2
        -- u must differ from k and i.
        have h_u_ne_k : u ≠ k.val := by
          rcases hu_disj1 with h | h
          · omega
          · omega
        have h_u_ne_i : u ≠ i.val := by
          rw [hi_val']
          rcases hu_disj2 with h | h
          · omega
          · omega
        have h_a_u : a.val[u]! = acc.val[u]! := by
          rw [ha_eq]
          rw [show ((acc.set i c2).set k c4).val[u]! = (acc.set i c2).val[u]! from by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne (acc.set i c2) k u c4 (Ne.symm h_u_ne_k)]
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc i u c2 (Ne.symm h_u_ne_i)
        rw [h_a_u]
        apply h_undone u hu_lt
        · rcases hu_disj1 with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
        · rcases hu_disj2 with h | h
          · exact Or.inl h
          · exact Or.inr (by omega)
      · -- Bound on all lanes of a.
        intro u hu_lt l hl
        by_cases h_u_k : u = k.val
        · subst h_u_k
          rw [ha_k]
          have hval := (h_c4_P l hl).1
          rw [hval]
          have hb := h_bd_ak l hl
          have ht := h_tmp1_bd l hl
          exact (sum_abs_bound (ak.values.val[l]!).val (tmp1.values.val[l]!).val B hb ht).1
        · by_cases h_u_i : u = i.val
          · subst h_u_i
            rw [ha_i]
            have hval := (h_c2_P l hl).1
            rw [hval]
            have hb := h_bd_ak l hl
            have ht := h_tmp1_bd l hl
            exact (sum_abs_bound (ak.values.val[l]!).val (tmp1.values.val[l]!).val B hb ht).2
          · -- Untouched lane: bound from invariant.
            have h_a_u : a.val[u]! = acc.val[u]! := by
              rw [ha_eq]
              rw [show ((acc.set i c2).set k c4).val[u]! = (acc.set i c2).val[u]! from by
                simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
                  Aeneas.Std.Array.getElem!_Nat_set_ne (acc.set i c2) k u c4 (Ne.symm h_u_k)]
              simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
                Aeneas.Std.Array.getElem!_Nat_set_ne acc i u c2 (Ne.symm h_u_i)
            rw [h_a_u]
            exact h_bd u hu_lt l hl
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ e, done.
    have hk_ge : k.val ≥ e.val := Nat.not_lt.mp h_lt
    have h_iter_none := iter_next_none_eq k e hk_ge
    have h_body :
        libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body STEP_BY ZETA
          { start := k, «end» := e } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := e } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok h_body
    show Layer3OuterFC.step_post OFFSET STEP_BY ZETA re B e k (.done acc)
    unfold Layer3OuterFC.step_post
    -- k = e since OFFSET ≤ k ≤ e and k ≥ e.
    have hk_eq : k.val = e.val := by omega
    show (Layer3OuterFC.inv OFFSET STEP_BY ZETA re B e acc).holds
    have h_inv_pure :
        (∀ j : Nat, OFFSET.val ≤ j → j < e.val →
            (∀ l : Nat, l < 8 →
              liftZ (acc.val[j]!).values.val[l]!.val
                = liftZ (re.val[j]!).values.val[l]!.val
                  + liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val)
          ∧ (∀ l : Nat, l < 8 →
              liftZ (acc.val[j + STEP_BY.val]!).values.val[l]!.val
                = liftZ (re.val[j]!).values.val[l]!.val
                  - liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val))
        ∧ (∀ u : Nat, u < 32 → (u < OFFSET.val ∨ e.val ≤ u) →
              (u < OFFSET.val + STEP_BY.val ∨ e.val + STEP_BY.val ≤ u) →
              acc.val[u]! = re.val[u]!)
        ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
              (acc.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) := by
      refine ⟨?_, ?_, h_bd⟩
      · intro j hj_ge hj_lt
        exact h_done j hj_ge (by rw [hk_eq]; exact hj_lt)
      · intro u hu_lt hu_disj1 hu_disj2
        apply h_undone u hu_lt
        · rcases hu_disj1 with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hk_eq]; exact h)
        · rcases hu_disj2 with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hk_eq]; exact h)
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- KEYSTONE cross-unit forward NTT layer op `outer_3_plus` FC. Loops `j` over
    `[OFFSET, OFFSET+STEP_BY)` applying a Cooley–Tukey butterfly to the pair of
    WHOLE `Coefficients` SIMD units `(j, j+STEP_BY)`. -/
@[spec]
theorem outer_3_plus_fc
    (OFFSET STEP_BY : Std.Usize) (ZETA : Std.I32)
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hzeta : ZETA.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hstep : 1 ≤ STEP_BY.val)
    (hbound : OFFSET.val + 2 * STEP_BY.val ≤ 32)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 → (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus OFFSET STEP_BY ZETA re
    ⦃ ⇓ r => ⌜
      (∀ j : Nat, OFFSET.val ≤ j → j < OFFSET.val + STEP_BY.val →
          (∀ l : Nat, l < 8 →
            liftZ (r.val[j]!).values.val[l]!.val
              = liftZ (re.val[j]!).values.val[l]!.val
                + liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val)
        ∧ (∀ l : Nat, l < 8 →
            liftZ (r.val[j + STEP_BY.val]!).values.val[l]!.val
              = liftZ (re.val[j]!).values.val[l]!.val
                - liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val))
      ∧ (∀ u : Nat, u < 32 → (u < OFFSET.val ∨ OFFSET.val + 2 * STEP_BY.val ≤ u) →
            r.val[u]! = re.val[u]!)
      ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
            (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus
  -- Discharge the checked `OFFSET + STEP_BY` add as `.ok e` (no overflow ≤ 32).
  have he_max : OFFSET.val + STEP_BY.val ≤ Std.Usize.max := by
    have h_kS_le_32 : OFFSET.val + STEP_BY.val ≤ 32 := by omega
    have h_32_le_max : (32 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  obtain ⟨e, he_eq, he_val⟩ := Layer3OuterFC.usize_add_ok_eq OFFSET STEP_BY he_max
  rw [he_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop
  have h_le : OFFSET.val ≤ e.val := by rw [he_val]; omega
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_dsa.simd.portable.ntt.outer_3_plus_loop.body STEP_BY ZETA iter1 acc1)
      (β := Layer3OuterFC.Acc)
      re
      OFFSET e
      (Layer3OuterFC.inv OFFSET STEP_BY ZETA re B)
      h_le
      (by
        -- h_init: at k = OFFSET the butterfly conjunct is vacuous, unchanged trivial, bound = hin.
        show (pure _ : Result Prop).holds
        have h_init_pure :
            (∀ j : Nat, OFFSET.val ≤ j → j < OFFSET.val →
                (∀ l : Nat, l < 8 →
                  liftZ (re.val[j]!).values.val[l]!.val
                    = liftZ (re.val[j]!).values.val[l]!.val
                      + liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val)
              ∧ (∀ l : Nat, l < 8 →
                  liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val
                    = liftZ (re.val[j]!).values.val[l]!.val
                      - liftZ (re.val[j + STEP_BY.val]!).values.val[l]!.val * liftZ ZETA.val))
            ∧ (∀ u : Nat, u < 32 → (u < OFFSET.val ∨ OFFSET.val ≤ u) →
                  (u < OFFSET.val + STEP_BY.val ∨ OFFSET.val + STEP_BY.val ≤ u) →
                  re.val[u]! = re.val[u]!)
            ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (re.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) := by
          refine ⟨?_, ?_, ?_⟩
          · intro j hj_ge hj_lt; exact absurd hj_lt (by omega)
          · intro u _ _ _; rfl
          · intro u hu l hl; have hbu := hin u hu l hl; omega
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_init_pure)
      ?_)
  · -- Post-entailment: inv at k=e yields the locked post.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer3OuterFC.inv OFFSET STEP_BY ZETA re B e r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    obtain ⟨h_done, h_undone, h_bd⟩ := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_holds
    refine ⟨?_, ?_, ?_⟩
    · -- Butterfly eqns: rewrite `< OFFSET+STEP_BY` into `< e.val`.
      intro j hj_ge hj_lt
      exact h_done j hj_ge (by rw [he_val]; exact hj_lt)
    · -- Unchanged units: derive the two inv-clauses from `u < OFFSET ∨ OFFSET+2S ≤ u`.
      intro u hu_lt hu_disj
      apply h_undone u hu_lt
      · rcases hu_disj with h | h
        · exact Or.inl h
        · exact Or.inr (by rw [he_val]; omega)
      · rcases hu_disj with h | h
        · exact Or.inl (by omega)
        · exact Or.inr (by rw [he_val]; omega)
    · -- Output bound.
      exact h_bd
  · -- Step lemma dispatch.
    intro acc k h_ge_k h_le_k hinv
    have h_step :=
      outer_3_plus_step_lemma_fc OFFSET STEP_BY ZETA re B hzeta hB hstep hbound hin acc k e
        h_ge_k h_le_k (by rw [he_val]) hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer3OuterFC.step_post OFFSET STEP_BY ZETA re B e k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3OuterFC.step_post] using hP
    · have hP : Layer3OuterFC.step_post OFFSET STEP_BY ZETA re B e k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3OuterFC.step_post] using hP


end libcrux_iot_ml_dsa.Vector.Portable.Ntt
