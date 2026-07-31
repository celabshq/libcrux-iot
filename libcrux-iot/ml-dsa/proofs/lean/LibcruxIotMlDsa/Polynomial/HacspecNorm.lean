/-
  # `Polynomial/HacspecNorm.lean` — `infinity_norm_exceeds` equivalence to the
  extracted hacspec (`arithmetic.coeff_norm` / `polynomial.poly_infinity_norm`)

  The poly-layer impl `infinity_norm_exceeds` FC (`Polynomial/InfinityNorm.lean::
  infinity_norm_exceeds_fc`) posts the impl result equal to the HAND spec
  `Spec.Pure.infinity_norm_exceeds` at RAW Int altitude (`r = decide (∃ i<256,
  bound ≤ |raw lane i|)`), using the RAW signed absolute value `|coefficient|`.

  This file proves the connection to the machine-EXTRACTED FIPS norm
  (`hacspec_ml_dsa.arithmetic.coeff_norm` / `polynomial.poly_infinity_norm`), which
  computes the CENTERED norm `coeff_norm a = (m = ((a%q)+q)%q; if m > q/2 then q-m else m)`
  and `poly_infinity_norm p = max_{i<256} coeff_norm(p[i])`.

  ## REPRESENTATION SUBTLETY (documented choice, NOT a bug)
  The impl/hand-spec compute RAW `|a|`; the extracted Rust spec computes the CENTERED
  FIPS norm `coeff_norm a`. They agree EXACTLY iff `a` is a centered representative
  (`|a| ≤ (Q-1)/2`). In the FIPS signing context the coefficients ARE centered, so they
  agree — but the impl no-overflow precond (`|lane| ≤ 2^30`) does NOT by itself guarantee
  centering. Hence the impl↔extracted connection FC (`infinity_norm_exceeds_hacspec_fc`)
  carries an explicit `hcentered` hypothesis. This surfaces the FIPS representation choice.

  Structure (mirrors `Spec/HacspecBridge.lean` + `Polynomial/InfinityNorm.lean`):
    (1) `coeff_norm_bridge` — extracted `coeff_norm` succeeds ∀ i32, output `=
        Pure.coeff_norm a.val`, in `[0, Q/2]` (first-principles, template `mod_q_eq`).
    (2) `coeff_norm_eq_abs_of_centered` + `coeff_norm` residue-invariance (pure Int).
    (3) `poly_infinity_norm_bridge` — running-max loop = `foldl max (coeff_norm) 0`,
        + `poly_infinity_norm_exceeds_iff`.
    (4) `@[spec] infinity_norm_exceeds_hacspec_fc` — compose the impl FC under centering.
-/
import LibcruxIotMlDsa.Spec.HacspecBridge
import LibcruxIotMlDsa.Polynomial.InfinityNorm

open CoreModels Aeneas Aeneas.Std Result Std.Do ControlFlow

namespace libcrux_iot_ml_dsa.Polynomial.HacspecNorm
open libcrux_iot_ml_dsa
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.HacspecBridge
open libcrux_iot_ml_dsa.Polynomial.InfinityNorm
open libcrux_iot_ml_dsa.Polynomial.Ntt
open libcrux_iot_ml_dsa.Util.LoopHelper
open libcrux_iot_ml_dsa.Util.LoopSpecs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## File-local scalar helpers (copies of `HacspecBridge` private aux). -/

/-- Sign-extending an `i32` to `i64` is always in-bounds; the `.val` is preserved
    (file-local copy of `HacspecBridge.cast_i64_ok`). -/
private theorem cast_i64_ok (z : Std.I32) :
    ∃ w : Std.I64, Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I64 z) = .ok w ∧ w.val = z.val := by
  have hb : Aeneas.Std.IScalar.min .I64 ≤ z.val ∧ z.val ≤ Aeneas.Std.IScalar.max .I64 := by
    have h1 := Aeneas.Std.IScalar.hBounds z
    simp only [IScalar.min_IScalarTy_I64_eq, IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.min,
      Aeneas.Std.I64.max, Aeneas.Std.I64.numBits, IScalarTy.I64_numBits_eq,
      IScalarTy.I32_numBits_eq] at *
    omega
  obtain ⟨w, hweq, hwval⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I64 z hb)
  exact ⟨w, hweq, hwval⟩

/-! ## (1) `coeff_norm` bridge: extracted = hand `Pure.coeff_norm`, in `[0, Q/2]`. -/

set_option maxHeartbeats 4000000 in
/-- **`coeff_norm` bridge.** The extracted `arithmetic.coeff_norm` succeeds for ALL `i32`;
    its result equals the hand `Pure.coeff_norm a.val` and lies in `[0, Q/2]`. Like
    `mod_q_eq`, first-principles Aeneas scalar reasoning: the i64 cast/`%`/`+`/`%`/cast chain
    computes the canonical residue `m = ((a%q)+q)%q ∈ [0,Q)`; then `if m > Q/2 then Q-m else m`
    lands in `[0, Q/2]`. -/
theorem coeff_norm_bridge (a : Std.I32) :
    ∃ r : Std.I32, hacspec_ml_dsa.arithmetic.coeff_norm a = .ok r
      ∧ (r.val : Int) = Pure.coeff_norm (a.val) ∧ 0 ≤ r.val ∧ r.val ≤ (Q : Int) / 2 := by
  unfold hacspec_ml_dsa.arithmetic.coeff_norm
  -- `i = (a : i64)`, value preserved.
  obtain ⟨wa, hwa_eq, hwa_val⟩ := cast_i64_ok a
  rw [hwa_eq]; simp only [Aeneas.Std.bind_tc_ok]
  -- `i1 = (Q : i64) = 8380417`.
  set qI64 : Std.I64 := Aeneas.Std.IScalar.cast .I64 hacspec_ml_dsa.parameters.Q with hq_def
  have hq_val : qI64.val = 8380417 := by
    rw [hq_def]; unfold hacspec_ml_dsa.parameters.Q; decide
  rw [show (Aeneas.Std.lift qI64 : Result Std.I64) = .ok qI64 from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `i2 = wa % qI64` (tmod, value `wa.val.tmod 8380417`, `|·| < Q`).
  have hqnz : qI64.val ≠ 0 := by rw [hq_val]; decide
  obtain ⟨i2, hi2_eq, hi2_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.rem_spec wa hqnz)
  rw [show (wa % qI64 : Result Std.I64) = .ok i2 from hi2_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hq_val] at hi2_val
  have hi2_abs : (i2.val).natAbs < 8380417 := by
    rw [hi2_val, Int.natAbs_tmod]; exact Nat.mod_lt _ (by decide)
  have hi2_bnd : -8380417 < i2.val ∧ i2.val < 8380417 := by omega
  -- `i4 = i2 + qI64`, value `i2.val + Q ∈ (0, 2Q)`, in i64 range.
  have hi4_min : Aeneas.Std.IScalar.min .I64 ≤ i2.val + qI64.val := by
    simp only [IScalar.min_IScalarTy_I64_eq, Aeneas.Std.I64.min, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq, hq_val]; omega
  have hi4_max : i2.val + qI64.val ≤ Aeneas.Std.IScalar.max .I64 := by
    simp only [IScalar.max_IScalarTy_I64_eq, Aeneas.Std.I64.max, Aeneas.Std.I64.numBits,
      IScalarTy.I64_numBits_eq, hq_val]; omega
  obtain ⟨i4, hi4_eq, hi4_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.add_spec (x := i2) (y := qI64) hi4_min hi4_max)
  rw [show (i2 + qI64 : Result Std.I64) = .ok i4 from hi4_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hq_val] at hi4_val
  -- `i6 = i4 % qI64`, value `(i2.val + Q).tmod Q = m ∈ [0, Q)` (since `i2.val + Q > 0`).
  obtain ⟨i6, hi6_eq, hi6_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.rem_spec i4 hqnz)
  rw [show (i4 % qI64 : Result Std.I64) = .ok i6 from hi6_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [hq_val, hi4_val] at hi6_val
  -- `i6.val = m = ((a%q)+q)%q` — the canonical residue used by `Pure.coeff_norm`.
  have hi2_a : i2.val = a.val.tmod 8380417 := by rw [hi2_val, hwa_val]
  have key : i6.val = ((a.val % 8380417) + 8380417) % 8380417 := by
    rw [hi6_val, hi2_a]
    have hnn : 0 ≤ a.val.tmod 8380417 + 8380417 := by
      rw [← hi2_a]; have := hi2_bnd.1; omega
    rw [Int.tmod_eq_emod_of_nonneg hnn, Int.add_emod_right, Int.tmod_def, Int.sub_emod,
      Int.mul_emod_right]
    simp
  have hi6_bnd : 0 ≤ i6.val ∧ i6.val < 8380417 := by
    rw [key]
    refine ⟨Int.emod_nonneg _ (by decide), Int.emod_lt_of_pos _ (by decide)⟩
  -- `a_mod = (i6 : i32)`, value preserved (i6.val ∈ [0, Q) ⊂ I32 range).
  have ha_mod_bnd :
      Aeneas.Std.IScalar.min .I32 ≤ i6.val ∧ i6.val ≤ Aeneas.Std.IScalar.max .I32 := by
    simp only [IScalar.min_IScalarTy_I32_eq, IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.min,
      Aeneas.Std.I32.max, Aeneas.Std.I32.numBits, IScalarTy.I32_numBits_eq]
    obtain ⟨hlo, hhi⟩ := hi6_bnd; omega
  obtain ⟨a_mod, ha_mod_eq, ha_mod_val⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Aeneas.Std.IScalar.cast_inBounds_spec .I32 i6 ha_mod_bnd)
  rw [show (Aeneas.Std.lift (Aeneas.Std.IScalar.cast .I32 i6) : Result Std.I32) = .ok a_mod
        from ha_mod_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `i7 = Q / 2#i32 = 4190208`.
  have hQ_i32_val : (hacspec_ml_dsa.parameters.Q).val = 8380417 := by
    unfold hacspec_ml_dsa.parameters.Q; decide
  obtain ⟨i7, hi7_eq, hi7_val⟩ :=
    Aeneas.Std.IScalar.div_spec (x := hacspec_ml_dsa.parameters.Q) (y := (2#i32 : Std.I32))
      (by decide)
      (by
        rintro ⟨_, hy⟩
        rw [show ((2#i32 : Std.I32)).val = (2 : Int) from rfl] at hy
        exact absurd hy (by decide))
  rw [show (hacspec_ml_dsa.parameters.Q / 2#i32 : Result Std.I32) = .ok i7 from hi7_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  have hi7_v : i7.val = 4190208 := by rw [hi7_val, hQ_i32_val]; decide
  -- `Pure.coeff_norm a.val = if m > Q/2 then Q - m else m`, with the same `m = i6.val`.
  have ha_mod_v : a_mod.val = ((a.val % 8380417) + 8380417) % 8380417 := by
    rw [ha_mod_val, key]
  have hcn : Pure.coeff_norm a.val
      = if ((a.val % 8380417) + 8380417) % 8380417 > 4190208
        then 8380417 - ((a.val % 8380417) + 8380417) % 8380417
        else ((a.val % 8380417) + 8380417) % 8380417 := by
    unfold Pure.coeff_norm
    have hQI : (Parameters.Q : Int) = 8380417 := by norm_num [Parameters.Q]
    simp only [hQI]
    norm_num
  -- the branch comparison `a_mod > i7` matches `m > Q/2`.
  have hQ_div2 : (Q : Int) / 2 = 4190208 := by norm_num [Q]
  by_cases hgt : a_mod > i7
  · -- `m > 4190208`: result `Q - a_mod = 8380417 - m`, in `(0, 4190209)`.
    rw [if_pos hgt]
    have hm_gt : a_mod.val > 4190208 := by
      have := (Aeneas.Std.IScalar.lt_equiv i7 a_mod).mp hgt
      rw [hi7_v] at this; exact this
    rw [ha_mod_v] at hm_gt
    -- `Q - a_mod` sub spec (in range).
    have hsub_min : Aeneas.Std.IScalar.min .I32 ≤ (hacspec_ml_dsa.parameters.Q).val - a_mod.val := by
      simp only [IScalar.min_IScalarTy_I32_eq, Aeneas.Std.I32.min, Aeneas.Std.I32.numBits,
        IScalarTy.I32_numBits_eq, hQ_i32_val]
      obtain ⟨_, hhi⟩ := hi6_bnd; rw [ha_mod_val]; omega
    have hsub_max : (hacspec_ml_dsa.parameters.Q).val - a_mod.val ≤ Aeneas.Std.IScalar.max .I32 := by
      simp only [IScalar.max_IScalarTy_I32_eq, Aeneas.Std.I32.max, Aeneas.Std.I32.numBits,
        IScalarTy.I32_numBits_eq, hQ_i32_val]
      rw [ha_mod_v]; obtain ⟨hlo, _⟩ := hi6_bnd; rw [← ha_mod_v, ha_mod_val]; omega
    obtain ⟨r, hr_eq, hr_val⟩ :=
      Aeneas.Std.WP.spec_imp_exists
        (Aeneas.Std.IScalar.sub_spec (x := hacspec_ml_dsa.parameters.Q) (y := a_mod)
          hsub_min hsub_max)
    refine ⟨r, hr_eq, ?_, ?_, ?_⟩
    · rw [hr_val, hQ_i32_val, ha_mod_v, hcn, if_pos hm_gt]
    · rw [hr_val, hQ_i32_val, ha_mod_v]
      obtain ⟨_, hhi⟩ := hi6_bnd; rw [← ha_mod_v, ha_mod_val]; omega
    · rw [hr_val, hQ_i32_val, ha_mod_v, hQ_div2, ← ha_mod_v]; omega
  · -- `m ≤ 4190208`: result `a_mod = m`.
    rw [if_neg hgt]
    have hm_le : a_mod.val ≤ 4190208 := by
      by_contra h
      exact hgt (by rw [gt_iff_lt, Aeneas.Std.IScalar.lt_equiv]; rw [hi7_v]; omega)
    rw [ha_mod_v] at hm_le
    refine ⟨a_mod, rfl, ?_, ?_, ?_⟩
    · rw [ha_mod_v, hcn, if_neg (by omega)]
    · rw [ha_mod_v]; obtain ⟨hlo, _⟩ := hi6_bnd; rw [← ha_mod_v, ha_mod_val]; omega
    · rw [ha_mod_v, hQ_div2]; omega

/-! ## (2) `coeff_norm` = raw `|·|` under centering + residue-invariance (pure Int). -/

/-- **`coeff_norm` = raw absolute value under centering.** For a centered representative
    (`|a| ≤ (Q-1)/2 = 4190208`), the FIPS centered norm `Pure.coeff_norm a` collapses to
    the raw signed absolute value `|a|`. (`(Q-1)/2 = 4190208`.) This is the precise
    condition under which the impl's RAW `|·|` agrees with the extracted CENTERED norm. -/
theorem coeff_norm_eq_abs_of_centered (a : Int) (h : |a| ≤ ((Q : Int) - 1) / 2) :
    Pure.coeff_norm a = |a| := by
  unfold Pure.coeff_norm
  simp only []
  have hQI : (Parameters.Q : Int) = 8380417 := by norm_num [Parameters.Q]
  rw [hQI]
  have h1 : -4190208 ≤ a ∧ a ≤ 4190208 := by
    rw [abs_le] at h; rw [hQI] at h; norm_num at h ⊢; omega
  have hcanon : (a % 8380417 + 8380417) % 8380417 = a % 8380417 := by
    rw [Int.add_emod_right, Int.emod_emod_of_dvd _ (dvd_refl _)]
  rw [hcanon]
  by_cases ha : 0 ≤ a
  · have hm : a % 8380417 = a := Int.emod_eq_of_lt ha (by omega)
    rw [hm, if_neg (by norm_num; omega), abs_of_nonneg ha]
  · have ha' : a < 0 := by omega
    have hm : a % 8380417 = a + 8380417 := by
      have : a % 8380417 = (a + 8380417) % 8380417 := by rw [Int.add_emod_right]
      rw [this, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hm, if_pos (by norm_num; omega), abs_of_neg ha']; ring

/-- **`coeff_norm` residue-invariance (mod `q`).** `coeff_norm` depends only on the
    residue class mod `q`: if `a ≡ b [mod q]` then `coeff_norm a = coeff_norm b`. -/
theorem coeff_norm_emod_invariant (a b : Int) (h : a % (Q : Int) = b % (Q : Int)) :
    Pure.coeff_norm a = Pure.coeff_norm b := by
  unfold Pure.coeff_norm; simp only []; rw [h]

/-- **`coeff_norm` on the canonical `Z_q` residue = `coeff_norm` on the raw int.**
    `(x : Zq).val` shares `x`'s residue class mod `q`, so the centered norm is unchanged.
    This is what lets the connection FC read `canon_raw self` (canonical-residue cells)
    and recover the raw-lane norm. -/
theorem coeff_norm_zq_val (x : Int) :
    Pure.coeff_norm (((x : Zq).val : Int)) = Pure.coeff_norm x := by
  apply coeff_norm_emod_invariant
  have h : ((((x : Zq).val : Int)) : Zq) = ((x : Int) : Zq) := by
    push_cast [ZMod.natCast_val, ZMod.intCast_cast]
    simp
  rw [ZMod.intCast_eq_intCast_iff'] at h
  exact h

/-! ## (3) `poly_infinity_norm` bridge: the running-max loop = `foldl max coeff_norm 0`.

Mirrors `Polynomial/InfinityNorm.lean`'s loop idiom: a running-max invariant
`acc.val = (List.range k).foldl (fun m i => max m (Pure.coeff_norm (p[i].val))) 0`,
discharging each per-cell `coeff_norm` via `coeff_norm_bridge`. -/

/-! ### Triple ↔ `Result.ok` reflection (file-scoped copies). -/

private theorem triple_of_ok_in
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_in
    {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_in {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_in {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-- The running-max fold up to `k`: `max` over `coeff_norm(p[i])` for `i < k`, base `0`. -/
def max_fold (p : Aeneas.Std.Array Std.I32 256#usize) (k : Nat) : Int :=
  (List.range k).foldl (fun m i => max m (Pure.coeff_norm (p.val[i]!.val))) 0

/-- `max_fold` is monotone-nonneg: it starts at `0` and `max`'s, so `0 ≤ max_fold`. -/
theorem max_fold_nonneg (p : Aeneas.Std.Array Std.I32 256#usize) (k : Nat) :
    0 ≤ max_fold p k := by
  unfold max_fold
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact le_trans ih (le_max_left _ _)

/-- `max_fold` extends by one step: `max_fold p (k+1) = max (max_fold p k) (coeff_norm p[k])`. -/
theorem max_fold_succ (p : Aeneas.Std.Array Std.I32 256#usize) (k : Nat) :
    max_fold p (k + 1) = max (max_fold p k) (Pure.coeff_norm (p.val[k]!.val)) := by
  unfold max_fold
  rw [List.range_succ, List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]

/-! ### The extracted running-max loop body / invariant / step. -/

/-- The extracted `poly_infinity_norm_loop.body` shape (`CoreIterTraitsIteratorIterator.next`
    reduced to `IteratorRange.next` by `rfl`). Accumulator is the running max `Std.I32`. -/
def pinf_body (p : Aeneas.Std.Array Std.I32 256#usize)
    (iter : CoreModels.core.ops.range.Range Std.Usize) (max : Std.I32) :
    Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Std.I32) Std.I32) := do
  let (o, iter1) ←
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | CoreModels.core.option.Option.None => ok (ControlFlow.done max)
  | CoreModels.core.option.Option.Some i =>
    let i1 ← Aeneas.Std.Array.index_usize p i
    let c ← hacspec_ml_dsa.arithmetic.coeff_norm i1
    if c > max
    then ok (ControlFlow.cont (iter1, c))
    else ok (ControlFlow.cont (iter1, max))

/-- The running-max loop invariant: `max.val = max_fold p k` and `0 ≤ max.val`. -/
def pinf_inv (p : Aeneas.Std.Array Std.I32 256#usize) :
    Std.Usize → Std.I32 → Result Prop :=
  fun k max => pure (max.val = max_fold p k.val ∧ 0 ≤ max.val)

/-- Per-iteration step post for the running-max loop. -/
def pinf_step_post (p : Aeneas.Std.Array Std.I32 256#usize) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Std.I32) Std.I32) : Prop :=
  match r with
  | .cont (iter', max') =>
      k.val < (256#usize : Std.Usize).val ∧ iter'.«end» = 256#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (pinf_inv p iter'.start max').holds
  | .done y => (pinf_inv p 256#usize y).holds

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma for the extracted running-max loop. -/
theorem pinf_step_lemma
    (p : Aeneas.Std.Array Std.I32 256#usize)
    (max : Std.I32) (k : Std.Usize)
    (h_le : k.val ≤ (256#usize : Std.Usize).val)
    (h_inv : (pinf_inv p k max).holds) :
    ⦃ ⌜ True ⌝ ⦄
    pinf_body p { start := k, «end» := 256#usize } max
    ⦃ ⇓ r => ⌜ pinf_step_post p k r ⌝ ⦄ := by
  have h_256 : (256#usize : Std.Usize).val = 256 := rfl
  have h_p_len : p.length = 256 := by show p.val.length = 256; exact p.property
  obtain ⟨h_max_val, h_max_nn⟩ : max.val = max_fold p k.val ∧ 0 ≤ max.val :=
    of_pure_prop_holds_in h_inv
  unfold pinf_body
  by_cases h_lt : k.val < (256#usize : Std.Usize).val
  · -- `Some k` branch.
    have hk_256 : k.val < 256 := by rw [h_256] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 256#usize h_lt
    set t : Std.I32 := p.val[k.val]! with ht_def
    have h_idx : Aeneas.Std.Array.index_usize p k = .ok t :=
      array_index_usize_ok_eq p k (by rw [h_p_len]; exact hk_256)
    -- per-cell coeff_norm via the bridge.
    obtain ⟨c, hc_eq, hc_val, hc_lo, hc_hi⟩ := coeff_norm_bridge t
    set new_max : Std.I32 := if c > max then c else max with hnm_def
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done max) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Std.I32) Std.I32))
          | CoreModels.core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize p i
            let c ← hacspec_ml_dsa.arithmetic.coeff_norm i1
            if c > max
            then ok (ControlFlow.cont (iter1, c))
            else ok (ControlFlow.cont (iter1, max)))
        = .ok (ControlFlow.cont
            (({ start := s, «end» := 256#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_max)) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hc_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [hnm_def]; split <;> rfl
    apply triple_of_ok_in h_body
    show pinf_step_post p k
      (.cont (({ start := s, «end» := 256#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_max))
    unfold pinf_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (pinf_inv p s new_max).holds
    apply pure_prop_holds_in
    show new_max.val = max_fold p s.val ∧ 0 ≤ new_max.val
    rw [hs_val, max_fold_succ p k.val]
    -- `c.val = Pure.coeff_norm (p[k].val)` and `new_max = max max c` as values.
    have hc_cn : c.val = Pure.coeff_norm (p.val[k.val]!.val) := by rw [hc_val, ht_def]
    rw [hnm_def]
    by_cases hgt : c > max
    · simp only [hgt, if_true]
      have hvgt : max.val < c.val := (Aeneas.Std.IScalar.lt_equiv max c).mp hgt
      refine ⟨?_, by omega⟩
      rw [hc_cn]; symm; apply max_eq_right; rw [← hc_cn, ← h_max_val]; omega
    · simp only [hgt, if_false]
      have hvle : c.val ≤ max.val := by
        by_contra h
        exact hgt (by rw [gt_iff_lt, Aeneas.Std.IScalar.lt_equiv]; omega)
      refine ⟨?_, h_max_nn⟩
      rw [h_max_val]; symm; apply max_eq_left; rw [← hc_cn, ← h_max_val]; omega
  · -- `None` branch.
    have hk_ge : k.val ≥ (256#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 256 := by rw [h_256] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 256#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done max) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Std.I32) Std.I32))
          | CoreModels.core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize p i
            let c ← hacspec_ml_dsa.arithmetic.coeff_norm i1
            if c > max
            then ok (ControlFlow.cont (iter1, c))
            else ok (ControlFlow.cont (iter1, max)))
        = .ok (ControlFlow.done max) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 256#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_in h_body
    show pinf_step_post p k (.done max)
    unfold pinf_step_post
    show (pinf_inv p 256#usize max).holds
    apply pure_prop_holds_in
    show max.val = max_fold p (256#usize : Std.Usize).val ∧ 0 ≤ max.val
    rw [h_256, ← hk_eq]; exact ⟨h_max_val, h_max_nn⟩

set_option maxHeartbeats 4000000 in
/-- **`poly_infinity_norm` bridge.** The extracted `polynomial.poly_infinity_norm`
    succeeds for ALL 256-cell `i32` arrays; its result equals the running-max
    `(List.range 256).foldl (fun m i => max m (Pure.coeff_norm p[i].val)) 0` and is `≥ 0`. -/
theorem poly_infinity_norm_bridge (p : Aeneas.Std.Array Std.I32 256#usize) :
    ∃ r : Std.I32, hacspec_ml_dsa.polynomial.poly_infinity_norm p = .ok r
      ∧ (r.val : Int)
          = (List.range 256).foldl (fun m i => max m (Pure.coeff_norm (p.val[i]!.val))) 0
      ∧ 0 ≤ r.val := by
  show ∃ r, hacspec_ml_dsa.polynomial.poly_infinity_norm_loop
              { start := 0#usize, «end» := 256#usize } p 0#i32 = .ok r ∧ _ ∧ _
  unfold hacspec_ml_dsa.polynomial.poly_infinity_norm_loop
  -- Bridge the extracted body to `pinf_body`.
  have h_body_eq :
      (fun (q : (CoreModels.core.ops.range.Range Std.Usize) × Std.I32) =>
        hacspec_ml_dsa.polynomial.poly_infinity_norm_loop.body p q.1 q.2)
      = (fun (q : (CoreModels.core.ops.range.Range Std.Usize) × Std.I32) =>
        pinf_body p q.1 q.2) := by
    funext q
    rcases q with ⟨iter1, max1⟩
    unfold hacspec_ml_dsa.polynomial.poly_infinity_norm_loop.body pinf_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_in
      (loop_range_spec_usize
        (fun q => pinf_body p q.1 q.2)
        0#i32 0#usize 256#usize
        (pinf_inv p)
        (by decide : (0#usize : Std.Usize).val ≤ (256#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_in
          show (0#i32 : Std.I32).val = max_fold p (0#usize : Std.Usize).val ∧ 0 ≤ (0#i32 : Std.I32).val
          refine ⟨?_, by decide⟩
          show (0 : Int) = max_fold p 0
          unfold max_fold; simp)
        (by
          intro acc k _h_ge h_le hinv
          have h_step := pinf_step_lemma p acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : pinf_step_post p k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [pinf_step_post] using hP
          · have hP : pinf_step_post p k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [pinf_step_post] using hP))
  refine ⟨out, h_out_eq, ?_, ?_⟩
  · obtain ⟨h_val, _⟩ : out.val = max_fold p (256#usize : Std.Usize).val ∧ 0 ≤ out.val :=
      of_pure_prop_holds_in h_out_holds
    rw [h_val]; rfl
  · obtain ⟨_, h_nn⟩ : out.val = max_fold p (256#usize : Std.Usize).val ∧ 0 ≤ out.val :=
      of_pure_prop_holds_in h_out_holds
    exact h_nn

/-! ### Running-max ↔ bounded-existential characterization. -/

/-- Generic `foldl max` characterization: `b ≤ foldl max base l ↔ b ≤ base ∨ ∃ i ∈ l, b ≤ f i`. -/
private theorem le_foldl_max_iff (b base : Int) (f : Nat → Int) (l : List Nat) :
    b ≤ l.foldl (fun m i => max m (f i)) base ↔ (b ≤ base ∨ ∃ i ∈ l, b ≤ f i) := by
  induction l generalizing base with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    constructor
    · rintro (h1 | ⟨i, hi, hb⟩)
      · rcases le_max_iff.mp h1 with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨h, Or.inl rfl, h2⟩
      · exact Or.inr ⟨i, Or.inr hi, hb⟩
    · rintro (h1 | ⟨i, (rfl | hi), hb⟩)
      · exact Or.inl (le_trans h1 (le_max_left _ _))
      · exact Or.inl (le_trans hb (le_max_right _ _))
      · exact Or.inr ⟨i, hi, hb⟩

/-- `Pure.coeff_norm` is always nonnegative (centered residue norm ∈ `[0, Q/2]`). -/
theorem coeff_norm_nonneg (a : Std.I32) : 0 ≤ Pure.coeff_norm (a.val) := by
  obtain ⟨_, _, hval, hlo, _⟩ := coeff_norm_bridge a
  rw [← hval]; exact hlo

/-- **`poly_infinity_norm` exceeds-iff.** The extracted check `bound ≤ poly_infinity_norm p`
    holds iff some coefficient's centered norm reaches `bound`:
    `bound ≤ max_{i<256} coeff_norm(p[i]) ↔ ∃ i<256, bound ≤ coeff_norm(p[i])`.
    (Uses `coeff_norm ≥ 0` and `256 > 0`: the base `0` is dominated, so the `b ≤ 0`
    case is subsumed by the existential at `i = 0`.) -/
theorem poly_infinity_norm_exceeds_iff (p : Aeneas.Std.Array Std.I32 256#usize) (bound : Int) :
    ∃ r, hacspec_ml_dsa.polynomial.poly_infinity_norm p = .ok r ∧
      ((bound ≤ r.val)
        ↔ (∃ i, i < 256 ∧ bound ≤ Pure.coeff_norm (p.val[i]!.val))) := by
  obtain ⟨r, hr_eq, hr_val, _hr_nn⟩ := poly_infinity_norm_bridge p
  refine ⟨r, hr_eq, ?_⟩
  rw [hr_val, le_foldl_max_iff bound 0 (fun i => Pure.coeff_norm (p.val[i]!.val)) (List.range 256)]
  constructor
  · rintro (h0 | ⟨i, hi, hb⟩)
    · -- `bound ≤ 0`: take `i = 0` (`coeff_norm ≥ 0 ≥ bound`).
      exact ⟨0, by decide, le_trans h0 (coeff_norm_nonneg (p.val[0]!))⟩
    · exact ⟨i, List.mem_range.mp hi, hb⟩
  · rintro ⟨i, hi, hb⟩
    exact Or.inr ⟨i, List.mem_range.mpr hi, hb⟩

/-! ## (4) hacspec-facing connection FC (centering precond — HONEST). -/

/-- The canonical-residue array of the RAW lanes of a ring element: cell `i` is the
    canonical `[0,Q)` re-encoding (`canonI32`) of the raw lane `i = 8·u + j`'s residue
    class mod `q`. `Pure.coeff_norm` depends only on that residue class, so reading
    `canon_raw self` recovers the raw-lane centered norm. -/
def canon_raw (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients) :
    Aeneas.Std.Array Std.I32 256#usize :=
  ⟨(List.range 256).map
      (fun i => canonI32 ((((self.simd_units.val[i / 8]!).values.val[i % 8]!).val : Int) : Zq)),
   by simp [List.length_map, List.length_range]⟩

/-- `(canon_raw self).val[i]!` is the `canonI32` re-encoding of raw lane `i` (`i < 256`). -/
private theorem canon_raw_getElem
    (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    (canon_raw self).val[i]!
      = canonI32 ((((self.simd_units.val[i / 8]!).values.val[i % 8]!).val : Int) : Zq) := by
  show ((List.range 256).map
      (fun i => canonI32 ((((self.simd_units.val[i / 8]!).values.val[i % 8]!).val : Int) : Zq)))[i]!
    = _
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

/-- `Pure.coeff_norm` of `(canon_raw self)[i]` = `Pure.coeff_norm` of the raw lane `i`
    (centered norm is residue-invariant; `canon_raw` shares the lane's residue class). -/
private theorem canon_raw_coeff_norm
    (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (i : Nat) (hi : i < 256) :
    Pure.coeff_norm ((canon_raw self).val[i]!.val)
      = Pure.coeff_norm (((self.simd_units.val[i / 8]!).values.val[i % 8]!).val) := by
  rw [canon_raw_getElem self i hi, canonI32_val]
  -- `(canonI32 z).val = z.val` (a Nat cast to Int); reduce to `coeff_norm_zq_val`.
  show Pure.coeff_norm
      (((((((self.simd_units.val[i / 8]!).values.val[i % 8]!).val : Int) : Zq).val : Nat) : Int))
    = _
  exact coeff_norm_zq_val (((self.simd_units.val[i / 8]!).values.val[i % 8]!).val)

set_option maxHeartbeats 4000000 in
/-- **`PolynomialRingElement.infinity_norm_exceeds` ↔ extracted
    `hacspec_ml_dsa.polynomial.poly_infinity_norm`.** Composes the impl `infinity_norm_exceeds_fc`
    (RAW `|·|` post) with `poly_infinity_norm_exceeds_iff` (extracted CENTERED norm) on the
    canonical-residue array `canon_raw self`.

    **Representation precond (`hcentered`).** The impl computes the RAW `|coefficient|`, the
    extracted spec the CENTERED FIPS norm `coeff_norm`; they agree iff each coefficient is a
    centered representative (`|·| ≤ (Q-1)/2`). The FIPS signing context feeds centered values,
    so this is a documented representation choice, NOT a bug. Only `hcentered` is required: it
    implies the impl no-overflow precond `|·| ≤ 2^30` (since `(Q-1)/2 = 4190208 ≤ 2^30`), which
    is derived internally. -/
@[spec]
theorem infinity_norm_exceeds_hacspec_fc
    (self : polynomial.PolynomialRingElement simd.portable.vector_type.Coefficients)
    (bound : Std.I32)
    (hcentered : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
        |(self.simd_units.val[u]!).values.val[j]!.val| ≤ ((Q : Int) - 1) / 2) :
    ⦃ ⌜ True ⌝ ⦄
    polynomial.PolynomialRingElement.infinity_norm_exceeds portable_ops_inst self bound
    ⦃ ⇓ r => ⌜ ∃ n, hacspec_ml_dsa.polynomial.poly_infinity_norm (canon_raw self) = .ok n
                ∧ (r = decide (bound.val ≤ n.val)) ⌝ ⦄ := by
  -- `hcentered` (|·| ≤ (Q-1)/2 = 4190208) implies the impl no-overflow bound |·| ≤ 2^30.
  have hpre : ∀ u : Nat, u < 32 → ∀ j : Nat, j < 8 →
      (self.simd_units.val[u]!).values.val[j]!.val.natAbs ≤ 2 ^ 30 := by
    intro u hu j hj
    have h := hcentered u hu j hj
    rw [abs_le] at h
    have hQ : Q = 8380417 := rfl
    have h2 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
    omega
  -- impl FC post: `r = decide (∃ i<256, bound.val ≤ |raw lane i|)`.
  obtain ⟨r, hr_eq, hr_post⟩ :=
    triple_exists_ok_in (InfinityNorm.infinity_norm_exceeds_fc self bound hpre)
  -- extracted exceeds-iff on `canon_raw self`.
  obtain ⟨n, hn_eq, hn_iff⟩ := poly_infinity_norm_exceeds_iff (canon_raw self) bound.val
  apply triple_of_ok_in hr_eq
  refine ⟨n, hn_eq, ?_⟩
  rw [hr_post, decide_eq_decide]
  -- bridge the two existentials: `|raw lane i| = coeff_norm (raw lane i) = coeff_norm (canon_raw[i])`.
  show Spec.Pure.infinity_norm_exceeds
        (fun k => ((self.simd_units.val[k / 8]!).values.val[k % 8]!).val) bound.val
      ↔ bound.val ≤ n.val
  rw [hn_iff]
  unfold Spec.Pure.infinity_norm_exceeds
  constructor
  · rintro ⟨i, hi, hb⟩
    refine ⟨i, hi, ?_⟩
    -- `coeff_norm (canon_raw[i]) = coeff_norm (raw lane i) = |raw lane i|` (centered).
    rw [canon_raw_coeff_norm self i hi]
    have hcen : |((self.simd_units.val[i / 8]!).values.val[i % 8]!).val| ≤ ((Q : Int) - 1) / 2 :=
      hcentered (i / 8) (by omega) (i % 8) (Nat.mod_lt i (by decide))
    rw [coeff_norm_eq_abs_of_centered _ hcen]; exact hb
  · rintro ⟨i, hi, hb⟩
    refine ⟨i, hi, ?_⟩
    rw [canon_raw_coeff_norm self i hi] at hb
    have hcen : |((self.simd_units.val[i / 8]!).values.val[i % 8]!).val| ≤ ((Q : Int) - 1) / 2 :=
      hcentered (i / 8) (by omega) (i % 8) (Nat.mod_lt i (by decide))
    rw [coeff_norm_eq_abs_of_centered _ hcen] at hb; exact hb

/--
info: 'libcrux_iot_ml_dsa.Polynomial.HacspecNorm.infinity_norm_exceeds_hacspec_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms infinity_norm_exceeds_hacspec_fc

end libcrux_iot_ml_dsa.Polynomial.HacspecNorm
