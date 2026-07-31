/-
  # `Vector/Portable/NttDriver.lean` — L3 forward NTT layer drivers (ML-DSA)

  The layer drivers (`ntt_at_layer_7 … ntt_at_layer_0`) tie one or more proven
  `outer_3_plus` cross-unit butterflies (keystone `outer_3_plus_fc`) into
  one `Pure.ntt_layer` step on the lifted flat 256-array. They operate on the raw
  `Array Coefficients 32#usize` (the `.simd_units` field), so they speak
  `Lift.lift_units` (the `Array`-level analogue of `lift_poly`).

  **`ntt_at_layer_7_fc`** is the keystone of this family: `ntt_at_layer_7` is
  exactly one `outer_3_plus 0 16 25847` call (`OFFSET=0, STEP_BY=16, ZETA=25847`).
  Since `0 + 2·16 = 32`, the "unchanged" clause is vacuous — every unit is
  butterflied — and the lifted result equals `ntt_layer (lift_units re) 7`
  (`len = 128`, base zeta index `k = 1`, so each lane uses `zeta 1`).

  The bridge `liftZ 25847 = zeta 1` is proven `decide` (KERNEL, axiom-clean;
  spot-checked by the existing `Spec/Lift.lean` `#guard`s) — NOT `native_decide`.
-/
import LibcruxIotMlDsa.Vector.Portable.Ntt
import LibcruxIotMlDsa.Spec.Lift

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.NttDriver
open Aeneas Aeneas.Std Std.Do Result
open libcrux_iot_ml_dsa.Spec
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Vector.Portable.Ntt
open libcrux_iot_ml_dsa.Util.LoopHelper

/-- Reflect a `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` Triple into an `.ok` witness plus the post
    (file-scoped copy of the §13.5 helper; the original is `private` in `Ntt`). -/
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

set_option maxRecDepth 4000 in
/-- The layer-7 inline zeta `25847` (Montgomery domain) strips to the clean
    `zeta 1`. KERNEL-checked by `decide` (NOT `native_decide`); the `Spec/Lift`
    `#guard`s validate this exact `liftZ <mont literal> = zeta <idx>` class. -/
private theorem zeta7_bridge : liftZ (25847 : Int) = zeta 1 := by decide

@[spec]
theorem ntt_at_layer_7_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_7 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 7
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_7
  -- Pull the cross-unit keystone at OFFSET=0, STEP_BY=16, ZETA=25847.
  have hzeta : (25847#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
  have hstep : 1 ≤ (16#usize : Std.Usize).val := by decide
  have hbound : (0#usize : Std.Usize).val + 2 * (16#usize : Std.Usize).val ≤ 32 := by decide
  obtain ⟨r, hr_eq, hbutter, hunch, hbd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 16#usize 25847#i32 re B hzeta hB hstep hbound hin)
  apply triple_of_ok hr_eq
  -- Normalize the usize literal coercions in the butterfly post to plain numerals.
  have h0 : (0#usize : Std.Usize).val = 0 := by decide
  have h16 : (16#usize : Std.Usize).val = 16 := by decide
  simp only [h0, h16, Nat.zero_add] at hbutter hunch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct: `lift_units r = ntt_layer (lift_units re) 7`.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Normalize the spec at layer 7: `len = 1<<<7 = 128`, `2*len = 256`,
    -- `k = 128/128 = 1`. For `i < 256`: `round = i/256 = 0`, `idx = i%256 = i`.
    have hround : i / 256 = 0 := by omega
    have hidx : i % 256 = i := by omega
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
    -- `liftZ ↑25847#i32 = zeta 1` (cast the i32 literal, then the kernel bridge).
    have hzeta_cast : ((25847#i32 : Std.I32).val : Int) = (25847 : Int) := by decide
    have hz : liftZ ((25847#i32 : Std.I32).val : Int) = zeta 1 := by
      rw [hzeta_cast]; exact zeta7_bridge
    by_cases hlt : i < 128
    · -- Low half: butterfly at unit `u = i/8 < 16`, lane `l = i%8`.
      rw [if_pos hlt]
      have hl : i % 8 < 8 := by omega
      have hdiv : (i + 128) / 8 = i / 8 + 16 := by omega
      have hmod : (i + 128) % 8 = i % 8 := by omega
      have hidx2_lt : i + 128 < 256 := by omega
      -- `build_getElem` on both spec lookups (indices `i` and `i+128`).
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 128) hidx2_lt, hdiv, hmod]
      -- The butterfly low-eq at `j = i/8` (needs `0 ≤ i/8` and `i/8 < 16`).
      obtain ⟨hlow, _hhigh⟩ := hbutter (i / 8) (by omega) (by omega)
      rw [hlow (i % 8) hl, hz, mul_comm]
    · -- High half: butterfly at unit `j = (i-128)/8 < 16`, with `u = i/8 = j+16`.
      rw [if_neg hlt]
      have hl : i % 8 < 8 := by omega
      have hdiv : i / 8 = (i - 128) / 8 + 16 := by omega
      have hmod_lo : (i - 128) % 8 = i % 8 := by omega
      have hidx2_lt : i - 128 < 256 := by omega
      rw [Pure.build_getElem _ (i - 128) hidx2_lt, Pure.build_getElem _ i hi, hmod_lo]
      -- The butterfly high-eq at `j = (i-128)/8` (`j + 16 = i/8`).
      obtain ⟨_hlow, hhigh⟩ := hbutter ((i - 128) / 8) (by omega) (by omega)
      have hhigh' := hhigh (i % 8) hl
      rw [hdiv]  -- goal LHS `r[i/8]` → `r[(i-128)/8 + 16]` to match `hhigh'`
      rw [hhigh', hz, mul_comm]
  · -- Bound conjunct = `hbd` directly.
    exact hbd

/-! ## Layer 6 (`len = 64`, `k = 2`, `STEP_BY = 8`, 2 cross-unit calls)

`ntt_at_layer_6` chains two `outer_3_plus` calls on the disjoint unit blocks
`[0,16)` (call 0, `ZETA = -2608894 → zeta 2`) and `[16,32)` (call 1,
`ZETA = -518909 → zeta 3`). The frame is one step: block-0 units are left
unchanged by call 1 (`OFFSET₁ = 16`), block-1 units are left unchanged by call 0
(`OFFSET₀ + 2·8 = 16`), so each block's butterfly is in terms of `re`. -/

set_option maxRecDepth 4000 in
private theorem zeta6_bridge0 :
    liftZ (((-2608894)#i32 : Std.I32).val : Int) = zeta 2 := by decide
set_option maxRecDepth 4000 in
private theorem zeta6_bridge1 :
    liftZ (((-518909)#i32 : Std.I32).val : Int) = zeta 3 := by decide

/-- i32 zeta-magnitude facts hoisted out of the Triple so the kernel does not
    recheck the (heavy, two's-complement) `decide` terms inside the big proof. -/
private theorem zeta6_mag0 : ((-2608894)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta6_mag1 : ((-518909)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_6_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_6 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 6
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_6
  -- Shared bound arguments for `outer_3_plus_fc`.
  have hstep : 1 ≤ (8#usize : Std.Usize).val := by scalar_tac
  have hz0 := zeta6_mag0
  have hz1 := zeta6_mag1
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (8#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (16#usize : Std.Usize).val + 2 * (8#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  have hB1 : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  -- Call 0 on block [0,16).
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 8#usize (-2608894)#i32 re B hz0 hB0 hstep hbnd0 hin)
  -- Call 1 on block [16,32); input bound is `B + 2^24` (from `h0bd`).
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 8#usize (-518909)#i32 r1 (B + 2 ^ 24) hz1 hB1 hstep hbnd1 h0bd)
  simp only [hr1_eq, Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr2_eq
  -- Normalize usize literal coercions in the butterfly/unchanged posts.
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  simp only [e0, e8, e16, Nat.zero_add] at h0butter h0unch h1butter h1unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Spec at layer 6: `len = 64`, `2*len = 128`, `k = 2`.
    have hzv0 : liftZ ((((-2608894)#i32 : Std.I32).val : Int)) = zeta 2 := zeta6_bridge0
    have hzv1 : liftZ ((((-518909)#i32 : Std.I32).val : Int)) = zeta 3 := zeta6_bridge1
    by_cases hround0 : i < 128
    · -- Round 0 (call 0), spec `round = 0`, `idx = i`, `z = zeta 2`.
      have hround : i / 128 = 0 := by omega
      have hidx : i % 128 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 64
      · -- Low half: unit `u = i/8 ∈ [0,8)`, paired `u+8`, coeff `i+64`.
        rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 64) / 8 = i / 8 + 8 := by omega
        have hmod : (i + 64) % 8 = i % 8 := by omega
        have hidx2 : i + 64 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 64) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        -- LHS unit `i/8` is in block 0: call 1 leaves it unchanged (`r2[i/8] = r1[i/8]`).
        rw [h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl, hzv0, mul_comm]
      · -- High half: paired unit `u-8 = (i-64)/8 ∈ [0,8)`, coeff `i-64`.
        rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 64) / 8 + 8 := by omega
        have hmod : (i - 64) % 8 = i % 8 := by omega
        have hidx2 : i - 64 < 256 := by omega
        rw [Pure.build_getElem _ (i - 64) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 64) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh', hzv0, mul_comm]
    · -- Round 1 (call 1), spec `round = 1`, `idx = i - 128`, `z = zeta (1+2) = zeta 3`.
      have hround : i / 128 = 1 := by omega
      have hidx : i % 128 = i - 128 := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
      by_cases hlt : i - 128 < 64
      · -- Low half: unit `u = i/8 ∈ [16,24)`, paired `u+8`, coeff `i+64`.
        rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 64) / 8 = i / 8 + 8 := by omega
        have hmod : (i + 64) % 8 = i % 8 := by omega
        have hidx2 : i + 64 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 64) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
        -- LHS `r2[i/8]` → butterfly in terms of `r1`; call 0 left block 1 = `re`.
        rw [hlow (i % 8) hl]
        rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 8) (by omega) (by omega)]
        rw [hzv1, mul_comm]
      · -- High half: paired unit `u-8 = (i-64)/8 ∈ [16,24)`, coeff `i-64`.
        rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 64) / 8 + 8 := by omega
        have hmod : (i - 64) % 8 = i % 8 := by omega
        have hidx2 : i - 64 < 256 := by omega
        rw [Pure.build_getElem _ (i - 64) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h1butter ((i - 64) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [hdiv, hhigh']
        rw [h0unch ((i - 64) / 8 + 8) (by omega) (by omega),
            h0unch ((i - 64) / 8) (by omega) (by omega)]
        rw [hzv1, mul_comm]
  · -- Bound conjunct: block 1 (units [16,32)) ≤ B+2·2^24 from `h1bd`; block 0 ≤
    -- B+2^24 from `h0bd`, carried through call 1 (`h1unch`), then `≤ B+2·2^24`.
    intro u hu l hl
    by_cases hb : u < 16
    · -- Block 0: unchanged by call 1.
      rw [h1unch u hu (by omega)]
      have h := h0bd u hu l hl
      have hmono : B + 2 ^ 24 ≤ B + 2 * 2 ^ 24 := by omega
      exact Nat.le_trans h hmono
    · -- Block 1: `h1bd` gives ≤ (B+2^24)+2^24; rewrite the target to that shape.
      rw [show B + 2 * 2 ^ 24 = B + 2 ^ 24 + 2 ^ 24 from by ring]
      exact h1bd u hu l hl

/-! ## Layer 5 (`len = 32`, `k = 4`, `STEP_BY = 4`, 4 cross-unit calls)

`ntt_at_layer_5` chains four `outer_3_plus` calls on disjoint unit blocks
`[0,8)`, `[8,16)`, `[16,24)`, `[24,32)` (`OFFSET = round·8`, `STEP_BY = 4`),
with `ZETA` values `237124→z4`, `-777960→z5`, `-876248→z6`, `466468→z7`. The
locked bound after 4 calls is `B + 4·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta5_bridge0 :
    liftZ ((237124#i32 : Std.I32).val : Int) = zeta 4 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge1 :
    liftZ (((-777960)#i32 : Std.I32).val : Int) = zeta 5 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge2 :
    liftZ (((-876248)#i32 : Std.I32).val : Int) = zeta 6 := by decide
set_option maxRecDepth 4000 in
private theorem zeta5_bridge3 :
    liftZ ((466468#i32 : Std.I32).val : Int) = zeta 7 := by decide

private theorem zeta5_mag0 : (237124#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag1 : ((-777960)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag2 : ((-876248)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta5_mag3 : (466468#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_5_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 4 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_5 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 5
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 4 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_5
  -- Shared bound arguments for `outer_3_plus_fc`.
  have hstep : 1 ≤ (4#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (8#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (16#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (24#usize : Std.Usize).val + 2 * (4#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  -- Call 0 on block [0,8); input bound `B`.
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 4#usize 237124#i32 re B zeta5_mag0 hB0 hstep hbnd0 hin)
  -- Generalise the running bound `B + 2^24` to a FRESH opaque Nat `B1` before the
  -- next call: a `set`/literal `B + k·2^24` keeps the `2^24` numerals, which the
  -- kernel re-expands and NESTS across calls → "(kernel) deep recursion". A true
  -- `generalize` fvar blocks that. (Same trick at each subsequent call.)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  -- Call 1 on block [8,16); input bound `B1 = B + 2^24`.
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 4#usize (-777960)#i32 r1 B1 zeta5_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm; push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  -- Call 2 on block [16,24); input bound `B2 = B + 2·2^24`.
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 4#usize (-876248)#i32 r2 B2 zeta5_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  -- Call 3 on block [24,32); input bound `B3 = B + 3·2^24`.
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 4#usize 466468#i32 r3 B3 zeta5_mag3 hB3raw hstep hbnd3 h2bd)
  -- Collapse the bind chain ONE call at a time (keeps each kernel-checked term
  -- shallow; a single `simp only [hr1_eq, hr2_eq, hr3_eq, ...]` builds a deeply
  -- nested `Result` bind that triggers kernel deep recursion).
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr4_eq
  -- Normalize usize literal coercions in the butterfly/unchanged posts.
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e24v : (24#usize : Std.Usize).val = 24 := by simp
  simp only [e0, e4, e8, e16, e24v, Nat.zero_add]
    at h0butter h0unch h1butter h1unch h2butter h2unch h3butter h3unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    -- Spec at layer 5: `len = 32`, `2*len = 64`, `k = 4`.
    have hzv0 : liftZ (((237124#i32 : Std.I32).val : Int)) = zeta 4 := zeta5_bridge0
    have hzv1 : liftZ ((((-777960)#i32 : Std.I32).val : Int)) = zeta 5 := zeta5_bridge1
    have hzv2 : liftZ ((((-876248)#i32 : Std.I32).val : Int)) = zeta 6 := zeta5_bridge2
    have hzv3 : liftZ (((466468#i32 : Std.I32).val : Int)) = zeta 7 := zeta5_bridge3
    by_cases hr0 : i < 64
    · -- Round 0 (call 0), spec `round = 0`, `idx = i`, `z = zeta 4`.
      have hround : i / 64 = 0 := by omega
      have hidx : i % 64 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 32
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
        have hmod : (i + 32) % 8 = i % 8 := by omega
        have hidx2 : i + 32 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        -- LHS unit `i/8 ∈ [0,4)` in block 0: calls 1,2,3 leave it unchanged.
        rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl, hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
        have hmod : (i - 32) % 8 = i % 8 := by omega
        have hidx2 : i - 32 < 256 := by omega
        rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 32) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh', hzv0, mul_comm]
    · by_cases hr1 : i < 128
      · -- Round 1 (call 1), spec `round = 1`, `idx = i - 64`, `z = zeta 5`.
        have hround : i / 64 = 1 := by omega
        have hidx : i % 64 = i - 64 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 64 < 32
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
          have hmod : (i + 32) % 8 = i % 8 := by omega
          have hidx2 : i + 32 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          -- LHS unit `i/8 ∈ [8,12)` in block 1: calls 2,3 leave it unchanged.
          rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          -- Butterfly in terms of `r1`; call 0 left block 1 = `re`.
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 4) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
          have hmod : (i - 32) % 8 = i % 8 := by omega
          have hidx2 : i - 32 < 256 := by omega
          rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 32) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h3unch (i / 8) (by omega) (by omega), h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
              h0unch ((i - 32) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · by_cases hr2 : i < 192
        · -- Round 2 (call 2), spec `round = 2`, `idx = i - 128`, `z = zeta 6`.
          have hround : i / 64 = 2 := by omega
          have hidx : i % 64 = i - 128 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 128 < 32
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
            have hmod : (i + 32) % 8 = i % 8 := by omega
            have hidx2 : i + 32 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            -- Butterfly in terms of `r2`; calls 0,1 left block 2 = `re`.
            rw [h1unch (i / 8) (by omega) (by omega), h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 4) (by omega) (by omega),
                h0unch (i / 8 + 4) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
            have hmod : (i - 32) % 8 = i % 8 := by omega
            have hidx2 : i - 32 < 256 := by omega
            rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 32) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h1unch ((i - 32) / 8) (by omega) (by omega),
                h0unch ((i - 32) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Round 3 (call 3), spec `round = 3`, `idx = i - 192`, `z = zeta 7`.
          have hround : i / 64 = 3 := by omega
          have hidx : i % 64 = i - 192 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 192 < 32
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 32) / 8 = i / 8 + 4 := by omega
            have hmod : (i + 32) % 8 = i % 8 := by omega
            have hidx2 : i + 32 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 32) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
            rw [hlow (i % 8) hl]
            -- Butterfly in terms of `r3`; calls 0,1,2 left block 3 = `re`.
            rw [h2unch (i / 8) (by omega) (by omega), h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h2unch (i / 8 + 4) (by omega) (by omega),
                h1unch (i / 8 + 4) (by omega) (by omega),
                h0unch (i / 8 + 4) (by omega) (by omega)]
            rw [hzv3, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 32) / 8 + 4 := by omega
            have hmod : (i - 32) % 8 = i % 8 := by omega
            have hidx2 : i - 32 < 256 := by omega
            rw [Pure.build_getElem _ (i - 32) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h3butter ((i - 32) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [hdiv, hhigh']
            rw [h2unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h1unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h0unch ((i - 32) / 8 + 4) (by omega) (by omega),
                h2unch ((i - 32) / 8) (by omega) (by omega),
                h1unch ((i - 32) / 8) (by omega) (by omega),
                h0unch ((i - 32) / 8) (by omega) (by omega)]
            rw [hzv3, mul_comm]
  · -- Bound conjunct: last call's bound `h3bd : |r4| ≤ B3 + 2^24` is already
    -- uniform; recover `B3 + 2^24 = B + 4·2^24` from the generalise equations.
    have heq : B3 + 2 ^ 24 = B + 4 * 2 ^ 24 := by
      rw [← hB3def, ← hB2def, ← hB1def]; ring
    intro u hu l hl
    have := h3bd u hu l hl
    rw [heq] at this
    exact this

/-! ## Layer 4 (`len = 16`, `k = 8`, `STEP_BY = 2`, 8 cross-unit calls)

`ntt_at_layer_4` chains eight `outer_3_plus` calls on disjoint unit blocks
`[4·round, 4·round+2)` (`OFFSET = 4·round`, `STEP_BY = 2`), `ZETA` values
`1826347→z8 … 2680103→z15`. The locked bound after 8 calls is `B + 8·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta4_bridge0 :
    liftZ ((1826347#i32 : Std.I32).val : Int) = zeta 8 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge1 :
    liftZ ((2353451#i32 : Std.I32).val : Int) = zeta 9 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge2 :
    liftZ (((-359251)#i32 : Std.I32).val : Int) = zeta 10 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge3 :
    liftZ (((-2091905)#i32 : Std.I32).val : Int) = zeta 11 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge4 :
    liftZ ((3119733#i32 : Std.I32).val : Int) = zeta 12 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge5 :
    liftZ (((-2884855)#i32 : Std.I32).val : Int) = zeta 13 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge6 :
    liftZ ((3111497#i32 : Std.I32).val : Int) = zeta 14 := by decide
set_option maxRecDepth 4000 in
private theorem zeta4_bridge7 :
    liftZ ((2680103#i32 : Std.I32).val : Int) = zeta 15 := by decide

private theorem zeta4_mag0 : (1826347#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag1 : (2353451#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag2 : ((-359251)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag3 : ((-2091905)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag4 : (3119733#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag5 : ((-2884855)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag6 : (3111497#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta4_mag7 : (2680103#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_4_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 8 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_4 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 4
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 8 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_4
  have hstep : 1 ≤ (2#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (4#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (8#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (12#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd4 : (16#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd5 : (20#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd6 : (24#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd7 : (28#usize : Std.Usize).val + 2 * (2#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 2#usize 1826347#i32 re B zeta4_mag0 hB0 hstep hbnd0 hin)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 4#usize 2#usize 2353451#i32 r1 B1 zeta4_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 2#usize (-359251)#i32 r2 B2 zeta4_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 12#usize 2#usize (-2091905)#i32 r3 B3 zeta4_mag3 hB3raw hstep hbnd3 h2bd)
  have hB4raw : ((B3 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    push_cast; omega
  generalize hB4def : B3 + 2 ^ 24 = B4 at h3bd hB4raw
  obtain ⟨r5, hr5_eq, h4butter, h4unch, h4bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 2#usize 3119733#i32 r4 B4 zeta4_mag4 hB4raw hstep hbnd4 h3bd)
  have hB5raw : ((B4 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    push_cast; omega
  generalize hB5def : B4 + 2 ^ 24 = B5 at h4bd hB5raw
  obtain ⟨r6, hr6_eq, h5butter, h5unch, h5bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 20#usize 2#usize (-2884855)#i32 r5 B5 zeta4_mag5 hB5raw hstep hbnd5 h4bd)
  have hB6raw : ((B5 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    push_cast; omega
  generalize hB6def : B5 + 2 ^ 24 = B6 at h5bd hB6raw
  obtain ⟨r7, hr7_eq, h6butter, h6unch, h6bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 2#usize 3111497#i32 r6 B6 zeta4_mag6 hB6raw hstep hbnd6 h5bd)
  have hB7raw : ((B6 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    push_cast; omega
  generalize hB7def : B6 + 2 ^ 24 = B7 at h6bd hB7raw
  obtain ⟨r8, hr8_eq, h7butter, h7unch, h7bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 28#usize 2#usize 2680103#i32 r7 B7 zeta4_mag7 hB7raw hstep hbnd7 h6bd)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr8_eq
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e2 : (2#usize : Std.Usize).val = 2 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e12 : (12#usize : Std.Usize).val = 12 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e20 : (20#usize : Std.Usize).val = 20 := by simp
  have e24 : (24#usize : Std.Usize).val = 24 := by simp
  have e28 : (28#usize : Std.Usize).val = 28 := by simp
  simp only [e0, e2, e4, e8, e12, e16, e20, e24, e28, Nat.zero_add]
    at h0butter h0unch h1butter h1unch h2butter h2unch h3butter h3unch
       h4butter h4unch h5butter h5unch h6butter h6unch h7butter h7unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    have hzv0 : liftZ (((1826347#i32 : Std.I32).val : Int)) = zeta 8 := zeta4_bridge0
    have hzv1 : liftZ (((2353451#i32 : Std.I32).val : Int)) = zeta 9 := zeta4_bridge1
    have hzv2 : liftZ ((((-359251)#i32 : Std.I32).val : Int)) = zeta 10 := zeta4_bridge2
    have hzv3 : liftZ ((((-2091905)#i32 : Std.I32).val : Int)) = zeta 11 := zeta4_bridge3
    have hzv4 : liftZ (((3119733#i32 : Std.I32).val : Int)) = zeta 12 := zeta4_bridge4
    have hzv5 : liftZ ((((-2884855)#i32 : Std.I32).val : Int)) = zeta 13 := zeta4_bridge5
    have hzv6 : liftZ (((3111497#i32 : Std.I32).val : Int)) = zeta 14 := zeta4_bridge6
    have hzv7 : liftZ (((2680103#i32 : Std.I32).val : Int)) = zeta 15 := zeta4_bridge7
    by_cases hr0 : i < 32
    · -- Round 0.
      have hround : i / 32 = 0 := by omega
      have hidx : i % 32 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 16
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
        have hmod : (i + 16) % 8 = i % 8 := by omega
        have hidx2 : i + 16 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        rw [h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl]
        rw [hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
        have hmod : (i - 16) % 8 = i % 8 := by omega
        have hidx2 : i - 16 < 256 := by omega
        rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 16) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh']
        rw [hzv0, mul_comm]
    · -- Rounds 1+.
      by_cases hr1 : i < 64
      · -- Round 1.
        have hround : i / 32 = 1 := by omega
        have hidx : i % 32 = i - 32 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 32 < 16
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
          have hmod : (i + 16) % 8 = i % 8 := by omega
          have hidx2 : i + 16 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          rw [h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 2) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
          have hmod : (i - 16) % 8 = i % 8 := by omega
          have hidx2 : i - 16 < 256 := by omega
          rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 16) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
              h0unch ((i - 16) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · -- Rounds 2+.
        by_cases hr2 : i < 96
        · -- Round 2.
          have hround : i / 32 = 2 := by omega
          have hidx : i % 32 = i - 64 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 64 < 16
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
            have hmod : (i + 16) % 8 = i % 8 := by omega
            have hidx2 : i + 16 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            rw [h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 2) (by omega) (by omega),
                h0unch (i / 8 + 2) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
            have hmod : (i - 16) % 8 = i % 8 := by omega
            have hidx2 : i - 16 < 256 := by omega
            rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 16) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                h1unch ((i - 16) / 8) (by omega) (by omega),
                h0unch ((i - 16) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Rounds 3+.
          by_cases hr3 : i < 128
          · -- Round 3.
            have hround : i / 32 = 3 := by omega
            have hidx : i % 32 = i - 96 := by omega
            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
              hround, hidx, Nat.reduceAdd]
            by_cases hlt : i - 96 < 16
            · rw [if_pos hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
              have hmod : (i + 16) % 8 = i % 8 := by omega
              have hidx2 : i + 16 < 256 := by omega
              rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
              obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
              rw [h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hlow (i % 8) hl]
              rw [h2unch (i / 8) (by omega) (by omega),
                  h1unch (i / 8) (by omega) (by omega),
                  h0unch (i / 8) (by omega) (by omega),
                  h2unch (i / 8 + 2) (by omega) (by omega),
                  h1unch (i / 8 + 2) (by omega) (by omega),
                  h0unch (i / 8 + 2) (by omega) (by omega)]
              rw [hzv3, mul_comm]
            · rw [if_neg hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
              have hmod : (i - 16) % 8 = i % 8 := by omega
              have hidx2 : i - 16 < 256 := by omega
              rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
              obtain ⟨_, hhigh⟩ := h3butter ((i - 16) / 8) (by omega) (by omega)
              have hhigh' := hhigh (i % 8) hl
              rw [h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hdiv, hhigh']
              rw [h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                  h2unch ((i - 16) / 8) (by omega) (by omega),
                  h1unch ((i - 16) / 8) (by omega) (by omega),
                  h0unch ((i - 16) / 8) (by omega) (by omega)]
              rw [hzv3, mul_comm]
          · -- Rounds 4+.
            by_cases hr4 : i < 160
            · -- Round 4.
              have hround : i / 32 = 4 := by omega
              have hidx : i % 32 = i - 128 := by omega
              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                hround, hidx, Nat.reduceAdd]
              by_cases hlt : i - 128 < 16
              · rw [if_pos hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                have hmod : (i + 16) % 8 = i % 8 := by omega
                have hidx2 : i + 16 < 256 := by omega
                rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                obtain ⟨hlow, _⟩ := h4butter (i / 8) (by omega) (by omega)
                rw [h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hlow (i % 8) hl]
                rw [h3unch (i / 8) (by omega) (by omega),
                    h2unch (i / 8) (by omega) (by omega),
                    h1unch (i / 8) (by omega) (by omega),
                    h0unch (i / 8) (by omega) (by omega),
                    h3unch (i / 8 + 2) (by omega) (by omega),
                    h2unch (i / 8 + 2) (by omega) (by omega),
                    h1unch (i / 8 + 2) (by omega) (by omega),
                    h0unch (i / 8 + 2) (by omega) (by omega)]
                rw [hzv4, mul_comm]
              · rw [if_neg hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                have hmod : (i - 16) % 8 = i % 8 := by omega
                have hidx2 : i - 16 < 256 := by omega
                rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                obtain ⟨_, hhigh⟩ := h4butter ((i - 16) / 8) (by omega) (by omega)
                have hhigh' := hhigh (i % 8) hl
                rw [h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hdiv, hhigh']
                rw [h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                    h3unch ((i - 16) / 8) (by omega) (by omega),
                    h2unch ((i - 16) / 8) (by omega) (by omega),
                    h1unch ((i - 16) / 8) (by omega) (by omega),
                    h0unch ((i - 16) / 8) (by omega) (by omega)]
                rw [hzv4, mul_comm]
            · -- Rounds 5+.
              by_cases hr5 : i < 192
              · -- Round 5.
                have hround : i / 32 = 5 := by omega
                have hidx : i % 32 = i - 160 := by omega
                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                  hround, hidx, Nat.reduceAdd]
                by_cases hlt : i - 160 < 16
                · rw [if_pos hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                  have hmod : (i + 16) % 8 = i % 8 := by omega
                  have hidx2 : i + 16 < 256 := by omega
                  rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                  obtain ⟨hlow, _⟩ := h5butter (i / 8) (by omega) (by omega)
                  rw [h7unch (i / 8) (by omega) (by omega), h6unch (i / 8) (by omega) (by omega)]
                  rw [hlow (i % 8) hl]
                  rw [h4unch (i / 8) (by omega) (by omega),
                      h3unch (i / 8) (by omega) (by omega),
                      h2unch (i / 8) (by omega) (by omega),
                      h1unch (i / 8) (by omega) (by omega),
                      h0unch (i / 8) (by omega) (by omega),
                      h4unch (i / 8 + 2) (by omega) (by omega),
                      h3unch (i / 8 + 2) (by omega) (by omega),
                      h2unch (i / 8 + 2) (by omega) (by omega),
                      h1unch (i / 8 + 2) (by omega) (by omega),
                      h0unch (i / 8 + 2) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
                · rw [if_neg hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                  have hmod : (i - 16) % 8 = i % 8 := by omega
                  have hidx2 : i - 16 < 256 := by omega
                  rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                  obtain ⟨_, hhigh⟩ := h5butter ((i - 16) / 8) (by omega) (by omega)
                  have hhigh' := hhigh (i % 8) hl
                  rw [h7unch (i / 8) (by omega) (by omega), h6unch (i / 8) (by omega) (by omega)]
                  rw [hdiv, hhigh']
                  rw [h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                      h4unch ((i - 16) / 8) (by omega) (by omega),
                      h3unch ((i - 16) / 8) (by omega) (by omega),
                      h2unch ((i - 16) / 8) (by omega) (by omega),
                      h1unch ((i - 16) / 8) (by omega) (by omega),
                      h0unch ((i - 16) / 8) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
              · -- Rounds 6+.
                by_cases hr6 : i < 224
                · -- Round 6.
                  have hround : i / 32 = 6 := by omega
                  have hidx : i % 32 = i - 192 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 192 < 16
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                    have hmod : (i + 16) % 8 = i % 8 := by omega
                    have hidx2 : i + 16 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h6butter (i / 8) (by omega) (by omega)
                    rw [h7unch (i / 8) (by omega) (by omega)]
                    rw [hlow (i % 8) hl]
                    rw [h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8 + 2) (by omega) (by omega),
                        h4unch (i / 8 + 2) (by omega) (by omega),
                        h3unch (i / 8 + 2) (by omega) (by omega),
                        h2unch (i / 8 + 2) (by omega) (by omega),
                        h1unch (i / 8 + 2) (by omega) (by omega),
                        h0unch (i / 8 + 2) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                    have hmod : (i - 16) % 8 = i % 8 := by omega
                    have hidx2 : i - 16 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h6butter ((i - 16) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [h7unch (i / 8) (by omega) (by omega)]
                    rw [hdiv, hhigh']
                    rw [h5unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h5unch ((i - 16) / 8) (by omega) (by omega),
                        h4unch ((i - 16) / 8) (by omega) (by omega),
                        h3unch ((i - 16) / 8) (by omega) (by omega),
                        h2unch ((i - 16) / 8) (by omega) (by omega),
                        h1unch ((i - 16) / 8) (by omega) (by omega),
                        h0unch ((i - 16) / 8) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                · -- Rounds 7+.
                  have hround : i / 32 = 7 := by omega
                  have hidx : i % 32 = i - 224 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 224 < 16
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 16) / 8 = i / 8 + 2 := by omega
                    have hmod : (i + 16) % 8 = i % 8 := by omega
                    have hidx2 : i + 16 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 16) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h7butter (i / 8) (by omega) (by omega)
                    rw [hlow (i % 8) hl]
                    rw [h6unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h6unch (i / 8 + 2) (by omega) (by omega),
                        h5unch (i / 8 + 2) (by omega) (by omega),
                        h4unch (i / 8 + 2) (by omega) (by omega),
                        h3unch (i / 8 + 2) (by omega) (by omega),
                        h2unch (i / 8 + 2) (by omega) (by omega),
                        h1unch (i / 8 + 2) (by omega) (by omega),
                        h0unch (i / 8 + 2) (by omega) (by omega)]
                    rw [hzv7, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 16) / 8 + 2 := by omega
                    have hmod : (i - 16) % 8 = i % 8 := by omega
                    have hidx2 : i - 16 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 16) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h7butter ((i - 16) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [hdiv, hhigh']
                    rw [h6unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h5unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h4unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h3unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h2unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h1unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h0unch ((i - 16) / 8 + 2) (by omega) (by omega),
                        h6unch ((i - 16) / 8) (by omega) (by omega),
                        h5unch ((i - 16) / 8) (by omega) (by omega),
                        h4unch ((i - 16) / 8) (by omega) (by omega),
                        h3unch ((i - 16) / 8) (by omega) (by omega),
                        h2unch ((i - 16) / 8) (by omega) (by omega),
                        h1unch ((i - 16) / 8) (by omega) (by omega),
                        h0unch ((i - 16) / 8) (by omega) (by omega)]
                    rw [hzv7, mul_comm]
  · -- Bound conjunct.
    have heq : B7 + 2 ^ 24 = B + 8 * 2 ^ 24 := by
      rw [← hB7def, ← hB6def, ← hB5def, ← hB4def, ← hB3def, ← hB2def, ← hB1def]; ring
    intro u hu l hl
    have := h7bd u hu l hl
    rw [heq] at this
    exact this

/-! ## Layer 3 (`len = 8`, `k = 16`, `STEP_BY = 1`, 16 cross-unit calls)

`ntt_at_layer_3` chains sixteen `outer_3_plus` calls on disjoint single-unit
blocks `[2·round, 2·round+1)` (`OFFSET = 2·round`, `STEP_BY = 1`), `ZETA` values
`2725464→z16 … 280005→z31`. The locked bound after 16 calls is `B + 16·2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta3_bridge0 :
    liftZ ((2725464#i32 : Std.I32).val : Int) = zeta 16 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge1 :
    liftZ ((1024112#i32 : Std.I32).val : Int) = zeta 17 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge2 :
    liftZ (((-1079900)#i32 : Std.I32).val : Int) = zeta 18 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge3 :
    liftZ ((3585928#i32 : Std.I32).val : Int) = zeta 19 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge4 :
    liftZ (((-549488)#i32 : Std.I32).val : Int) = zeta 20 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge5 :
    liftZ (((-1119584)#i32 : Std.I32).val : Int) = zeta 21 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge6 :
    liftZ ((2619752#i32 : Std.I32).val : Int) = zeta 22 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge7 :
    liftZ (((-2108549)#i32 : Std.I32).val : Int) = zeta 23 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge8 :
    liftZ (((-2118186)#i32 : Std.I32).val : Int) = zeta 24 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge9 :
    liftZ (((-3859737)#i32 : Std.I32).val : Int) = zeta 25 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge10 :
    liftZ (((-1399561)#i32 : Std.I32).val : Int) = zeta 26 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge11 :
    liftZ (((-3277672)#i32 : Std.I32).val : Int) = zeta 27 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge12 :
    liftZ ((1757237#i32 : Std.I32).val : Int) = zeta 28 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge13 :
    liftZ (((-19422)#i32 : Std.I32).val : Int) = zeta 29 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge14 :
    liftZ ((4010497#i32 : Std.I32).val : Int) = zeta 30 := by decide
set_option maxRecDepth 4000 in
private theorem zeta3_bridge15 :
    liftZ ((280005#i32 : Std.I32).val : Int) = zeta 31 := by decide

private theorem zeta3_mag0 : (2725464#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag1 : (1024112#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag2 : ((-1079900)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag3 : (3585928#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag4 : ((-549488)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag5 : ((-1119584)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag6 : (2619752#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag7 : ((-2108549)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag8 : ((-2118186)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag9 : ((-3859737)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag10 : ((-1399561)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag11 : ((-3277672)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag12 : (1757237#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag13 : ((-19422)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag14 : (4010497#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta3_mag15 : (280005#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_3_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 16 * 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_3 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 3
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 16 * 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_3
  have hstep : 1 ≤ (1#usize : Std.Usize).val := by scalar_tac
  have hbnd0 : (0#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd1 : (2#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd2 : (4#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd3 : (6#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd4 : (8#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd5 : (10#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd6 : (12#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd7 : (14#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd8 : (16#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd9 : (18#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd10 : (20#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd11 : (22#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd12 : (24#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd13 : (26#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd14 : (28#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have hbnd15 : (30#usize : Std.Usize).val + 2 * (1#usize : Std.Usize).val ≤ 32 := by scalar_tac
  have e24 : (2 : Int) ^ 24 = 16777216 := by norm_num
  have e31 : (2 : Int) ^ 31 = 2147483648 := by norm_num
  have hB0 : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by omega
  obtain ⟨r1, hr1_eq, h0butter, h0unch, h0bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 0#usize 1#usize 2725464#i32 re B zeta3_mag0 hB0 hstep hbnd0 hin)
  have hB1raw : ((B + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by push_cast; omega
  generalize hB1def : B + 2 ^ 24 = B1 at h0bd hB1raw
  obtain ⟨r2, hr2_eq, h1butter, h1unch, h1bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 2#usize 1#usize 1024112#i32 r1 B1 zeta3_mag1 hB1raw hstep hbnd1 h0bd)
  have hB2raw : ((B1 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    push_cast; omega
  generalize hB2def : B1 + 2 ^ 24 = B2 at h1bd hB2raw
  obtain ⟨r3, hr3_eq, h2butter, h2unch, h2bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 4#usize 1#usize (-1079900)#i32 r2 B2 zeta3_mag2 hB2raw hstep hbnd2 h1bd)
  have hB3raw : ((B2 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    push_cast; omega
  generalize hB3def : B2 + 2 ^ 24 = B3 at h2bd hB3raw
  obtain ⟨r4, hr4_eq, h3butter, h3unch, h3bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 6#usize 1#usize 3585928#i32 r3 B3 zeta3_mag3 hB3raw hstep hbnd3 h2bd)
  have hB4raw : ((B3 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    push_cast; omega
  generalize hB4def : B3 + 2 ^ 24 = B4 at h3bd hB4raw
  obtain ⟨r5, hr5_eq, h4butter, h4unch, h4bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 8#usize 1#usize (-549488)#i32 r4 B4 zeta3_mag4 hB4raw hstep hbnd4 h3bd)
  have hB5raw : ((B4 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    push_cast; omega
  generalize hB5def : B4 + 2 ^ 24 = B5 at h4bd hB5raw
  obtain ⟨r6, hr6_eq, h5butter, h5unch, h5bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 10#usize 1#usize (-1119584)#i32 r5 B5 zeta3_mag5 hB5raw hstep hbnd5 h4bd)
  have hB6raw : ((B5 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    push_cast; omega
  generalize hB6def : B5 + 2 ^ 24 = B6 at h5bd hB6raw
  obtain ⟨r7, hr7_eq, h6butter, h6unch, h6bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 12#usize 1#usize 2619752#i32 r6 B6 zeta3_mag6 hB6raw hstep hbnd6 h5bd)
  have hB7raw : ((B6 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    push_cast; omega
  generalize hB7def : B6 + 2 ^ 24 = B7 at h6bd hB7raw
  obtain ⟨r8, hr8_eq, h7butter, h7unch, h7bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 14#usize 1#usize (-2108549)#i32 r7 B7 zeta3_mag7 hB7raw hstep hbnd7 h6bd)
  have hB8raw : ((B7 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    push_cast; omega
  generalize hB8def : B7 + 2 ^ 24 = B8 at h7bd hB8raw
  obtain ⟨r9, hr9_eq, h8butter, h8unch, h8bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 16#usize 1#usize (-2118186)#i32 r8 B8 zeta3_mag8 hB8raw hstep hbnd8 h7bd)
  have hB9raw : ((B8 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    push_cast; omega
  generalize hB9def : B8 + 2 ^ 24 = B9 at h8bd hB9raw
  obtain ⟨r10, hr10_eq, h9butter, h9unch, h9bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 18#usize 1#usize (-3859737)#i32 r9 B9 zeta3_mag9 hB9raw hstep hbnd9 h8bd)
  have hB10raw : ((B9 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    push_cast; omega
  generalize hB10def : B9 + 2 ^ 24 = B10 at h9bd hB10raw
  obtain ⟨r11, hr11_eq, h10butter, h10unch, h10bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 20#usize 1#usize (-1399561)#i32 r10 B10
        zeta3_mag10 hB10raw hstep hbnd10 h9bd)
  have hB11raw : ((B10 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    push_cast; omega
  generalize hB11def : B10 + 2 ^ 24 = B11 at h10bd hB11raw
  obtain ⟨r12, hr12_eq, h11butter, h11unch, h11bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 22#usize 1#usize (-3277672)#i32 r11 B11
        zeta3_mag11 hB11raw hstep hbnd11 h10bd)
  have hB12raw : ((B11 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    push_cast; omega
  generalize hB12def : B11 + 2 ^ 24 = B12 at h11bd hB12raw
  obtain ⟨r13, hr13_eq, h12butter, h12unch, h12bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 24#usize 1#usize 1757237#i32 r12 B12 zeta3_mag12 hB12raw hstep hbnd12 h11bd)
  have hB13raw : ((B12 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    push_cast; omega
  generalize hB13def : B12 + 2 ^ 24 = B13 at h12bd hB13raw
  obtain ⟨r14, hr14_eq, h13butter, h13unch, h13bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 26#usize 1#usize (-19422)#i32 r13 B13 zeta3_mag13 hB13raw hstep hbnd13 h12bd)
  have hB14raw : ((B13 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    have e13 : B13 = B12 + 2 ^ 24 := hB13def.symm
    push_cast; omega
  generalize hB14def : B13 + 2 ^ 24 = B14 at h13bd hB14raw
  obtain ⟨r15, hr15_eq, h14butter, h14unch, h14bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 28#usize 1#usize 4010497#i32 r14 B14 zeta3_mag14 hB14raw hstep hbnd14 h13bd)
  have hB15raw : ((B14 + 2 ^ 24 : Nat) : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1 := by
    have e1 : B1 = B + 2 ^ 24 := hB1def.symm
    have e2 : B2 = B1 + 2 ^ 24 := hB2def.symm
    have e3 : B3 = B2 + 2 ^ 24 := hB3def.symm
    have e4 : B4 = B3 + 2 ^ 24 := hB4def.symm
    have e5 : B5 = B4 + 2 ^ 24 := hB5def.symm
    have e6 : B6 = B5 + 2 ^ 24 := hB6def.symm
    have e7 : B7 = B6 + 2 ^ 24 := hB7def.symm
    have e8 : B8 = B7 + 2 ^ 24 := hB8def.symm
    have e9 : B9 = B8 + 2 ^ 24 := hB9def.symm
    have e10 : B10 = B9 + 2 ^ 24 := hB10def.symm
    have e11 : B11 = B10 + 2 ^ 24 := hB11def.symm
    have e12 : B12 = B11 + 2 ^ 24 := hB12def.symm
    have e13 : B13 = B12 + 2 ^ 24 := hB13def.symm
    have e14 : B14 = B13 + 2 ^ 24 := hB14def.symm
    push_cast; omega
  generalize hB15def : B14 + 2 ^ 24 = B15 at h14bd hB15raw
  obtain ⟨r16, hr16_eq, h15butter, h15unch, h15bd⟩ :=
    triple_exists_ok
      (outer_3_plus_fc 30#usize 1#usize 280005#i32 r15 B15 zeta3_mag15 hB15raw hstep hbnd15 h14bd)
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr9_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr10_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr11_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr12_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr13_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr14_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr15_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr16_eq
  have e1 : (1#usize : Std.Usize).val = 1 := by simp
  have e0 : (0#usize : Std.Usize).val = 0 := by simp
  have e2 : (2#usize : Std.Usize).val = 2 := by simp
  have e4 : (4#usize : Std.Usize).val = 4 := by simp
  have e6 : (6#usize : Std.Usize).val = 6 := by simp
  have e8 : (8#usize : Std.Usize).val = 8 := by simp
  have e10 : (10#usize : Std.Usize).val = 10 := by simp
  have e12 : (12#usize : Std.Usize).val = 12 := by simp
  have e14 : (14#usize : Std.Usize).val = 14 := by simp
  have e16 : (16#usize : Std.Usize).val = 16 := by simp
  have e18 : (18#usize : Std.Usize).val = 18 := by simp
  have e20 : (20#usize : Std.Usize).val = 20 := by simp
  have e22 : (22#usize : Std.Usize).val = 22 := by simp
  have e24 : (24#usize : Std.Usize).val = 24 := by simp
  have e26 : (26#usize : Std.Usize).val = 26 := by simp
  have e28 : (28#usize : Std.Usize).val = 28 := by simp
  have e30 : (30#usize : Std.Usize).val = 30 := by simp
  simp only [e0, e1, e2, e4, e6, e8, e10, e12, e14, e16,
    e18, e20, e22, e24, e26, e28, e30, Nat.zero_add]
    at h0butter h0unch h1butter h1unch
       h2butter h2unch h3butter h3unch
       h4butter h4unch h5butter h5unch
       h6butter h6unch h7butter h7unch
       h8butter h8unch h9butter h9unch h10butter h10unch h11butter h11unch
       h12butter h12unch h13butter h13unch h14butter h14unch h15butter h15unch
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    have hzv0 : liftZ (((2725464#i32 : Std.I32).val : Int)) = zeta 16 := zeta3_bridge0
    have hzv1 : liftZ (((1024112#i32 : Std.I32).val : Int)) = zeta 17 := zeta3_bridge1
    have hzv2 : liftZ ((((-1079900)#i32 : Std.I32).val : Int)) = zeta 18 := zeta3_bridge2
    have hzv3 : liftZ (((3585928#i32 : Std.I32).val : Int)) = zeta 19 := zeta3_bridge3
    have hzv4 : liftZ ((((-549488)#i32 : Std.I32).val : Int)) = zeta 20 := zeta3_bridge4
    have hzv5 : liftZ ((((-1119584)#i32 : Std.I32).val : Int)) = zeta 21 := zeta3_bridge5
    have hzv6 : liftZ (((2619752#i32 : Std.I32).val : Int)) = zeta 22 := zeta3_bridge6
    have hzv7 : liftZ ((((-2108549)#i32 : Std.I32).val : Int)) = zeta 23 := zeta3_bridge7
    have hzv8 : liftZ ((((-2118186)#i32 : Std.I32).val : Int)) = zeta 24 := zeta3_bridge8
    have hzv9 : liftZ ((((-3859737)#i32 : Std.I32).val : Int)) = zeta 25 := zeta3_bridge9
    have hzv10 : liftZ ((((-1399561)#i32 : Std.I32).val : Int)) = zeta 26 := zeta3_bridge10
    have hzv11 : liftZ ((((-3277672)#i32 : Std.I32).val : Int)) = zeta 27 := zeta3_bridge11
    have hzv12 : liftZ (((1757237#i32 : Std.I32).val : Int)) = zeta 28 := zeta3_bridge12
    have hzv13 : liftZ ((((-19422)#i32 : Std.I32).val : Int)) = zeta 29 := zeta3_bridge13
    have hzv14 : liftZ (((4010497#i32 : Std.I32).val : Int)) = zeta 30 := zeta3_bridge14
    have hzv15 : liftZ (((280005#i32 : Std.I32).val : Int)) = zeta 31 := zeta3_bridge15
    by_cases hr0 : i < 16
    · -- Round 0.
      have hround : i / 16 = 0 := by omega
      have hidx : i % 16 = i := by omega
      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.zero_add]
      by_cases hlt : i < 8
      · rw [if_pos hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
        have hmod : (i + 8) % 8 = i % 8 := by omega
        have hidx2 : i + 8 < 256 := by omega
        rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
        obtain ⟨hlow, _⟩ := h0butter (i / 8) (by omega) (by omega)
        rw [h15unch (i / 8) (by omega) (by omega),
            h14unch (i / 8) (by omega) (by omega),
            h13unch (i / 8) (by omega) (by omega),
            h12unch (i / 8) (by omega) (by omega),
            h11unch (i / 8) (by omega) (by omega),
            h10unch (i / 8) (by omega) (by omega),
            h9unch (i / 8) (by omega) (by omega),
            h8unch (i / 8) (by omega) (by omega),
            h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hlow (i % 8) hl]
        rw [hzv0, mul_comm]
      · rw [if_neg hlt]
        have hl : i % 8 < 8 := by omega
        have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
        have hmod : (i - 8) % 8 = i % 8 := by omega
        have hidx2 : i - 8 < 256 := by omega
        rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
        obtain ⟨_, hhigh⟩ := h0butter ((i - 8) / 8) (by omega) (by omega)
        have hhigh' := hhigh (i % 8) hl
        rw [h15unch (i / 8) (by omega) (by omega),
            h14unch (i / 8) (by omega) (by omega),
            h13unch (i / 8) (by omega) (by omega),
            h12unch (i / 8) (by omega) (by omega),
            h11unch (i / 8) (by omega) (by omega),
            h10unch (i / 8) (by omega) (by omega),
            h9unch (i / 8) (by omega) (by omega),
            h8unch (i / 8) (by omega) (by omega),
            h7unch (i / 8) (by omega) (by omega),
            h6unch (i / 8) (by omega) (by omega),
            h5unch (i / 8) (by omega) (by omega),
            h4unch (i / 8) (by omega) (by omega),
            h3unch (i / 8) (by omega) (by omega),
            h2unch (i / 8) (by omega) (by omega),
            h1unch (i / 8) (by omega) (by omega)]
        rw [hdiv, hhigh']
        rw [hzv0, mul_comm]
    · -- Rounds 1+.
      by_cases hr1 : i < 32
      · -- Round 1.
        have hround : i / 16 = 1 := by omega
        have hidx : i % 16 = i - 16 := by omega
        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
        by_cases hlt : i - 16 < 8
        · rw [if_pos hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
          have hmod : (i + 8) % 8 = i % 8 := by omega
          have hidx2 : i + 8 < 256 := by omega
          rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
          obtain ⟨hlow, _⟩ := h1butter (i / 8) (by omega) (by omega)
          rw [h15unch (i / 8) (by omega) (by omega),
              h14unch (i / 8) (by omega) (by omega),
              h13unch (i / 8) (by omega) (by omega),
              h12unch (i / 8) (by omega) (by omega),
              h11unch (i / 8) (by omega) (by omega),
              h10unch (i / 8) (by omega) (by omega),
              h9unch (i / 8) (by omega) (by omega),
              h8unch (i / 8) (by omega) (by omega),
              h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hlow (i % 8) hl]
          rw [h0unch (i / 8) (by omega) (by omega), h0unch (i / 8 + 1) (by omega) (by omega)]
          rw [hzv1, mul_comm]
        · rw [if_neg hlt]
          have hl : i % 8 < 8 := by omega
          have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
          have hmod : (i - 8) % 8 = i % 8 := by omega
          have hidx2 : i - 8 < 256 := by omega
          rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
          obtain ⟨_, hhigh⟩ := h1butter ((i - 8) / 8) (by omega) (by omega)
          have hhigh' := hhigh (i % 8) hl
          rw [h15unch (i / 8) (by omega) (by omega),
              h14unch (i / 8) (by omega) (by omega),
              h13unch (i / 8) (by omega) (by omega),
              h12unch (i / 8) (by omega) (by omega),
              h11unch (i / 8) (by omega) (by omega),
              h10unch (i / 8) (by omega) (by omega),
              h9unch (i / 8) (by omega) (by omega),
              h8unch (i / 8) (by omega) (by omega),
              h7unch (i / 8) (by omega) (by omega),
              h6unch (i / 8) (by omega) (by omega),
              h5unch (i / 8) (by omega) (by omega),
              h4unch (i / 8) (by omega) (by omega),
              h3unch (i / 8) (by omega) (by omega),
              h2unch (i / 8) (by omega) (by omega)]
          rw [hdiv, hhigh']
          rw [h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
              h0unch ((i - 8) / 8) (by omega) (by omega)]
          rw [hzv1, mul_comm]
      · -- Rounds 2+.
        by_cases hr2 : i < 48
        · -- Round 2.
          have hround : i / 16 = 2 := by omega
          have hidx : i % 16 = i - 32 := by omega
          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv, hround, hidx, Nat.reduceAdd]
          by_cases hlt : i - 32 < 8
          · rw [if_pos hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
            have hmod : (i + 8) % 8 = i % 8 := by omega
            have hidx2 : i + 8 < 256 := by omega
            rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
            obtain ⟨hlow, _⟩ := h2butter (i / 8) (by omega) (by omega)
            rw [h15unch (i / 8) (by omega) (by omega),
                h14unch (i / 8) (by omega) (by omega),
                h13unch (i / 8) (by omega) (by omega),
                h12unch (i / 8) (by omega) (by omega),
                h11unch (i / 8) (by omega) (by omega),
                h10unch (i / 8) (by omega) (by omega),
                h9unch (i / 8) (by omega) (by omega),
                h8unch (i / 8) (by omega) (by omega),
                h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hlow (i % 8) hl]
            rw [h1unch (i / 8) (by omega) (by omega),
                h0unch (i / 8) (by omega) (by omega),
                h1unch (i / 8 + 1) (by omega) (by omega),
                h0unch (i / 8 + 1) (by omega) (by omega)]
            rw [hzv2, mul_comm]
          · rw [if_neg hlt]
            have hl : i % 8 < 8 := by omega
            have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
            have hmod : (i - 8) % 8 = i % 8 := by omega
            have hidx2 : i - 8 < 256 := by omega
            rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
            obtain ⟨_, hhigh⟩ := h2butter ((i - 8) / 8) (by omega) (by omega)
            have hhigh' := hhigh (i % 8) hl
            rw [h15unch (i / 8) (by omega) (by omega),
                h14unch (i / 8) (by omega) (by omega),
                h13unch (i / 8) (by omega) (by omega),
                h12unch (i / 8) (by omega) (by omega),
                h11unch (i / 8) (by omega) (by omega),
                h10unch (i / 8) (by omega) (by omega),
                h9unch (i / 8) (by omega) (by omega),
                h8unch (i / 8) (by omega) (by omega),
                h7unch (i / 8) (by omega) (by omega),
                h6unch (i / 8) (by omega) (by omega),
                h5unch (i / 8) (by omega) (by omega),
                h4unch (i / 8) (by omega) (by omega),
                h3unch (i / 8) (by omega) (by omega)]
            rw [hdiv, hhigh']
            rw [h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                h1unch ((i - 8) / 8) (by omega) (by omega),
                h0unch ((i - 8) / 8) (by omega) (by omega)]
            rw [hzv2, mul_comm]
        · -- Rounds 3+.
          by_cases hr3 : i < 64
          · -- Round 3.
            have hround : i / 16 = 3 := by omega
            have hidx : i % 16 = i - 48 := by omega
            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
              hround, hidx, Nat.reduceAdd]
            by_cases hlt : i - 48 < 8
            · rw [if_pos hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
              have hmod : (i + 8) % 8 = i % 8 := by omega
              have hidx2 : i + 8 < 256 := by omega
              rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
              obtain ⟨hlow, _⟩ := h3butter (i / 8) (by omega) (by omega)
              rw [h15unch (i / 8) (by omega) (by omega),
                  h14unch (i / 8) (by omega) (by omega),
                  h13unch (i / 8) (by omega) (by omega),
                  h12unch (i / 8) (by omega) (by omega),
                  h11unch (i / 8) (by omega) (by omega),
                  h10unch (i / 8) (by omega) (by omega),
                  h9unch (i / 8) (by omega) (by omega),
                  h8unch (i / 8) (by omega) (by omega),
                  h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hlow (i % 8) hl]
              rw [h2unch (i / 8) (by omega) (by omega),
                  h1unch (i / 8) (by omega) (by omega),
                  h0unch (i / 8) (by omega) (by omega),
                  h2unch (i / 8 + 1) (by omega) (by omega),
                  h1unch (i / 8 + 1) (by omega) (by omega),
                  h0unch (i / 8 + 1) (by omega) (by omega)]
              rw [hzv3, mul_comm]
            · rw [if_neg hlt]
              have hl : i % 8 < 8 := by omega
              have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
              have hmod : (i - 8) % 8 = i % 8 := by omega
              have hidx2 : i - 8 < 256 := by omega
              rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
              obtain ⟨_, hhigh⟩ := h3butter ((i - 8) / 8) (by omega) (by omega)
              have hhigh' := hhigh (i % 8) hl
              rw [h15unch (i / 8) (by omega) (by omega),
                  h14unch (i / 8) (by omega) (by omega),
                  h13unch (i / 8) (by omega) (by omega),
                  h12unch (i / 8) (by omega) (by omega),
                  h11unch (i / 8) (by omega) (by omega),
                  h10unch (i / 8) (by omega) (by omega),
                  h9unch (i / 8) (by omega) (by omega),
                  h8unch (i / 8) (by omega) (by omega),
                  h7unch (i / 8) (by omega) (by omega),
                  h6unch (i / 8) (by omega) (by omega),
                  h5unch (i / 8) (by omega) (by omega),
                  h4unch (i / 8) (by omega) (by omega)]
              rw [hdiv, hhigh']
              rw [h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                  h2unch ((i - 8) / 8) (by omega) (by omega),
                  h1unch ((i - 8) / 8) (by omega) (by omega),
                  h0unch ((i - 8) / 8) (by omega) (by omega)]
              rw [hzv3, mul_comm]
          · -- Rounds 4+.
            by_cases hr4 : i < 80
            · -- Round 4.
              have hround : i / 16 = 4 := by omega
              have hidx : i % 16 = i - 64 := by omega
              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                hround, hidx, Nat.reduceAdd]
              by_cases hlt : i - 64 < 8
              · rw [if_pos hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                have hmod : (i + 8) % 8 = i % 8 := by omega
                have hidx2 : i + 8 < 256 := by omega
                rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                obtain ⟨hlow, _⟩ := h4butter (i / 8) (by omega) (by omega)
                rw [h15unch (i / 8) (by omega) (by omega),
                    h14unch (i / 8) (by omega) (by omega),
                    h13unch (i / 8) (by omega) (by omega),
                    h12unch (i / 8) (by omega) (by omega),
                    h11unch (i / 8) (by omega) (by omega),
                    h10unch (i / 8) (by omega) (by omega),
                    h9unch (i / 8) (by omega) (by omega),
                    h8unch (i / 8) (by omega) (by omega),
                    h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hlow (i % 8) hl]
                rw [h3unch (i / 8) (by omega) (by omega),
                    h2unch (i / 8) (by omega) (by omega),
                    h1unch (i / 8) (by omega) (by omega),
                    h0unch (i / 8) (by omega) (by omega),
                    h3unch (i / 8 + 1) (by omega) (by omega),
                    h2unch (i / 8 + 1) (by omega) (by omega),
                    h1unch (i / 8 + 1) (by omega) (by omega),
                    h0unch (i / 8 + 1) (by omega) (by omega)]
                rw [hzv4, mul_comm]
              · rw [if_neg hlt]
                have hl : i % 8 < 8 := by omega
                have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                have hmod : (i - 8) % 8 = i % 8 := by omega
                have hidx2 : i - 8 < 256 := by omega
                rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                obtain ⟨_, hhigh⟩ := h4butter ((i - 8) / 8) (by omega) (by omega)
                have hhigh' := hhigh (i % 8) hl
                rw [h15unch (i / 8) (by omega) (by omega),
                    h14unch (i / 8) (by omega) (by omega),
                    h13unch (i / 8) (by omega) (by omega),
                    h12unch (i / 8) (by omega) (by omega),
                    h11unch (i / 8) (by omega) (by omega),
                    h10unch (i / 8) (by omega) (by omega),
                    h9unch (i / 8) (by omega) (by omega),
                    h8unch (i / 8) (by omega) (by omega),
                    h7unch (i / 8) (by omega) (by omega),
                    h6unch (i / 8) (by omega) (by omega),
                    h5unch (i / 8) (by omega) (by omega)]
                rw [hdiv, hhigh']
                rw [h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                    h3unch ((i - 8) / 8) (by omega) (by omega),
                    h2unch ((i - 8) / 8) (by omega) (by omega),
                    h1unch ((i - 8) / 8) (by omega) (by omega),
                    h0unch ((i - 8) / 8) (by omega) (by omega)]
                rw [hzv4, mul_comm]
            · -- Rounds 5+.
              by_cases hr5 : i < 96
              · -- Round 5.
                have hround : i / 16 = 5 := by omega
                have hidx : i % 16 = i - 80 := by omega
                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                  hround, hidx, Nat.reduceAdd]
                by_cases hlt : i - 80 < 8
                · rw [if_pos hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                  have hmod : (i + 8) % 8 = i % 8 := by omega
                  have hidx2 : i + 8 < 256 := by omega
                  rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                  obtain ⟨hlow, _⟩ := h5butter (i / 8) (by omega) (by omega)
                  rw [h15unch (i / 8) (by omega) (by omega),
                      h14unch (i / 8) (by omega) (by omega),
                      h13unch (i / 8) (by omega) (by omega),
                      h12unch (i / 8) (by omega) (by omega),
                      h11unch (i / 8) (by omega) (by omega),
                      h10unch (i / 8) (by omega) (by omega),
                      h9unch (i / 8) (by omega) (by omega),
                      h8unch (i / 8) (by omega) (by omega),
                      h7unch (i / 8) (by omega) (by omega),
                      h6unch (i / 8) (by omega) (by omega)]
                  rw [hlow (i % 8) hl]
                  rw [h4unch (i / 8) (by omega) (by omega),
                      h3unch (i / 8) (by omega) (by omega),
                      h2unch (i / 8) (by omega) (by omega),
                      h1unch (i / 8) (by omega) (by omega),
                      h0unch (i / 8) (by omega) (by omega),
                      h4unch (i / 8 + 1) (by omega) (by omega),
                      h3unch (i / 8 + 1) (by omega) (by omega),
                      h2unch (i / 8 + 1) (by omega) (by omega),
                      h1unch (i / 8 + 1) (by omega) (by omega),
                      h0unch (i / 8 + 1) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
                · rw [if_neg hlt]
                  have hl : i % 8 < 8 := by omega
                  have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                  have hmod : (i - 8) % 8 = i % 8 := by omega
                  have hidx2 : i - 8 < 256 := by omega
                  rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                  obtain ⟨_, hhigh⟩ := h5butter ((i - 8) / 8) (by omega) (by omega)
                  have hhigh' := hhigh (i % 8) hl
                  rw [h15unch (i / 8) (by omega) (by omega),
                      h14unch (i / 8) (by omega) (by omega),
                      h13unch (i / 8) (by omega) (by omega),
                      h12unch (i / 8) (by omega) (by omega),
                      h11unch (i / 8) (by omega) (by omega),
                      h10unch (i / 8) (by omega) (by omega),
                      h9unch (i / 8) (by omega) (by omega),
                      h8unch (i / 8) (by omega) (by omega),
                      h7unch (i / 8) (by omega) (by omega),
                      h6unch (i / 8) (by omega) (by omega)]
                  rw [hdiv, hhigh']
                  rw [h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                      h4unch ((i - 8) / 8) (by omega) (by omega),
                      h3unch ((i - 8) / 8) (by omega) (by omega),
                      h2unch ((i - 8) / 8) (by omega) (by omega),
                      h1unch ((i - 8) / 8) (by omega) (by omega),
                      h0unch ((i - 8) / 8) (by omega) (by omega)]
                  rw [hzv5, mul_comm]
              · -- Rounds 6+.
                by_cases hr6 : i < 112
                · -- Round 6.
                  have hround : i / 16 = 6 := by omega
                  have hidx : i % 16 = i - 96 := by omega
                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                    hround, hidx, Nat.reduceAdd]
                  by_cases hlt : i - 96 < 8
                  · rw [if_pos hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                    have hmod : (i + 8) % 8 = i % 8 := by omega
                    have hidx2 : i + 8 < 256 := by omega
                    rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                    obtain ⟨hlow, _⟩ := h6butter (i / 8) (by omega) (by omega)
                    rw [h15unch (i / 8) (by omega) (by omega),
                        h14unch (i / 8) (by omega) (by omega),
                        h13unch (i / 8) (by omega) (by omega),
                        h12unch (i / 8) (by omega) (by omega),
                        h11unch (i / 8) (by omega) (by omega),
                        h10unch (i / 8) (by omega) (by omega),
                        h9unch (i / 8) (by omega) (by omega),
                        h8unch (i / 8) (by omega) (by omega),
                        h7unch (i / 8) (by omega) (by omega)]
                    rw [hlow (i % 8) hl]
                    rw [h5unch (i / 8) (by omega) (by omega),
                        h4unch (i / 8) (by omega) (by omega),
                        h3unch (i / 8) (by omega) (by omega),
                        h2unch (i / 8) (by omega) (by omega),
                        h1unch (i / 8) (by omega) (by omega),
                        h0unch (i / 8) (by omega) (by omega),
                        h5unch (i / 8 + 1) (by omega) (by omega),
                        h4unch (i / 8 + 1) (by omega) (by omega),
                        h3unch (i / 8 + 1) (by omega) (by omega),
                        h2unch (i / 8 + 1) (by omega) (by omega),
                        h1unch (i / 8 + 1) (by omega) (by omega),
                        h0unch (i / 8 + 1) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                  · rw [if_neg hlt]
                    have hl : i % 8 < 8 := by omega
                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                    have hmod : (i - 8) % 8 = i % 8 := by omega
                    have hidx2 : i - 8 < 256 := by omega
                    rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                    obtain ⟨_, hhigh⟩ := h6butter ((i - 8) / 8) (by omega) (by omega)
                    have hhigh' := hhigh (i % 8) hl
                    rw [h15unch (i / 8) (by omega) (by omega),
                        h14unch (i / 8) (by omega) (by omega),
                        h13unch (i / 8) (by omega) (by omega),
                        h12unch (i / 8) (by omega) (by omega),
                        h11unch (i / 8) (by omega) (by omega),
                        h10unch (i / 8) (by omega) (by omega),
                        h9unch (i / 8) (by omega) (by omega),
                        h8unch (i / 8) (by omega) (by omega),
                        h7unch (i / 8) (by omega) (by omega)]
                    rw [hdiv, hhigh']
                    rw [h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                        h5unch ((i - 8) / 8) (by omega) (by omega),
                        h4unch ((i - 8) / 8) (by omega) (by omega),
                        h3unch ((i - 8) / 8) (by omega) (by omega),
                        h2unch ((i - 8) / 8) (by omega) (by omega),
                        h1unch ((i - 8) / 8) (by omega) (by omega),
                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                    rw [hzv6, mul_comm]
                · -- Rounds 7+.
                  by_cases hr7 : i < 128
                  · -- Round 7.
                    have hround : i / 16 = 7 := by omega
                    have hidx : i % 16 = i - 112 := by omega
                    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                      hround, hidx, Nat.reduceAdd]
                    by_cases hlt : i - 112 < 8
                    · rw [if_pos hlt]
                      have hl : i % 8 < 8 := by omega
                      have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                      have hmod : (i + 8) % 8 = i % 8 := by omega
                      have hidx2 : i + 8 < 256 := by omega
                      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 8) hidx2, hdiv, hmod]
                      obtain ⟨hlow, _⟩ := h7butter (i / 8) (by omega) (by omega)
                      rw [h15unch (i / 8) (by omega) (by omega),
                          h14unch (i / 8) (by omega) (by omega),
                          h13unch (i / 8) (by omega) (by omega),
                          h12unch (i / 8) (by omega) (by omega),
                          h11unch (i / 8) (by omega) (by omega),
                          h10unch (i / 8) (by omega) (by omega),
                          h9unch (i / 8) (by omega) (by omega),
                          h8unch (i / 8) (by omega) (by omega)]
                      rw [hlow (i % 8) hl]
                      rw [h6unch (i / 8) (by omega) (by omega),
                          h5unch (i / 8) (by omega) (by omega),
                          h4unch (i / 8) (by omega) (by omega),
                          h3unch (i / 8) (by omega) (by omega),
                          h2unch (i / 8) (by omega) (by omega),
                          h1unch (i / 8) (by omega) (by omega),
                          h0unch (i / 8) (by omega) (by omega),
                          h6unch (i / 8 + 1) (by omega) (by omega),
                          h5unch (i / 8 + 1) (by omega) (by omega),
                          h4unch (i / 8 + 1) (by omega) (by omega),
                          h3unch (i / 8 + 1) (by omega) (by omega),
                          h2unch (i / 8 + 1) (by omega) (by omega),
                          h1unch (i / 8 + 1) (by omega) (by omega),
                          h0unch (i / 8 + 1) (by omega) (by omega)]
                      rw [hzv7, mul_comm]
                    · rw [if_neg hlt]
                      have hl : i % 8 < 8 := by omega
                      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                      have hmod : (i - 8) % 8 = i % 8 := by omega
                      have hidx2 : i - 8 < 256 := by omega
                      rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                      obtain ⟨_, hhigh⟩ := h7butter ((i - 8) / 8) (by omega) (by omega)
                      have hhigh' := hhigh (i % 8) hl
                      rw [h15unch (i / 8) (by omega) (by omega),
                          h14unch (i / 8) (by omega) (by omega),
                          h13unch (i / 8) (by omega) (by omega),
                          h12unch (i / 8) (by omega) (by omega),
                          h11unch (i / 8) (by omega) (by omega),
                          h10unch (i / 8) (by omega) (by omega),
                          h9unch (i / 8) (by omega) (by omega),
                          h8unch (i / 8) (by omega) (by omega)]
                      rw [hdiv, hhigh']
                      rw [h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                          h6unch ((i - 8) / 8) (by omega) (by omega),
                          h5unch ((i - 8) / 8) (by omega) (by omega),
                          h4unch ((i - 8) / 8) (by omega) (by omega),
                          h3unch ((i - 8) / 8) (by omega) (by omega),
                          h2unch ((i - 8) / 8) (by omega) (by omega),
                          h1unch ((i - 8) / 8) (by omega) (by omega),
                          h0unch ((i - 8) / 8) (by omega) (by omega)]
                      rw [hzv7, mul_comm]
                  · -- Rounds 8+.
                    by_cases hr8 : i < 144
                    · -- Round 8.
                      have hround : i / 16 = 8 := by omega
                      have hidx : i % 16 = i - 128 := by omega
                      simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                        hround, hidx, Nat.reduceAdd]
                      by_cases hlt : i - 128 < 8
                      · rw [if_pos hlt]
                        have hl : i % 8 < 8 := by omega
                        have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                        have hmod : (i + 8) % 8 = i % 8 := by omega
                        have hidx2 : i + 8 < 256 := by omega
                        rw [Pure.build_getElem _ i hi,
                            Pure.build_getElem _ (i + 8) hidx2,
                            hdiv,
                            hmod]
                        obtain ⟨hlow, _⟩ := h8butter (i / 8) (by omega) (by omega)
                        rw [h15unch (i / 8) (by omega) (by omega),
                            h14unch (i / 8) (by omega) (by omega),
                            h13unch (i / 8) (by omega) (by omega),
                            h12unch (i / 8) (by omega) (by omega),
                            h11unch (i / 8) (by omega) (by omega),
                            h10unch (i / 8) (by omega) (by omega),
                            h9unch (i / 8) (by omega) (by omega)]
                        rw [hlow (i % 8) hl]
                        rw [h7unch (i / 8) (by omega) (by omega),
                            h6unch (i / 8) (by omega) (by omega),
                            h5unch (i / 8) (by omega) (by omega),
                            h4unch (i / 8) (by omega) (by omega),
                            h3unch (i / 8) (by omega) (by omega),
                            h2unch (i / 8) (by omega) (by omega),
                            h1unch (i / 8) (by omega) (by omega),
                            h0unch (i / 8) (by omega) (by omega),
                            h7unch (i / 8 + 1) (by omega) (by omega),
                            h6unch (i / 8 + 1) (by omega) (by omega),
                            h5unch (i / 8 + 1) (by omega) (by omega),
                            h4unch (i / 8 + 1) (by omega) (by omega),
                            h3unch (i / 8 + 1) (by omega) (by omega),
                            h2unch (i / 8 + 1) (by omega) (by omega),
                            h1unch (i / 8 + 1) (by omega) (by omega),
                            h0unch (i / 8 + 1) (by omega) (by omega)]
                        rw [hzv8, mul_comm]
                      · rw [if_neg hlt]
                        have hl : i % 8 < 8 := by omega
                        have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                        have hmod : (i - 8) % 8 = i % 8 := by omega
                        have hidx2 : i - 8 < 256 := by omega
                        rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                        obtain ⟨_, hhigh⟩ := h8butter ((i - 8) / 8) (by omega) (by omega)
                        have hhigh' := hhigh (i % 8) hl
                        rw [h15unch (i / 8) (by omega) (by omega),
                            h14unch (i / 8) (by omega) (by omega),
                            h13unch (i / 8) (by omega) (by omega),
                            h12unch (i / 8) (by omega) (by omega),
                            h11unch (i / 8) (by omega) (by omega),
                            h10unch (i / 8) (by omega) (by omega),
                            h9unch (i / 8) (by omega) (by omega)]
                        rw [hdiv, hhigh']
                        rw [h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                            h7unch ((i - 8) / 8) (by omega) (by omega),
                            h6unch ((i - 8) / 8) (by omega) (by omega),
                            h5unch ((i - 8) / 8) (by omega) (by omega),
                            h4unch ((i - 8) / 8) (by omega) (by omega),
                            h3unch ((i - 8) / 8) (by omega) (by omega),
                            h2unch ((i - 8) / 8) (by omega) (by omega),
                            h1unch ((i - 8) / 8) (by omega) (by omega),
                            h0unch ((i - 8) / 8) (by omega) (by omega)]
                        rw [hzv8, mul_comm]
                    · -- Rounds 9+.
                      by_cases hr9 : i < 160
                      · -- Round 9.
                        have hround : i / 16 = 9 := by omega
                        have hidx : i % 16 = i - 144 := by omega
                        simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                          hround, hidx, Nat.reduceAdd]
                        by_cases hlt : i - 144 < 8
                        · rw [if_pos hlt]
                          have hl : i % 8 < 8 := by omega
                          have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                          have hmod : (i + 8) % 8 = i % 8 := by omega
                          have hidx2 : i + 8 < 256 := by omega
                          rw [Pure.build_getElem _ i hi,
                              Pure.build_getElem _ (i + 8) hidx2,
                              hdiv,
                              hmod]
                          obtain ⟨hlow, _⟩ := h9butter (i / 8) (by omega) (by omega)
                          rw [h15unch (i / 8) (by omega) (by omega),
                              h14unch (i / 8) (by omega) (by omega),
                              h13unch (i / 8) (by omega) (by omega),
                              h12unch (i / 8) (by omega) (by omega),
                              h11unch (i / 8) (by omega) (by omega),
                              h10unch (i / 8) (by omega) (by omega)]
                          rw [hlow (i % 8) hl]
                          rw [h8unch (i / 8) (by omega) (by omega),
                              h7unch (i / 8) (by omega) (by omega),
                              h6unch (i / 8) (by omega) (by omega),
                              h5unch (i / 8) (by omega) (by omega),
                              h4unch (i / 8) (by omega) (by omega),
                              h3unch (i / 8) (by omega) (by omega),
                              h2unch (i / 8) (by omega) (by omega),
                              h1unch (i / 8) (by omega) (by omega),
                              h0unch (i / 8) (by omega) (by omega),
                              h8unch (i / 8 + 1) (by omega) (by omega),
                              h7unch (i / 8 + 1) (by omega) (by omega),
                              h6unch (i / 8 + 1) (by omega) (by omega),
                              h5unch (i / 8 + 1) (by omega) (by omega),
                              h4unch (i / 8 + 1) (by omega) (by omega),
                              h3unch (i / 8 + 1) (by omega) (by omega),
                              h2unch (i / 8 + 1) (by omega) (by omega),
                              h1unch (i / 8 + 1) (by omega) (by omega),
                              h0unch (i / 8 + 1) (by omega) (by omega)]
                          rw [hzv9, mul_comm]
                        · rw [if_neg hlt]
                          have hl : i % 8 < 8 := by omega
                          have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                          have hmod : (i - 8) % 8 = i % 8 := by omega
                          have hidx2 : i - 8 < 256 := by omega
                          rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                          obtain ⟨_, hhigh⟩ := h9butter ((i - 8) / 8) (by omega) (by omega)
                          have hhigh' := hhigh (i % 8) hl
                          rw [h15unch (i / 8) (by omega) (by omega),
                              h14unch (i / 8) (by omega) (by omega),
                              h13unch (i / 8) (by omega) (by omega),
                              h12unch (i / 8) (by omega) (by omega),
                              h11unch (i / 8) (by omega) (by omega),
                              h10unch (i / 8) (by omega) (by omega)]
                          rw [hdiv, hhigh']
                          rw [h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                              h8unch ((i - 8) / 8) (by omega) (by omega),
                              h7unch ((i - 8) / 8) (by omega) (by omega),
                              h6unch ((i - 8) / 8) (by omega) (by omega),
                              h5unch ((i - 8) / 8) (by omega) (by omega),
                              h4unch ((i - 8) / 8) (by omega) (by omega),
                              h3unch ((i - 8) / 8) (by omega) (by omega),
                              h2unch ((i - 8) / 8) (by omega) (by omega),
                              h1unch ((i - 8) / 8) (by omega) (by omega),
                              h0unch ((i - 8) / 8) (by omega) (by omega)]
                          rw [hzv9, mul_comm]
                      · -- Rounds 10+.
                        by_cases hr10 : i < 176
                        · -- Round 10.
                          have hround : i / 16 = 10 := by omega
                          have hidx : i % 16 = i - 160 := by omega
                          simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                            hround, hidx, Nat.reduceAdd]
                          by_cases hlt : i - 160 < 8
                          · rw [if_pos hlt]
                            have hl : i % 8 < 8 := by omega
                            have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                            have hmod : (i + 8) % 8 = i % 8 := by omega
                            have hidx2 : i + 8 < 256 := by omega
                            rw [Pure.build_getElem _ i hi,
                                Pure.build_getElem _ (i + 8) hidx2,
                                hdiv,
                                hmod]
                            obtain ⟨hlow, _⟩ := h10butter (i / 8) (by omega) (by omega)
                            rw [h15unch (i / 8) (by omega) (by omega),
                                h14unch (i / 8) (by omega) (by omega),
                                h13unch (i / 8) (by omega) (by omega),
                                h12unch (i / 8) (by omega) (by omega),
                                h11unch (i / 8) (by omega) (by omega)]
                            rw [hlow (i % 8) hl]
                            rw [h9unch (i / 8) (by omega) (by omega),
                                h8unch (i / 8) (by omega) (by omega),
                                h7unch (i / 8) (by omega) (by omega),
                                h6unch (i / 8) (by omega) (by omega),
                                h5unch (i / 8) (by omega) (by omega),
                                h4unch (i / 8) (by omega) (by omega),
                                h3unch (i / 8) (by omega) (by omega),
                                h2unch (i / 8) (by omega) (by omega),
                                h1unch (i / 8) (by omega) (by omega),
                                h0unch (i / 8) (by omega) (by omega),
                                h9unch (i / 8 + 1) (by omega) (by omega),
                                h8unch (i / 8 + 1) (by omega) (by omega),
                                h7unch (i / 8 + 1) (by omega) (by omega),
                                h6unch (i / 8 + 1) (by omega) (by omega),
                                h5unch (i / 8 + 1) (by omega) (by omega),
                                h4unch (i / 8 + 1) (by omega) (by omega),
                                h3unch (i / 8 + 1) (by omega) (by omega),
                                h2unch (i / 8 + 1) (by omega) (by omega),
                                h1unch (i / 8 + 1) (by omega) (by omega),
                                h0unch (i / 8 + 1) (by omega) (by omega)]
                            rw [hzv10, mul_comm]
                          · rw [if_neg hlt]
                            have hl : i % 8 < 8 := by omega
                            have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                            have hmod : (i - 8) % 8 = i % 8 := by omega
                            have hidx2 : i - 8 < 256 := by omega
                            rw [Pure.build_getElem _ (i - 8) hidx2, Pure.build_getElem _ i hi, hmod]
                            obtain ⟨_, hhigh⟩ := h10butter ((i - 8) / 8) (by omega) (by omega)
                            have hhigh' := hhigh (i % 8) hl
                            rw [h15unch (i / 8) (by omega) (by omega),
                                h14unch (i / 8) (by omega) (by omega),
                                h13unch (i / 8) (by omega) (by omega),
                                h12unch (i / 8) (by omega) (by omega),
                                h11unch (i / 8) (by omega) (by omega)]
                            rw [hdiv, hhigh']
                            rw [h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                h9unch ((i - 8) / 8) (by omega) (by omega),
                                h8unch ((i - 8) / 8) (by omega) (by omega),
                                h7unch ((i - 8) / 8) (by omega) (by omega),
                                h6unch ((i - 8) / 8) (by omega) (by omega),
                                h5unch ((i - 8) / 8) (by omega) (by omega),
                                h4unch ((i - 8) / 8) (by omega) (by omega),
                                h3unch ((i - 8) / 8) (by omega) (by omega),
                                h2unch ((i - 8) / 8) (by omega) (by omega),
                                h1unch ((i - 8) / 8) (by omega) (by omega),
                                h0unch ((i - 8) / 8) (by omega) (by omega)]
                            rw [hzv10, mul_comm]
                        · -- Rounds 11+.
                          by_cases hr11 : i < 192
                          · -- Round 11.
                            have hround : i / 16 = 11 := by omega
                            have hidx : i % 16 = i - 176 := by omega
                            simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                              hround, hidx, Nat.reduceAdd]
                            by_cases hlt : i - 176 < 8
                            · rw [if_pos hlt]
                              have hl : i % 8 < 8 := by omega
                              have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                              have hmod : (i + 8) % 8 = i % 8 := by omega
                              have hidx2 : i + 8 < 256 := by omega
                              rw [Pure.build_getElem _ i hi,
                                  Pure.build_getElem _ (i + 8) hidx2,
                                  hdiv,
                                  hmod]
                              obtain ⟨hlow, _⟩ := h11butter (i / 8) (by omega) (by omega)
                              rw [h15unch (i / 8) (by omega) (by omega),
                                  h14unch (i / 8) (by omega) (by omega),
                                  h13unch (i / 8) (by omega) (by omega),
                                  h12unch (i / 8) (by omega) (by omega)]
                              rw [hlow (i % 8) hl]
                              rw [h10unch (i / 8) (by omega) (by omega),
                                  h9unch (i / 8) (by omega) (by omega),
                                  h8unch (i / 8) (by omega) (by omega),
                                  h7unch (i / 8) (by omega) (by omega),
                                  h6unch (i / 8) (by omega) (by omega),
                                  h5unch (i / 8) (by omega) (by omega),
                                  h4unch (i / 8) (by omega) (by omega),
                                  h3unch (i / 8) (by omega) (by omega),
                                  h2unch (i / 8) (by omega) (by omega),
                                  h1unch (i / 8) (by omega) (by omega),
                                  h0unch (i / 8) (by omega) (by omega),
                                  h10unch (i / 8 + 1) (by omega) (by omega),
                                  h9unch (i / 8 + 1) (by omega) (by omega),
                                  h8unch (i / 8 + 1) (by omega) (by omega),
                                  h7unch (i / 8 + 1) (by omega) (by omega),
                                  h6unch (i / 8 + 1) (by omega) (by omega),
                                  h5unch (i / 8 + 1) (by omega) (by omega),
                                  h4unch (i / 8 + 1) (by omega) (by omega),
                                  h3unch (i / 8 + 1) (by omega) (by omega),
                                  h2unch (i / 8 + 1) (by omega) (by omega),
                                  h1unch (i / 8 + 1) (by omega) (by omega),
                                  h0unch (i / 8 + 1) (by omega) (by omega)]
                              rw [hzv11, mul_comm]
                            · rw [if_neg hlt]
                              have hl : i % 8 < 8 := by omega
                              have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                              have hmod : (i - 8) % 8 = i % 8 := by omega
                              have hidx2 : i - 8 < 256 := by omega
                              rw [Pure.build_getElem _ (i - 8) hidx2,
                                  Pure.build_getElem _ i hi,
                                  hmod]
                              obtain ⟨_, hhigh⟩ := h11butter ((i - 8) / 8) (by omega) (by omega)
                              have hhigh' := hhigh (i % 8) hl
                              rw [h15unch (i / 8) (by omega) (by omega),
                                  h14unch (i / 8) (by omega) (by omega),
                                  h13unch (i / 8) (by omega) (by omega),
                                  h12unch (i / 8) (by omega) (by omega)]
                              rw [hdiv, hhigh']
                              rw [h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                  h10unch ((i - 8) / 8) (by omega) (by omega),
                                  h9unch ((i - 8) / 8) (by omega) (by omega),
                                  h8unch ((i - 8) / 8) (by omega) (by omega),
                                  h7unch ((i - 8) / 8) (by omega) (by omega),
                                  h6unch ((i - 8) / 8) (by omega) (by omega),
                                  h5unch ((i - 8) / 8) (by omega) (by omega),
                                  h4unch ((i - 8) / 8) (by omega) (by omega),
                                  h3unch ((i - 8) / 8) (by omega) (by omega),
                                  h2unch ((i - 8) / 8) (by omega) (by omega),
                                  h1unch ((i - 8) / 8) (by omega) (by omega),
                                  h0unch ((i - 8) / 8) (by omega) (by omega)]
                              rw [hzv11, mul_comm]
                          · -- Rounds 12+.
                            by_cases hr12 : i < 208
                            · -- Round 12.
                              have hround : i / 16 = 12 := by omega
                              have hidx : i % 16 = i - 192 := by omega
                              simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                hround, hidx, Nat.reduceAdd]
                              by_cases hlt : i - 192 < 8
                              · rw [if_pos hlt]
                                have hl : i % 8 < 8 := by omega
                                have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                have hmod : (i + 8) % 8 = i % 8 := by omega
                                have hidx2 : i + 8 < 256 := by omega
                                rw [Pure.build_getElem _ i hi,
                                    Pure.build_getElem _ (i + 8) hidx2,
                                    hdiv,
                                    hmod]
                                obtain ⟨hlow, _⟩ := h12butter (i / 8) (by omega) (by omega)
                                rw [h15unch (i / 8) (by omega) (by omega),
                                    h14unch (i / 8) (by omega) (by omega),
                                    h13unch (i / 8) (by omega) (by omega)]
                                rw [hlow (i % 8) hl]
                                rw [h11unch (i / 8) (by omega) (by omega),
                                    h10unch (i / 8) (by omega) (by omega),
                                    h9unch (i / 8) (by omega) (by omega),
                                    h8unch (i / 8) (by omega) (by omega),
                                    h7unch (i / 8) (by omega) (by omega),
                                    h6unch (i / 8) (by omega) (by omega),
                                    h5unch (i / 8) (by omega) (by omega),
                                    h4unch (i / 8) (by omega) (by omega),
                                    h3unch (i / 8) (by omega) (by omega),
                                    h2unch (i / 8) (by omega) (by omega),
                                    h1unch (i / 8) (by omega) (by omega),
                                    h0unch (i / 8) (by omega) (by omega),
                                    h11unch (i / 8 + 1) (by omega) (by omega),
                                    h10unch (i / 8 + 1) (by omega) (by omega),
                                    h9unch (i / 8 + 1) (by omega) (by omega),
                                    h8unch (i / 8 + 1) (by omega) (by omega),
                                    h7unch (i / 8 + 1) (by omega) (by omega),
                                    h6unch (i / 8 + 1) (by omega) (by omega),
                                    h5unch (i / 8 + 1) (by omega) (by omega),
                                    h4unch (i / 8 + 1) (by omega) (by omega),
                                    h3unch (i / 8 + 1) (by omega) (by omega),
                                    h2unch (i / 8 + 1) (by omega) (by omega),
                                    h1unch (i / 8 + 1) (by omega) (by omega),
                                    h0unch (i / 8 + 1) (by omega) (by omega)]
                                rw [hzv12, mul_comm]
                              · rw [if_neg hlt]
                                have hl : i % 8 < 8 := by omega
                                have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                have hmod : (i - 8) % 8 = i % 8 := by omega
                                have hidx2 : i - 8 < 256 := by omega
                                rw [Pure.build_getElem _ (i - 8) hidx2,
                                    Pure.build_getElem _ i hi,
                                    hmod]
                                obtain ⟨_, hhigh⟩ := h12butter ((i - 8) / 8) (by omega) (by omega)
                                have hhigh' := hhigh (i % 8) hl
                                rw [h15unch (i / 8) (by omega) (by omega),
                                    h14unch (i / 8) (by omega) (by omega),
                                    h13unch (i / 8) (by omega) (by omega)]
                                rw [hdiv, hhigh']
                                rw [h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                    h11unch ((i - 8) / 8) (by omega) (by omega),
                                    h10unch ((i - 8) / 8) (by omega) (by omega),
                                    h9unch ((i - 8) / 8) (by omega) (by omega),
                                    h8unch ((i - 8) / 8) (by omega) (by omega),
                                    h7unch ((i - 8) / 8) (by omega) (by omega),
                                    h6unch ((i - 8) / 8) (by omega) (by omega),
                                    h5unch ((i - 8) / 8) (by omega) (by omega),
                                    h4unch ((i - 8) / 8) (by omega) (by omega),
                                    h3unch ((i - 8) / 8) (by omega) (by omega),
                                    h2unch ((i - 8) / 8) (by omega) (by omega),
                                    h1unch ((i - 8) / 8) (by omega) (by omega),
                                    h0unch ((i - 8) / 8) (by omega) (by omega)]
                                rw [hzv12, mul_comm]
                            · -- Rounds 13+.
                              by_cases hr13 : i < 224
                              · -- Round 13.
                                have hround : i / 16 = 13 := by omega
                                have hidx : i % 16 = i - 208 := by omega
                                simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                  hround, hidx, Nat.reduceAdd]
                                by_cases hlt : i - 208 < 8
                                · rw [if_pos hlt]
                                  have hl : i % 8 < 8 := by omega
                                  have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                  have hmod : (i + 8) % 8 = i % 8 := by omega
                                  have hidx2 : i + 8 < 256 := by omega
                                  rw [Pure.build_getElem _ i hi,
                                      Pure.build_getElem _ (i + 8) hidx2,
                                      hdiv,
                                      hmod]
                                  obtain ⟨hlow, _⟩ := h13butter (i / 8) (by omega) (by omega)
                                  rw [h15unch (i / 8) (by omega) (by omega),
                                      h14unch (i / 8) (by omega) (by omega)]
                                  rw [hlow (i % 8) hl]
                                  rw [h12unch (i / 8) (by omega) (by omega),
                                      h11unch (i / 8) (by omega) (by omega),
                                      h10unch (i / 8) (by omega) (by omega),
                                      h9unch (i / 8) (by omega) (by omega),
                                      h8unch (i / 8) (by omega) (by omega),
                                      h7unch (i / 8) (by omega) (by omega),
                                      h6unch (i / 8) (by omega) (by omega),
                                      h5unch (i / 8) (by omega) (by omega),
                                      h4unch (i / 8) (by omega) (by omega),
                                      h3unch (i / 8) (by omega) (by omega),
                                      h2unch (i / 8) (by omega) (by omega),
                                      h1unch (i / 8) (by omega) (by omega),
                                      h0unch (i / 8) (by omega) (by omega),
                                      h12unch (i / 8 + 1) (by omega) (by omega),
                                      h11unch (i / 8 + 1) (by omega) (by omega),
                                      h10unch (i / 8 + 1) (by omega) (by omega),
                                      h9unch (i / 8 + 1) (by omega) (by omega),
                                      h8unch (i / 8 + 1) (by omega) (by omega),
                                      h7unch (i / 8 + 1) (by omega) (by omega),
                                      h6unch (i / 8 + 1) (by omega) (by omega),
                                      h5unch (i / 8 + 1) (by omega) (by omega),
                                      h4unch (i / 8 + 1) (by omega) (by omega),
                                      h3unch (i / 8 + 1) (by omega) (by omega),
                                      h2unch (i / 8 + 1) (by omega) (by omega),
                                      h1unch (i / 8 + 1) (by omega) (by omega),
                                      h0unch (i / 8 + 1) (by omega) (by omega)]
                                  rw [hzv13, mul_comm]
                                · rw [if_neg hlt]
                                  have hl : i % 8 < 8 := by omega
                                  have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                  have hmod : (i - 8) % 8 = i % 8 := by omega
                                  have hidx2 : i - 8 < 256 := by omega
                                  rw [Pure.build_getElem _ (i - 8) hidx2,
                                      Pure.build_getElem _ i hi,
                                      hmod]
                                  obtain ⟨_, hhigh⟩ := h13butter ((i - 8) / 8) (by omega) (by omega)
                                  have hhigh' := hhigh (i % 8) hl
                                  rw [h15unch (i / 8) (by omega) (by omega),
                                      h14unch (i / 8) (by omega) (by omega)]
                                  rw [hdiv, hhigh']
                                  rw [h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                      h12unch ((i - 8) / 8) (by omega) (by omega),
                                      h11unch ((i - 8) / 8) (by omega) (by omega),
                                      h10unch ((i - 8) / 8) (by omega) (by omega),
                                      h9unch ((i - 8) / 8) (by omega) (by omega),
                                      h8unch ((i - 8) / 8) (by omega) (by omega),
                                      h7unch ((i - 8) / 8) (by omega) (by omega),
                                      h6unch ((i - 8) / 8) (by omega) (by omega),
                                      h5unch ((i - 8) / 8) (by omega) (by omega),
                                      h4unch ((i - 8) / 8) (by omega) (by omega),
                                      h3unch ((i - 8) / 8) (by omega) (by omega),
                                      h2unch ((i - 8) / 8) (by omega) (by omega),
                                      h1unch ((i - 8) / 8) (by omega) (by omega),
                                      h0unch ((i - 8) / 8) (by omega) (by omega)]
                                  rw [hzv13, mul_comm]
                              · -- Rounds 14+.
                                by_cases hr14 : i < 240
                                · -- Round 14.
                                  have hround : i / 16 = 14 := by omega
                                  have hidx : i % 16 = i - 224 := by omega
                                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                    hround, hidx, Nat.reduceAdd]
                                  by_cases hlt : i - 224 < 8
                                  · rw [if_pos hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                    have hmod : (i + 8) % 8 = i % 8 := by omega
                                    have hidx2 : i + 8 < 256 := by omega
                                    rw [Pure.build_getElem _ i hi,
                                        Pure.build_getElem _ (i + 8) hidx2,
                                        hdiv,
                                        hmod]
                                    obtain ⟨hlow, _⟩ := h14butter (i / 8) (by omega) (by omega)
                                    rw [h15unch (i / 8) (by omega) (by omega)]
                                    rw [hlow (i % 8) hl]
                                    rw [h13unch (i / 8) (by omega) (by omega),
                                        h12unch (i / 8) (by omega) (by omega),
                                        h11unch (i / 8) (by omega) (by omega),
                                        h10unch (i / 8) (by omega) (by omega),
                                        h9unch (i / 8) (by omega) (by omega),
                                        h8unch (i / 8) (by omega) (by omega),
                                        h7unch (i / 8) (by omega) (by omega),
                                        h6unch (i / 8) (by omega) (by omega),
                                        h5unch (i / 8) (by omega) (by omega),
                                        h4unch (i / 8) (by omega) (by omega),
                                        h3unch (i / 8) (by omega) (by omega),
                                        h2unch (i / 8) (by omega) (by omega),
                                        h1unch (i / 8) (by omega) (by omega),
                                        h0unch (i / 8) (by omega) (by omega),
                                        h13unch (i / 8 + 1) (by omega) (by omega),
                                        h12unch (i / 8 + 1) (by omega) (by omega),
                                        h11unch (i / 8 + 1) (by omega) (by omega),
                                        h10unch (i / 8 + 1) (by omega) (by omega),
                                        h9unch (i / 8 + 1) (by omega) (by omega),
                                        h8unch (i / 8 + 1) (by omega) (by omega),
                                        h7unch (i / 8 + 1) (by omega) (by omega),
                                        h6unch (i / 8 + 1) (by omega) (by omega),
                                        h5unch (i / 8 + 1) (by omega) (by omega),
                                        h4unch (i / 8 + 1) (by omega) (by omega),
                                        h3unch (i / 8 + 1) (by omega) (by omega),
                                        h2unch (i / 8 + 1) (by omega) (by omega),
                                        h1unch (i / 8 + 1) (by omega) (by omega),
                                        h0unch (i / 8 + 1) (by omega) (by omega)]
                                    rw [hzv14, mul_comm]
                                  · rw [if_neg hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                    have hmod : (i - 8) % 8 = i % 8 := by omega
                                    have hidx2 : i - 8 < 256 := by omega
                                    rw [Pure.build_getElem _ (i - 8) hidx2,
                                        Pure.build_getElem _ i hi,
                                        hmod]
                                    obtain ⟨_, hhigh⟩ :=
                                      h14butter ((i - 8) / 8) (by omega) (by omega)
                                    have hhigh' := hhigh (i % 8) hl
                                    rw [h15unch (i / 8) (by omega) (by omega)]
                                    rw [hdiv, hhigh']
                                    rw [h13unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h13unch ((i - 8) / 8) (by omega) (by omega),
                                        h12unch ((i - 8) / 8) (by omega) (by omega),
                                        h11unch ((i - 8) / 8) (by omega) (by omega),
                                        h10unch ((i - 8) / 8) (by omega) (by omega),
                                        h9unch ((i - 8) / 8) (by omega) (by omega),
                                        h8unch ((i - 8) / 8) (by omega) (by omega),
                                        h7unch ((i - 8) / 8) (by omega) (by omega),
                                        h6unch ((i - 8) / 8) (by omega) (by omega),
                                        h5unch ((i - 8) / 8) (by omega) (by omega),
                                        h4unch ((i - 8) / 8) (by omega) (by omega),
                                        h3unch ((i - 8) / 8) (by omega) (by omega),
                                        h2unch ((i - 8) / 8) (by omega) (by omega),
                                        h1unch ((i - 8) / 8) (by omega) (by omega),
                                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                                    rw [hzv14, mul_comm]
                                · -- Rounds 15+.
                                  have hround : i / 16 = 15 := by omega
                                  have hidx : i % 16 = i - 240 := by omega
                                  simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv,
                                    hround, hidx, Nat.reduceAdd]
                                  by_cases hlt : i - 240 < 8
                                  · rw [if_pos hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : (i + 8) / 8 = i / 8 + 1 := by omega
                                    have hmod : (i + 8) % 8 = i % 8 := by omega
                                    have hidx2 : i + 8 < 256 := by omega
                                    rw [Pure.build_getElem _ i hi,
                                        Pure.build_getElem _ (i + 8) hidx2,
                                        hdiv,
                                        hmod]
                                    obtain ⟨hlow, _⟩ := h15butter (i / 8) (by omega) (by omega)
                                    rw [hlow (i % 8) hl]
                                    rw [h14unch (i / 8) (by omega) (by omega),
                                        h13unch (i / 8) (by omega) (by omega),
                                        h12unch (i / 8) (by omega) (by omega),
                                        h11unch (i / 8) (by omega) (by omega),
                                        h10unch (i / 8) (by omega) (by omega),
                                        h9unch (i / 8) (by omega) (by omega),
                                        h8unch (i / 8) (by omega) (by omega),
                                        h7unch (i / 8) (by omega) (by omega),
                                        h6unch (i / 8) (by omega) (by omega),
                                        h5unch (i / 8) (by omega) (by omega),
                                        h4unch (i / 8) (by omega) (by omega),
                                        h3unch (i / 8) (by omega) (by omega),
                                        h2unch (i / 8) (by omega) (by omega),
                                        h1unch (i / 8) (by omega) (by omega),
                                        h0unch (i / 8) (by omega) (by omega),
                                        h14unch (i / 8 + 1) (by omega) (by omega),
                                        h13unch (i / 8 + 1) (by omega) (by omega),
                                        h12unch (i / 8 + 1) (by omega) (by omega),
                                        h11unch (i / 8 + 1) (by omega) (by omega),
                                        h10unch (i / 8 + 1) (by omega) (by omega),
                                        h9unch (i / 8 + 1) (by omega) (by omega),
                                        h8unch (i / 8 + 1) (by omega) (by omega),
                                        h7unch (i / 8 + 1) (by omega) (by omega),
                                        h6unch (i / 8 + 1) (by omega) (by omega),
                                        h5unch (i / 8 + 1) (by omega) (by omega),
                                        h4unch (i / 8 + 1) (by omega) (by omega),
                                        h3unch (i / 8 + 1) (by omega) (by omega),
                                        h2unch (i / 8 + 1) (by omega) (by omega),
                                        h1unch (i / 8 + 1) (by omega) (by omega),
                                        h0unch (i / 8 + 1) (by omega) (by omega)]
                                    rw [hzv15, mul_comm]
                                  · rw [if_neg hlt]
                                    have hl : i % 8 < 8 := by omega
                                    have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
                                    have hmod : (i - 8) % 8 = i % 8 := by omega
                                    have hidx2 : i - 8 < 256 := by omega
                                    rw [Pure.build_getElem _ (i - 8) hidx2,
                                        Pure.build_getElem _ i hi,
                                        hmod]
                                    obtain ⟨_, hhigh⟩ :=
                                      h15butter ((i - 8) / 8) (by omega) (by omega)
                                    have hhigh' := hhigh (i % 8) hl
                                    rw [hdiv, hhigh']
                                    rw [h14unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h13unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h12unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h11unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h10unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h9unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h8unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h7unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h6unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h5unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h4unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h3unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h2unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h1unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h0unch ((i - 8) / 8 + 1) (by omega) (by omega),
                                        h14unch ((i - 8) / 8) (by omega) (by omega),
                                        h13unch ((i - 8) / 8) (by omega) (by omega),
                                        h12unch ((i - 8) / 8) (by omega) (by omega),
                                        h11unch ((i - 8) / 8) (by omega) (by omega),
                                        h10unch ((i - 8) / 8) (by omega) (by omega),
                                        h9unch ((i - 8) / 8) (by omega) (by omega),
                                        h8unch ((i - 8) / 8) (by omega) (by omega),
                                        h7unch ((i - 8) / 8) (by omega) (by omega),
                                        h6unch ((i - 8) / 8) (by omega) (by omega),
                                        h5unch ((i - 8) / 8) (by omega) (by omega),
                                        h4unch ((i - 8) / 8) (by omega) (by omega),
                                        h3unch ((i - 8) / 8) (by omega) (by omega),
                                        h2unch ((i - 8) / 8) (by omega) (by omega),
                                        h1unch ((i - 8) / 8) (by omega) (by omega),
                                        h0unch ((i - 8) / 8) (by omega) (by omega)]
                                    rw [hzv15, mul_comm]
  · -- Bound conjunct.
    have heq : B15 + 2 ^ 24 = B + 16 * 2 ^ 24 := by
      rw [← hB15def,
          ← hB14def,
          ← hB13def,
          ← hB12def,
          ← hB11def,
          ← hB10def,
          ← hB9def,
          ← hB8def,
          ← hB7def,
          ← hB6def,
          ← hB5def,
          ← hB4def,
          ← hB3def,
          ← hB2def,
          ← hB1def]
      ring
    intro u hu l hl
    have := h15bd u hu l hl
    rw [heq] at this
    exact this

/-! ## Layer 2 (`len = 4`, `k = 32`, within-unit; 32 `round` calls)

`ntt_at_layer_2` chains 32 `round` calls; round `u` reads unit `u`, applies the
per-unit butterfly `simd_unit_ntt_at_layer_2 _ ZETA_u`, and writes unit `u` back
(touching ONLY unit `u`). Since round `u` is the first/only writer of unit `u`, its
input at unit `u` is the original `re[u]`; the lifted result equals
`ntt_layer (lift_units re) 2` (`len = 4`, `k = 32`, lane split at 4 WITHIN each unit,
zeta `zeta (u + 32)`). Uniform output bound `B + 2^24` (each unit touched once). -/

set_option maxRecDepth 4000 in
private theorem zeta2_bridge0 :
    liftZ ((2706023#i32 : Std.I32).val : Int) = zeta 32 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge1 :
    liftZ ((95776#i32 : Std.I32).val : Int) = zeta 33 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge2 :
    liftZ ((3077325#i32 : Std.I32).val : Int) = zeta 34 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge3 :
    liftZ ((3530437#i32 : Std.I32).val : Int) = zeta 35 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge4 :
    liftZ (((-1661693)#i32 : Std.I32).val : Int) = zeta 36 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge5 :
    liftZ (((-3592148)#i32 : Std.I32).val : Int) = zeta 37 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge6 :
    liftZ (((-2537516)#i32 : Std.I32).val : Int) = zeta 38 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge7 :
    liftZ ((3915439#i32 : Std.I32).val : Int) = zeta 39 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge8 :
    liftZ (((-3861115)#i32 : Std.I32).val : Int) = zeta 40 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge9 :
    liftZ (((-3043716)#i32 : Std.I32).val : Int) = zeta 41 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge10 :
    liftZ ((3574422#i32 : Std.I32).val : Int) = zeta 42 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge11 :
    liftZ (((-2867647)#i32 : Std.I32).val : Int) = zeta 43 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge12 :
    liftZ ((3539968#i32 : Std.I32).val : Int) = zeta 44 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge13 :
    liftZ (((-300467)#i32 : Std.I32).val : Int) = zeta 45 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge14 :
    liftZ ((2348700#i32 : Std.I32).val : Int) = zeta 46 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge15 :
    liftZ (((-539299)#i32 : Std.I32).val : Int) = zeta 47 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge16 :
    liftZ (((-1699267)#i32 : Std.I32).val : Int) = zeta 48 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge17 :
    liftZ (((-1643818)#i32 : Std.I32).val : Int) = zeta 49 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge18 :
    liftZ ((3505694#i32 : Std.I32).val : Int) = zeta 50 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge19 :
    liftZ (((-3821735)#i32 : Std.I32).val : Int) = zeta 51 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge20 :
    liftZ ((3507263#i32 : Std.I32).val : Int) = zeta 52 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge21 :
    liftZ (((-2140649)#i32 : Std.I32).val : Int) = zeta 53 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge22 :
    liftZ (((-1600420)#i32 : Std.I32).val : Int) = zeta 54 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge23 :
    liftZ ((3699596#i32 : Std.I32).val : Int) = zeta 55 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge24 :
    liftZ ((811944#i32 : Std.I32).val : Int) = zeta 56 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge25 :
    liftZ ((531354#i32 : Std.I32).val : Int) = zeta 57 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge26 :
    liftZ ((954230#i32 : Std.I32).val : Int) = zeta 58 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge27 :
    liftZ ((3881043#i32 : Std.I32).val : Int) = zeta 59 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge28 :
    liftZ ((3900724#i32 : Std.I32).val : Int) = zeta 60 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge29 :
    liftZ (((-2556880)#i32 : Std.I32).val : Int) = zeta 61 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge30 :
    liftZ ((2071892#i32 : Std.I32).val : Int) = zeta 62 := by decide
set_option maxRecDepth 4000 in
private theorem zeta2_bridge31 :
    liftZ (((-2797779)#i32 : Std.I32).val : Int) = zeta 63 := by decide

private theorem zeta2_mag0 : (2706023#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag1 : (95776#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag2 : (3077325#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag3 : (3530437#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag4 : ((-1661693)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag5 : ((-3592148)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag6 : ((-2537516)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag7 : (3915439#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag8 : ((-3861115)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag9 : ((-3043716)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag10 : (3574422#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag11 : ((-2867647)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag12 : (3539968#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag13 : ((-300467)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag14 : (2348700#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag15 : ((-539299)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag16 : ((-1699267)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag17 : ((-1643818)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag18 : (3505694#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag19 : ((-3821735)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag20 : (3507263#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag21 : ((-2140649)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag22 : ((-1600420)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag23 : (3699596#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag24 : (811944#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag25 : (531354#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag26 : (954230#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag27 : (3881043#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag28 : (3900724#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag29 : ((-2556880)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag30 : (2071892#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta2_mag31 : ((-2797779)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of layer 2: read unit `k`, apply the per-unit butterfly with `zeta`,
    write unit `k` back (touching only unit `k`). Gives the 8 per-lane lift equations
    on the new unit `k`, the frame `out[u] = re[u]` for `u ≠ k`, and the per-lane
    bound `≤ B + 2^24` on unit `k`. -/
private theorem round2_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta : Std.I32) (B : Nat)
    (hz : zeta.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_2.round re k#usize zeta = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[4]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val + liftZ ((re.val[k]!).values.val[5]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val + liftZ ((re.val[k]!).values.val[6]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = liftZ ((re.val[k]!).values.val[3]!).val + liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val - liftZ ((re.val[k]!).values.val[4]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val - liftZ ((re.val[k]!).values.val[5]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val - liftZ ((re.val[k]!).values.val[6]!).val * liftZ zeta.val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = liftZ ((re.val[k]!).values.val[3]!).val - liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta.val)
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_2.round
  -- (1) index_mut_usize re k = .ok (re[k], re.set k).
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  -- Make `ak := re[k]` OPAQUE so `simp` cannot unfold its `[!]` (`?.getD default`)
  -- form when collapsing the do-block (proven `outer_3_plus` idiom).
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  -- (2) leaf butterfly on unit k = ak.
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_ntt_at_layer_2_fc ak zeta B hz hB hin)
  -- `out[k] = (re.set k c1)[k] = c1`, in the `.val[k]!` form the statement uses.
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · -- `.ok` equation: `ak` opaque ⇒ full `simp` with the `.ok` facts collapses the
    -- bind, pair-`let` projections and leaf call (proven `outer_3_plus` idiom).
    simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · -- Butterfly eqs.
    rw [hset_k]; exact hc1_butter
  · -- Frame: out[u] = re[u] for u ≠ k.
    intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · -- Bound on unit k.
    intro l hl
    rw [hset_k]; exact hc1_bd l hl


set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_2_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_2 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 2
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_2
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    round2_fc re 0 (by decide) (2706023#i32) B (zeta2_mag0) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    round2_fc r1 1 (by decide) (95776#i32) B (zeta2_mag1) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    round2_fc r2 2 (by decide) (3077325#i32) B (zeta2_mag2) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    round2_fc r3 3 (by decide) (3530437#i32) B (zeta2_mag3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    round2_fc r4 4 (by decide) ((-1661693)#i32) B (zeta2_mag4) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    round2_fc r5 5 (by decide) ((-3592148)#i32) B (zeta2_mag5) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    round2_fc r6 6 (by decide) ((-2537516)#i32) B (zeta2_mag6) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    round2_fc r7 7 (by decide) (3915439#i32) B (zeta2_mag7) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    round2_fc r8 8 (by decide) ((-3861115)#i32) B (zeta2_mag8) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    round2_fc r9 9 (by decide) ((-3043716)#i32) B (zeta2_mag9) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    round2_fc r10 10 (by decide) (3574422#i32) B (zeta2_mag10) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    round2_fc r11 11 (by decide) ((-2867647)#i32) B (zeta2_mag11) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    round2_fc r12 12 (by decide) (3539968#i32) B (zeta2_mag12) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    round2_fc r13 13 (by decide) ((-300467)#i32) B (zeta2_mag13) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    round2_fc r14 14 (by decide) (2348700#i32) B (zeta2_mag14) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    round2_fc r15 15 (by decide) ((-539299)#i32) B (zeta2_mag15) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    round2_fc r16 16 (by decide) ((-1699267)#i32) B (zeta2_mag16) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    round2_fc r17 17 (by decide) ((-1643818)#i32) B (zeta2_mag17) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    round2_fc r18 18 (by decide) (3505694#i32) B (zeta2_mag18) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    round2_fc r19 19 (by decide) ((-3821735)#i32) B (zeta2_mag19) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    round2_fc r20 20 (by decide) (3507263#i32) B (zeta2_mag20) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    round2_fc r21 21 (by decide) ((-2140649)#i32) B (zeta2_mag21) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    round2_fc r22 22 (by decide) ((-1600420)#i32) B (zeta2_mag22) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    round2_fc r23 23 (by decide) (3699596#i32) B (zeta2_mag23) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    round2_fc r24 24 (by decide) (811944#i32) B (zeta2_mag24) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    round2_fc r25 25 (by decide) (531354#i32) B (zeta2_mag25) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    round2_fc r26 26 (by decide) (954230#i32) B (zeta2_mag26) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    round2_fc r27 27 (by decide) (3881043#i32) B (zeta2_mag27) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    round2_fc r28 28 (by decide) (3900724#i32) B (zeta2_mag28) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    round2_fc r29 29 (by decide) ((-2556880)#i32) B (zeta2_mag29) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    round2_fc r30 30 (by decide) (2071892#i32) B (zeta2_mag30) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    round2_fc r31 31 (by decide) ((-2797779)#i32) B (zeta2_mag31) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr9_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr10_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr11_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr12_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr13_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr14_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr15_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[0]!).values.val[l]!).val
            + zeta (0 + 32) * liftZ ((re.val[0]!).values.val[l + 4]!).val
         else liftZ ((re.val[0]!).values.val[l - 4]!).val
            - zeta (0 + 32) * liftZ ((re.val[0]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge0, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge0, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge0, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge0, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge0, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge0, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge0, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[1]!).values.val[l]!).val
            + zeta (1 + 32) * liftZ ((re.val[1]!).values.val[l + 4]!).val
         else liftZ ((re.val[1]!).values.val[l - 4]!).val
            - zeta (1 + 32) * liftZ ((re.val[1]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge1, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge1, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge1, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge1, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge1, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge1, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge1, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge1, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[2]!).values.val[l]!).val
            + zeta (2 + 32) * liftZ ((re.val[2]!).values.val[l + 4]!).val
         else liftZ ((re.val[2]!).values.val[l - 4]!).val
            - zeta (2 + 32) * liftZ ((re.val[2]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge2, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge2, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge2, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge2, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge2, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge2, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge2, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[3]!).values.val[l]!).val
            + zeta (3 + 32) * liftZ ((re.val[3]!).values.val[l + 4]!).val
         else liftZ ((re.val[3]!).values.val[l - 4]!).val
            - zeta (3 + 32) * liftZ ((re.val[3]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge3, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge3, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge3, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge3, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge3, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge3, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[4]!).values.val[l]!).val
            + zeta (4 + 32) * liftZ ((re.val[4]!).values.val[l + 4]!).val
         else liftZ ((re.val[4]!).values.val[l - 4]!).val
            - zeta (4 + 32) * liftZ ((re.val[4]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge4, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge4, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge4, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge4, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge4, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge4, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge4, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge4, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[5]!).values.val[l]!).val
            + zeta (5 + 32) * liftZ ((re.val[5]!).values.val[l + 4]!).val
         else liftZ ((re.val[5]!).values.val[l - 4]!).val
            - zeta (5 + 32) * liftZ ((re.val[5]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge5, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge5, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge5, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge5, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge5, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge5, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge5, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge5, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[6]!).values.val[l]!).val
            + zeta (6 + 32) * liftZ ((re.val[6]!).values.val[l + 4]!).val
         else liftZ ((re.val[6]!).values.val[l - 4]!).val
            - zeta (6 + 32) * liftZ ((re.val[6]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge6, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge6, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge6, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge6, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge6, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge6, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge6, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge6, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[7]!).values.val[l]!).val
            + zeta (7 + 32) * liftZ ((re.val[7]!).values.val[l + 4]!).val
         else liftZ ((re.val[7]!).values.val[l - 4]!).val
            - zeta (7 + 32) * liftZ ((re.val[7]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge7, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge7, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge7, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge7, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge7, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge7, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge7, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge7, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[8]!).values.val[l]!).val
            + zeta (8 + 32) * liftZ ((re.val[8]!).values.val[l + 4]!).val
         else liftZ ((re.val[8]!).values.val[l - 4]!).val
            - zeta (8 + 32) * liftZ ((re.val[8]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge8, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge8, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge8, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge8, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge8, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge8, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge8, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge8, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[9]!).values.val[l]!).val
            + zeta (9 + 32) * liftZ ((re.val[9]!).values.val[l + 4]!).val
         else liftZ ((re.val[9]!).values.val[l - 4]!).val
            - zeta (9 + 32) * liftZ ((re.val[9]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge9, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge9, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge9, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge9, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge9, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge9, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge9, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge9, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[10]!).values.val[l]!).val
            + zeta (10 + 32) * liftZ ((re.val[10]!).values.val[l + 4]!).val
         else liftZ ((re.val[10]!).values.val[l - 4]!).val
            - zeta (10 + 32) * liftZ ((re.val[10]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge10, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge10, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge10, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge10, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge10, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge10, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge10, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge10, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[11]!).values.val[l]!).val
            + zeta (11 + 32) * liftZ ((re.val[11]!).values.val[l + 4]!).val
         else liftZ ((re.val[11]!).values.val[l - 4]!).val
            - zeta (11 + 32) * liftZ ((re.val[11]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge11, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge11, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge11, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge11, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge11, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge11, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge11, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge11, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[12]!).values.val[l]!).val
            + zeta (12 + 32) * liftZ ((re.val[12]!).values.val[l + 4]!).val
         else liftZ ((re.val[12]!).values.val[l - 4]!).val
            - zeta (12 + 32) * liftZ ((re.val[12]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge12, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge12, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge12, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge12, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge12, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge12, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge12, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge12, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[13]!).values.val[l]!).val
            + zeta (13 + 32) * liftZ ((re.val[13]!).values.val[l + 4]!).val
         else liftZ ((re.val[13]!).values.val[l - 4]!).val
            - zeta (13 + 32) * liftZ ((re.val[13]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge13, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge13, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge13, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge13, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge13, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge13, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge13, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge13, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[14]!).values.val[l]!).val
            + zeta (14 + 32) * liftZ ((re.val[14]!).values.val[l + 4]!).val
         else liftZ ((re.val[14]!).values.val[l - 4]!).val
            - zeta (14 + 32) * liftZ ((re.val[14]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge14, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge14, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge14, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge14, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge14, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge14, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge14, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge14, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[15]!).values.val[l]!).val
            + zeta (15 + 32) * liftZ ((re.val[15]!).values.val[l + 4]!).val
         else liftZ ((re.val[15]!).values.val[l - 4]!).val
            - zeta (15 + 32) * liftZ ((re.val[15]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge15, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge15, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge15, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge15, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge15, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge15, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge15, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge15, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[16]!).values.val[l]!).val
            + zeta (16 + 32) * liftZ ((re.val[16]!).values.val[l + 4]!).val
         else liftZ ((re.val[16]!).values.val[l - 4]!).val
            - zeta (16 + 32) * liftZ ((re.val[16]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge16, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge16, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge16, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge16, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge16, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge16, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge16, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge16, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[17]!).values.val[l]!).val
            + zeta (17 + 32) * liftZ ((re.val[17]!).values.val[l + 4]!).val
         else liftZ ((re.val[17]!).values.val[l - 4]!).val
            - zeta (17 + 32) * liftZ ((re.val[17]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge17, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge17, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge17, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge17, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge17, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge17, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge17, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge17, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[18]!).values.val[l]!).val
            + zeta (18 + 32) * liftZ ((re.val[18]!).values.val[l + 4]!).val
         else liftZ ((re.val[18]!).values.val[l - 4]!).val
            - zeta (18 + 32) * liftZ ((re.val[18]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge18, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge18, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge18, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge18, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge18, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge18, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge18, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge18, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[19]!).values.val[l]!).val
            + zeta (19 + 32) * liftZ ((re.val[19]!).values.val[l + 4]!).val
         else liftZ ((re.val[19]!).values.val[l - 4]!).val
            - zeta (19 + 32) * liftZ ((re.val[19]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge19, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge19, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge19, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge19, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge19, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge19, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge19, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge19, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[20]!).values.val[l]!).val
            + zeta (20 + 32) * liftZ ((re.val[20]!).values.val[l + 4]!).val
         else liftZ ((re.val[20]!).values.val[l - 4]!).val
            - zeta (20 + 32) * liftZ ((re.val[20]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge20, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge20, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge20, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge20, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge20, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge20, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge20, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge20, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[21]!).values.val[l]!).val
            + zeta (21 + 32) * liftZ ((re.val[21]!).values.val[l + 4]!).val
         else liftZ ((re.val[21]!).values.val[l - 4]!).val
            - zeta (21 + 32) * liftZ ((re.val[21]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge21, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge21, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge21, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge21, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge21, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge21, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge21, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge21, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[22]!).values.val[l]!).val
            + zeta (22 + 32) * liftZ ((re.val[22]!).values.val[l + 4]!).val
         else liftZ ((re.val[22]!).values.val[l - 4]!).val
            - zeta (22 + 32) * liftZ ((re.val[22]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge22, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge22, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge22, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge22, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge22, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge22, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge22, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge22, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[23]!).values.val[l]!).val
            + zeta (23 + 32) * liftZ ((re.val[23]!).values.val[l + 4]!).val
         else liftZ ((re.val[23]!).values.val[l - 4]!).val
            - zeta (23 + 32) * liftZ ((re.val[23]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge23, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge23, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge23, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge23, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge23, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge23, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge23, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge23, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[24]!).values.val[l]!).val
            + zeta (24 + 32) * liftZ ((re.val[24]!).values.val[l + 4]!).val
         else liftZ ((re.val[24]!).values.val[l - 4]!).val
            - zeta (24 + 32) * liftZ ((re.val[24]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge24, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge24, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge24, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge24, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge24, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge24, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge24, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge24, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[25]!).values.val[l]!).val
            + zeta (25 + 32) * liftZ ((re.val[25]!).values.val[l + 4]!).val
         else liftZ ((re.val[25]!).values.val[l - 4]!).val
            - zeta (25 + 32) * liftZ ((re.val[25]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge25, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge25, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge25, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge25, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge25, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge25, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge25, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge25, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[26]!).values.val[l]!).val
            + zeta (26 + 32) * liftZ ((re.val[26]!).values.val[l + 4]!).val
         else liftZ ((re.val[26]!).values.val[l - 4]!).val
            - zeta (26 + 32) * liftZ ((re.val[26]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge26, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge26, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge26, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge26, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge26, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge26, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge26, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge26, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[27]!).values.val[l]!).val
            + zeta (27 + 32) * liftZ ((re.val[27]!).values.val[l + 4]!).val
         else liftZ ((re.val[27]!).values.val[l - 4]!).val
            - zeta (27 + 32) * liftZ ((re.val[27]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge27, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge27, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge27, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge27, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge27, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge27, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge27, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge27, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[28]!).values.val[l]!).val
            + zeta (28 + 32) * liftZ ((re.val[28]!).values.val[l + 4]!).val
         else liftZ ((re.val[28]!).values.val[l - 4]!).val
            - zeta (28 + 32) * liftZ ((re.val[28]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge28, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge28, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge28, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge28, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge28, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge28, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge28, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge28, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[29]!).values.val[l]!).val
            + zeta (29 + 32) * liftZ ((re.val[29]!).values.val[l + 4]!).val
         else liftZ ((re.val[29]!).values.val[l - 4]!).val
            - zeta (29 + 32) * liftZ ((re.val[29]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge29, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge29, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge29, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge29, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge29, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge29, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge29, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge29, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[30]!).values.val[l]!).val
            + zeta (30 + 32) * liftZ ((re.val[30]!).values.val[l + 4]!).val
         else liftZ ((re.val[30]!).values.val[l - 4]!).val
            - zeta (30 + 32) * liftZ ((re.val[30]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge30, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge30, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge30, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge30, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge30, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge30, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge30, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge30, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[31]!).values.val[l]!).val
            + zeta (31 + 32) * liftZ ((re.val[31]!).values.val[l + 4]!).val
         else liftZ ((re.val[31]!).values.val[l - 4]!).val
            - zeta (31 + 32) * liftZ ((re.val[31]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0, zeta2_bridge31, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1, zeta2_bridge31, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2, zeta2_bridge31, mul_comm]
    | 3, _ => rw [if_pos (by decide), b3, zeta2_bridge31, mul_comm]
    | 4, _ => rw [if_neg (by decide), b4, zeta2_bridge31, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5, zeta2_bridge31, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6, zeta2_bridge31, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7, zeta2_bridge31, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l < 4 then liftZ ((re.val[u]!).values.val[l]!).val
            + zeta (u + 32) * liftZ ((re.val[u]!).values.val[l + 4]!).val
         else liftZ ((re.val[u]!).values.val[l - 4]!).val
            - zeta (u + 32) * liftZ ((re.val[u]!).values.val[l]!).val) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · -- Equality conjunct.
    unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 8 < 4
    · rw [if_pos hlt]
      rw [if_pos hlt] at hb
      have hdiv : (i + 4) / 8 = i / 8 := by omega
      have hmod : (i + 4) % 8 = i % 8 + 4 := by omega
      have hidx2 : i + 4 < 256 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 4) hidx2, hdiv, hmod]
      exact hb
    · rw [if_neg hlt]
      rw [if_neg hlt] at hb
      have hdiv : (i - 4) / 8 = i / 8 := by omega
      have hmod : (i - 4) % 8 = i % 8 - 4 := by omega
      have hidx2 : i - 4 < 256 := by omega
      rw [Pure.build_getElem _ (i - 4) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      exact hb
  · -- Bound conjunct.
    exact hbnd



/-! ### Layer-1 within-unit forward driver `ntt_at_layer_1_fc`.

    `ntt_at_layer_1` chains 32 `round` calls; round `u` reads unit `u`, applies the
    per-unit butterfly `simd_unit_ntt_at_layer_1 _ Z0_u Z1_u` (pairs (0,2)(1,3) use
    `Z0_u`, pairs (4,6)(5,7) use `Z1_u`), and writes unit `u` back (touching ONLY
    unit `u`). The lifted result equals `ntt_layer (lift_units re) 1` (`len = 2`,
    `k = 64`; within each unit two sub-rounds `2u`/`2u+1`, lane split at `l % 4 < 2`,
    zetas `zeta (64 + 2u)` / `zeta (64 + 2u + 1)`). Uniform bound `B + 2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta1_bridge0 :
    liftZ (((-3930395)#i32 : Std.I32).val : Int) = zeta 64 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge0 :
    liftZ (((-1528703)#i32 : Std.I32).val : Int) = zeta 65 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge1 :
    liftZ (((-3677745)#i32 : Std.I32).val : Int) = zeta 66 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge1 :
    liftZ (((-3041255)#i32 : Std.I32).val : Int) = zeta 67 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge2 :
    liftZ (((-1452451)#i32 : Std.I32).val : Int) = zeta 68 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge2 :
    liftZ ((3475950#i32 : Std.I32).val : Int) = zeta 69 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge3 :
    liftZ ((2176455#i32 : Std.I32).val : Int) = zeta 70 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge3 :
    liftZ (((-1585221)#i32 : Std.I32).val : Int) = zeta 71 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge4 :
    liftZ (((-1257611)#i32 : Std.I32).val : Int) = zeta 72 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge4 :
    liftZ ((1939314#i32 : Std.I32).val : Int) = zeta 73 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge5 :
    liftZ (((-4083598)#i32 : Std.I32).val : Int) = zeta 74 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge5 :
    liftZ (((-1000202)#i32 : Std.I32).val : Int) = zeta 75 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge6 :
    liftZ (((-3190144)#i32 : Std.I32).val : Int) = zeta 76 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge6 :
    liftZ (((-3157330)#i32 : Std.I32).val : Int) = zeta 77 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge7 :
    liftZ (((-3632928)#i32 : Std.I32).val : Int) = zeta 78 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge7 :
    liftZ ((126922#i32 : Std.I32).val : Int) = zeta 79 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge8 :
    liftZ ((3412210#i32 : Std.I32).val : Int) = zeta 80 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge8 :
    liftZ (((-983419)#i32 : Std.I32).val : Int) = zeta 81 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge9 :
    liftZ ((2147896#i32 : Std.I32).val : Int) = zeta 82 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge9 :
    liftZ ((2715295#i32 : Std.I32).val : Int) = zeta 83 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge10 :
    liftZ (((-2967645)#i32 : Std.I32).val : Int) = zeta 84 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge10 :
    liftZ (((-3693493)#i32 : Std.I32).val : Int) = zeta 85 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge11 :
    liftZ (((-411027)#i32 : Std.I32).val : Int) = zeta 86 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge11 :
    liftZ (((-2477047)#i32 : Std.I32).val : Int) = zeta 87 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge12 :
    liftZ (((-671102)#i32 : Std.I32).val : Int) = zeta 88 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge12 :
    liftZ (((-1228525)#i32 : Std.I32).val : Int) = zeta 89 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge13 :
    liftZ (((-22981)#i32 : Std.I32).val : Int) = zeta 90 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge13 :
    liftZ (((-1308169)#i32 : Std.I32).val : Int) = zeta 91 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge14 :
    liftZ (((-381987)#i32 : Std.I32).val : Int) = zeta 92 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge14 :
    liftZ ((1349076#i32 : Std.I32).val : Int) = zeta 93 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge15 :
    liftZ ((1852771#i32 : Std.I32).val : Int) = zeta 94 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge15 :
    liftZ (((-1430430)#i32 : Std.I32).val : Int) = zeta 95 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge16 :
    liftZ (((-3343383)#i32 : Std.I32).val : Int) = zeta 96 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge16 :
    liftZ ((264944#i32 : Std.I32).val : Int) = zeta 97 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge17 :
    liftZ ((508951#i32 : Std.I32).val : Int) = zeta 98 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge17 :
    liftZ ((3097992#i32 : Std.I32).val : Int) = zeta 99 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge18 :
    liftZ ((44288#i32 : Std.I32).val : Int) = zeta 100 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge18 :
    liftZ (((-1100098)#i32 : Std.I32).val : Int) = zeta 101 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge19 :
    liftZ ((904516#i32 : Std.I32).val : Int) = zeta 102 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge19 :
    liftZ ((3958618#i32 : Std.I32).val : Int) = zeta 103 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge20 :
    liftZ (((-3724342)#i32 : Std.I32).val : Int) = zeta 104 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge20 :
    liftZ (((-8578)#i32 : Std.I32).val : Int) = zeta 105 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge21 :
    liftZ ((1653064#i32 : Std.I32).val : Int) = zeta 106 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge21 :
    liftZ (((-3249728)#i32 : Std.I32).val : Int) = zeta 107 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge22 :
    liftZ ((2389356#i32 : Std.I32).val : Int) = zeta 108 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge22 :
    liftZ (((-210977)#i32 : Std.I32).val : Int) = zeta 109 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge23 :
    liftZ ((759969#i32 : Std.I32).val : Int) = zeta 110 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge23 :
    liftZ (((-1316856)#i32 : Std.I32).val : Int) = zeta 111 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge24 :
    liftZ ((189548#i32 : Std.I32).val : Int) = zeta 112 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge24 :
    liftZ (((-3553272)#i32 : Std.I32).val : Int) = zeta 113 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge25 :
    liftZ ((3159746#i32 : Std.I32).val : Int) = zeta 114 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge25 :
    liftZ (((-1851402)#i32 : Std.I32).val : Int) = zeta 115 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge26 :
    liftZ (((-2409325)#i32 : Std.I32).val : Int) = zeta 116 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge26 :
    liftZ (((-177440)#i32 : Std.I32).val : Int) = zeta 117 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge27 :
    liftZ ((1315589#i32 : Std.I32).val : Int) = zeta 118 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge27 :
    liftZ ((1341330#i32 : Std.I32).val : Int) = zeta 119 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge28 :
    liftZ ((1285669#i32 : Std.I32).val : Int) = zeta 120 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge28 :
    liftZ (((-1584928)#i32 : Std.I32).val : Int) = zeta 121 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge29 :
    liftZ (((-812732)#i32 : Std.I32).val : Int) = zeta 122 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge29 :
    liftZ (((-1439742)#i32 : Std.I32).val : Int) = zeta 123 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge30 :
    liftZ (((-3019102)#i32 : Std.I32).val : Int) = zeta 124 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge30 :
    liftZ (((-3881060)#i32 : Std.I32).val : Int) = zeta 125 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1_bridge31 :
    liftZ (((-3628969)#i32 : Std.I32).val : Int) = zeta 126 := by decide
set_option maxRecDepth 4000 in
private theorem zeta1b_bridge31 :
    liftZ ((3839961#i32 : Std.I32).val : Int) = zeta 127 := by decide
private theorem zeta1_mag0 : ((-3930395)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag0 : ((-1528703)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag1 : ((-3677745)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag1 : ((-3041255)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag2 : ((-1452451)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag2 : (3475950#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag3 : (2176455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag3 : ((-1585221)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag4 : ((-1257611)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag4 : (1939314#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag5 : ((-4083598)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag5 : ((-1000202)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag6 : ((-3190144)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag6 : ((-3157330)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag7 : ((-3632928)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag7 : (126922#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag8 : (3412210#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag8 : ((-983419)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag9 : (2147896#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag9 : (2715295#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag10 : ((-2967645)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag10 : ((-3693493)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag11 : ((-411027)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag11 : ((-2477047)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag12 : ((-671102)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag12 : ((-1228525)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag13 : ((-22981)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag13 : ((-1308169)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag14 : ((-381987)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag14 : (1349076#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag15 : (1852771#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag15 : ((-1430430)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag16 : ((-3343383)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag16 : (264944#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag17 : (508951#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag17 : (3097992#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag18 : (44288#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag18 : ((-1100098)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag19 : (904516#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag19 : (3958618#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag20 : ((-3724342)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag20 : ((-8578)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag21 : (1653064#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag21 : ((-3249728)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag22 : (2389356#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag22 : ((-210977)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag23 : (759969#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag23 : ((-1316856)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag24 : (189548#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag24 : ((-3553272)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag25 : (3159746#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag25 : ((-1851402)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag26 : ((-2409325)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag26 : ((-177440)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag27 : (1315589#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag27 : (1341330#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag28 : (1285669#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag28 : ((-1584928)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag29 : ((-812732)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag29 : ((-1439742)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag30 : ((-3019102)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag30 : ((-3881060)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1_mag31 : ((-3628969)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta1b_mag31 : (3839961#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of layer 1: read unit `k`, apply the per-unit butterfly with
    `zeta1` (pairs 0/2, 1/3) and `zeta2` (pairs 4/6, 5/7), write unit `k` back. -/
private theorem round1_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta1 zeta2 : Std.I32) (B : Nat)
    (hz1 : zeta1.val.natAbs ≤ 8380416) (hz2 : zeta2.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_1.round re k#usize zeta1 zeta2 = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[2]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val + liftZ ((re.val[k]!).values.val[3]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val - liftZ ((re.val[k]!).values.val[2]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = liftZ ((re.val[k]!).values.val[1]!).val - liftZ ((re.val[k]!).values.val[3]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val + liftZ ((re.val[k]!).values.val[6]!).val * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = liftZ ((re.val[k]!).values.val[5]!).val + liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val - liftZ ((re.val[k]!).values.val[6]!).val * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = liftZ ((re.val[k]!).values.val[5]!).val - liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta2.val
        )
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_1.round
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_ntt_at_layer_1_fc ak zeta1 zeta2 B hz1 hz2 hB hin)
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · rw [hset_k]; exact hc1_butter
  · intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · intro l hl
    rw [hset_k]; exact hc1_bd l hl


set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_1_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_1 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 1
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_1
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    round1_fc re 0 (by decide) ((-3930395)#i32) ((-1528703)#i32) B (zeta1_mag0) (zeta1b_mag0) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    round1_fc r1 1 (by decide) ((-3677745)#i32) ((-3041255)#i32) B (zeta1_mag1) (zeta1b_mag1) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    round1_fc r2 2 (by decide) ((-1452451)#i32) (3475950#i32) B (zeta1_mag2) (zeta1b_mag2) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    round1_fc r3 3 (by decide) (2176455#i32) ((-1585221)#i32) B (zeta1_mag3) (zeta1b_mag3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    round1_fc r4 4 (by decide) ((-1257611)#i32) (1939314#i32) B (zeta1_mag4) (zeta1b_mag4) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    round1_fc r5 5 (by decide) ((-4083598)#i32) ((-1000202)#i32) B (zeta1_mag5) (zeta1b_mag5) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    round1_fc r6 6 (by decide) ((-3190144)#i32) ((-3157330)#i32) B (zeta1_mag6) (zeta1b_mag6) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    round1_fc r7 7 (by decide) ((-3632928)#i32) (126922#i32) B (zeta1_mag7) (zeta1b_mag7) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    round1_fc r8 8 (by decide) (3412210#i32) ((-983419)#i32) B (zeta1_mag8) (zeta1b_mag8) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    round1_fc r9 9 (by decide) (2147896#i32) (2715295#i32) B (zeta1_mag9) (zeta1b_mag9) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    round1_fc r10 10 (by decide) ((-2967645)#i32) ((-3693493)#i32) B (zeta1_mag10) (zeta1b_mag10) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    round1_fc r11 11 (by decide) ((-411027)#i32) ((-2477047)#i32) B (zeta1_mag11) (zeta1b_mag11) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    round1_fc r12 12 (by decide) ((-671102)#i32) ((-1228525)#i32) B (zeta1_mag12) (zeta1b_mag12) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    round1_fc r13 13 (by decide) ((-22981)#i32) ((-1308169)#i32) B (zeta1_mag13) (zeta1b_mag13) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    round1_fc r14 14 (by decide) ((-381987)#i32) (1349076#i32) B (zeta1_mag14) (zeta1b_mag14) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    round1_fc r15 15 (by decide) (1852771#i32) ((-1430430)#i32) B (zeta1_mag15) (zeta1b_mag15) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    round1_fc r16 16 (by decide) ((-3343383)#i32) (264944#i32) B (zeta1_mag16) (zeta1b_mag16) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    round1_fc r17 17 (by decide) (508951#i32) (3097992#i32) B (zeta1_mag17) (zeta1b_mag17) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    round1_fc r18 18 (by decide) (44288#i32) ((-1100098)#i32) B (zeta1_mag18) (zeta1b_mag18) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    round1_fc r19 19 (by decide) (904516#i32) (3958618#i32) B (zeta1_mag19) (zeta1b_mag19) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    round1_fc r20 20 (by decide) ((-3724342)#i32) ((-8578)#i32) B (zeta1_mag20) (zeta1b_mag20) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    round1_fc r21 21 (by decide) (1653064#i32) ((-3249728)#i32) B (zeta1_mag21) (zeta1b_mag21) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    round1_fc r22 22 (by decide) (2389356#i32) ((-210977)#i32) B (zeta1_mag22) (zeta1b_mag22) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    round1_fc r23 23 (by decide) (759969#i32) ((-1316856)#i32) B (zeta1_mag23) (zeta1b_mag23) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    round1_fc r24 24 (by decide) (189548#i32) ((-3553272)#i32) B (zeta1_mag24) (zeta1b_mag24) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    round1_fc r25 25 (by decide) (3159746#i32) ((-1851402)#i32) B (zeta1_mag25) (zeta1b_mag25) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    round1_fc r26 26 (by decide) ((-2409325)#i32) ((-177440)#i32) B (zeta1_mag26) (zeta1b_mag26) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    round1_fc r27 27 (by decide) (1315589#i32) (1341330#i32) B (zeta1_mag27) (zeta1b_mag27) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    round1_fc r28 28 (by decide) (1285669#i32) ((-1584928)#i32) B (zeta1_mag28) (zeta1b_mag28) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    round1_fc r29 29 (by decide) ((-812732)#i32) ((-1439742)#i32) B (zeta1_mag29) (zeta1b_mag29) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    round1_fc r30 30 (by decide) ((-3019102)#i32) ((-3881060)#i32) B (zeta1_mag30) (zeta1b_mag30) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    round1_fc r31 31 (by decide) ((-3628969)#i32) (3839961#i32) B (zeta1_mag31) (zeta1b_mag31) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr9_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr10_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr11_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr12_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr13_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr14_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr15_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[0]!).values.val[l]!).val
            + zeta (2 * 0 + l / 4 + 64) * liftZ ((re.val[0]!).values.val[l + 2]!).val
         else liftZ ((re.val[0]!).values.val[l - 2]!).val
            - zeta (2 * 0 + l / 4 + 64) * liftZ ((re.val[0]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 0 + 0 / 4 + 64) = 64 from by decide, zeta1_bridge0, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 0 + 1 / 4 + 64) = 64 from by decide, zeta1_bridge0, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 0 + 2 / 4 + 64) = 64 from by decide, zeta1_bridge0, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 0 + 3 / 4 + 64) = 64 from by decide, zeta1_bridge0, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 0 + 4 / 4 + 64) = 65 from by decide, zeta1b_bridge0, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 0 + 5 / 4 + 64) = 65 from by decide, zeta1b_bridge0, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 0 + 6 / 4 + 64) = 65 from by decide, zeta1b_bridge0, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 0 + 7 / 4 + 64) = 65 from by decide, zeta1b_bridge0, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[1]!).values.val[l]!).val
            + zeta (2 * 1 + l / 4 + 64) * liftZ ((re.val[1]!).values.val[l + 2]!).val
         else liftZ ((re.val[1]!).values.val[l - 2]!).val
            - zeta (2 * 1 + l / 4 + 64) * liftZ ((re.val[1]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 1 + 0 / 4 + 64) = 66 from by decide, zeta1_bridge1, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 1 + 1 / 4 + 64) = 66 from by decide, zeta1_bridge1, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 1 + 2 / 4 + 64) = 66 from by decide, zeta1_bridge1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 1 + 3 / 4 + 64) = 66 from by decide, zeta1_bridge1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 1 + 4 / 4 + 64) = 67 from by decide, zeta1b_bridge1, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 1 + 5 / 4 + 64) = 67 from by decide, zeta1b_bridge1, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 1 + 6 / 4 + 64) = 67 from by decide, zeta1b_bridge1, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 1 + 7 / 4 + 64) = 67 from by decide, zeta1b_bridge1, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[2]!).values.val[l]!).val
            + zeta (2 * 2 + l / 4 + 64) * liftZ ((re.val[2]!).values.val[l + 2]!).val
         else liftZ ((re.val[2]!).values.val[l - 2]!).val
            - zeta (2 * 2 + l / 4 + 64) * liftZ ((re.val[2]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 2 + 0 / 4 + 64) = 68 from by decide, zeta1_bridge2, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 2 + 1 / 4 + 64) = 68 from by decide, zeta1_bridge2, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 2 + 2 / 4 + 64) = 68 from by decide, zeta1_bridge2, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 2 + 3 / 4 + 64) = 68 from by decide, zeta1_bridge2, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 2 + 4 / 4 + 64) = 69 from by decide, zeta1b_bridge2, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 2 + 5 / 4 + 64) = 69 from by decide, zeta1b_bridge2, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 2 + 6 / 4 + 64) = 69 from by decide, zeta1b_bridge2, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 2 + 7 / 4 + 64) = 69 from by decide, zeta1b_bridge2, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[3]!).values.val[l]!).val
            + zeta (2 * 3 + l / 4 + 64) * liftZ ((re.val[3]!).values.val[l + 2]!).val
         else liftZ ((re.val[3]!).values.val[l - 2]!).val
            - zeta (2 * 3 + l / 4 + 64) * liftZ ((re.val[3]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 3 + 0 / 4 + 64) = 70 from by decide, zeta1_bridge3, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 3 + 1 / 4 + 64) = 70 from by decide, zeta1_bridge3, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 3 + 2 / 4 + 64) = 70 from by decide, zeta1_bridge3, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 3 + 3 / 4 + 64) = 70 from by decide, zeta1_bridge3, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 3 + 4 / 4 + 64) = 71 from by decide, zeta1b_bridge3, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 3 + 5 / 4 + 64) = 71 from by decide, zeta1b_bridge3, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 3 + 6 / 4 + 64) = 71 from by decide, zeta1b_bridge3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 3 + 7 / 4 + 64) = 71 from by decide, zeta1b_bridge3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[4]!).values.val[l]!).val
            + zeta (2 * 4 + l / 4 + 64) * liftZ ((re.val[4]!).values.val[l + 2]!).val
         else liftZ ((re.val[4]!).values.val[l - 2]!).val
            - zeta (2 * 4 + l / 4 + 64) * liftZ ((re.val[4]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 4 + 0 / 4 + 64) = 72 from by decide, zeta1_bridge4, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 4 + 1 / 4 + 64) = 72 from by decide, zeta1_bridge4, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 4 + 2 / 4 + 64) = 72 from by decide, zeta1_bridge4, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 4 + 3 / 4 + 64) = 72 from by decide, zeta1_bridge4, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 4 + 4 / 4 + 64) = 73 from by decide, zeta1b_bridge4, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 4 + 5 / 4 + 64) = 73 from by decide, zeta1b_bridge4, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 4 + 6 / 4 + 64) = 73 from by decide, zeta1b_bridge4, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 4 + 7 / 4 + 64) = 73 from by decide, zeta1b_bridge4, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[5]!).values.val[l]!).val
            + zeta (2 * 5 + l / 4 + 64) * liftZ ((re.val[5]!).values.val[l + 2]!).val
         else liftZ ((re.val[5]!).values.val[l - 2]!).val
            - zeta (2 * 5 + l / 4 + 64) * liftZ ((re.val[5]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 5 + 0 / 4 + 64) = 74 from by decide, zeta1_bridge5, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 5 + 1 / 4 + 64) = 74 from by decide, zeta1_bridge5, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 5 + 2 / 4 + 64) = 74 from by decide, zeta1_bridge5, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 5 + 3 / 4 + 64) = 74 from by decide, zeta1_bridge5, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 5 + 4 / 4 + 64) = 75 from by decide, zeta1b_bridge5, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 5 + 5 / 4 + 64) = 75 from by decide, zeta1b_bridge5, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 5 + 6 / 4 + 64) = 75 from by decide, zeta1b_bridge5, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 5 + 7 / 4 + 64) = 75 from by decide, zeta1b_bridge5, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[6]!).values.val[l]!).val
            + zeta (2 * 6 + l / 4 + 64) * liftZ ((re.val[6]!).values.val[l + 2]!).val
         else liftZ ((re.val[6]!).values.val[l - 2]!).val
            - zeta (2 * 6 + l / 4 + 64) * liftZ ((re.val[6]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 6 + 0 / 4 + 64) = 76 from by decide, zeta1_bridge6, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 6 + 1 / 4 + 64) = 76 from by decide, zeta1_bridge6, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 6 + 2 / 4 + 64) = 76 from by decide, zeta1_bridge6, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 6 + 3 / 4 + 64) = 76 from by decide, zeta1_bridge6, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 6 + 4 / 4 + 64) = 77 from by decide, zeta1b_bridge6, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 6 + 5 / 4 + 64) = 77 from by decide, zeta1b_bridge6, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 6 + 6 / 4 + 64) = 77 from by decide, zeta1b_bridge6, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 6 + 7 / 4 + 64) = 77 from by decide, zeta1b_bridge6, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[7]!).values.val[l]!).val
            + zeta (2 * 7 + l / 4 + 64) * liftZ ((re.val[7]!).values.val[l + 2]!).val
         else liftZ ((re.val[7]!).values.val[l - 2]!).val
            - zeta (2 * 7 + l / 4 + 64) * liftZ ((re.val[7]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 7 + 0 / 4 + 64) = 78 from by decide, zeta1_bridge7, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 7 + 1 / 4 + 64) = 78 from by decide, zeta1_bridge7, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 7 + 2 / 4 + 64) = 78 from by decide, zeta1_bridge7, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 7 + 3 / 4 + 64) = 78 from by decide, zeta1_bridge7, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 7 + 4 / 4 + 64) = 79 from by decide, zeta1b_bridge7, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 7 + 5 / 4 + 64) = 79 from by decide, zeta1b_bridge7, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 7 + 6 / 4 + 64) = 79 from by decide, zeta1b_bridge7, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 7 + 7 / 4 + 64) = 79 from by decide, zeta1b_bridge7, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[8]!).values.val[l]!).val
            + zeta (2 * 8 + l / 4 + 64) * liftZ ((re.val[8]!).values.val[l + 2]!).val
         else liftZ ((re.val[8]!).values.val[l - 2]!).val
            - zeta (2 * 8 + l / 4 + 64) * liftZ ((re.val[8]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 8 + 0 / 4 + 64) = 80 from by decide, zeta1_bridge8, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 8 + 1 / 4 + 64) = 80 from by decide, zeta1_bridge8, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 8 + 2 / 4 + 64) = 80 from by decide, zeta1_bridge8, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 8 + 3 / 4 + 64) = 80 from by decide, zeta1_bridge8, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 8 + 4 / 4 + 64) = 81 from by decide, zeta1b_bridge8, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 8 + 5 / 4 + 64) = 81 from by decide, zeta1b_bridge8, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 8 + 6 / 4 + 64) = 81 from by decide, zeta1b_bridge8, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 8 + 7 / 4 + 64) = 81 from by decide, zeta1b_bridge8, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[9]!).values.val[l]!).val
            + zeta (2 * 9 + l / 4 + 64) * liftZ ((re.val[9]!).values.val[l + 2]!).val
         else liftZ ((re.val[9]!).values.val[l - 2]!).val
            - zeta (2 * 9 + l / 4 + 64) * liftZ ((re.val[9]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 9 + 0 / 4 + 64) = 82 from by decide, zeta1_bridge9, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 9 + 1 / 4 + 64) = 82 from by decide, zeta1_bridge9, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 9 + 2 / 4 + 64) = 82 from by decide, zeta1_bridge9, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 9 + 3 / 4 + 64) = 82 from by decide, zeta1_bridge9, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 9 + 4 / 4 + 64) = 83 from by decide, zeta1b_bridge9, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 9 + 5 / 4 + 64) = 83 from by decide, zeta1b_bridge9, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 9 + 6 / 4 + 64) = 83 from by decide, zeta1b_bridge9, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 9 + 7 / 4 + 64) = 83 from by decide, zeta1b_bridge9, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[10]!).values.val[l]!).val
            + zeta (2 * 10 + l / 4 + 64) * liftZ ((re.val[10]!).values.val[l + 2]!).val
         else liftZ ((re.val[10]!).values.val[l - 2]!).val
            - zeta (2 * 10 + l / 4 + 64) * liftZ ((re.val[10]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 10 + 0 / 4 + 64) = 84 from by decide, zeta1_bridge10, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 10 + 1 / 4 + 64) = 84 from by decide, zeta1_bridge10, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 10 + 2 / 4 + 64) = 84 from by decide, zeta1_bridge10, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 10 + 3 / 4 + 64) = 84 from by decide, zeta1_bridge10, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 10 + 4 / 4 + 64) = 85 from by decide, zeta1b_bridge10, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 10 + 5 / 4 + 64) = 85 from by decide, zeta1b_bridge10, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 10 + 6 / 4 + 64) = 85 from by decide, zeta1b_bridge10, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 10 + 7 / 4 + 64) = 85 from by decide, zeta1b_bridge10, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[11]!).values.val[l]!).val
            + zeta (2 * 11 + l / 4 + 64) * liftZ ((re.val[11]!).values.val[l + 2]!).val
         else liftZ ((re.val[11]!).values.val[l - 2]!).val
            - zeta (2 * 11 + l / 4 + 64) * liftZ ((re.val[11]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 11 + 0 / 4 + 64) = 86 from by decide, zeta1_bridge11, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 11 + 1 / 4 + 64) = 86 from by decide, zeta1_bridge11, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 11 + 2 / 4 + 64) = 86 from by decide, zeta1_bridge11, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 11 + 3 / 4 + 64) = 86 from by decide, zeta1_bridge11, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 11 + 4 / 4 + 64) = 87 from by decide, zeta1b_bridge11, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 11 + 5 / 4 + 64) = 87 from by decide, zeta1b_bridge11, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 11 + 6 / 4 + 64) = 87 from by decide, zeta1b_bridge11, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 11 + 7 / 4 + 64) = 87 from by decide, zeta1b_bridge11, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[12]!).values.val[l]!).val
            + zeta (2 * 12 + l / 4 + 64) * liftZ ((re.val[12]!).values.val[l + 2]!).val
         else liftZ ((re.val[12]!).values.val[l - 2]!).val
            - zeta (2 * 12 + l / 4 + 64) * liftZ ((re.val[12]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 12 + 0 / 4 + 64) = 88 from by decide, zeta1_bridge12, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 12 + 1 / 4 + 64) = 88 from by decide, zeta1_bridge12, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 12 + 2 / 4 + 64) = 88 from by decide, zeta1_bridge12, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 12 + 3 / 4 + 64) = 88 from by decide, zeta1_bridge12, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 12 + 4 / 4 + 64) = 89 from by decide, zeta1b_bridge12, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 12 + 5 / 4 + 64) = 89 from by decide, zeta1b_bridge12, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 12 + 6 / 4 + 64) = 89 from by decide, zeta1b_bridge12, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 12 + 7 / 4 + 64) = 89 from by decide, zeta1b_bridge12, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[13]!).values.val[l]!).val
            + zeta (2 * 13 + l / 4 + 64) * liftZ ((re.val[13]!).values.val[l + 2]!).val
         else liftZ ((re.val[13]!).values.val[l - 2]!).val
            - zeta (2 * 13 + l / 4 + 64) * liftZ ((re.val[13]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 13 + 0 / 4 + 64) = 90 from by decide, zeta1_bridge13, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 13 + 1 / 4 + 64) = 90 from by decide, zeta1_bridge13, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 13 + 2 / 4 + 64) = 90 from by decide, zeta1_bridge13, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 13 + 3 / 4 + 64) = 90 from by decide, zeta1_bridge13, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 13 + 4 / 4 + 64) = 91 from by decide, zeta1b_bridge13, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 13 + 5 / 4 + 64) = 91 from by decide, zeta1b_bridge13, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 13 + 6 / 4 + 64) = 91 from by decide, zeta1b_bridge13, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 13 + 7 / 4 + 64) = 91 from by decide, zeta1b_bridge13, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[14]!).values.val[l]!).val
            + zeta (2 * 14 + l / 4 + 64) * liftZ ((re.val[14]!).values.val[l + 2]!).val
         else liftZ ((re.val[14]!).values.val[l - 2]!).val
            - zeta (2 * 14 + l / 4 + 64) * liftZ ((re.val[14]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 14 + 0 / 4 + 64) = 92 from by decide, zeta1_bridge14, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 14 + 1 / 4 + 64) = 92 from by decide, zeta1_bridge14, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 14 + 2 / 4 + 64) = 92 from by decide, zeta1_bridge14, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 14 + 3 / 4 + 64) = 92 from by decide, zeta1_bridge14, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 14 + 4 / 4 + 64) = 93 from by decide, zeta1b_bridge14, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 14 + 5 / 4 + 64) = 93 from by decide, zeta1b_bridge14, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 14 + 6 / 4 + 64) = 93 from by decide, zeta1b_bridge14, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 14 + 7 / 4 + 64) = 93 from by decide, zeta1b_bridge14, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[15]!).values.val[l]!).val
            + zeta (2 * 15 + l / 4 + 64) * liftZ ((re.val[15]!).values.val[l + 2]!).val
         else liftZ ((re.val[15]!).values.val[l - 2]!).val
            - zeta (2 * 15 + l / 4 + 64) * liftZ ((re.val[15]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 15 + 0 / 4 + 64) = 94 from by decide, zeta1_bridge15, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 15 + 1 / 4 + 64) = 94 from by decide, zeta1_bridge15, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 15 + 2 / 4 + 64) = 94 from by decide, zeta1_bridge15, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 15 + 3 / 4 + 64) = 94 from by decide, zeta1_bridge15, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 15 + 4 / 4 + 64) = 95 from by decide, zeta1b_bridge15, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 15 + 5 / 4 + 64) = 95 from by decide, zeta1b_bridge15, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 15 + 6 / 4 + 64) = 95 from by decide, zeta1b_bridge15, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 15 + 7 / 4 + 64) = 95 from by decide, zeta1b_bridge15, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[16]!).values.val[l]!).val
            + zeta (2 * 16 + l / 4 + 64) * liftZ ((re.val[16]!).values.val[l + 2]!).val
         else liftZ ((re.val[16]!).values.val[l - 2]!).val
            - zeta (2 * 16 + l / 4 + 64) * liftZ ((re.val[16]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 16 + 0 / 4 + 64) = 96 from by decide, zeta1_bridge16, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 16 + 1 / 4 + 64) = 96 from by decide, zeta1_bridge16, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 16 + 2 / 4 + 64) = 96 from by decide, zeta1_bridge16, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 16 + 3 / 4 + 64) = 96 from by decide, zeta1_bridge16, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 16 + 4 / 4 + 64) = 97 from by decide, zeta1b_bridge16, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 16 + 5 / 4 + 64) = 97 from by decide, zeta1b_bridge16, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 16 + 6 / 4 + 64) = 97 from by decide, zeta1b_bridge16, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 16 + 7 / 4 + 64) = 97 from by decide, zeta1b_bridge16, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[17]!).values.val[l]!).val
            + zeta (2 * 17 + l / 4 + 64) * liftZ ((re.val[17]!).values.val[l + 2]!).val
         else liftZ ((re.val[17]!).values.val[l - 2]!).val
            - zeta (2 * 17 + l / 4 + 64) * liftZ ((re.val[17]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 17 + 0 / 4 + 64) = 98 from by decide, zeta1_bridge17, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 17 + 1 / 4 + 64) = 98 from by decide, zeta1_bridge17, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 17 + 2 / 4 + 64) = 98 from by decide, zeta1_bridge17, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 17 + 3 / 4 + 64) = 98 from by decide, zeta1_bridge17, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 17 + 4 / 4 + 64) = 99 from by decide, zeta1b_bridge17, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 17 + 5 / 4 + 64) = 99 from by decide, zeta1b_bridge17, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 17 + 6 / 4 + 64) = 99 from by decide, zeta1b_bridge17, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 17 + 7 / 4 + 64) = 99 from by decide, zeta1b_bridge17, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[18]!).values.val[l]!).val
            + zeta (2 * 18 + l / 4 + 64) * liftZ ((re.val[18]!).values.val[l + 2]!).val
         else liftZ ((re.val[18]!).values.val[l - 2]!).val
            - zeta (2 * 18 + l / 4 + 64) * liftZ ((re.val[18]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 18 + 0 / 4 + 64) = 100 from by decide, zeta1_bridge18, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 18 + 1 / 4 + 64) = 100 from by decide, zeta1_bridge18, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 18 + 2 / 4 + 64) = 100 from by decide, zeta1_bridge18, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 18 + 3 / 4 + 64) = 100 from by decide, zeta1_bridge18, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 18 + 4 / 4 + 64) = 101 from by decide, zeta1b_bridge18, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 18 + 5 / 4 + 64) = 101 from by decide, zeta1b_bridge18, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 18 + 6 / 4 + 64) = 101 from by decide, zeta1b_bridge18, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 18 + 7 / 4 + 64) = 101 from by decide, zeta1b_bridge18, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[19]!).values.val[l]!).val
            + zeta (2 * 19 + l / 4 + 64) * liftZ ((re.val[19]!).values.val[l + 2]!).val
         else liftZ ((re.val[19]!).values.val[l - 2]!).val
            - zeta (2 * 19 + l / 4 + 64) * liftZ ((re.val[19]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 19 + 0 / 4 + 64) = 102 from by decide, zeta1_bridge19, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 19 + 1 / 4 + 64) = 102 from by decide, zeta1_bridge19, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 19 + 2 / 4 + 64) = 102 from by decide, zeta1_bridge19, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 19 + 3 / 4 + 64) = 102 from by decide, zeta1_bridge19, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 19 + 4 / 4 + 64) = 103 from by decide, zeta1b_bridge19, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 19 + 5 / 4 + 64) = 103 from by decide, zeta1b_bridge19, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 19 + 6 / 4 + 64) = 103 from by decide, zeta1b_bridge19, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 19 + 7 / 4 + 64) = 103 from by decide, zeta1b_bridge19, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[20]!).values.val[l]!).val
            + zeta (2 * 20 + l / 4 + 64) * liftZ ((re.val[20]!).values.val[l + 2]!).val
         else liftZ ((re.val[20]!).values.val[l - 2]!).val
            - zeta (2 * 20 + l / 4 + 64) * liftZ ((re.val[20]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 20 + 0 / 4 + 64) = 104 from by decide, zeta1_bridge20, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 20 + 1 / 4 + 64) = 104 from by decide, zeta1_bridge20, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 20 + 2 / 4 + 64) = 104 from by decide, zeta1_bridge20, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 20 + 3 / 4 + 64) = 104 from by decide, zeta1_bridge20, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 20 + 4 / 4 + 64) = 105 from by decide, zeta1b_bridge20, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 20 + 5 / 4 + 64) = 105 from by decide, zeta1b_bridge20, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 20 + 6 / 4 + 64) = 105 from by decide, zeta1b_bridge20, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 20 + 7 / 4 + 64) = 105 from by decide, zeta1b_bridge20, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[21]!).values.val[l]!).val
            + zeta (2 * 21 + l / 4 + 64) * liftZ ((re.val[21]!).values.val[l + 2]!).val
         else liftZ ((re.val[21]!).values.val[l - 2]!).val
            - zeta (2 * 21 + l / 4 + 64) * liftZ ((re.val[21]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 21 + 0 / 4 + 64) = 106 from by decide, zeta1_bridge21, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 21 + 1 / 4 + 64) = 106 from by decide, zeta1_bridge21, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 21 + 2 / 4 + 64) = 106 from by decide, zeta1_bridge21, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 21 + 3 / 4 + 64) = 106 from by decide, zeta1_bridge21, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 21 + 4 / 4 + 64) = 107 from by decide, zeta1b_bridge21, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 21 + 5 / 4 + 64) = 107 from by decide, zeta1b_bridge21, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 21 + 6 / 4 + 64) = 107 from by decide, zeta1b_bridge21, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 21 + 7 / 4 + 64) = 107 from by decide, zeta1b_bridge21, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[22]!).values.val[l]!).val
            + zeta (2 * 22 + l / 4 + 64) * liftZ ((re.val[22]!).values.val[l + 2]!).val
         else liftZ ((re.val[22]!).values.val[l - 2]!).val
            - zeta (2 * 22 + l / 4 + 64) * liftZ ((re.val[22]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 22 + 0 / 4 + 64) = 108 from by decide, zeta1_bridge22, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 22 + 1 / 4 + 64) = 108 from by decide, zeta1_bridge22, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 22 + 2 / 4 + 64) = 108 from by decide, zeta1_bridge22, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 22 + 3 / 4 + 64) = 108 from by decide, zeta1_bridge22, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 22 + 4 / 4 + 64) = 109 from by decide, zeta1b_bridge22, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 22 + 5 / 4 + 64) = 109 from by decide, zeta1b_bridge22, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 22 + 6 / 4 + 64) = 109 from by decide, zeta1b_bridge22, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 22 + 7 / 4 + 64) = 109 from by decide, zeta1b_bridge22, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[23]!).values.val[l]!).val
            + zeta (2 * 23 + l / 4 + 64) * liftZ ((re.val[23]!).values.val[l + 2]!).val
         else liftZ ((re.val[23]!).values.val[l - 2]!).val
            - zeta (2 * 23 + l / 4 + 64) * liftZ ((re.val[23]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 23 + 0 / 4 + 64) = 110 from by decide, zeta1_bridge23, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 23 + 1 / 4 + 64) = 110 from by decide, zeta1_bridge23, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 23 + 2 / 4 + 64) = 110 from by decide, zeta1_bridge23, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 23 + 3 / 4 + 64) = 110 from by decide, zeta1_bridge23, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 23 + 4 / 4 + 64) = 111 from by decide, zeta1b_bridge23, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 23 + 5 / 4 + 64) = 111 from by decide, zeta1b_bridge23, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 23 + 6 / 4 + 64) = 111 from by decide, zeta1b_bridge23, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 23 + 7 / 4 + 64) = 111 from by decide, zeta1b_bridge23, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[24]!).values.val[l]!).val
            + zeta (2 * 24 + l / 4 + 64) * liftZ ((re.val[24]!).values.val[l + 2]!).val
         else liftZ ((re.val[24]!).values.val[l - 2]!).val
            - zeta (2 * 24 + l / 4 + 64) * liftZ ((re.val[24]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 24 + 0 / 4 + 64) = 112 from by decide, zeta1_bridge24, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 24 + 1 / 4 + 64) = 112 from by decide, zeta1_bridge24, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 24 + 2 / 4 + 64) = 112 from by decide, zeta1_bridge24, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 24 + 3 / 4 + 64) = 112 from by decide, zeta1_bridge24, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 24 + 4 / 4 + 64) = 113 from by decide, zeta1b_bridge24, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 24 + 5 / 4 + 64) = 113 from by decide, zeta1b_bridge24, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 24 + 6 / 4 + 64) = 113 from by decide, zeta1b_bridge24, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 24 + 7 / 4 + 64) = 113 from by decide, zeta1b_bridge24, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[25]!).values.val[l]!).val
            + zeta (2 * 25 + l / 4 + 64) * liftZ ((re.val[25]!).values.val[l + 2]!).val
         else liftZ ((re.val[25]!).values.val[l - 2]!).val
            - zeta (2 * 25 + l / 4 + 64) * liftZ ((re.val[25]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 25 + 0 / 4 + 64) = 114 from by decide, zeta1_bridge25, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 25 + 1 / 4 + 64) = 114 from by decide, zeta1_bridge25, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 25 + 2 / 4 + 64) = 114 from by decide, zeta1_bridge25, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 25 + 3 / 4 + 64) = 114 from by decide, zeta1_bridge25, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 25 + 4 / 4 + 64) = 115 from by decide, zeta1b_bridge25, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 25 + 5 / 4 + 64) = 115 from by decide, zeta1b_bridge25, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 25 + 6 / 4 + 64) = 115 from by decide, zeta1b_bridge25, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 25 + 7 / 4 + 64) = 115 from by decide, zeta1b_bridge25, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[26]!).values.val[l]!).val
            + zeta (2 * 26 + l / 4 + 64) * liftZ ((re.val[26]!).values.val[l + 2]!).val
         else liftZ ((re.val[26]!).values.val[l - 2]!).val
            - zeta (2 * 26 + l / 4 + 64) * liftZ ((re.val[26]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 26 + 0 / 4 + 64) = 116 from by decide, zeta1_bridge26, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 26 + 1 / 4 + 64) = 116 from by decide, zeta1_bridge26, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 26 + 2 / 4 + 64) = 116 from by decide, zeta1_bridge26, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 26 + 3 / 4 + 64) = 116 from by decide, zeta1_bridge26, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 26 + 4 / 4 + 64) = 117 from by decide, zeta1b_bridge26, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 26 + 5 / 4 + 64) = 117 from by decide, zeta1b_bridge26, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 26 + 6 / 4 + 64) = 117 from by decide, zeta1b_bridge26, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 26 + 7 / 4 + 64) = 117 from by decide, zeta1b_bridge26, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[27]!).values.val[l]!).val
            + zeta (2 * 27 + l / 4 + 64) * liftZ ((re.val[27]!).values.val[l + 2]!).val
         else liftZ ((re.val[27]!).values.val[l - 2]!).val
            - zeta (2 * 27 + l / 4 + 64) * liftZ ((re.val[27]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 27 + 0 / 4 + 64) = 118 from by decide, zeta1_bridge27, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 27 + 1 / 4 + 64) = 118 from by decide, zeta1_bridge27, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 27 + 2 / 4 + 64) = 118 from by decide, zeta1_bridge27, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 27 + 3 / 4 + 64) = 118 from by decide, zeta1_bridge27, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 27 + 4 / 4 + 64) = 119 from by decide, zeta1b_bridge27, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 27 + 5 / 4 + 64) = 119 from by decide, zeta1b_bridge27, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 27 + 6 / 4 + 64) = 119 from by decide, zeta1b_bridge27, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 27 + 7 / 4 + 64) = 119 from by decide, zeta1b_bridge27, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[28]!).values.val[l]!).val
            + zeta (2 * 28 + l / 4 + 64) * liftZ ((re.val[28]!).values.val[l + 2]!).val
         else liftZ ((re.val[28]!).values.val[l - 2]!).val
            - zeta (2 * 28 + l / 4 + 64) * liftZ ((re.val[28]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 28 + 0 / 4 + 64) = 120 from by decide, zeta1_bridge28, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 28 + 1 / 4 + 64) = 120 from by decide, zeta1_bridge28, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 28 + 2 / 4 + 64) = 120 from by decide, zeta1_bridge28, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 28 + 3 / 4 + 64) = 120 from by decide, zeta1_bridge28, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 28 + 4 / 4 + 64) = 121 from by decide, zeta1b_bridge28, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 28 + 5 / 4 + 64) = 121 from by decide, zeta1b_bridge28, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 28 + 6 / 4 + 64) = 121 from by decide, zeta1b_bridge28, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 28 + 7 / 4 + 64) = 121 from by decide, zeta1b_bridge28, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[29]!).values.val[l]!).val
            + zeta (2 * 29 + l / 4 + 64) * liftZ ((re.val[29]!).values.val[l + 2]!).val
         else liftZ ((re.val[29]!).values.val[l - 2]!).val
            - zeta (2 * 29 + l / 4 + 64) * liftZ ((re.val[29]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 29 + 0 / 4 + 64) = 122 from by decide, zeta1_bridge29, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 29 + 1 / 4 + 64) = 122 from by decide, zeta1_bridge29, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 29 + 2 / 4 + 64) = 122 from by decide, zeta1_bridge29, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 29 + 3 / 4 + 64) = 122 from by decide, zeta1_bridge29, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 29 + 4 / 4 + 64) = 123 from by decide, zeta1b_bridge29, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 29 + 5 / 4 + 64) = 123 from by decide, zeta1b_bridge29, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 29 + 6 / 4 + 64) = 123 from by decide, zeta1b_bridge29, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 29 + 7 / 4 + 64) = 123 from by decide, zeta1b_bridge29, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[30]!).values.val[l]!).val
            + zeta (2 * 30 + l / 4 + 64) * liftZ ((re.val[30]!).values.val[l + 2]!).val
         else liftZ ((re.val[30]!).values.val[l - 2]!).val
            - zeta (2 * 30 + l / 4 + 64) * liftZ ((re.val[30]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 30 + 0 / 4 + 64) = 124 from by decide, zeta1_bridge30, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 30 + 1 / 4 + 64) = 124 from by decide, zeta1_bridge30, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 30 + 2 / 4 + 64) = 124 from by decide, zeta1_bridge30, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 30 + 3 / 4 + 64) = 124 from by decide, zeta1_bridge30, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 30 + 4 / 4 + 64) = 125 from by decide, zeta1b_bridge30, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 30 + 5 / 4 + 64) = 125 from by decide, zeta1b_bridge30, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 30 + 6 / 4 + 64) = 125 from by decide, zeta1b_bridge30, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 30 + 7 / 4 + 64) = 125 from by decide, zeta1b_bridge30, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[31]!).values.val[l]!).val
            + zeta (2 * 31 + l / 4 + 64) * liftZ ((re.val[31]!).values.val[l + 2]!).val
         else liftZ ((re.val[31]!).values.val[l - 2]!).val
            - zeta (2 * 31 + l / 4 + 64) * liftZ ((re.val[31]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (2 * 31 + 0 / 4 + 64) = 126 from by decide, zeta1_bridge31, mul_comm]
    | 1, _ => rw [if_pos (by decide), b1]; rw [show (2 * 31 + 1 / 4 + 64) = 126 from by decide, zeta1_bridge31, mul_comm]
    | 2, _ => rw [if_neg (by decide), b2]; rw [show (2 * 31 + 2 / 4 + 64) = 126 from by decide, zeta1_bridge31, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (2 * 31 + 3 / 4 + 64) = 126 from by decide, zeta1_bridge31, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (2 * 31 + 4 / 4 + 64) = 127 from by decide, zeta1b_bridge31, mul_comm]
    | 5, _ => rw [if_pos (by decide), b5]; rw [show (2 * 31 + 5 / 4 + 64) = 127 from by decide, zeta1b_bridge31, mul_comm]
    | 6, _ => rw [if_neg (by decide), b6]; rw [show (2 * 31 + 6 / 4 + 64) = 127 from by decide, zeta1b_bridge31, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (2 * 31 + 7 / 4 + 64) = 127 from by decide, zeta1b_bridge31, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l % 4 < 2 then liftZ ((re.val[u]!).values.val[l]!).val
            + zeta (2 * u + l / 4 + 64) * liftZ ((re.val[u]!).values.val[l + 2]!).val
         else liftZ ((re.val[u]!).values.val[l - 2]!).val
            - zeta (2 * u + l / 4 + 64) * liftZ ((re.val[u]!).values.val[l]!).val) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 4 < 2
    · have hcond : i % 8 % 4 < 2 := by omega
      rw [if_pos hlt]
      rw [if_pos hcond] at hb
      have hdiv : (i + 2) / 8 = i / 8 := by omega
      have hmod : (i + 2) % 8 = i % 8 + 2 := by omega
      have hidx2 : i + 2 < 256 := by omega
      have hz : 2 * (i / 8) + i % 8 / 4 + 64 = i / 4 + 64 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 2) hidx2, hdiv, hmod]
      rw [hz] at hb
      exact hb
    · have hcond : ¬ i % 8 % 4 < 2 := by omega
      rw [if_neg hlt]
      rw [if_neg hcond] at hb
      have hdiv : (i - 2) / 8 = i / 8 := by omega
      have hmod : (i - 2) % 8 = i % 8 - 2 := by omega
      have hidx2 : i - 2 < 256 := by omega
      have hz : 2 * (i / 8) + i % 8 / 4 + 64 = i / 4 + 64 := by omega
      rw [Pure.build_getElem _ (i - 2) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      rw [hz] at hb
      exact hb
  · exact hbnd




/-! ### Layer-0 within-unit forward driver `ntt_at_layer_0_fc`.

    `ntt_at_layer_0` chains 32 `round` calls; round `u` reads unit `u`, applies the
    per-unit butterfly `simd_unit_ntt_at_layer_0 _ Z0 Z1 Z2 Z3` (adjacent pairs
    (0,1)(2,3)(4,5)(6,7), even lane = low, odd lane = high), and writes unit `u`
    back (touching ONLY unit `u`). The lifted result equals
    `ntt_layer (lift_units re) 0` (`len = 1`, `k = 128`; within each unit four
    sub-rounds, lane split at `l % 2 < 1`, zetas `zeta (128 + 4u + p)`). Uniform
    bound `B + 2^24`. -/

set_option maxRecDepth 4000 in
private theorem zeta0_bridge0_0 :
    liftZ ((2091667#i32 : Std.I32).val : Int) = zeta 128 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge0_1 :
    liftZ ((3407706#i32 : Std.I32).val : Int) = zeta 129 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge0_2 :
    liftZ ((2316500#i32 : Std.I32).val : Int) = zeta 130 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge0_3 :
    liftZ ((3817976#i32 : Std.I32).val : Int) = zeta 131 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge1_0 :
    liftZ (((-3342478)#i32 : Std.I32).val : Int) = zeta 132 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge1_1 :
    liftZ ((2244091#i32 : Std.I32).val : Int) = zeta 133 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge1_2 :
    liftZ (((-2446433)#i32 : Std.I32).val : Int) = zeta 134 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge1_3 :
    liftZ (((-3562462)#i32 : Std.I32).val : Int) = zeta 135 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge2_0 :
    liftZ ((266997#i32 : Std.I32).val : Int) = zeta 136 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge2_1 :
    liftZ ((2434439#i32 : Std.I32).val : Int) = zeta 137 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge2_2 :
    liftZ (((-1235728)#i32 : Std.I32).val : Int) = zeta 138 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge2_3 :
    liftZ ((3513181#i32 : Std.I32).val : Int) = zeta 139 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge3_0 :
    liftZ (((-3520352)#i32 : Std.I32).val : Int) = zeta 140 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge3_1 :
    liftZ (((-3759364)#i32 : Std.I32).val : Int) = zeta 141 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge3_2 :
    liftZ (((-1197226)#i32 : Std.I32).val : Int) = zeta 142 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge3_3 :
    liftZ (((-3193378)#i32 : Std.I32).val : Int) = zeta 143 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge4_0 :
    liftZ ((900702#i32 : Std.I32).val : Int) = zeta 144 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge4_1 :
    liftZ ((1859098#i32 : Std.I32).val : Int) = zeta 145 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge4_2 :
    liftZ ((909542#i32 : Std.I32).val : Int) = zeta 146 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge4_3 :
    liftZ ((819034#i32 : Std.I32).val : Int) = zeta 147 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge5_0 :
    liftZ ((495491#i32 : Std.I32).val : Int) = zeta 148 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge5_1 :
    liftZ (((-1613174)#i32 : Std.I32).val : Int) = zeta 149 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge5_2 :
    liftZ (((-43260)#i32 : Std.I32).val : Int) = zeta 150 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge5_3 :
    liftZ (((-522500)#i32 : Std.I32).val : Int) = zeta 151 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge6_0 :
    liftZ (((-655327)#i32 : Std.I32).val : Int) = zeta 152 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge6_1 :
    liftZ (((-3122442)#i32 : Std.I32).val : Int) = zeta 153 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge6_2 :
    liftZ ((2031748#i32 : Std.I32).val : Int) = zeta 154 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge6_3 :
    liftZ ((3207046#i32 : Std.I32).val : Int) = zeta 155 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge7_0 :
    liftZ (((-3556995)#i32 : Std.I32).val : Int) = zeta 156 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge7_1 :
    liftZ (((-525098)#i32 : Std.I32).val : Int) = zeta 157 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge7_2 :
    liftZ (((-768622)#i32 : Std.I32).val : Int) = zeta 158 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge7_3 :
    liftZ (((-3595838)#i32 : Std.I32).val : Int) = zeta 159 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge8_0 :
    liftZ ((342297#i32 : Std.I32).val : Int) = zeta 160 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge8_1 :
    liftZ ((286988#i32 : Std.I32).val : Int) = zeta 161 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge8_2 :
    liftZ (((-2437823)#i32 : Std.I32).val : Int) = zeta 162 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge8_3 :
    liftZ ((4108315#i32 : Std.I32).val : Int) = zeta 163 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge9_0 :
    liftZ ((3437287#i32 : Std.I32).val : Int) = zeta 164 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge9_1 :
    liftZ (((-3342277)#i32 : Std.I32).val : Int) = zeta 165 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge9_2 :
    liftZ ((1735879#i32 : Std.I32).val : Int) = zeta 166 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge9_3 :
    liftZ ((203044#i32 : Std.I32).val : Int) = zeta 167 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge10_0 :
    liftZ ((2842341#i32 : Std.I32).val : Int) = zeta 168 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge10_1 :
    liftZ ((2691481#i32 : Std.I32).val : Int) = zeta 169 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge10_2 :
    liftZ (((-2590150)#i32 : Std.I32).val : Int) = zeta 170 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge10_3 :
    liftZ ((1265009#i32 : Std.I32).val : Int) = zeta 171 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge11_0 :
    liftZ ((4055324#i32 : Std.I32).val : Int) = zeta 172 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge11_1 :
    liftZ ((1247620#i32 : Std.I32).val : Int) = zeta 173 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge11_2 :
    liftZ ((2486353#i32 : Std.I32).val : Int) = zeta 174 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge11_3 :
    liftZ ((1595974#i32 : Std.I32).val : Int) = zeta 175 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge12_0 :
    liftZ (((-3767016)#i32 : Std.I32).val : Int) = zeta 176 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge12_1 :
    liftZ ((1250494#i32 : Std.I32).val : Int) = zeta 177 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge12_2 :
    liftZ ((2635921#i32 : Std.I32).val : Int) = zeta 178 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge12_3 :
    liftZ (((-3548272)#i32 : Std.I32).val : Int) = zeta 179 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge13_0 :
    liftZ (((-2994039)#i32 : Std.I32).val : Int) = zeta 180 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge13_1 :
    liftZ ((1869119#i32 : Std.I32).val : Int) = zeta 181 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge13_2 :
    liftZ ((1903435#i32 : Std.I32).val : Int) = zeta 182 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge13_3 :
    liftZ (((-1050970)#i32 : Std.I32).val : Int) = zeta 183 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge14_0 :
    liftZ (((-1333058)#i32 : Std.I32).val : Int) = zeta 184 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge14_1 :
    liftZ ((1237275#i32 : Std.I32).val : Int) = zeta 185 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge14_2 :
    liftZ (((-3318210)#i32 : Std.I32).val : Int) = zeta 186 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge14_3 :
    liftZ (((-1430225)#i32 : Std.I32).val : Int) = zeta 187 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge15_0 :
    liftZ (((-451100)#i32 : Std.I32).val : Int) = zeta 188 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge15_1 :
    liftZ ((1312455#i32 : Std.I32).val : Int) = zeta 189 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge15_2 :
    liftZ ((3306115#i32 : Std.I32).val : Int) = zeta 190 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge15_3 :
    liftZ (((-1962642)#i32 : Std.I32).val : Int) = zeta 191 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge16_0 :
    liftZ (((-1279661)#i32 : Std.I32).val : Int) = zeta 192 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge16_1 :
    liftZ ((1917081#i32 : Std.I32).val : Int) = zeta 193 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge16_2 :
    liftZ (((-2546312)#i32 : Std.I32).val : Int) = zeta 194 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge16_3 :
    liftZ (((-1374803)#i32 : Std.I32).val : Int) = zeta 195 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge17_0 :
    liftZ ((1500165#i32 : Std.I32).val : Int) = zeta 196 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge17_1 :
    liftZ ((777191#i32 : Std.I32).val : Int) = zeta 197 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge17_2 :
    liftZ ((2235880#i32 : Std.I32).val : Int) = zeta 198 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge17_3 :
    liftZ ((3406031#i32 : Std.I32).val : Int) = zeta 199 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge18_0 :
    liftZ (((-542412)#i32 : Std.I32).val : Int) = zeta 200 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge18_1 :
    liftZ (((-2831860)#i32 : Std.I32).val : Int) = zeta 201 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge18_2 :
    liftZ (((-1671176)#i32 : Std.I32).val : Int) = zeta 202 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge18_3 :
    liftZ (((-1846953)#i32 : Std.I32).val : Int) = zeta 203 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge19_0 :
    liftZ (((-2584293)#i32 : Std.I32).val : Int) = zeta 204 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge19_1 :
    liftZ (((-3724270)#i32 : Std.I32).val : Int) = zeta 205 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge19_2 :
    liftZ ((594136#i32 : Std.I32).val : Int) = zeta 206 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge19_3 :
    liftZ (((-3776993)#i32 : Std.I32).val : Int) = zeta 207 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge20_0 :
    liftZ (((-2013608)#i32 : Std.I32).val : Int) = zeta 208 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge20_1 :
    liftZ ((2432395#i32 : Std.I32).val : Int) = zeta 209 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge20_2 :
    liftZ ((2454455#i32 : Std.I32).val : Int) = zeta 210 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge20_3 :
    liftZ (((-164721)#i32 : Std.I32).val : Int) = zeta 211 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge21_0 :
    liftZ ((1957272#i32 : Std.I32).val : Int) = zeta 212 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge21_1 :
    liftZ ((3369112#i32 : Std.I32).val : Int) = zeta 213 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge21_2 :
    liftZ ((185531#i32 : Std.I32).val : Int) = zeta 214 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge21_3 :
    liftZ (((-1207385)#i32 : Std.I32).val : Int) = zeta 215 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge22_0 :
    liftZ (((-3183426)#i32 : Std.I32).val : Int) = zeta 216 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge22_1 :
    liftZ ((162844#i32 : Std.I32).val : Int) = zeta 217 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge22_2 :
    liftZ ((1616392#i32 : Std.I32).val : Int) = zeta 218 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge22_3 :
    liftZ ((3014001#i32 : Std.I32).val : Int) = zeta 219 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge23_0 :
    liftZ ((810149#i32 : Std.I32).val : Int) = zeta 220 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge23_1 :
    liftZ ((1652634#i32 : Std.I32).val : Int) = zeta 221 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge23_2 :
    liftZ (((-3694233)#i32 : Std.I32).val : Int) = zeta 222 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge23_3 :
    liftZ (((-1799107)#i32 : Std.I32).val : Int) = zeta 223 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge24_0 :
    liftZ (((-3038916)#i32 : Std.I32).val : Int) = zeta 224 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge24_1 :
    liftZ ((3523897#i32 : Std.I32).val : Int) = zeta 225 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge24_2 :
    liftZ ((3866901#i32 : Std.I32).val : Int) = zeta 226 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge24_3 :
    liftZ ((269760#i32 : Std.I32).val : Int) = zeta 227 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge25_0 :
    liftZ ((2213111#i32 : Std.I32).val : Int) = zeta 228 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge25_1 :
    liftZ (((-975884)#i32 : Std.I32).val : Int) = zeta 229 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge25_2 :
    liftZ ((1717735#i32 : Std.I32).val : Int) = zeta 230 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge25_3 :
    liftZ ((472078#i32 : Std.I32).val : Int) = zeta 231 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge26_0 :
    liftZ (((-426683)#i32 : Std.I32).val : Int) = zeta 232 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge26_1 :
    liftZ ((1723600#i32 : Std.I32).val : Int) = zeta 233 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge26_2 :
    liftZ (((-1803090)#i32 : Std.I32).val : Int) = zeta 234 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge26_3 :
    liftZ ((1910376#i32 : Std.I32).val : Int) = zeta 235 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge27_0 :
    liftZ (((-1667432)#i32 : Std.I32).val : Int) = zeta 236 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge27_1 :
    liftZ (((-1104333)#i32 : Std.I32).val : Int) = zeta 237 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge27_2 :
    liftZ (((-260646)#i32 : Std.I32).val : Int) = zeta 238 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge27_3 :
    liftZ (((-3833893)#i32 : Std.I32).val : Int) = zeta 239 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge28_0 :
    liftZ (((-2939036)#i32 : Std.I32).val : Int) = zeta 240 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge28_1 :
    liftZ (((-2235985)#i32 : Std.I32).val : Int) = zeta 241 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge28_2 :
    liftZ (((-420899)#i32 : Std.I32).val : Int) = zeta 242 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge28_3 :
    liftZ (((-2286327)#i32 : Std.I32).val : Int) = zeta 243 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge29_0 :
    liftZ ((183443#i32 : Std.I32).val : Int) = zeta 244 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge29_1 :
    liftZ (((-976891)#i32 : Std.I32).val : Int) = zeta 245 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge29_2 :
    liftZ ((1612842#i32 : Std.I32).val : Int) = zeta 246 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge29_3 :
    liftZ (((-3545687)#i32 : Std.I32).val : Int) = zeta 247 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge30_0 :
    liftZ (((-554416)#i32 : Std.I32).val : Int) = zeta 248 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge30_1 :
    liftZ ((3919660#i32 : Std.I32).val : Int) = zeta 249 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge30_2 :
    liftZ (((-48306)#i32 : Std.I32).val : Int) = zeta 250 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge30_3 :
    liftZ (((-1362209)#i32 : Std.I32).val : Int) = zeta 251 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge31_0 :
    liftZ ((3937738#i32 : Std.I32).val : Int) = zeta 252 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge31_1 :
    liftZ ((1400424#i32 : Std.I32).val : Int) = zeta 253 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge31_2 :
    liftZ (((-846154)#i32 : Std.I32).val : Int) = zeta 254 := by decide
set_option maxRecDepth 4000 in
private theorem zeta0_bridge31_3 :
    liftZ ((1976782#i32 : Std.I32).val : Int) = zeta 255 := by decide
private theorem zeta0_mag0_0 : (2091667#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag0_1 : (3407706#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag0_2 : (2316500#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag0_3 : (3817976#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag1_0 : ((-3342478)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag1_1 : (2244091#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag1_2 : ((-2446433)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag1_3 : ((-3562462)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag2_0 : (266997#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag2_1 : (2434439#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag2_2 : ((-1235728)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag2_3 : (3513181#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag3_0 : ((-3520352)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag3_1 : ((-3759364)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag3_2 : ((-1197226)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag3_3 : ((-3193378)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag4_0 : (900702#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag4_1 : (1859098#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag4_2 : (909542#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag4_3 : (819034#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag5_0 : (495491#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag5_1 : ((-1613174)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag5_2 : ((-43260)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag5_3 : ((-522500)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag6_0 : ((-655327)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag6_1 : ((-3122442)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag6_2 : (2031748#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag6_3 : (3207046#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag7_0 : ((-3556995)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag7_1 : ((-525098)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag7_2 : ((-768622)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag7_3 : ((-3595838)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag8_0 : (342297#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag8_1 : (286988#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag8_2 : ((-2437823)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag8_3 : (4108315#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag9_0 : (3437287#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag9_1 : ((-3342277)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag9_2 : (1735879#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag9_3 : (203044#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag10_0 : (2842341#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag10_1 : (2691481#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag10_2 : ((-2590150)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag10_3 : (1265009#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag11_0 : (4055324#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag11_1 : (1247620#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag11_2 : (2486353#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag11_3 : (1595974#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag12_0 : ((-3767016)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag12_1 : (1250494#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag12_2 : (2635921#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag12_3 : ((-3548272)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag13_0 : ((-2994039)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag13_1 : (1869119#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag13_2 : (1903435#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag13_3 : ((-1050970)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag14_0 : ((-1333058)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag14_1 : (1237275#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag14_2 : ((-3318210)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag14_3 : ((-1430225)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag15_0 : ((-451100)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag15_1 : (1312455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag15_2 : (3306115#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag15_3 : ((-1962642)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag16_0 : ((-1279661)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag16_1 : (1917081#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag16_2 : ((-2546312)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag16_3 : ((-1374803)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag17_0 : (1500165#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag17_1 : (777191#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag17_2 : (2235880#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag17_3 : (3406031#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag18_0 : ((-542412)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag18_1 : ((-2831860)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag18_2 : ((-1671176)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag18_3 : ((-1846953)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag19_0 : ((-2584293)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag19_1 : ((-3724270)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag19_2 : (594136#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag19_3 : ((-3776993)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag20_0 : ((-2013608)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag20_1 : (2432395#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag20_2 : (2454455#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag20_3 : ((-164721)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag21_0 : (1957272#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag21_1 : (3369112#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag21_2 : (185531#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag21_3 : ((-1207385)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag22_0 : ((-3183426)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag22_1 : (162844#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag22_2 : (1616392#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag22_3 : (3014001#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag23_0 : (810149#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag23_1 : (1652634#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag23_2 : ((-3694233)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag23_3 : ((-1799107)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag24_0 : ((-3038916)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag24_1 : (3523897#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag24_2 : (3866901#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag24_3 : (269760#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag25_0 : (2213111#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag25_1 : ((-975884)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag25_2 : (1717735#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag25_3 : (472078#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag26_0 : ((-426683)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag26_1 : (1723600#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag26_2 : ((-1803090)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag26_3 : (1910376#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag27_0 : ((-1667432)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag27_1 : ((-1104333)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag27_2 : ((-260646)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag27_3 : ((-3833893)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag28_0 : ((-2939036)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag28_1 : ((-2235985)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag28_2 : ((-420899)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag28_3 : ((-2286327)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag29_0 : (183443#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag29_1 : ((-976891)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag29_2 : (1612842#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag29_3 : ((-3545687)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag30_0 : ((-554416)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag30_1 : (3919660#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag30_2 : ((-48306)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag30_3 : ((-1362209)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag31_0 : (3937738#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag31_1 : (1400424#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag31_2 : ((-846154)#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide
private theorem zeta0_mag31_3 : (1976782#i32 : Std.I32).val.natAbs ≤ 8380416 := by decide

/-- One `round` of layer 0: read unit `k`, apply the per-unit butterfly with the
    four zetas (adjacent pairs (0,1)(2,3)(4,5)(6,7)), write unit `k` back. -/
private theorem round0_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (k : Nat) (hk : k < 32) (zeta0 zeta1 zeta2 zeta3 : Std.I32) (B : Nat)
    (hz0 : zeta0.val.natAbs ≤ 8380416) (hz1 : zeta1.val.natAbs ≤ 8380416)
    (hz2 : zeta2.val.natAbs ≤ 8380416) (hz3 : zeta3.val.natAbs ≤ 8380416)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ l : Nat, l < 8 → ((re.val[k]!).values.val[l]!).val.natAbs ≤ B) :
    ∃ out, libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_0.round re k#usize zeta0 zeta1 zeta2 zeta3 = .ok out
      ∧ (liftZ ((out.val[k]!).values.val[0]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val + liftZ ((re.val[k]!).values.val[1]!).val * liftZ zeta0.val
        ∧ liftZ ((out.val[k]!).values.val[1]!).val
            = liftZ ((re.val[k]!).values.val[0]!).val - liftZ ((re.val[k]!).values.val[1]!).val * liftZ zeta0.val
        ∧ liftZ ((out.val[k]!).values.val[2]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val + liftZ ((re.val[k]!).values.val[3]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[3]!).val
            = liftZ ((re.val[k]!).values.val[2]!).val - liftZ ((re.val[k]!).values.val[3]!).val * liftZ zeta1.val
        ∧ liftZ ((out.val[k]!).values.val[4]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val + liftZ ((re.val[k]!).values.val[5]!).val * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[5]!).val
            = liftZ ((re.val[k]!).values.val[4]!).val - liftZ ((re.val[k]!).values.val[5]!).val * liftZ zeta2.val
        ∧ liftZ ((out.val[k]!).values.val[6]!).val
            = liftZ ((re.val[k]!).values.val[6]!).val + liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta3.val
        ∧ liftZ ((out.val[k]!).values.val[7]!).val
            = liftZ ((re.val[k]!).values.val[6]!).val - liftZ ((re.val[k]!).values.val[7]!).val * liftZ zeta3.val
        )
      ∧ (∀ u : Nat, u < 32 → u ≠ k → out.val[u]! = re.val[u]!)
      ∧ (∀ l : Nat, l < 8 → ((out.val[k]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24) := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_0.round
  have hre_len : re.length = 32 := Std.Array.length_eq _
  have hk_len : (k#usize : Std.Usize).val < re.length := by
    rw [hre_len]; simpa using hk
  have h_idx : Array.index_usize re k#usize = .ok (re.val[k]!) :=
    array_index_usize_ok_eq re k#usize hk_len
  set ak : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients :=
    re.val[k]! with hak
  have h_imt : Array.index_mut_usize re k#usize = .ok (ak, re.set k#usize) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_idx]; rfl
  obtain ⟨c1, hc1_eq, hc1_butter, hc1_bd⟩ :=
    triple_exists_ok (simd_unit_ntt_at_layer_0_fc ak zeta0 zeta1 zeta2 zeta3 B hz0 hz1 hz2 hz3 hB hin)
  have hset_k : (re.set k#usize c1).val[k]! = c1 := by
    rw [← Std.Array.getElem!_Nat_eq]
    exact Std.Array.getElem!_Nat_set_eq re k#usize k c1 ⟨rfl, by rw [hre_len]; exact hk⟩
  refine ⟨re.set k#usize c1, ?_, ?_, ?_, ?_⟩
  · simp [Aeneas.Std.bind_tc_ok, h_imt, hc1_eq]
  · rw [hset_k]; exact hc1_butter
  · intro u hu hne
    rw [← Std.Array.getElem!_Nat_eq, ← Std.Array.getElem!_Nat_eq (v := re)]
    exact Std.Array.getElem!_Nat_set_ne re k#usize u c1 (fun h => hne h.symm)
  · intro l hl
    rw [hset_k]; exact hc1_bd l hl

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_0_fc
    (re : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize)
    (B : Nat)
    (hB : (B : Int) + 2 ^ 24 ≤ 2 ^ 31 - 1)
    (hin : ∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
        (re.val[u]!).values.val[l]!.val.natAbs ≤ B) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_0 re
    ⦃ ⇓ r => ⌜ lift_units r = Pure.ntt_layer (lift_units re) 0
             ∧ (∀ u : Nat, u < 32 → ∀ l : Nat, l < 8 →
                  (r.val[u]!).values.val[l]!.val.natAbs ≤ B + 2 ^ 24) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.ntt.ntt_at_layer_0
  have hkeep0 : ∀ u, 0 ≤ u → u < 32 → re.val[u]! = re.val[u]! := fun u _ _ => rfl
  obtain ⟨r1, hr1_eq, hbut0, hfr0, hbd0⟩ :=
    round0_fc re 0 (by decide) (2091667#i32) (3407706#i32) (2316500#i32) (3817976#i32) B (zeta0_mag0_0) (zeta0_mag0_1) (zeta0_mag0_2) (zeta0_mag0_3) hB
      (fun l hl => by rw [hkeep0 0 (by omega) (by omega)]; exact hin 0 (by decide) l hl)
  have hkeep1 : ∀ u, 1 ≤ u → u < 32 → r1.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr0 u hu2 (by omega), hkeep0 u (by omega) hu2]
  obtain ⟨r2, hr2_eq, hbut1, hfr1, hbd1⟩ :=
    round0_fc r1 1 (by decide) ((-3342478)#i32) (2244091#i32) ((-2446433)#i32) ((-3562462)#i32) B (zeta0_mag1_0) (zeta0_mag1_1) (zeta0_mag1_2) (zeta0_mag1_3) hB
      (fun l hl => by rw [hkeep1 1 (by omega) (by omega)]; exact hin 1 (by decide) l hl)
  have hkeep2 : ∀ u, 2 ≤ u → u < 32 → r2.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr1 u hu2 (by omega), hkeep1 u (by omega) hu2]
  obtain ⟨r3, hr3_eq, hbut2, hfr2, hbd2⟩ :=
    round0_fc r2 2 (by decide) (266997#i32) (2434439#i32) ((-1235728)#i32) (3513181#i32) B (zeta0_mag2_0) (zeta0_mag2_1) (zeta0_mag2_2) (zeta0_mag2_3) hB
      (fun l hl => by rw [hkeep2 2 (by omega) (by omega)]; exact hin 2 (by decide) l hl)
  have hkeep3 : ∀ u, 3 ≤ u → u < 32 → r3.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr2 u hu2 (by omega), hkeep2 u (by omega) hu2]
  obtain ⟨r4, hr4_eq, hbut3, hfr3, hbd3⟩ :=
    round0_fc r3 3 (by decide) ((-3520352)#i32) ((-3759364)#i32) ((-1197226)#i32) ((-3193378)#i32) B (zeta0_mag3_0) (zeta0_mag3_1) (zeta0_mag3_2) (zeta0_mag3_3) hB
      (fun l hl => by rw [hkeep3 3 (by omega) (by omega)]; exact hin 3 (by decide) l hl)
  have hkeep4 : ∀ u, 4 ≤ u → u < 32 → r4.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr3 u hu2 (by omega), hkeep3 u (by omega) hu2]
  obtain ⟨r5, hr5_eq, hbut4, hfr4, hbd4⟩ :=
    round0_fc r4 4 (by decide) (900702#i32) (1859098#i32) (909542#i32) (819034#i32) B (zeta0_mag4_0) (zeta0_mag4_1) (zeta0_mag4_2) (zeta0_mag4_3) hB
      (fun l hl => by rw [hkeep4 4 (by omega) (by omega)]; exact hin 4 (by decide) l hl)
  have hkeep5 : ∀ u, 5 ≤ u → u < 32 → r5.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr4 u hu2 (by omega), hkeep4 u (by omega) hu2]
  obtain ⟨r6, hr6_eq, hbut5, hfr5, hbd5⟩ :=
    round0_fc r5 5 (by decide) (495491#i32) ((-1613174)#i32) ((-43260)#i32) ((-522500)#i32) B (zeta0_mag5_0) (zeta0_mag5_1) (zeta0_mag5_2) (zeta0_mag5_3) hB
      (fun l hl => by rw [hkeep5 5 (by omega) (by omega)]; exact hin 5 (by decide) l hl)
  have hkeep6 : ∀ u, 6 ≤ u → u < 32 → r6.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr5 u hu2 (by omega), hkeep5 u (by omega) hu2]
  obtain ⟨r7, hr7_eq, hbut6, hfr6, hbd6⟩ :=
    round0_fc r6 6 (by decide) ((-655327)#i32) ((-3122442)#i32) (2031748#i32) (3207046#i32) B (zeta0_mag6_0) (zeta0_mag6_1) (zeta0_mag6_2) (zeta0_mag6_3) hB
      (fun l hl => by rw [hkeep6 6 (by omega) (by omega)]; exact hin 6 (by decide) l hl)
  have hkeep7 : ∀ u, 7 ≤ u → u < 32 → r7.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr6 u hu2 (by omega), hkeep6 u (by omega) hu2]
  obtain ⟨r8, hr8_eq, hbut7, hfr7, hbd7⟩ :=
    round0_fc r7 7 (by decide) ((-3556995)#i32) ((-525098)#i32) ((-768622)#i32) ((-3595838)#i32) B (zeta0_mag7_0) (zeta0_mag7_1) (zeta0_mag7_2) (zeta0_mag7_3) hB
      (fun l hl => by rw [hkeep7 7 (by omega) (by omega)]; exact hin 7 (by decide) l hl)
  have hkeep8 : ∀ u, 8 ≤ u → u < 32 → r8.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr7 u hu2 (by omega), hkeep7 u (by omega) hu2]
  obtain ⟨r9, hr9_eq, hbut8, hfr8, hbd8⟩ :=
    round0_fc r8 8 (by decide) (342297#i32) (286988#i32) ((-2437823)#i32) (4108315#i32) B (zeta0_mag8_0) (zeta0_mag8_1) (zeta0_mag8_2) (zeta0_mag8_3) hB
      (fun l hl => by rw [hkeep8 8 (by omega) (by omega)]; exact hin 8 (by decide) l hl)
  have hkeep9 : ∀ u, 9 ≤ u → u < 32 → r9.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr8 u hu2 (by omega), hkeep8 u (by omega) hu2]
  obtain ⟨r10, hr10_eq, hbut9, hfr9, hbd9⟩ :=
    round0_fc r9 9 (by decide) (3437287#i32) ((-3342277)#i32) (1735879#i32) (203044#i32) B (zeta0_mag9_0) (zeta0_mag9_1) (zeta0_mag9_2) (zeta0_mag9_3) hB
      (fun l hl => by rw [hkeep9 9 (by omega) (by omega)]; exact hin 9 (by decide) l hl)
  have hkeep10 : ∀ u, 10 ≤ u → u < 32 → r10.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr9 u hu2 (by omega), hkeep9 u (by omega) hu2]
  obtain ⟨r11, hr11_eq, hbut10, hfr10, hbd10⟩ :=
    round0_fc r10 10 (by decide) (2842341#i32) (2691481#i32) ((-2590150)#i32) (1265009#i32) B (zeta0_mag10_0) (zeta0_mag10_1) (zeta0_mag10_2) (zeta0_mag10_3) hB
      (fun l hl => by rw [hkeep10 10 (by omega) (by omega)]; exact hin 10 (by decide) l hl)
  have hkeep11 : ∀ u, 11 ≤ u → u < 32 → r11.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr10 u hu2 (by omega), hkeep10 u (by omega) hu2]
  obtain ⟨r12, hr12_eq, hbut11, hfr11, hbd11⟩ :=
    round0_fc r11 11 (by decide) (4055324#i32) (1247620#i32) (2486353#i32) (1595974#i32) B (zeta0_mag11_0) (zeta0_mag11_1) (zeta0_mag11_2) (zeta0_mag11_3) hB
      (fun l hl => by rw [hkeep11 11 (by omega) (by omega)]; exact hin 11 (by decide) l hl)
  have hkeep12 : ∀ u, 12 ≤ u → u < 32 → r12.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr11 u hu2 (by omega), hkeep11 u (by omega) hu2]
  obtain ⟨r13, hr13_eq, hbut12, hfr12, hbd12⟩ :=
    round0_fc r12 12 (by decide) ((-3767016)#i32) (1250494#i32) (2635921#i32) ((-3548272)#i32) B (zeta0_mag12_0) (zeta0_mag12_1) (zeta0_mag12_2) (zeta0_mag12_3) hB
      (fun l hl => by rw [hkeep12 12 (by omega) (by omega)]; exact hin 12 (by decide) l hl)
  have hkeep13 : ∀ u, 13 ≤ u → u < 32 → r13.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr12 u hu2 (by omega), hkeep12 u (by omega) hu2]
  obtain ⟨r14, hr14_eq, hbut13, hfr13, hbd13⟩ :=
    round0_fc r13 13 (by decide) ((-2994039)#i32) (1869119#i32) (1903435#i32) ((-1050970)#i32) B (zeta0_mag13_0) (zeta0_mag13_1) (zeta0_mag13_2) (zeta0_mag13_3) hB
      (fun l hl => by rw [hkeep13 13 (by omega) (by omega)]; exact hin 13 (by decide) l hl)
  have hkeep14 : ∀ u, 14 ≤ u → u < 32 → r14.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr13 u hu2 (by omega), hkeep13 u (by omega) hu2]
  obtain ⟨r15, hr15_eq, hbut14, hfr14, hbd14⟩ :=
    round0_fc r14 14 (by decide) ((-1333058)#i32) (1237275#i32) ((-3318210)#i32) ((-1430225)#i32) B (zeta0_mag14_0) (zeta0_mag14_1) (zeta0_mag14_2) (zeta0_mag14_3) hB
      (fun l hl => by rw [hkeep14 14 (by omega) (by omega)]; exact hin 14 (by decide) l hl)
  have hkeep15 : ∀ u, 15 ≤ u → u < 32 → r15.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr14 u hu2 (by omega), hkeep14 u (by omega) hu2]
  obtain ⟨r16, hr16_eq, hbut15, hfr15, hbd15⟩ :=
    round0_fc r15 15 (by decide) ((-451100)#i32) (1312455#i32) (3306115#i32) ((-1962642)#i32) B (zeta0_mag15_0) (zeta0_mag15_1) (zeta0_mag15_2) (zeta0_mag15_3) hB
      (fun l hl => by rw [hkeep15 15 (by omega) (by omega)]; exact hin 15 (by decide) l hl)
  have hkeep16 : ∀ u, 16 ≤ u → u < 32 → r16.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr15 u hu2 (by omega), hkeep15 u (by omega) hu2]
  obtain ⟨r17, hr17_eq, hbut16, hfr16, hbd16⟩ :=
    round0_fc r16 16 (by decide) ((-1279661)#i32) (1917081#i32) ((-2546312)#i32) ((-1374803)#i32) B (zeta0_mag16_0) (zeta0_mag16_1) (zeta0_mag16_2) (zeta0_mag16_3) hB
      (fun l hl => by rw [hkeep16 16 (by omega) (by omega)]; exact hin 16 (by decide) l hl)
  have hkeep17 : ∀ u, 17 ≤ u → u < 32 → r17.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr16 u hu2 (by omega), hkeep16 u (by omega) hu2]
  obtain ⟨r18, hr18_eq, hbut17, hfr17, hbd17⟩ :=
    round0_fc r17 17 (by decide) (1500165#i32) (777191#i32) (2235880#i32) (3406031#i32) B (zeta0_mag17_0) (zeta0_mag17_1) (zeta0_mag17_2) (zeta0_mag17_3) hB
      (fun l hl => by rw [hkeep17 17 (by omega) (by omega)]; exact hin 17 (by decide) l hl)
  have hkeep18 : ∀ u, 18 ≤ u → u < 32 → r18.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr17 u hu2 (by omega), hkeep17 u (by omega) hu2]
  obtain ⟨r19, hr19_eq, hbut18, hfr18, hbd18⟩ :=
    round0_fc r18 18 (by decide) ((-542412)#i32) ((-2831860)#i32) ((-1671176)#i32) ((-1846953)#i32) B (zeta0_mag18_0) (zeta0_mag18_1) (zeta0_mag18_2) (zeta0_mag18_3) hB
      (fun l hl => by rw [hkeep18 18 (by omega) (by omega)]; exact hin 18 (by decide) l hl)
  have hkeep19 : ∀ u, 19 ≤ u → u < 32 → r19.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr18 u hu2 (by omega), hkeep18 u (by omega) hu2]
  obtain ⟨r20, hr20_eq, hbut19, hfr19, hbd19⟩ :=
    round0_fc r19 19 (by decide) ((-2584293)#i32) ((-3724270)#i32) (594136#i32) ((-3776993)#i32) B (zeta0_mag19_0) (zeta0_mag19_1) (zeta0_mag19_2) (zeta0_mag19_3) hB
      (fun l hl => by rw [hkeep19 19 (by omega) (by omega)]; exact hin 19 (by decide) l hl)
  have hkeep20 : ∀ u, 20 ≤ u → u < 32 → r20.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr19 u hu2 (by omega), hkeep19 u (by omega) hu2]
  obtain ⟨r21, hr21_eq, hbut20, hfr20, hbd20⟩ :=
    round0_fc r20 20 (by decide) ((-2013608)#i32) (2432395#i32) (2454455#i32) ((-164721)#i32) B (zeta0_mag20_0) (zeta0_mag20_1) (zeta0_mag20_2) (zeta0_mag20_3) hB
      (fun l hl => by rw [hkeep20 20 (by omega) (by omega)]; exact hin 20 (by decide) l hl)
  have hkeep21 : ∀ u, 21 ≤ u → u < 32 → r21.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr20 u hu2 (by omega), hkeep20 u (by omega) hu2]
  obtain ⟨r22, hr22_eq, hbut21, hfr21, hbd21⟩ :=
    round0_fc r21 21 (by decide) (1957272#i32) (3369112#i32) (185531#i32) ((-1207385)#i32) B (zeta0_mag21_0) (zeta0_mag21_1) (zeta0_mag21_2) (zeta0_mag21_3) hB
      (fun l hl => by rw [hkeep21 21 (by omega) (by omega)]; exact hin 21 (by decide) l hl)
  have hkeep22 : ∀ u, 22 ≤ u → u < 32 → r22.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr21 u hu2 (by omega), hkeep21 u (by omega) hu2]
  obtain ⟨r23, hr23_eq, hbut22, hfr22, hbd22⟩ :=
    round0_fc r22 22 (by decide) ((-3183426)#i32) (162844#i32) (1616392#i32) (3014001#i32) B (zeta0_mag22_0) (zeta0_mag22_1) (zeta0_mag22_2) (zeta0_mag22_3) hB
      (fun l hl => by rw [hkeep22 22 (by omega) (by omega)]; exact hin 22 (by decide) l hl)
  have hkeep23 : ∀ u, 23 ≤ u → u < 32 → r23.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr22 u hu2 (by omega), hkeep22 u (by omega) hu2]
  obtain ⟨r24, hr24_eq, hbut23, hfr23, hbd23⟩ :=
    round0_fc r23 23 (by decide) (810149#i32) (1652634#i32) ((-3694233)#i32) ((-1799107)#i32) B (zeta0_mag23_0) (zeta0_mag23_1) (zeta0_mag23_2) (zeta0_mag23_3) hB
      (fun l hl => by rw [hkeep23 23 (by omega) (by omega)]; exact hin 23 (by decide) l hl)
  have hkeep24 : ∀ u, 24 ≤ u → u < 32 → r24.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr23 u hu2 (by omega), hkeep23 u (by omega) hu2]
  obtain ⟨r25, hr25_eq, hbut24, hfr24, hbd24⟩ :=
    round0_fc r24 24 (by decide) ((-3038916)#i32) (3523897#i32) (3866901#i32) (269760#i32) B (zeta0_mag24_0) (zeta0_mag24_1) (zeta0_mag24_2) (zeta0_mag24_3) hB
      (fun l hl => by rw [hkeep24 24 (by omega) (by omega)]; exact hin 24 (by decide) l hl)
  have hkeep25 : ∀ u, 25 ≤ u → u < 32 → r25.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr24 u hu2 (by omega), hkeep24 u (by omega) hu2]
  obtain ⟨r26, hr26_eq, hbut25, hfr25, hbd25⟩ :=
    round0_fc r25 25 (by decide) (2213111#i32) ((-975884)#i32) (1717735#i32) (472078#i32) B (zeta0_mag25_0) (zeta0_mag25_1) (zeta0_mag25_2) (zeta0_mag25_3) hB
      (fun l hl => by rw [hkeep25 25 (by omega) (by omega)]; exact hin 25 (by decide) l hl)
  have hkeep26 : ∀ u, 26 ≤ u → u < 32 → r26.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr25 u hu2 (by omega), hkeep25 u (by omega) hu2]
  obtain ⟨r27, hr27_eq, hbut26, hfr26, hbd26⟩ :=
    round0_fc r26 26 (by decide) ((-426683)#i32) (1723600#i32) ((-1803090)#i32) (1910376#i32) B (zeta0_mag26_0) (zeta0_mag26_1) (zeta0_mag26_2) (zeta0_mag26_3) hB
      (fun l hl => by rw [hkeep26 26 (by omega) (by omega)]; exact hin 26 (by decide) l hl)
  have hkeep27 : ∀ u, 27 ≤ u → u < 32 → r27.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr26 u hu2 (by omega), hkeep26 u (by omega) hu2]
  obtain ⟨r28, hr28_eq, hbut27, hfr27, hbd27⟩ :=
    round0_fc r27 27 (by decide) ((-1667432)#i32) ((-1104333)#i32) ((-260646)#i32) ((-3833893)#i32) B (zeta0_mag27_0) (zeta0_mag27_1) (zeta0_mag27_2) (zeta0_mag27_3) hB
      (fun l hl => by rw [hkeep27 27 (by omega) (by omega)]; exact hin 27 (by decide) l hl)
  have hkeep28 : ∀ u, 28 ≤ u → u < 32 → r28.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr27 u hu2 (by omega), hkeep27 u (by omega) hu2]
  obtain ⟨r29, hr29_eq, hbut28, hfr28, hbd28⟩ :=
    round0_fc r28 28 (by decide) ((-2939036)#i32) ((-2235985)#i32) ((-420899)#i32) ((-2286327)#i32) B (zeta0_mag28_0) (zeta0_mag28_1) (zeta0_mag28_2) (zeta0_mag28_3) hB
      (fun l hl => by rw [hkeep28 28 (by omega) (by omega)]; exact hin 28 (by decide) l hl)
  have hkeep29 : ∀ u, 29 ≤ u → u < 32 → r29.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr28 u hu2 (by omega), hkeep28 u (by omega) hu2]
  obtain ⟨r30, hr30_eq, hbut29, hfr29, hbd29⟩ :=
    round0_fc r29 29 (by decide) (183443#i32) ((-976891)#i32) (1612842#i32) ((-3545687)#i32) B (zeta0_mag29_0) (zeta0_mag29_1) (zeta0_mag29_2) (zeta0_mag29_3) hB
      (fun l hl => by rw [hkeep29 29 (by omega) (by omega)]; exact hin 29 (by decide) l hl)
  have hkeep30 : ∀ u, 30 ≤ u → u < 32 → r30.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr29 u hu2 (by omega), hkeep29 u (by omega) hu2]
  obtain ⟨r31, hr31_eq, hbut30, hfr30, hbd30⟩ :=
    round0_fc r30 30 (by decide) ((-554416)#i32) (3919660#i32) ((-48306)#i32) ((-1362209)#i32) B (zeta0_mag30_0) (zeta0_mag30_1) (zeta0_mag30_2) (zeta0_mag30_3) hB
      (fun l hl => by rw [hkeep30 30 (by omega) (by omega)]; exact hin 30 (by decide) l hl)
  have hkeep31 : ∀ u, 31 ≤ u → u < 32 → r31.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr30 u hu2 (by omega), hkeep30 u (by omega) hu2]
  obtain ⟨r32, hr32_eq, hbut31, hfr31, hbd31⟩ :=
    round0_fc r31 31 (by decide) (3937738#i32) (1400424#i32) ((-846154)#i32) (1976782#i32) B (zeta0_mag31_0) (zeta0_mag31_1) (zeta0_mag31_2) (zeta0_mag31_3) hB
      (fun l hl => by rw [hkeep31 31 (by omega) (by omega)]; exact hin 31 (by decide) l hl)
  have hkeep32 : ∀ u, 32 ≤ u → u < 32 → r32.val[u]! = re.val[u]! := by
    intro u hu1 hu2; rw [hfr31 u hu2 (by omega), hkeep31 u (by omega) hu2]
  rw [hr1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr2_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr3_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr4_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr5_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr6_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr7_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr8_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr9_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr10_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr11_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr12_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr13_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr14_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr15_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr16_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr17_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr18_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr19_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr20_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr21_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr22_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr23_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr24_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr25_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr26_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr27_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr28_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr29_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr30_eq]; simp only [Aeneas.Std.bind_tc_ok]
  rw [hr31_eq]; simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok hr32_eq
  have hr32u0 : r32.val[0]! = r1.val[0]! := by
    rw [hfr31 0 (by decide) (by decide), hfr30 0 (by decide) (by decide), hfr29 0 (by decide) (by decide), hfr28 0 (by decide) (by decide), hfr27 0 (by decide) (by decide), hfr26 0 (by decide) (by decide), hfr25 0 (by decide) (by decide), hfr24 0 (by decide) (by decide), hfr23 0 (by decide) (by decide), hfr22 0 (by decide) (by decide), hfr21 0 (by decide) (by decide), hfr20 0 (by decide) (by decide), hfr19 0 (by decide) (by decide), hfr18 0 (by decide) (by decide), hfr17 0 (by decide) (by decide), hfr16 0 (by decide) (by decide), hfr15 0 (by decide) (by decide), hfr14 0 (by decide) (by decide), hfr13 0 (by decide) (by decide), hfr12 0 (by decide) (by decide), hfr11 0 (by decide) (by decide), hfr10 0 (by decide) (by decide), hfr9 0 (by decide) (by decide), hfr8 0 (by decide) (by decide), hfr7 0 (by decide) (by decide), hfr6 0 (by decide) (by decide), hfr5 0 (by decide) (by decide), hfr4 0 (by decide) (by decide), hfr3 0 (by decide) (by decide), hfr2 0 (by decide) (by decide), hfr1 0 (by decide) (by decide)]
  have hr32u1 : r32.val[1]! = r2.val[1]! := by
    rw [hfr31 1 (by decide) (by decide), hfr30 1 (by decide) (by decide), hfr29 1 (by decide) (by decide), hfr28 1 (by decide) (by decide), hfr27 1 (by decide) (by decide), hfr26 1 (by decide) (by decide), hfr25 1 (by decide) (by decide), hfr24 1 (by decide) (by decide), hfr23 1 (by decide) (by decide), hfr22 1 (by decide) (by decide), hfr21 1 (by decide) (by decide), hfr20 1 (by decide) (by decide), hfr19 1 (by decide) (by decide), hfr18 1 (by decide) (by decide), hfr17 1 (by decide) (by decide), hfr16 1 (by decide) (by decide), hfr15 1 (by decide) (by decide), hfr14 1 (by decide) (by decide), hfr13 1 (by decide) (by decide), hfr12 1 (by decide) (by decide), hfr11 1 (by decide) (by decide), hfr10 1 (by decide) (by decide), hfr9 1 (by decide) (by decide), hfr8 1 (by decide) (by decide), hfr7 1 (by decide) (by decide), hfr6 1 (by decide) (by decide), hfr5 1 (by decide) (by decide), hfr4 1 (by decide) (by decide), hfr3 1 (by decide) (by decide), hfr2 1 (by decide) (by decide)]
  rw [hkeep1 1 (by decide) (by decide)] at hbut1
  have hr32u2 : r32.val[2]! = r3.val[2]! := by
    rw [hfr31 2 (by decide) (by decide), hfr30 2 (by decide) (by decide), hfr29 2 (by decide) (by decide), hfr28 2 (by decide) (by decide), hfr27 2 (by decide) (by decide), hfr26 2 (by decide) (by decide), hfr25 2 (by decide) (by decide), hfr24 2 (by decide) (by decide), hfr23 2 (by decide) (by decide), hfr22 2 (by decide) (by decide), hfr21 2 (by decide) (by decide), hfr20 2 (by decide) (by decide), hfr19 2 (by decide) (by decide), hfr18 2 (by decide) (by decide), hfr17 2 (by decide) (by decide), hfr16 2 (by decide) (by decide), hfr15 2 (by decide) (by decide), hfr14 2 (by decide) (by decide), hfr13 2 (by decide) (by decide), hfr12 2 (by decide) (by decide), hfr11 2 (by decide) (by decide), hfr10 2 (by decide) (by decide), hfr9 2 (by decide) (by decide), hfr8 2 (by decide) (by decide), hfr7 2 (by decide) (by decide), hfr6 2 (by decide) (by decide), hfr5 2 (by decide) (by decide), hfr4 2 (by decide) (by decide), hfr3 2 (by decide) (by decide)]
  rw [hkeep2 2 (by decide) (by decide)] at hbut2
  have hr32u3 : r32.val[3]! = r4.val[3]! := by
    rw [hfr31 3 (by decide) (by decide), hfr30 3 (by decide) (by decide), hfr29 3 (by decide) (by decide), hfr28 3 (by decide) (by decide), hfr27 3 (by decide) (by decide), hfr26 3 (by decide) (by decide), hfr25 3 (by decide) (by decide), hfr24 3 (by decide) (by decide), hfr23 3 (by decide) (by decide), hfr22 3 (by decide) (by decide), hfr21 3 (by decide) (by decide), hfr20 3 (by decide) (by decide), hfr19 3 (by decide) (by decide), hfr18 3 (by decide) (by decide), hfr17 3 (by decide) (by decide), hfr16 3 (by decide) (by decide), hfr15 3 (by decide) (by decide), hfr14 3 (by decide) (by decide), hfr13 3 (by decide) (by decide), hfr12 3 (by decide) (by decide), hfr11 3 (by decide) (by decide), hfr10 3 (by decide) (by decide), hfr9 3 (by decide) (by decide), hfr8 3 (by decide) (by decide), hfr7 3 (by decide) (by decide), hfr6 3 (by decide) (by decide), hfr5 3 (by decide) (by decide), hfr4 3 (by decide) (by decide)]
  rw [hkeep3 3 (by decide) (by decide)] at hbut3
  have hr32u4 : r32.val[4]! = r5.val[4]! := by
    rw [hfr31 4 (by decide) (by decide), hfr30 4 (by decide) (by decide), hfr29 4 (by decide) (by decide), hfr28 4 (by decide) (by decide), hfr27 4 (by decide) (by decide), hfr26 4 (by decide) (by decide), hfr25 4 (by decide) (by decide), hfr24 4 (by decide) (by decide), hfr23 4 (by decide) (by decide), hfr22 4 (by decide) (by decide), hfr21 4 (by decide) (by decide), hfr20 4 (by decide) (by decide), hfr19 4 (by decide) (by decide), hfr18 4 (by decide) (by decide), hfr17 4 (by decide) (by decide), hfr16 4 (by decide) (by decide), hfr15 4 (by decide) (by decide), hfr14 4 (by decide) (by decide), hfr13 4 (by decide) (by decide), hfr12 4 (by decide) (by decide), hfr11 4 (by decide) (by decide), hfr10 4 (by decide) (by decide), hfr9 4 (by decide) (by decide), hfr8 4 (by decide) (by decide), hfr7 4 (by decide) (by decide), hfr6 4 (by decide) (by decide), hfr5 4 (by decide) (by decide)]
  rw [hkeep4 4 (by decide) (by decide)] at hbut4
  have hr32u5 : r32.val[5]! = r6.val[5]! := by
    rw [hfr31 5 (by decide) (by decide), hfr30 5 (by decide) (by decide), hfr29 5 (by decide) (by decide), hfr28 5 (by decide) (by decide), hfr27 5 (by decide) (by decide), hfr26 5 (by decide) (by decide), hfr25 5 (by decide) (by decide), hfr24 5 (by decide) (by decide), hfr23 5 (by decide) (by decide), hfr22 5 (by decide) (by decide), hfr21 5 (by decide) (by decide), hfr20 5 (by decide) (by decide), hfr19 5 (by decide) (by decide), hfr18 5 (by decide) (by decide), hfr17 5 (by decide) (by decide), hfr16 5 (by decide) (by decide), hfr15 5 (by decide) (by decide), hfr14 5 (by decide) (by decide), hfr13 5 (by decide) (by decide), hfr12 5 (by decide) (by decide), hfr11 5 (by decide) (by decide), hfr10 5 (by decide) (by decide), hfr9 5 (by decide) (by decide), hfr8 5 (by decide) (by decide), hfr7 5 (by decide) (by decide), hfr6 5 (by decide) (by decide)]
  rw [hkeep5 5 (by decide) (by decide)] at hbut5
  have hr32u6 : r32.val[6]! = r7.val[6]! := by
    rw [hfr31 6 (by decide) (by decide), hfr30 6 (by decide) (by decide), hfr29 6 (by decide) (by decide), hfr28 6 (by decide) (by decide), hfr27 6 (by decide) (by decide), hfr26 6 (by decide) (by decide), hfr25 6 (by decide) (by decide), hfr24 6 (by decide) (by decide), hfr23 6 (by decide) (by decide), hfr22 6 (by decide) (by decide), hfr21 6 (by decide) (by decide), hfr20 6 (by decide) (by decide), hfr19 6 (by decide) (by decide), hfr18 6 (by decide) (by decide), hfr17 6 (by decide) (by decide), hfr16 6 (by decide) (by decide), hfr15 6 (by decide) (by decide), hfr14 6 (by decide) (by decide), hfr13 6 (by decide) (by decide), hfr12 6 (by decide) (by decide), hfr11 6 (by decide) (by decide), hfr10 6 (by decide) (by decide), hfr9 6 (by decide) (by decide), hfr8 6 (by decide) (by decide), hfr7 6 (by decide) (by decide)]
  rw [hkeep6 6 (by decide) (by decide)] at hbut6
  have hr32u7 : r32.val[7]! = r8.val[7]! := by
    rw [hfr31 7 (by decide) (by decide), hfr30 7 (by decide) (by decide), hfr29 7 (by decide) (by decide), hfr28 7 (by decide) (by decide), hfr27 7 (by decide) (by decide), hfr26 7 (by decide) (by decide), hfr25 7 (by decide) (by decide), hfr24 7 (by decide) (by decide), hfr23 7 (by decide) (by decide), hfr22 7 (by decide) (by decide), hfr21 7 (by decide) (by decide), hfr20 7 (by decide) (by decide), hfr19 7 (by decide) (by decide), hfr18 7 (by decide) (by decide), hfr17 7 (by decide) (by decide), hfr16 7 (by decide) (by decide), hfr15 7 (by decide) (by decide), hfr14 7 (by decide) (by decide), hfr13 7 (by decide) (by decide), hfr12 7 (by decide) (by decide), hfr11 7 (by decide) (by decide), hfr10 7 (by decide) (by decide), hfr9 7 (by decide) (by decide), hfr8 7 (by decide) (by decide)]
  rw [hkeep7 7 (by decide) (by decide)] at hbut7
  have hr32u8 : r32.val[8]! = r9.val[8]! := by
    rw [hfr31 8 (by decide) (by decide), hfr30 8 (by decide) (by decide), hfr29 8 (by decide) (by decide), hfr28 8 (by decide) (by decide), hfr27 8 (by decide) (by decide), hfr26 8 (by decide) (by decide), hfr25 8 (by decide) (by decide), hfr24 8 (by decide) (by decide), hfr23 8 (by decide) (by decide), hfr22 8 (by decide) (by decide), hfr21 8 (by decide) (by decide), hfr20 8 (by decide) (by decide), hfr19 8 (by decide) (by decide), hfr18 8 (by decide) (by decide), hfr17 8 (by decide) (by decide), hfr16 8 (by decide) (by decide), hfr15 8 (by decide) (by decide), hfr14 8 (by decide) (by decide), hfr13 8 (by decide) (by decide), hfr12 8 (by decide) (by decide), hfr11 8 (by decide) (by decide), hfr10 8 (by decide) (by decide), hfr9 8 (by decide) (by decide)]
  rw [hkeep8 8 (by decide) (by decide)] at hbut8
  have hr32u9 : r32.val[9]! = r10.val[9]! := by
    rw [hfr31 9 (by decide) (by decide), hfr30 9 (by decide) (by decide), hfr29 9 (by decide) (by decide), hfr28 9 (by decide) (by decide), hfr27 9 (by decide) (by decide), hfr26 9 (by decide) (by decide), hfr25 9 (by decide) (by decide), hfr24 9 (by decide) (by decide), hfr23 9 (by decide) (by decide), hfr22 9 (by decide) (by decide), hfr21 9 (by decide) (by decide), hfr20 9 (by decide) (by decide), hfr19 9 (by decide) (by decide), hfr18 9 (by decide) (by decide), hfr17 9 (by decide) (by decide), hfr16 9 (by decide) (by decide), hfr15 9 (by decide) (by decide), hfr14 9 (by decide) (by decide), hfr13 9 (by decide) (by decide), hfr12 9 (by decide) (by decide), hfr11 9 (by decide) (by decide), hfr10 9 (by decide) (by decide)]
  rw [hkeep9 9 (by decide) (by decide)] at hbut9
  have hr32u10 : r32.val[10]! = r11.val[10]! := by
    rw [hfr31 10 (by decide) (by decide), hfr30 10 (by decide) (by decide), hfr29 10 (by decide) (by decide), hfr28 10 (by decide) (by decide), hfr27 10 (by decide) (by decide), hfr26 10 (by decide) (by decide), hfr25 10 (by decide) (by decide), hfr24 10 (by decide) (by decide), hfr23 10 (by decide) (by decide), hfr22 10 (by decide) (by decide), hfr21 10 (by decide) (by decide), hfr20 10 (by decide) (by decide), hfr19 10 (by decide) (by decide), hfr18 10 (by decide) (by decide), hfr17 10 (by decide) (by decide), hfr16 10 (by decide) (by decide), hfr15 10 (by decide) (by decide), hfr14 10 (by decide) (by decide), hfr13 10 (by decide) (by decide), hfr12 10 (by decide) (by decide), hfr11 10 (by decide) (by decide)]
  rw [hkeep10 10 (by decide) (by decide)] at hbut10
  have hr32u11 : r32.val[11]! = r12.val[11]! := by
    rw [hfr31 11 (by decide) (by decide), hfr30 11 (by decide) (by decide), hfr29 11 (by decide) (by decide), hfr28 11 (by decide) (by decide), hfr27 11 (by decide) (by decide), hfr26 11 (by decide) (by decide), hfr25 11 (by decide) (by decide), hfr24 11 (by decide) (by decide), hfr23 11 (by decide) (by decide), hfr22 11 (by decide) (by decide), hfr21 11 (by decide) (by decide), hfr20 11 (by decide) (by decide), hfr19 11 (by decide) (by decide), hfr18 11 (by decide) (by decide), hfr17 11 (by decide) (by decide), hfr16 11 (by decide) (by decide), hfr15 11 (by decide) (by decide), hfr14 11 (by decide) (by decide), hfr13 11 (by decide) (by decide), hfr12 11 (by decide) (by decide)]
  rw [hkeep11 11 (by decide) (by decide)] at hbut11
  have hr32u12 : r32.val[12]! = r13.val[12]! := by
    rw [hfr31 12 (by decide) (by decide), hfr30 12 (by decide) (by decide), hfr29 12 (by decide) (by decide), hfr28 12 (by decide) (by decide), hfr27 12 (by decide) (by decide), hfr26 12 (by decide) (by decide), hfr25 12 (by decide) (by decide), hfr24 12 (by decide) (by decide), hfr23 12 (by decide) (by decide), hfr22 12 (by decide) (by decide), hfr21 12 (by decide) (by decide), hfr20 12 (by decide) (by decide), hfr19 12 (by decide) (by decide), hfr18 12 (by decide) (by decide), hfr17 12 (by decide) (by decide), hfr16 12 (by decide) (by decide), hfr15 12 (by decide) (by decide), hfr14 12 (by decide) (by decide), hfr13 12 (by decide) (by decide)]
  rw [hkeep12 12 (by decide) (by decide)] at hbut12
  have hr32u13 : r32.val[13]! = r14.val[13]! := by
    rw [hfr31 13 (by decide) (by decide), hfr30 13 (by decide) (by decide), hfr29 13 (by decide) (by decide), hfr28 13 (by decide) (by decide), hfr27 13 (by decide) (by decide), hfr26 13 (by decide) (by decide), hfr25 13 (by decide) (by decide), hfr24 13 (by decide) (by decide), hfr23 13 (by decide) (by decide), hfr22 13 (by decide) (by decide), hfr21 13 (by decide) (by decide), hfr20 13 (by decide) (by decide), hfr19 13 (by decide) (by decide), hfr18 13 (by decide) (by decide), hfr17 13 (by decide) (by decide), hfr16 13 (by decide) (by decide), hfr15 13 (by decide) (by decide), hfr14 13 (by decide) (by decide)]
  rw [hkeep13 13 (by decide) (by decide)] at hbut13
  have hr32u14 : r32.val[14]! = r15.val[14]! := by
    rw [hfr31 14 (by decide) (by decide), hfr30 14 (by decide) (by decide), hfr29 14 (by decide) (by decide), hfr28 14 (by decide) (by decide), hfr27 14 (by decide) (by decide), hfr26 14 (by decide) (by decide), hfr25 14 (by decide) (by decide), hfr24 14 (by decide) (by decide), hfr23 14 (by decide) (by decide), hfr22 14 (by decide) (by decide), hfr21 14 (by decide) (by decide), hfr20 14 (by decide) (by decide), hfr19 14 (by decide) (by decide), hfr18 14 (by decide) (by decide), hfr17 14 (by decide) (by decide), hfr16 14 (by decide) (by decide), hfr15 14 (by decide) (by decide)]
  rw [hkeep14 14 (by decide) (by decide)] at hbut14
  have hr32u15 : r32.val[15]! = r16.val[15]! := by
    rw [hfr31 15 (by decide) (by decide), hfr30 15 (by decide) (by decide), hfr29 15 (by decide) (by decide), hfr28 15 (by decide) (by decide), hfr27 15 (by decide) (by decide), hfr26 15 (by decide) (by decide), hfr25 15 (by decide) (by decide), hfr24 15 (by decide) (by decide), hfr23 15 (by decide) (by decide), hfr22 15 (by decide) (by decide), hfr21 15 (by decide) (by decide), hfr20 15 (by decide) (by decide), hfr19 15 (by decide) (by decide), hfr18 15 (by decide) (by decide), hfr17 15 (by decide) (by decide), hfr16 15 (by decide) (by decide)]
  rw [hkeep15 15 (by decide) (by decide)] at hbut15
  have hr32u16 : r32.val[16]! = r17.val[16]! := by
    rw [hfr31 16 (by decide) (by decide), hfr30 16 (by decide) (by decide), hfr29 16 (by decide) (by decide), hfr28 16 (by decide) (by decide), hfr27 16 (by decide) (by decide), hfr26 16 (by decide) (by decide), hfr25 16 (by decide) (by decide), hfr24 16 (by decide) (by decide), hfr23 16 (by decide) (by decide), hfr22 16 (by decide) (by decide), hfr21 16 (by decide) (by decide), hfr20 16 (by decide) (by decide), hfr19 16 (by decide) (by decide), hfr18 16 (by decide) (by decide), hfr17 16 (by decide) (by decide)]
  rw [hkeep16 16 (by decide) (by decide)] at hbut16
  have hr32u17 : r32.val[17]! = r18.val[17]! := by
    rw [hfr31 17 (by decide) (by decide), hfr30 17 (by decide) (by decide), hfr29 17 (by decide) (by decide), hfr28 17 (by decide) (by decide), hfr27 17 (by decide) (by decide), hfr26 17 (by decide) (by decide), hfr25 17 (by decide) (by decide), hfr24 17 (by decide) (by decide), hfr23 17 (by decide) (by decide), hfr22 17 (by decide) (by decide), hfr21 17 (by decide) (by decide), hfr20 17 (by decide) (by decide), hfr19 17 (by decide) (by decide), hfr18 17 (by decide) (by decide)]
  rw [hkeep17 17 (by decide) (by decide)] at hbut17
  have hr32u18 : r32.val[18]! = r19.val[18]! := by
    rw [hfr31 18 (by decide) (by decide), hfr30 18 (by decide) (by decide), hfr29 18 (by decide) (by decide), hfr28 18 (by decide) (by decide), hfr27 18 (by decide) (by decide), hfr26 18 (by decide) (by decide), hfr25 18 (by decide) (by decide), hfr24 18 (by decide) (by decide), hfr23 18 (by decide) (by decide), hfr22 18 (by decide) (by decide), hfr21 18 (by decide) (by decide), hfr20 18 (by decide) (by decide), hfr19 18 (by decide) (by decide)]
  rw [hkeep18 18 (by decide) (by decide)] at hbut18
  have hr32u19 : r32.val[19]! = r20.val[19]! := by
    rw [hfr31 19 (by decide) (by decide), hfr30 19 (by decide) (by decide), hfr29 19 (by decide) (by decide), hfr28 19 (by decide) (by decide), hfr27 19 (by decide) (by decide), hfr26 19 (by decide) (by decide), hfr25 19 (by decide) (by decide), hfr24 19 (by decide) (by decide), hfr23 19 (by decide) (by decide), hfr22 19 (by decide) (by decide), hfr21 19 (by decide) (by decide), hfr20 19 (by decide) (by decide)]
  rw [hkeep19 19 (by decide) (by decide)] at hbut19
  have hr32u20 : r32.val[20]! = r21.val[20]! := by
    rw [hfr31 20 (by decide) (by decide), hfr30 20 (by decide) (by decide), hfr29 20 (by decide) (by decide), hfr28 20 (by decide) (by decide), hfr27 20 (by decide) (by decide), hfr26 20 (by decide) (by decide), hfr25 20 (by decide) (by decide), hfr24 20 (by decide) (by decide), hfr23 20 (by decide) (by decide), hfr22 20 (by decide) (by decide), hfr21 20 (by decide) (by decide)]
  rw [hkeep20 20 (by decide) (by decide)] at hbut20
  have hr32u21 : r32.val[21]! = r22.val[21]! := by
    rw [hfr31 21 (by decide) (by decide), hfr30 21 (by decide) (by decide), hfr29 21 (by decide) (by decide), hfr28 21 (by decide) (by decide), hfr27 21 (by decide) (by decide), hfr26 21 (by decide) (by decide), hfr25 21 (by decide) (by decide), hfr24 21 (by decide) (by decide), hfr23 21 (by decide) (by decide), hfr22 21 (by decide) (by decide)]
  rw [hkeep21 21 (by decide) (by decide)] at hbut21
  have hr32u22 : r32.val[22]! = r23.val[22]! := by
    rw [hfr31 22 (by decide) (by decide), hfr30 22 (by decide) (by decide), hfr29 22 (by decide) (by decide), hfr28 22 (by decide) (by decide), hfr27 22 (by decide) (by decide), hfr26 22 (by decide) (by decide), hfr25 22 (by decide) (by decide), hfr24 22 (by decide) (by decide), hfr23 22 (by decide) (by decide)]
  rw [hkeep22 22 (by decide) (by decide)] at hbut22
  have hr32u23 : r32.val[23]! = r24.val[23]! := by
    rw [hfr31 23 (by decide) (by decide), hfr30 23 (by decide) (by decide), hfr29 23 (by decide) (by decide), hfr28 23 (by decide) (by decide), hfr27 23 (by decide) (by decide), hfr26 23 (by decide) (by decide), hfr25 23 (by decide) (by decide), hfr24 23 (by decide) (by decide)]
  rw [hkeep23 23 (by decide) (by decide)] at hbut23
  have hr32u24 : r32.val[24]! = r25.val[24]! := by
    rw [hfr31 24 (by decide) (by decide), hfr30 24 (by decide) (by decide), hfr29 24 (by decide) (by decide), hfr28 24 (by decide) (by decide), hfr27 24 (by decide) (by decide), hfr26 24 (by decide) (by decide), hfr25 24 (by decide) (by decide)]
  rw [hkeep24 24 (by decide) (by decide)] at hbut24
  have hr32u25 : r32.val[25]! = r26.val[25]! := by
    rw [hfr31 25 (by decide) (by decide), hfr30 25 (by decide) (by decide), hfr29 25 (by decide) (by decide), hfr28 25 (by decide) (by decide), hfr27 25 (by decide) (by decide), hfr26 25 (by decide) (by decide)]
  rw [hkeep25 25 (by decide) (by decide)] at hbut25
  have hr32u26 : r32.val[26]! = r27.val[26]! := by
    rw [hfr31 26 (by decide) (by decide), hfr30 26 (by decide) (by decide), hfr29 26 (by decide) (by decide), hfr28 26 (by decide) (by decide), hfr27 26 (by decide) (by decide)]
  rw [hkeep26 26 (by decide) (by decide)] at hbut26
  have hr32u27 : r32.val[27]! = r28.val[27]! := by
    rw [hfr31 27 (by decide) (by decide), hfr30 27 (by decide) (by decide), hfr29 27 (by decide) (by decide), hfr28 27 (by decide) (by decide)]
  rw [hkeep27 27 (by decide) (by decide)] at hbut27
  have hr32u28 : r32.val[28]! = r29.val[28]! := by
    rw [hfr31 28 (by decide) (by decide), hfr30 28 (by decide) (by decide), hfr29 28 (by decide) (by decide)]
  rw [hkeep28 28 (by decide) (by decide)] at hbut28
  have hr32u29 : r32.val[29]! = r30.val[29]! := by
    rw [hfr31 29 (by decide) (by decide), hfr30 29 (by decide) (by decide)]
  rw [hkeep29 29 (by decide) (by decide)] at hbut29
  have hr32u30 : r32.val[30]! = r31.val[30]! := by
    rw [hfr31 30 (by decide) (by decide)]
  rw [hkeep30 30 (by decide) (by decide)] at hbut30
  have hr32u31 : r32.val[31]! = r32.val[31]! := by
    rfl
  rw [hkeep31 31 (by decide) (by decide)] at hbut31
  have hbfu0 : ∀ l, l < 8 →
      liftZ ((r32.val[0]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[0]!).values.val[l]!).val
            + zeta (4 * 0 + l / 2 + 128) * liftZ ((re.val[0]!).values.val[l + 1]!).val
         else liftZ ((re.val[0]!).values.val[l - 1]!).val
            - zeta (4 * 0 + l / 2 + 128) * liftZ ((re.val[0]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u0]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut0
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 0 + 0 / 2 + 128) = 128 from by decide, zeta0_bridge0_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 0 + 1 / 2 + 128) = 128 from by decide, zeta0_bridge0_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 0 + 2 / 2 + 128) = 129 from by decide, zeta0_bridge0_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 0 + 3 / 2 + 128) = 129 from by decide, zeta0_bridge0_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 0 + 4 / 2 + 128) = 130 from by decide, zeta0_bridge0_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 0 + 5 / 2 + 128) = 130 from by decide, zeta0_bridge0_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 0 + 6 / 2 + 128) = 131 from by decide, zeta0_bridge0_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 0 + 7 / 2 + 128) = 131 from by decide, zeta0_bridge0_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu1 : ∀ l, l < 8 →
      liftZ ((r32.val[1]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[1]!).values.val[l]!).val
            + zeta (4 * 1 + l / 2 + 128) * liftZ ((re.val[1]!).values.val[l + 1]!).val
         else liftZ ((re.val[1]!).values.val[l - 1]!).val
            - zeta (4 * 1 + l / 2 + 128) * liftZ ((re.val[1]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u1]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut1
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 1 + 0 / 2 + 128) = 132 from by decide, zeta0_bridge1_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 1 + 1 / 2 + 128) = 132 from by decide, zeta0_bridge1_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 1 + 2 / 2 + 128) = 133 from by decide, zeta0_bridge1_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 1 + 3 / 2 + 128) = 133 from by decide, zeta0_bridge1_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 1 + 4 / 2 + 128) = 134 from by decide, zeta0_bridge1_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 1 + 5 / 2 + 128) = 134 from by decide, zeta0_bridge1_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 1 + 6 / 2 + 128) = 135 from by decide, zeta0_bridge1_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 1 + 7 / 2 + 128) = 135 from by decide, zeta0_bridge1_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu2 : ∀ l, l < 8 →
      liftZ ((r32.val[2]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[2]!).values.val[l]!).val
            + zeta (4 * 2 + l / 2 + 128) * liftZ ((re.val[2]!).values.val[l + 1]!).val
         else liftZ ((re.val[2]!).values.val[l - 1]!).val
            - zeta (4 * 2 + l / 2 + 128) * liftZ ((re.val[2]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u2]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut2
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 2 + 0 / 2 + 128) = 136 from by decide, zeta0_bridge2_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 2 + 1 / 2 + 128) = 136 from by decide, zeta0_bridge2_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 2 + 2 / 2 + 128) = 137 from by decide, zeta0_bridge2_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 2 + 3 / 2 + 128) = 137 from by decide, zeta0_bridge2_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 2 + 4 / 2 + 128) = 138 from by decide, zeta0_bridge2_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 2 + 5 / 2 + 128) = 138 from by decide, zeta0_bridge2_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 2 + 6 / 2 + 128) = 139 from by decide, zeta0_bridge2_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 2 + 7 / 2 + 128) = 139 from by decide, zeta0_bridge2_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu3 : ∀ l, l < 8 →
      liftZ ((r32.val[3]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[3]!).values.val[l]!).val
            + zeta (4 * 3 + l / 2 + 128) * liftZ ((re.val[3]!).values.val[l + 1]!).val
         else liftZ ((re.val[3]!).values.val[l - 1]!).val
            - zeta (4 * 3 + l / 2 + 128) * liftZ ((re.val[3]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u3]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut3
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 3 + 0 / 2 + 128) = 140 from by decide, zeta0_bridge3_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 3 + 1 / 2 + 128) = 140 from by decide, zeta0_bridge3_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 3 + 2 / 2 + 128) = 141 from by decide, zeta0_bridge3_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 3 + 3 / 2 + 128) = 141 from by decide, zeta0_bridge3_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 3 + 4 / 2 + 128) = 142 from by decide, zeta0_bridge3_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 3 + 5 / 2 + 128) = 142 from by decide, zeta0_bridge3_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 3 + 6 / 2 + 128) = 143 from by decide, zeta0_bridge3_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 3 + 7 / 2 + 128) = 143 from by decide, zeta0_bridge3_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu4 : ∀ l, l < 8 →
      liftZ ((r32.val[4]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[4]!).values.val[l]!).val
            + zeta (4 * 4 + l / 2 + 128) * liftZ ((re.val[4]!).values.val[l + 1]!).val
         else liftZ ((re.val[4]!).values.val[l - 1]!).val
            - zeta (4 * 4 + l / 2 + 128) * liftZ ((re.val[4]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u4]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut4
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 4 + 0 / 2 + 128) = 144 from by decide, zeta0_bridge4_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 4 + 1 / 2 + 128) = 144 from by decide, zeta0_bridge4_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 4 + 2 / 2 + 128) = 145 from by decide, zeta0_bridge4_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 4 + 3 / 2 + 128) = 145 from by decide, zeta0_bridge4_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 4 + 4 / 2 + 128) = 146 from by decide, zeta0_bridge4_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 4 + 5 / 2 + 128) = 146 from by decide, zeta0_bridge4_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 4 + 6 / 2 + 128) = 147 from by decide, zeta0_bridge4_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 4 + 7 / 2 + 128) = 147 from by decide, zeta0_bridge4_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu5 : ∀ l, l < 8 →
      liftZ ((r32.val[5]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[5]!).values.val[l]!).val
            + zeta (4 * 5 + l / 2 + 128) * liftZ ((re.val[5]!).values.val[l + 1]!).val
         else liftZ ((re.val[5]!).values.val[l - 1]!).val
            - zeta (4 * 5 + l / 2 + 128) * liftZ ((re.val[5]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u5]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut5
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 5 + 0 / 2 + 128) = 148 from by decide, zeta0_bridge5_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 5 + 1 / 2 + 128) = 148 from by decide, zeta0_bridge5_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 5 + 2 / 2 + 128) = 149 from by decide, zeta0_bridge5_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 5 + 3 / 2 + 128) = 149 from by decide, zeta0_bridge5_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 5 + 4 / 2 + 128) = 150 from by decide, zeta0_bridge5_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 5 + 5 / 2 + 128) = 150 from by decide, zeta0_bridge5_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 5 + 6 / 2 + 128) = 151 from by decide, zeta0_bridge5_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 5 + 7 / 2 + 128) = 151 from by decide, zeta0_bridge5_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu6 : ∀ l, l < 8 →
      liftZ ((r32.val[6]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[6]!).values.val[l]!).val
            + zeta (4 * 6 + l / 2 + 128) * liftZ ((re.val[6]!).values.val[l + 1]!).val
         else liftZ ((re.val[6]!).values.val[l - 1]!).val
            - zeta (4 * 6 + l / 2 + 128) * liftZ ((re.val[6]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u6]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut6
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 6 + 0 / 2 + 128) = 152 from by decide, zeta0_bridge6_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 6 + 1 / 2 + 128) = 152 from by decide, zeta0_bridge6_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 6 + 2 / 2 + 128) = 153 from by decide, zeta0_bridge6_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 6 + 3 / 2 + 128) = 153 from by decide, zeta0_bridge6_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 6 + 4 / 2 + 128) = 154 from by decide, zeta0_bridge6_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 6 + 5 / 2 + 128) = 154 from by decide, zeta0_bridge6_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 6 + 6 / 2 + 128) = 155 from by decide, zeta0_bridge6_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 6 + 7 / 2 + 128) = 155 from by decide, zeta0_bridge6_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu7 : ∀ l, l < 8 →
      liftZ ((r32.val[7]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[7]!).values.val[l]!).val
            + zeta (4 * 7 + l / 2 + 128) * liftZ ((re.val[7]!).values.val[l + 1]!).val
         else liftZ ((re.val[7]!).values.val[l - 1]!).val
            - zeta (4 * 7 + l / 2 + 128) * liftZ ((re.val[7]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u7]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut7
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 7 + 0 / 2 + 128) = 156 from by decide, zeta0_bridge7_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 7 + 1 / 2 + 128) = 156 from by decide, zeta0_bridge7_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 7 + 2 / 2 + 128) = 157 from by decide, zeta0_bridge7_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 7 + 3 / 2 + 128) = 157 from by decide, zeta0_bridge7_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 7 + 4 / 2 + 128) = 158 from by decide, zeta0_bridge7_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 7 + 5 / 2 + 128) = 158 from by decide, zeta0_bridge7_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 7 + 6 / 2 + 128) = 159 from by decide, zeta0_bridge7_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 7 + 7 / 2 + 128) = 159 from by decide, zeta0_bridge7_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu8 : ∀ l, l < 8 →
      liftZ ((r32.val[8]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[8]!).values.val[l]!).val
            + zeta (4 * 8 + l / 2 + 128) * liftZ ((re.val[8]!).values.val[l + 1]!).val
         else liftZ ((re.val[8]!).values.val[l - 1]!).val
            - zeta (4 * 8 + l / 2 + 128) * liftZ ((re.val[8]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u8]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut8
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 8 + 0 / 2 + 128) = 160 from by decide, zeta0_bridge8_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 8 + 1 / 2 + 128) = 160 from by decide, zeta0_bridge8_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 8 + 2 / 2 + 128) = 161 from by decide, zeta0_bridge8_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 8 + 3 / 2 + 128) = 161 from by decide, zeta0_bridge8_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 8 + 4 / 2 + 128) = 162 from by decide, zeta0_bridge8_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 8 + 5 / 2 + 128) = 162 from by decide, zeta0_bridge8_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 8 + 6 / 2 + 128) = 163 from by decide, zeta0_bridge8_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 8 + 7 / 2 + 128) = 163 from by decide, zeta0_bridge8_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu9 : ∀ l, l < 8 →
      liftZ ((r32.val[9]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[9]!).values.val[l]!).val
            + zeta (4 * 9 + l / 2 + 128) * liftZ ((re.val[9]!).values.val[l + 1]!).val
         else liftZ ((re.val[9]!).values.val[l - 1]!).val
            - zeta (4 * 9 + l / 2 + 128) * liftZ ((re.val[9]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u9]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut9
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 9 + 0 / 2 + 128) = 164 from by decide, zeta0_bridge9_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 9 + 1 / 2 + 128) = 164 from by decide, zeta0_bridge9_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 9 + 2 / 2 + 128) = 165 from by decide, zeta0_bridge9_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 9 + 3 / 2 + 128) = 165 from by decide, zeta0_bridge9_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 9 + 4 / 2 + 128) = 166 from by decide, zeta0_bridge9_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 9 + 5 / 2 + 128) = 166 from by decide, zeta0_bridge9_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 9 + 6 / 2 + 128) = 167 from by decide, zeta0_bridge9_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 9 + 7 / 2 + 128) = 167 from by decide, zeta0_bridge9_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu10 : ∀ l, l < 8 →
      liftZ ((r32.val[10]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[10]!).values.val[l]!).val
            + zeta (4 * 10 + l / 2 + 128) * liftZ ((re.val[10]!).values.val[l + 1]!).val
         else liftZ ((re.val[10]!).values.val[l - 1]!).val
            - zeta (4 * 10 + l / 2 + 128) * liftZ ((re.val[10]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u10]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut10
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 10 + 0 / 2 + 128) = 168 from by decide, zeta0_bridge10_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 10 + 1 / 2 + 128) = 168 from by decide, zeta0_bridge10_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 10 + 2 / 2 + 128) = 169 from by decide, zeta0_bridge10_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 10 + 3 / 2 + 128) = 169 from by decide, zeta0_bridge10_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 10 + 4 / 2 + 128) = 170 from by decide, zeta0_bridge10_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 10 + 5 / 2 + 128) = 170 from by decide, zeta0_bridge10_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 10 + 6 / 2 + 128) = 171 from by decide, zeta0_bridge10_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 10 + 7 / 2 + 128) = 171 from by decide, zeta0_bridge10_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu11 : ∀ l, l < 8 →
      liftZ ((r32.val[11]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[11]!).values.val[l]!).val
            + zeta (4 * 11 + l / 2 + 128) * liftZ ((re.val[11]!).values.val[l + 1]!).val
         else liftZ ((re.val[11]!).values.val[l - 1]!).val
            - zeta (4 * 11 + l / 2 + 128) * liftZ ((re.val[11]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u11]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut11
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 11 + 0 / 2 + 128) = 172 from by decide, zeta0_bridge11_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 11 + 1 / 2 + 128) = 172 from by decide, zeta0_bridge11_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 11 + 2 / 2 + 128) = 173 from by decide, zeta0_bridge11_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 11 + 3 / 2 + 128) = 173 from by decide, zeta0_bridge11_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 11 + 4 / 2 + 128) = 174 from by decide, zeta0_bridge11_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 11 + 5 / 2 + 128) = 174 from by decide, zeta0_bridge11_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 11 + 6 / 2 + 128) = 175 from by decide, zeta0_bridge11_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 11 + 7 / 2 + 128) = 175 from by decide, zeta0_bridge11_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu12 : ∀ l, l < 8 →
      liftZ ((r32.val[12]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[12]!).values.val[l]!).val
            + zeta (4 * 12 + l / 2 + 128) * liftZ ((re.val[12]!).values.val[l + 1]!).val
         else liftZ ((re.val[12]!).values.val[l - 1]!).val
            - zeta (4 * 12 + l / 2 + 128) * liftZ ((re.val[12]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u12]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut12
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 12 + 0 / 2 + 128) = 176 from by decide, zeta0_bridge12_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 12 + 1 / 2 + 128) = 176 from by decide, zeta0_bridge12_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 12 + 2 / 2 + 128) = 177 from by decide, zeta0_bridge12_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 12 + 3 / 2 + 128) = 177 from by decide, zeta0_bridge12_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 12 + 4 / 2 + 128) = 178 from by decide, zeta0_bridge12_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 12 + 5 / 2 + 128) = 178 from by decide, zeta0_bridge12_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 12 + 6 / 2 + 128) = 179 from by decide, zeta0_bridge12_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 12 + 7 / 2 + 128) = 179 from by decide, zeta0_bridge12_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu13 : ∀ l, l < 8 →
      liftZ ((r32.val[13]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[13]!).values.val[l]!).val
            + zeta (4 * 13 + l / 2 + 128) * liftZ ((re.val[13]!).values.val[l + 1]!).val
         else liftZ ((re.val[13]!).values.val[l - 1]!).val
            - zeta (4 * 13 + l / 2 + 128) * liftZ ((re.val[13]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u13]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut13
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 13 + 0 / 2 + 128) = 180 from by decide, zeta0_bridge13_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 13 + 1 / 2 + 128) = 180 from by decide, zeta0_bridge13_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 13 + 2 / 2 + 128) = 181 from by decide, zeta0_bridge13_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 13 + 3 / 2 + 128) = 181 from by decide, zeta0_bridge13_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 13 + 4 / 2 + 128) = 182 from by decide, zeta0_bridge13_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 13 + 5 / 2 + 128) = 182 from by decide, zeta0_bridge13_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 13 + 6 / 2 + 128) = 183 from by decide, zeta0_bridge13_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 13 + 7 / 2 + 128) = 183 from by decide, zeta0_bridge13_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu14 : ∀ l, l < 8 →
      liftZ ((r32.val[14]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[14]!).values.val[l]!).val
            + zeta (4 * 14 + l / 2 + 128) * liftZ ((re.val[14]!).values.val[l + 1]!).val
         else liftZ ((re.val[14]!).values.val[l - 1]!).val
            - zeta (4 * 14 + l / 2 + 128) * liftZ ((re.val[14]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u14]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut14
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 14 + 0 / 2 + 128) = 184 from by decide, zeta0_bridge14_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 14 + 1 / 2 + 128) = 184 from by decide, zeta0_bridge14_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 14 + 2 / 2 + 128) = 185 from by decide, zeta0_bridge14_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 14 + 3 / 2 + 128) = 185 from by decide, zeta0_bridge14_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 14 + 4 / 2 + 128) = 186 from by decide, zeta0_bridge14_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 14 + 5 / 2 + 128) = 186 from by decide, zeta0_bridge14_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 14 + 6 / 2 + 128) = 187 from by decide, zeta0_bridge14_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 14 + 7 / 2 + 128) = 187 from by decide, zeta0_bridge14_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu15 : ∀ l, l < 8 →
      liftZ ((r32.val[15]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[15]!).values.val[l]!).val
            + zeta (4 * 15 + l / 2 + 128) * liftZ ((re.val[15]!).values.val[l + 1]!).val
         else liftZ ((re.val[15]!).values.val[l - 1]!).val
            - zeta (4 * 15 + l / 2 + 128) * liftZ ((re.val[15]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u15]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut15
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 15 + 0 / 2 + 128) = 188 from by decide, zeta0_bridge15_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 15 + 1 / 2 + 128) = 188 from by decide, zeta0_bridge15_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 15 + 2 / 2 + 128) = 189 from by decide, zeta0_bridge15_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 15 + 3 / 2 + 128) = 189 from by decide, zeta0_bridge15_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 15 + 4 / 2 + 128) = 190 from by decide, zeta0_bridge15_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 15 + 5 / 2 + 128) = 190 from by decide, zeta0_bridge15_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 15 + 6 / 2 + 128) = 191 from by decide, zeta0_bridge15_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 15 + 7 / 2 + 128) = 191 from by decide, zeta0_bridge15_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu16 : ∀ l, l < 8 →
      liftZ ((r32.val[16]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[16]!).values.val[l]!).val
            + zeta (4 * 16 + l / 2 + 128) * liftZ ((re.val[16]!).values.val[l + 1]!).val
         else liftZ ((re.val[16]!).values.val[l - 1]!).val
            - zeta (4 * 16 + l / 2 + 128) * liftZ ((re.val[16]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u16]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut16
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 16 + 0 / 2 + 128) = 192 from by decide, zeta0_bridge16_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 16 + 1 / 2 + 128) = 192 from by decide, zeta0_bridge16_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 16 + 2 / 2 + 128) = 193 from by decide, zeta0_bridge16_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 16 + 3 / 2 + 128) = 193 from by decide, zeta0_bridge16_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 16 + 4 / 2 + 128) = 194 from by decide, zeta0_bridge16_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 16 + 5 / 2 + 128) = 194 from by decide, zeta0_bridge16_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 16 + 6 / 2 + 128) = 195 from by decide, zeta0_bridge16_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 16 + 7 / 2 + 128) = 195 from by decide, zeta0_bridge16_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu17 : ∀ l, l < 8 →
      liftZ ((r32.val[17]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[17]!).values.val[l]!).val
            + zeta (4 * 17 + l / 2 + 128) * liftZ ((re.val[17]!).values.val[l + 1]!).val
         else liftZ ((re.val[17]!).values.val[l - 1]!).val
            - zeta (4 * 17 + l / 2 + 128) * liftZ ((re.val[17]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u17]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut17
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 17 + 0 / 2 + 128) = 196 from by decide, zeta0_bridge17_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 17 + 1 / 2 + 128) = 196 from by decide, zeta0_bridge17_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 17 + 2 / 2 + 128) = 197 from by decide, zeta0_bridge17_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 17 + 3 / 2 + 128) = 197 from by decide, zeta0_bridge17_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 17 + 4 / 2 + 128) = 198 from by decide, zeta0_bridge17_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 17 + 5 / 2 + 128) = 198 from by decide, zeta0_bridge17_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 17 + 6 / 2 + 128) = 199 from by decide, zeta0_bridge17_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 17 + 7 / 2 + 128) = 199 from by decide, zeta0_bridge17_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu18 : ∀ l, l < 8 →
      liftZ ((r32.val[18]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[18]!).values.val[l]!).val
            + zeta (4 * 18 + l / 2 + 128) * liftZ ((re.val[18]!).values.val[l + 1]!).val
         else liftZ ((re.val[18]!).values.val[l - 1]!).val
            - zeta (4 * 18 + l / 2 + 128) * liftZ ((re.val[18]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u18]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut18
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 18 + 0 / 2 + 128) = 200 from by decide, zeta0_bridge18_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 18 + 1 / 2 + 128) = 200 from by decide, zeta0_bridge18_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 18 + 2 / 2 + 128) = 201 from by decide, zeta0_bridge18_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 18 + 3 / 2 + 128) = 201 from by decide, zeta0_bridge18_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 18 + 4 / 2 + 128) = 202 from by decide, zeta0_bridge18_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 18 + 5 / 2 + 128) = 202 from by decide, zeta0_bridge18_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 18 + 6 / 2 + 128) = 203 from by decide, zeta0_bridge18_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 18 + 7 / 2 + 128) = 203 from by decide, zeta0_bridge18_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu19 : ∀ l, l < 8 →
      liftZ ((r32.val[19]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[19]!).values.val[l]!).val
            + zeta (4 * 19 + l / 2 + 128) * liftZ ((re.val[19]!).values.val[l + 1]!).val
         else liftZ ((re.val[19]!).values.val[l - 1]!).val
            - zeta (4 * 19 + l / 2 + 128) * liftZ ((re.val[19]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u19]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut19
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 19 + 0 / 2 + 128) = 204 from by decide, zeta0_bridge19_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 19 + 1 / 2 + 128) = 204 from by decide, zeta0_bridge19_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 19 + 2 / 2 + 128) = 205 from by decide, zeta0_bridge19_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 19 + 3 / 2 + 128) = 205 from by decide, zeta0_bridge19_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 19 + 4 / 2 + 128) = 206 from by decide, zeta0_bridge19_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 19 + 5 / 2 + 128) = 206 from by decide, zeta0_bridge19_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 19 + 6 / 2 + 128) = 207 from by decide, zeta0_bridge19_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 19 + 7 / 2 + 128) = 207 from by decide, zeta0_bridge19_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu20 : ∀ l, l < 8 →
      liftZ ((r32.val[20]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[20]!).values.val[l]!).val
            + zeta (4 * 20 + l / 2 + 128) * liftZ ((re.val[20]!).values.val[l + 1]!).val
         else liftZ ((re.val[20]!).values.val[l - 1]!).val
            - zeta (4 * 20 + l / 2 + 128) * liftZ ((re.val[20]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u20]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut20
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 20 + 0 / 2 + 128) = 208 from by decide, zeta0_bridge20_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 20 + 1 / 2 + 128) = 208 from by decide, zeta0_bridge20_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 20 + 2 / 2 + 128) = 209 from by decide, zeta0_bridge20_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 20 + 3 / 2 + 128) = 209 from by decide, zeta0_bridge20_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 20 + 4 / 2 + 128) = 210 from by decide, zeta0_bridge20_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 20 + 5 / 2 + 128) = 210 from by decide, zeta0_bridge20_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 20 + 6 / 2 + 128) = 211 from by decide, zeta0_bridge20_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 20 + 7 / 2 + 128) = 211 from by decide, zeta0_bridge20_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu21 : ∀ l, l < 8 →
      liftZ ((r32.val[21]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[21]!).values.val[l]!).val
            + zeta (4 * 21 + l / 2 + 128) * liftZ ((re.val[21]!).values.val[l + 1]!).val
         else liftZ ((re.val[21]!).values.val[l - 1]!).val
            - zeta (4 * 21 + l / 2 + 128) * liftZ ((re.val[21]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u21]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut21
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 21 + 0 / 2 + 128) = 212 from by decide, zeta0_bridge21_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 21 + 1 / 2 + 128) = 212 from by decide, zeta0_bridge21_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 21 + 2 / 2 + 128) = 213 from by decide, zeta0_bridge21_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 21 + 3 / 2 + 128) = 213 from by decide, zeta0_bridge21_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 21 + 4 / 2 + 128) = 214 from by decide, zeta0_bridge21_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 21 + 5 / 2 + 128) = 214 from by decide, zeta0_bridge21_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 21 + 6 / 2 + 128) = 215 from by decide, zeta0_bridge21_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 21 + 7 / 2 + 128) = 215 from by decide, zeta0_bridge21_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu22 : ∀ l, l < 8 →
      liftZ ((r32.val[22]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[22]!).values.val[l]!).val
            + zeta (4 * 22 + l / 2 + 128) * liftZ ((re.val[22]!).values.val[l + 1]!).val
         else liftZ ((re.val[22]!).values.val[l - 1]!).val
            - zeta (4 * 22 + l / 2 + 128) * liftZ ((re.val[22]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u22]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut22
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 22 + 0 / 2 + 128) = 216 from by decide, zeta0_bridge22_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 22 + 1 / 2 + 128) = 216 from by decide, zeta0_bridge22_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 22 + 2 / 2 + 128) = 217 from by decide, zeta0_bridge22_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 22 + 3 / 2 + 128) = 217 from by decide, zeta0_bridge22_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 22 + 4 / 2 + 128) = 218 from by decide, zeta0_bridge22_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 22 + 5 / 2 + 128) = 218 from by decide, zeta0_bridge22_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 22 + 6 / 2 + 128) = 219 from by decide, zeta0_bridge22_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 22 + 7 / 2 + 128) = 219 from by decide, zeta0_bridge22_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu23 : ∀ l, l < 8 →
      liftZ ((r32.val[23]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[23]!).values.val[l]!).val
            + zeta (4 * 23 + l / 2 + 128) * liftZ ((re.val[23]!).values.val[l + 1]!).val
         else liftZ ((re.val[23]!).values.val[l - 1]!).val
            - zeta (4 * 23 + l / 2 + 128) * liftZ ((re.val[23]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u23]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut23
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 23 + 0 / 2 + 128) = 220 from by decide, zeta0_bridge23_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 23 + 1 / 2 + 128) = 220 from by decide, zeta0_bridge23_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 23 + 2 / 2 + 128) = 221 from by decide, zeta0_bridge23_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 23 + 3 / 2 + 128) = 221 from by decide, zeta0_bridge23_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 23 + 4 / 2 + 128) = 222 from by decide, zeta0_bridge23_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 23 + 5 / 2 + 128) = 222 from by decide, zeta0_bridge23_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 23 + 6 / 2 + 128) = 223 from by decide, zeta0_bridge23_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 23 + 7 / 2 + 128) = 223 from by decide, zeta0_bridge23_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu24 : ∀ l, l < 8 →
      liftZ ((r32.val[24]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[24]!).values.val[l]!).val
            + zeta (4 * 24 + l / 2 + 128) * liftZ ((re.val[24]!).values.val[l + 1]!).val
         else liftZ ((re.val[24]!).values.val[l - 1]!).val
            - zeta (4 * 24 + l / 2 + 128) * liftZ ((re.val[24]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u24]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut24
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 24 + 0 / 2 + 128) = 224 from by decide, zeta0_bridge24_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 24 + 1 / 2 + 128) = 224 from by decide, zeta0_bridge24_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 24 + 2 / 2 + 128) = 225 from by decide, zeta0_bridge24_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 24 + 3 / 2 + 128) = 225 from by decide, zeta0_bridge24_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 24 + 4 / 2 + 128) = 226 from by decide, zeta0_bridge24_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 24 + 5 / 2 + 128) = 226 from by decide, zeta0_bridge24_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 24 + 6 / 2 + 128) = 227 from by decide, zeta0_bridge24_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 24 + 7 / 2 + 128) = 227 from by decide, zeta0_bridge24_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu25 : ∀ l, l < 8 →
      liftZ ((r32.val[25]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[25]!).values.val[l]!).val
            + zeta (4 * 25 + l / 2 + 128) * liftZ ((re.val[25]!).values.val[l + 1]!).val
         else liftZ ((re.val[25]!).values.val[l - 1]!).val
            - zeta (4 * 25 + l / 2 + 128) * liftZ ((re.val[25]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u25]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut25
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 25 + 0 / 2 + 128) = 228 from by decide, zeta0_bridge25_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 25 + 1 / 2 + 128) = 228 from by decide, zeta0_bridge25_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 25 + 2 / 2 + 128) = 229 from by decide, zeta0_bridge25_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 25 + 3 / 2 + 128) = 229 from by decide, zeta0_bridge25_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 25 + 4 / 2 + 128) = 230 from by decide, zeta0_bridge25_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 25 + 5 / 2 + 128) = 230 from by decide, zeta0_bridge25_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 25 + 6 / 2 + 128) = 231 from by decide, zeta0_bridge25_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 25 + 7 / 2 + 128) = 231 from by decide, zeta0_bridge25_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu26 : ∀ l, l < 8 →
      liftZ ((r32.val[26]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[26]!).values.val[l]!).val
            + zeta (4 * 26 + l / 2 + 128) * liftZ ((re.val[26]!).values.val[l + 1]!).val
         else liftZ ((re.val[26]!).values.val[l - 1]!).val
            - zeta (4 * 26 + l / 2 + 128) * liftZ ((re.val[26]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u26]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut26
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 26 + 0 / 2 + 128) = 232 from by decide, zeta0_bridge26_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 26 + 1 / 2 + 128) = 232 from by decide, zeta0_bridge26_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 26 + 2 / 2 + 128) = 233 from by decide, zeta0_bridge26_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 26 + 3 / 2 + 128) = 233 from by decide, zeta0_bridge26_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 26 + 4 / 2 + 128) = 234 from by decide, zeta0_bridge26_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 26 + 5 / 2 + 128) = 234 from by decide, zeta0_bridge26_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 26 + 6 / 2 + 128) = 235 from by decide, zeta0_bridge26_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 26 + 7 / 2 + 128) = 235 from by decide, zeta0_bridge26_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu27 : ∀ l, l < 8 →
      liftZ ((r32.val[27]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[27]!).values.val[l]!).val
            + zeta (4 * 27 + l / 2 + 128) * liftZ ((re.val[27]!).values.val[l + 1]!).val
         else liftZ ((re.val[27]!).values.val[l - 1]!).val
            - zeta (4 * 27 + l / 2 + 128) * liftZ ((re.val[27]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u27]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut27
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 27 + 0 / 2 + 128) = 236 from by decide, zeta0_bridge27_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 27 + 1 / 2 + 128) = 236 from by decide, zeta0_bridge27_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 27 + 2 / 2 + 128) = 237 from by decide, zeta0_bridge27_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 27 + 3 / 2 + 128) = 237 from by decide, zeta0_bridge27_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 27 + 4 / 2 + 128) = 238 from by decide, zeta0_bridge27_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 27 + 5 / 2 + 128) = 238 from by decide, zeta0_bridge27_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 27 + 6 / 2 + 128) = 239 from by decide, zeta0_bridge27_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 27 + 7 / 2 + 128) = 239 from by decide, zeta0_bridge27_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu28 : ∀ l, l < 8 →
      liftZ ((r32.val[28]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[28]!).values.val[l]!).val
            + zeta (4 * 28 + l / 2 + 128) * liftZ ((re.val[28]!).values.val[l + 1]!).val
         else liftZ ((re.val[28]!).values.val[l - 1]!).val
            - zeta (4 * 28 + l / 2 + 128) * liftZ ((re.val[28]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u28]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut28
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 28 + 0 / 2 + 128) = 240 from by decide, zeta0_bridge28_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 28 + 1 / 2 + 128) = 240 from by decide, zeta0_bridge28_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 28 + 2 / 2 + 128) = 241 from by decide, zeta0_bridge28_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 28 + 3 / 2 + 128) = 241 from by decide, zeta0_bridge28_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 28 + 4 / 2 + 128) = 242 from by decide, zeta0_bridge28_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 28 + 5 / 2 + 128) = 242 from by decide, zeta0_bridge28_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 28 + 6 / 2 + 128) = 243 from by decide, zeta0_bridge28_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 28 + 7 / 2 + 128) = 243 from by decide, zeta0_bridge28_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu29 : ∀ l, l < 8 →
      liftZ ((r32.val[29]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[29]!).values.val[l]!).val
            + zeta (4 * 29 + l / 2 + 128) * liftZ ((re.val[29]!).values.val[l + 1]!).val
         else liftZ ((re.val[29]!).values.val[l - 1]!).val
            - zeta (4 * 29 + l / 2 + 128) * liftZ ((re.val[29]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u29]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut29
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 29 + 0 / 2 + 128) = 244 from by decide, zeta0_bridge29_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 29 + 1 / 2 + 128) = 244 from by decide, zeta0_bridge29_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 29 + 2 / 2 + 128) = 245 from by decide, zeta0_bridge29_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 29 + 3 / 2 + 128) = 245 from by decide, zeta0_bridge29_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 29 + 4 / 2 + 128) = 246 from by decide, zeta0_bridge29_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 29 + 5 / 2 + 128) = 246 from by decide, zeta0_bridge29_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 29 + 6 / 2 + 128) = 247 from by decide, zeta0_bridge29_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 29 + 7 / 2 + 128) = 247 from by decide, zeta0_bridge29_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu30 : ∀ l, l < 8 →
      liftZ ((r32.val[30]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[30]!).values.val[l]!).val
            + zeta (4 * 30 + l / 2 + 128) * liftZ ((re.val[30]!).values.val[l + 1]!).val
         else liftZ ((re.val[30]!).values.val[l - 1]!).val
            - zeta (4 * 30 + l / 2 + 128) * liftZ ((re.val[30]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u30]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut30
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 30 + 0 / 2 + 128) = 248 from by decide, zeta0_bridge30_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 30 + 1 / 2 + 128) = 248 from by decide, zeta0_bridge30_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 30 + 2 / 2 + 128) = 249 from by decide, zeta0_bridge30_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 30 + 3 / 2 + 128) = 249 from by decide, zeta0_bridge30_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 30 + 4 / 2 + 128) = 250 from by decide, zeta0_bridge30_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 30 + 5 / 2 + 128) = 250 from by decide, zeta0_bridge30_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 30 + 6 / 2 + 128) = 251 from by decide, zeta0_bridge30_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 30 + 7 / 2 + 128) = 251 from by decide, zeta0_bridge30_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbfu31 : ∀ l, l < 8 →
      liftZ ((r32.val[31]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[31]!).values.val[l]!).val
            + zeta (4 * 31 + l / 2 + 128) * liftZ ((re.val[31]!).values.val[l + 1]!).val
         else liftZ ((re.val[31]!).values.val[l - 1]!).val
            - zeta (4 * 31 + l / 2 + 128) * liftZ ((re.val[31]!).values.val[l]!).val) := by
    intro l hl; rw [hr32u31]
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := hbut31
    match l, hl with
    | 0, _ => rw [if_pos (by decide), b0]; rw [show (4 * 31 + 0 / 2 + 128) = 252 from by decide, zeta0_bridge31_0, mul_comm]
    | 1, _ => rw [if_neg (by decide), b1]; rw [show (4 * 31 + 1 / 2 + 128) = 252 from by decide, zeta0_bridge31_0, mul_comm]
    | 2, _ => rw [if_pos (by decide), b2]; rw [show (4 * 31 + 2 / 2 + 128) = 253 from by decide, zeta0_bridge31_1, mul_comm]
    | 3, _ => rw [if_neg (by decide), b3]; rw [show (4 * 31 + 3 / 2 + 128) = 253 from by decide, zeta0_bridge31_1, mul_comm]
    | 4, _ => rw [if_pos (by decide), b4]; rw [show (4 * 31 + 4 / 2 + 128) = 254 from by decide, zeta0_bridge31_2, mul_comm]
    | 5, _ => rw [if_neg (by decide), b5]; rw [show (4 * 31 + 5 / 2 + 128) = 254 from by decide, zeta0_bridge31_2, mul_comm]
    | 6, _ => rw [if_pos (by decide), b6]; rw [show (4 * 31 + 6 / 2 + 128) = 255 from by decide, zeta0_bridge31_3, mul_comm]
    | 7, _ => rw [if_neg (by decide), b7]; rw [show (4 * 31 + 7 / 2 + 128) = 255 from by decide, zeta0_bridge31_3, mul_comm]
    | (n + 8), h => exact absurd h (by omega)
  have hbf : ∀ u, u < 32 → ∀ l, l < 8 →
      liftZ ((r32.val[u]!).values.val[l]!).val =
        (if l % 2 < 1 then liftZ ((re.val[u]!).values.val[l]!).val
            + zeta (4 * u + l / 2 + 128) * liftZ ((re.val[u]!).values.val[l + 1]!).val
         else liftZ ((re.val[u]!).values.val[l - 1]!).val
            - zeta (4 * u + l / 2 + 128) * liftZ ((re.val[u]!).values.val[l]!).val) := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbfu0 l hl
    | 1, _ => exact hbfu1 l hl
    | 2, _ => exact hbfu2 l hl
    | 3, _ => exact hbfu3 l hl
    | 4, _ => exact hbfu4 l hl
    | 5, _ => exact hbfu5 l hl
    | 6, _ => exact hbfu6 l hl
    | 7, _ => exact hbfu7 l hl
    | 8, _ => exact hbfu8 l hl
    | 9, _ => exact hbfu9 l hl
    | 10, _ => exact hbfu10 l hl
    | 11, _ => exact hbfu11 l hl
    | 12, _ => exact hbfu12 l hl
    | 13, _ => exact hbfu13 l hl
    | 14, _ => exact hbfu14 l hl
    | 15, _ => exact hbfu15 l hl
    | 16, _ => exact hbfu16 l hl
    | 17, _ => exact hbfu17 l hl
    | 18, _ => exact hbfu18 l hl
    | 19, _ => exact hbfu19 l hl
    | 20, _ => exact hbfu20 l hl
    | 21, _ => exact hbfu21 l hl
    | 22, _ => exact hbfu22 l hl
    | 23, _ => exact hbfu23 l hl
    | 24, _ => exact hbfu24 l hl
    | 25, _ => exact hbfu25 l hl
    | 26, _ => exact hbfu26 l hl
    | 27, _ => exact hbfu27 l hl
    | 28, _ => exact hbfu28 l hl
    | 29, _ => exact hbfu29 l hl
    | 30, _ => exact hbfu30 l hl
    | 31, _ => exact hbfu31 l hl
    | (n + 32), h => exact absurd h (by omega)
  have hbnd0 : ∀ l, l < 8 → ((r32.val[0]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u0]; exact hbd0 l hl
  have hbnd1 : ∀ l, l < 8 → ((r32.val[1]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u1]; exact hbd1 l hl
  have hbnd2 : ∀ l, l < 8 → ((r32.val[2]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u2]; exact hbd2 l hl
  have hbnd3 : ∀ l, l < 8 → ((r32.val[3]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u3]; exact hbd3 l hl
  have hbnd4 : ∀ l, l < 8 → ((r32.val[4]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u4]; exact hbd4 l hl
  have hbnd5 : ∀ l, l < 8 → ((r32.val[5]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u5]; exact hbd5 l hl
  have hbnd6 : ∀ l, l < 8 → ((r32.val[6]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u6]; exact hbd6 l hl
  have hbnd7 : ∀ l, l < 8 → ((r32.val[7]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u7]; exact hbd7 l hl
  have hbnd8 : ∀ l, l < 8 → ((r32.val[8]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u8]; exact hbd8 l hl
  have hbnd9 : ∀ l, l < 8 → ((r32.val[9]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u9]; exact hbd9 l hl
  have hbnd10 : ∀ l, l < 8 → ((r32.val[10]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u10]; exact hbd10 l hl
  have hbnd11 : ∀ l, l < 8 → ((r32.val[11]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u11]; exact hbd11 l hl
  have hbnd12 : ∀ l, l < 8 → ((r32.val[12]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u12]; exact hbd12 l hl
  have hbnd13 : ∀ l, l < 8 → ((r32.val[13]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u13]; exact hbd13 l hl
  have hbnd14 : ∀ l, l < 8 → ((r32.val[14]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u14]; exact hbd14 l hl
  have hbnd15 : ∀ l, l < 8 → ((r32.val[15]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u15]; exact hbd15 l hl
  have hbnd16 : ∀ l, l < 8 → ((r32.val[16]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u16]; exact hbd16 l hl
  have hbnd17 : ∀ l, l < 8 → ((r32.val[17]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u17]; exact hbd17 l hl
  have hbnd18 : ∀ l, l < 8 → ((r32.val[18]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u18]; exact hbd18 l hl
  have hbnd19 : ∀ l, l < 8 → ((r32.val[19]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u19]; exact hbd19 l hl
  have hbnd20 : ∀ l, l < 8 → ((r32.val[20]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u20]; exact hbd20 l hl
  have hbnd21 : ∀ l, l < 8 → ((r32.val[21]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u21]; exact hbd21 l hl
  have hbnd22 : ∀ l, l < 8 → ((r32.val[22]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u22]; exact hbd22 l hl
  have hbnd23 : ∀ l, l < 8 → ((r32.val[23]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u23]; exact hbd23 l hl
  have hbnd24 : ∀ l, l < 8 → ((r32.val[24]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u24]; exact hbd24 l hl
  have hbnd25 : ∀ l, l < 8 → ((r32.val[25]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u25]; exact hbd25 l hl
  have hbnd26 : ∀ l, l < 8 → ((r32.val[26]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u26]; exact hbd26 l hl
  have hbnd27 : ∀ l, l < 8 → ((r32.val[27]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u27]; exact hbd27 l hl
  have hbnd28 : ∀ l, l < 8 → ((r32.val[28]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u28]; exact hbd28 l hl
  have hbnd29 : ∀ l, l < 8 → ((r32.val[29]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u29]; exact hbd29 l hl
  have hbnd30 : ∀ l, l < 8 → ((r32.val[30]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u30]; exact hbd30 l hl
  have hbnd31 : ∀ l, l < 8 → ((r32.val[31]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro l hl; rw [hr32u31]; exact hbd31 l hl
  have hbnd : ∀ u, u < 32 → ∀ l, l < 8 →
      ((r32.val[u]!).values.val[l]!).val.natAbs ≤ B + 2 ^ 24 := by
    intro u hu l hl
    match u, hu with
    | 0, _ => exact hbnd0 l hl
    | 1, _ => exact hbnd1 l hl
    | 2, _ => exact hbnd2 l hl
    | 3, _ => exact hbnd3 l hl
    | 4, _ => exact hbnd4 l hl
    | 5, _ => exact hbnd5 l hl
    | 6, _ => exact hbnd6 l hl
    | 7, _ => exact hbnd7 l hl
    | 8, _ => exact hbnd8 l hl
    | 9, _ => exact hbnd9 l hl
    | 10, _ => exact hbnd10 l hl
    | 11, _ => exact hbnd11 l hl
    | 12, _ => exact hbnd12 l hl
    | 13, _ => exact hbnd13 l hl
    | 14, _ => exact hbnd14 l hl
    | 15, _ => exact hbnd15 l hl
    | 16, _ => exact hbnd16 l hl
    | 17, _ => exact hbnd17 l hl
    | 18, _ => exact hbnd18 l hl
    | 19, _ => exact hbnd19 l hl
    | 20, _ => exact hbnd20 l hl
    | 21, _ => exact hbnd21 l hl
    | 22, _ => exact hbnd22 l hl
    | 23, _ => exact hbnd23 l hl
    | 24, _ => exact hbnd24 l hl
    | 25, _ => exact hbnd25 l hl
    | 26, _ => exact hbnd26 l hl
    | 27, _ => exact hbnd27 l hl
    | 28, _ => exact hbnd28 l hl
    | 29, _ => exact hbnd29 l hl
    | 30, _ => exact hbnd30 l hl
    | 31, _ => exact hbnd31 l hl
    | (n + 32), h => exact absurd h (by omega)
  refine ⟨?_, ?_⟩
  · unfold lift_units
    apply Pure.build_congr
    intro i hi
    simp only [Nat.reduceShiftLeft, Nat.reduceMul, Nat.reduceDiv]
    have huu : i / 8 < 32 := by omega
    have hll : i % 8 < 8 := by omega
    have hb := hbf (i / 8) huu (i % 8) hll
    by_cases hlt : i % 2 < 1
    · have hcond : i % 8 % 2 < 1 := by omega
      rw [if_pos hlt]
      rw [if_pos hcond] at hb
      have hdiv : (i + 1) / 8 = i / 8 := by omega
      have hmod : (i + 1) % 8 = i % 8 + 1 := by omega
      have hidx2 : i + 1 < 256 := by omega
      have hz : 4 * (i / 8) + i % 8 / 2 + 128 = i / 2 + 128 := by omega
      rw [Pure.build_getElem _ i hi, Pure.build_getElem _ (i + 1) hidx2, hdiv, hmod]
      rw [hz] at hb
      exact hb
    · have hcond : ¬ i % 8 % 2 < 1 := by omega
      rw [if_neg hlt]
      rw [if_neg hcond] at hb
      have hdiv : (i - 1) / 8 = i / 8 := by omega
      have hmod : (i - 1) % 8 = i % 8 - 1 := by omega
      have hidx2 : i - 1 < 256 := by omega
      have hz : 4 * (i / 8) + i % 8 / 2 + 128 = i / 2 + 128 := by omega
      rw [Pure.build_getElem _ (i - 1) hidx2, Pure.build_getElem _ i hi, hdiv, hmod]
      rw [hz] at hb
      exact hb
  · exact hbnd

end libcrux_iot_ml_dsa.Vector.Portable.NttDriver
