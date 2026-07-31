import LibcruxIotMlDsa.Vector.Portable.Arithmetic
import LibcruxIotMlDsa.Util.LoopHelper

/-!
  # `Vector/Portable/Rounding.lean` — `decompose` dual-output keystone

  Split out of `Arithmetic.lean` purely for **build performance**: the monolithic
  `unfold decompose_impl_value; simp only []` route produced one enormous kernel
  proof term (~35 GB / ~6 min per `val` lemma → OOM). Here the impl closed form is
  factored into small **compositional component defs** (`d_i1`, `d_r1`, `d_ceil`,
  `d_res95232`, `d_high95232`, `d_res261888`, `d_high261888`, `d_center`, `d_low`,
  `d_high`), and each `.val` lemma keeps a tiny goal (one operation over an already
  proven `.val`), so the bv operations stay behind opaque named defs and never get
  inlined into a giant term.

  The integer identities (`decompose_int_identity_*`) are split into an opaque-param
  `_core` (all products have literal coefficients ⇒ `omega` stays linear/fast) plus a
  thin `let`-based wrapper that derives the linear hypotheses from the `Int.ediv`
  defining inequalities.

  - `decompose_element_eq_ok` — the do-block reduces to `.ok (decompose_impl_value …)`
  - `decompose_val_{95232,261888}` — impl projections in terms of `rPlus/ceil/res`
  - `decompose_int_identity_{95232,261888}` — ties those to `Spec.Rounding.decompose`
  - `decompose_element_spec` — per-lane Triple (swap: `.1 = spec.2`, `.2 = spec.1`)
  - `decompose_spec` — top-level dual-output `@[spec]` Triple (read-source-separate loop)
-/

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.Rounding
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Util.LoopHelper

/-! ## Re-stated infra (kept private/local; copies of the `Arithmetic.lean` privates so
    this file is self-contained and `Arithmetic.lean` stays byte-identical). -/

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok_l0 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Triple, Std.Do.WP.wp, PostCond.noThrow, Std.Do.PredTrans.apply, hp]

private theorem triple_exists_ok_l0 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
    exact ⟨v, rfl,
      (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ =>
    exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div =>
    exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem coeff_slice_len_eq (a : CoeffArray) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (8#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  rw [Aeneas.Std.Slice.len_val]
  show (Aeneas.Std.Array.to_slice a).length = (8#usize : Std.Usize).val
  rw [Aeneas.Std.Array.length_to_slice a]

private theorem sshiftRight_val_i32 (x : Std.I32) (k : Nat) :
    (⟨x.bv.sshiftRight k⟩ : Std.I32).val = x.val / (2 ^ k : Int) := by
  show (x.bv.sshiftRight k).toInt = _
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast

private theorem wrapping_add_val_noov (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val + y.val) (hub : x.val + y.val < 2 ^ 31) :
    (Aeneas.Std.I32.wrapping_add x y).val = x.val + y.val := by
  rw [Aeneas.Std.I32.wrapping_add_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hlb
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hub

private theorem wrapping_sub_val_noov (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val - y.val) (hub : x.val - y.val < 2 ^ 31) :
    (Aeneas.Std.I32.wrapping_sub x y).val = x.val - y.val := by
  rw [Aeneas.Std.I32.wrapping_sub_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hlb
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hub

private theorem wrapping_mul_val_noov (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val * y.val) (hub : x.val * y.val < 2 ^ 31) :
    (Aeneas.Std.I32.wrapping_mul x y).val = x.val * y.val := by
  rw [Aeneas.Std.I32.wrapping_mul_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hlb
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hub

/-- Sign-mask `.val`: `(x >> 31) & q` is `q` iff `x < 0`, else `0` (kernel-checkable). -/
private theorem sign_mask_and_val (x : Std.I32) :
    (⟨(x.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32).val
      = if x.val < 0 then 8380417 else 0 := by
  have h_bd := Aeneas.Std.IScalar.hBounds x
  have h_shrtoInt : (x.bv.sshiftRight 31).toInt = x.val / (2 ^ 31 : Int) := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  have h_lb : -(2 ^ 31 : Int) ≤ x.val := by
    have := h_bd.1; simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_ub : x.val < (2 ^ 31 : Int) := by
    have := h_bd.2; simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  by_cases h : x.val < 0
  · rw [if_pos h]
    have h_div : x.val / (2 ^ 31 : Int) = -1 := by omega
    have h_allones : x.bv.sshiftRight 31 = BitVec.allOnes 32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((x.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv).toInt = _
    rw [h_allones, BitVec.allOnes_and]; decide
  · rw [if_neg h]
    have h_div : x.val / (2 ^ 31 : Int) = 0 := by omega
    have h_zero : x.bv.sshiftRight 31 = 0#32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((x.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv).toInt = _
    rw [h_zero, BitVec.zero_and]; decide

/-- `(result ^^^ (s >> 31)) & result` clamps `result` to `0` when `s < 0`, else keeps it.
    With `s = 43 - result` this is `if 43 < result then 0 else result`. -/
private theorem xor_clamp_val (s result : Std.I32)
    (hs : s.val = 43 - result.val) (h0 : 0 ≤ result.val) (hub : result.val < 8380417) :
    (⟨((result ^^^ (⟨s.bv.sshiftRight 31⟩ : Std.I32)).bv) &&& result.bv⟩ : Std.I32).val
      = if 43 < result.val then 0 else result.val := by
  have h_bd := Aeneas.Std.IScalar.hBounds s
  have h_lb : -(2 ^ 31 : Int) ≤ s.val := by
    have := h_bd.1; simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_ub : s.val < (2 ^ 31 : Int) := by
    have := h_bd.2; simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_shrtoInt : (s.bv.sshiftRight 31).toInt = s.val / (2 ^ 31 : Int) := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  by_cases h : 43 < result.val
  · rw [if_pos h]
    have h_div : s.val / (2 ^ 31 : Int) = -1 := by omega
    have h_allones : s.bv.sshiftRight 31 = BitVec.allOnes 32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((result.bv ^^^ (⟨s.bv.sshiftRight 31⟩ : Std.I32).bv) &&& result.bv).toInt = _
    rw [show (⟨s.bv.sshiftRight 31⟩ : Std.I32).bv = s.bv.sshiftRight 31 from rfl, h_allones]
    rw [show result.bv ^^^ BitVec.allOnes 32 = ~~~ result.bv from by rw [BitVec.xor_allOnes]]
    rw [BitVec.not_and_self result.bv]; rfl
  · rw [if_neg h]
    have h_div : s.val / (2 ^ 31 : Int) = 0 := by omega
    have h_zero : s.bv.sshiftRight 31 = 0#32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((result.bv ^^^ (⟨s.bv.sshiftRight 31⟩ : Std.I32).bv) &&& result.bv).toInt = _
    rw [show (⟨s.bv.sshiftRight 31⟩ : Std.I32).bv = s.bv.sshiftRight 31 from rfl, h_zero]
    rw [show result.bv ^^^ 0#32 = result.bv from by rw [BitVec.xor_zero], BitVec.and_self]
    rfl

/-- `result & 15 = result % 16` for `0 ≤ result < q`. -/
private theorem and_15_val (result : Std.I32) (h0 : 0 ≤ result.val) (hub : result.val < 8380417) :
    (⟨result.bv &&& (15#i32 : Std.I32).bv⟩ : Std.I32).val = result.val % 16 := by
  have h15 : (15#i32 : Std.I32).bv = (15 : BitVec 32) := rfl
  have h_two_lt : 2 * result.bv.toNat < 2^32 := by
    have hcond := BitVec.toInt_eq_msb_cond result.bv
    have hv : result.bv.toInt = result.val := rfl
    by_cases hm : result.bv.msb = true
    · rw [hm, if_pos rfl] at hcond
      have hb := result.bv.isLt
      have : (result.bv.toNat : Int) < 2^32 := by exact_mod_cast hb
      rw [hv] at hcond; omega
    · simp only [Bool.not_eq_true] at hm
      exact BitVec.msb_eq_false_iff_two_mul_lt.mp hm
  have h_val_toNat : result.val = (result.bv.toNat : Int) := by
    show result.bv.toInt = _; rw [BitVec.toInt_eq_toNat_of_lt h_two_lt]
  have h_and_toNat : (result.bv &&& (15 : BitVec 32)).toNat = result.bv.toNat % 16 := by
    rw [BitVec.toNat_and]
    show result.bv.toNat &&& (15 : BitVec 32).toNat = result.bv.toNat % 16
    rw [show (15 : BitVec 32).toNat = 15 from rfl, show (15:Nat) = 2^4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
  have h_lt : 2 * (result.bv &&& (15 : BitVec 32)).toNat < 2^32 := by
    rw [h_and_toNat]; have := Nat.mod_lt result.bv.toNat (show 0 < 16 by decide); omega
  show (result.bv &&& (15#i32 : Std.I32).bv).toInt = result.val % 16
  rw [h15, BitVec.toInt_eq_toNat_of_lt h_lt, h_and_toNat, h_val_toNat]; push_cast; rfl

/-! ## Compositional component defs (impl closed form, factored so each `.val` is small). -/

def d_i (r : Std.I32) : Std.I32 := ⟨r.bv.sshiftRight 31⟩
def d_i1 (r : Std.I32) : Std.I32 := ⟨(d_i r).bv &&& (8380417#i32 : Std.I32).bv⟩
def d_r1 (r : Std.I32) : Std.I32 := Aeneas.Std.I32.wrapping_add r (d_i1 r)
def d_ceil (r : Std.I32) : Std.I32 :=
  ⟨(Aeneas.Std.I32.wrapping_add (d_r1 r) (127#i32)).bv.sshiftRight 7⟩

def d_res95232 (r : Std.I32) : Std.I32 :=
  ⟨(Aeneas.Std.I32.wrapping_add (Aeneas.Std.I32.wrapping_mul (d_ceil r) (11275#i32))
      ⟨(1#i32 : Std.I32).bv.shiftLeft 23⟩).bv.sshiftRight 24⟩
def d_high95232 (r : Std.I32) : Std.I32 :=
  ⟨((d_res95232 r) ^^^ ⟨(Aeneas.Std.I32.wrapping_sub (43#i32) (d_res95232 r)).bv.sshiftRight 31⟩).bv
      &&& (d_res95232 r).bv⟩

def d_res261888 (r : Std.I32) : Std.I32 :=
  ⟨(Aeneas.Std.I32.wrapping_add (Aeneas.Std.I32.wrapping_mul (d_ceil r) (1025#i32))
      ⟨(1#i32 : Std.I32).bv.shiftLeft 21⟩).bv.sshiftRight 22⟩
def d_high261888 (r : Std.I32) : Std.I32 :=
  ⟨(d_res261888 r).bv &&& (15#i32 : Std.I32).bv⟩

def d_high (gamma2 r : Std.I32) : Std.I32 :=
  match gamma2 with
  | 95232#iscalar => d_high95232 r
  | 261888#iscalar => d_high261888 r
  | _ => 0#i32

/-- Centering tail (shared by both `gamma2`): `r0 ↦ r0 - (if 4190208 < r0 then q else 0)`. -/
def d_center (r0 : Std.I32) : Std.I32 :=
  Aeneas.Std.I32.wrapping_sub r0
    ⟨(⟨(Aeneas.Std.I32.wrapping_sub (4190208#i32) r0).bv.sshiftRight 31⟩ : Std.I32).bv
        &&& (8380417#i32 : Std.I32).bv⟩

def d_low (gamma2 r r11 : Std.I32) : Std.I32 :=
  d_center (Aeneas.Std.I32.wrapping_sub (d_r1 r)
    (Aeneas.Std.I32.wrapping_mul r11 (Aeneas.Std.I32.wrapping_mul gamma2 (2#i32))))

/-- Closed pure form of `decompose_element` (LOW, HIGH). -/
def decompose_impl_value (gamma2 r : Std.I32) : Std.I32 × Std.I32 :=
  (d_low gamma2 r (d_high gamma2 r), d_high gamma2 r)

/-! ## `eq_ok` — the do-block reduces to `.ok (decompose_impl_value …)`. -/

/-- `(q-1)/2 = 4190208` as the I32 checked division (the single checked-div the `whnf`
    cannot reduce). -/
private theorem div_q1_half (X : Std.I32) (hX : X.bv = (8380416#i32 : Std.I32).bv) :
    (X / (2#i32 : Std.I32) : Result Std.I32) = .ok (4190208#i32) := by
  show Aeneas.Std.IScalar.div X (2#i32 : Std.I32) = _
  unfold Aeneas.Std.IScalar.div
  have hval : X.val = 8380416 := by rw [show X.val = X.bv.toInt from rfl, hX]; decide
  rw [if_pos (by decide), if_pos (by simp only [hval, Aeneas.Std.IScalar.min]; decide)]
  rw [show (X.bv.sdiv (2#i32 : Std.I32).bv) = (4190208#i32 : Std.I32).bv from by rw [hX]; decide]

set_option maxHeartbeats 4000000 in
theorem decompose_element_eq_ok (gamma2 r : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element gamma2 r
      = .ok (decompose_impl_value gamma2 r) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element decompose_impl_value
        d_low d_center d_high d_high95232 d_high261888 d_res95232 d_res261888 d_ceil d_r1 d_i1 d_i
        libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS
  rcases hg with hg | hg <;> subst hg <;>
  · conv_lhs => whnf
    rw [div_q1_half _ (by rfl)]
    conv_lhs => whnf
    rfl

/-! ## Per-component `.val` lemmas (each goal is one operation over an opaque component). -/

theorem d_i1_val (r : Std.I32) :
    (d_i1 r).val = if r.val < 0 then 8380417 else 0 := by
  unfold d_i1 d_i
  exact sign_mask_and_val r

theorem d_r1_val (r : Std.I32) (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < 8380417) :
    (d_r1 r).val = r.val + (if r.val < 0 then 8380417 else 0) := by
  unfold d_r1
  rw [wrapping_add_val_noov r (d_i1 r) (by rw [d_i1_val]; split <;> omega)
        (by rw [d_i1_val]; split <;> omega), d_i1_val]

theorem d_ceil_val (r : Std.I32) (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < 8380417) :
    (d_ceil r).val = (r.val + (if r.val < 0 then 8380417 else 0) + 127) / 128 := by
  unfold d_ceil
  rw [sshiftRight_val_i32,
      wrapping_add_val_noov (d_r1 r) (127#i32)
        (by rw [d_r1_val r hlo hhi, show ((127#i32 : Std.I32).val) = 127 from rfl]; split <;> omega)
        (by rw [d_r1_val r hlo hhi, show ((127#i32 : Std.I32).val) = 127 from rfl]; split <;> omega),
      d_r1_val r hlo hhi, show ((127#i32 : Std.I32).val) = 127 from rfl,
      show ((2 : Int) ^ 7) = 128 from by norm_num]

theorem d_res95232_val (r : Std.I32)
    (hcl : 0 ≤ (d_ceil r).val) (hch : (d_ceil r).val ≤ 65472) :
    (d_res95232 r).val = ((d_ceil r).val * 11275 + 8388608) / 16777216 := by
  unfold d_res95232
  have h_i4 : (⟨(1#i32 : Std.I32).bv.shiftLeft 23⟩ : Std.I32).val = 8388608 := by decide
  have h_i3 : (Aeneas.Std.I32.wrapping_mul (d_ceil r) (11275#i32)).val = (d_ceil r).val * 11275 := by
    rw [wrapping_mul_val_noov (d_ceil r) (11275#i32)
        (by rw [show ((11275#i32 : Std.I32).val) = 11275 from rfl]; nlinarith [hcl])
        (by rw [show ((11275#i32 : Std.I32).val) = 11275 from rfl]; nlinarith [hch]),
        show ((11275#i32 : Std.I32).val) = 11275 from rfl]
  rw [sshiftRight_val_i32,
      wrapping_add_val_noov _ _ (by rw [h_i3, h_i4]; nlinarith [hcl]) (by rw [h_i3, h_i4]; nlinarith [hch]),
      h_i3, h_i4, show ((2 : Int) ^ 24) = 16777216 from by norm_num]

theorem d_high95232_val (r : Std.I32)
    (hrl : 0 ≤ (d_res95232 r).val) (hrh : (d_res95232 r).val < 8380417) :
    (d_high95232 r).val = if 43 < (d_res95232 r).val then 0 else (d_res95232 r).val := by
  unfold d_high95232
  have h_i7 : (Aeneas.Std.I32.wrapping_sub (43#i32) (d_res95232 r)).val = 43 - (d_res95232 r).val := by
    rw [wrapping_sub_val_noov (43#i32) (d_res95232 r)
        (by rw [show ((43#i32 : Std.I32).val) = 43 from rfl]; omega)
        (by rw [show ((43#i32 : Std.I32).val) = 43 from rfl]; omega),
        show ((43#i32 : Std.I32).val) = 43 from rfl]
  exact xor_clamp_val (Aeneas.Std.I32.wrapping_sub (43#i32) (d_res95232 r)) (d_res95232 r) h_i7 hrl hrh

theorem d_res261888_val (r : Std.I32)
    (hcl : 0 ≤ (d_ceil r).val) (hch : (d_ceil r).val ≤ 65472) :
    (d_res261888 r).val = ((d_ceil r).val * 1025 + 2097152) / 4194304 := by
  unfold d_res261888
  have h_i4 : (⟨(1#i32 : Std.I32).bv.shiftLeft 21⟩ : Std.I32).val = 2097152 := by decide
  have h_i3 : (Aeneas.Std.I32.wrapping_mul (d_ceil r) (1025#i32)).val = (d_ceil r).val * 1025 := by
    rw [wrapping_mul_val_noov (d_ceil r) (1025#i32)
        (by rw [show ((1025#i32 : Std.I32).val) = 1025 from rfl]; nlinarith [hcl])
        (by rw [show ((1025#i32 : Std.I32).val) = 1025 from rfl]; nlinarith [hch]),
        show ((1025#i32 : Std.I32).val) = 1025 from rfl]
  rw [sshiftRight_val_i32,
      wrapping_add_val_noov _ _ (by rw [h_i3, h_i4]; nlinarith [hcl]) (by rw [h_i3, h_i4]; nlinarith [hch]),
      h_i3, h_i4, show ((2 : Int) ^ 22) = 4194304 from by norm_num]

theorem d_high261888_val (r : Std.I32)
    (hrl : 0 ≤ (d_res261888 r).val) (hrh : (d_res261888 r).val < 8380417) :
    (d_high261888 r).val = (d_res261888 r).val % 16 := by
  unfold d_high261888
  exact and_15_val (d_res261888 r) hrl hrh

/-- Centering tail value: `r0 ↦ r0 - (if 4190208 < r0 then q else 0)` for `r0 ∈ [-q, q)`. -/
theorem d_center_val (r0 : Std.I32) (hlo : -(8380417 : Int) ≤ r0.val) (hhi : r0.val < 8380417) :
    (d_center r0).val = r0.val - (if 4190208 < r0.val then 8380417 else 0) := by
  unfold d_center
  have h_i7' : (Aeneas.Std.I32.wrapping_sub (4190208#i32) r0).val = 4190208 - r0.val := by
    rw [wrapping_sub_val_noov (4190208#i32) r0
        (by rw [show ((4190208#i32 : Std.I32).val) = 4190208 from rfl]; omega)
        (by rw [show ((4190208#i32 : Std.I32).val) = 4190208 from rfl]; omega),
        show ((4190208#i32 : Std.I32).val) = 4190208 from rfl]
  have h_i9' : (⟨(⟨(Aeneas.Std.I32.wrapping_sub (4190208#i32) r0).bv.sshiftRight 31⟩ : Std.I32).bv
        &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32).val = if 4190208 < r0.val then 8380417 else 0 := by
    rw [sign_mask_and_val (Aeneas.Std.I32.wrapping_sub (4190208#i32) r0), h_i7']
    by_cases hc : 4190208 < r0.val
    · rw [if_pos (by omega), if_pos hc]
    · rw [if_neg (by omega), if_neg hc]
  rw [wrapping_sub_val_noov r0 _ (by rw [h_i9']; split <;> omega) (by rw [h_i9']; split <;> omega), h_i9']

/-- Low/centered output, generic over the high value `r11` and the inner product `P = r11·α`. -/
theorem d_low_val (gamma2 r r11 : Std.I32) (rPlus P : Int)
    (h_r1 : (d_r1 r).val = rPlus)
    (h_mul : (Aeneas.Std.I32.wrapping_mul r11 (Aeneas.Std.I32.wrapping_mul gamma2 (2#i32))).val = P)
    (hr0_lo : -(8380417 : Int) ≤ rPlus - P) (hr0_hi : rPlus - P < 8380417) :
    (d_low gamma2 r r11).val
      = (rPlus - P) - (if 4190208 < rPlus - P then 8380417 else 0) := by
  unfold d_low
  have h_r0 : (Aeneas.Std.I32.wrapping_sub (d_r1 r)
      (Aeneas.Std.I32.wrapping_mul r11 (Aeneas.Std.I32.wrapping_mul gamma2 (2#i32)))).val
        = rPlus - P := by
    rw [wrapping_sub_val_noov _ _ (by rw [h_r1, h_mul]; omega) (by rw [h_r1, h_mul]; omega), h_r1, h_mul]
  rw [d_center_val _ (by rw [h_r0]; omega) (by rw [h_r0]; omega), h_r0]

/-! ## Assembled per-branch impl-value projections (in terms of `rPlus/ceil/res`). -/

set_option maxHeartbeats 1000000 in
theorem decompose_val_95232 (r : Std.I32) (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < 8380417) :
    let rPlus := r.val + (if r.val < 0 then 8380417 else 0)
    let ceilv := (rPlus + 127) / 128
    let res := (ceilv * 11275 + 8388608) / 16777216
    let r11v := (if 43 < res then 0 else res)
    (decompose_impl_value 95232#i32 r).2.val = r11v
    ∧ (decompose_impl_value 95232#i32 r).1.val
        = (rPlus - r11v * 190464) - (if 4190208 < rPlus - r11v * 190464 then 8380417 else 0) := by
  intro rPlus ceilv res r11v
  have hrP_lo : 0 ≤ rPlus := by simp only [rPlus]; split <;> omega
  have hrP_hi : rPlus < 8380417 := by simp only [rPlus]; split <;> omega
  have h_ceilv : (d_ceil r).val = ceilv := d_ceil_val r hlo hhi
  have h_ceil_lo : 0 ≤ (d_ceil r).val := by rw [h_ceilv]; simp only [ceilv]; omega
  have h_ceil_hi : (d_ceil r).val ≤ 65472 := by rw [h_ceilv]; simp only [ceilv]; omega
  have h_resv : (d_res95232 r).val = res := by
    rw [d_res95232_val r h_ceil_lo h_ceil_hi, h_ceilv]
  have h_res_lo : 0 ≤ (d_res95232 r).val := by
    rw [h_resv]; simp only [res]; apply Int.ediv_nonneg _ (by norm_num); nlinarith [h_ceil_lo, h_ceilv]
  have h_res_hi : (d_res95232 r).val ≤ 44 := by
    rw [h_resv]; simp only [res]
    have hb : ceilv * 11275 + 8388608 ≤ 65472 * 11275 + 8388608 := by nlinarith [h_ceil_hi, h_ceilv]
    calc (ceilv * 11275 + 8388608) / 16777216
        ≤ (65472 * 11275 + 8388608) / 16777216 := Int.ediv_le_ediv (by norm_num) hb
      _ = 44 := by norm_num
  have h_res_q : (d_res95232 r).val < 8380417 := by omega
  -- high (r11) projection
  have h_high : (decompose_impl_value 95232#i32 r).2.val = r11v := by
    show (d_high95232 r).val = r11v
    rw [d_high95232_val r h_res_lo h_res_q, h_resv]
  -- r11v bounds
  have hr11_lo : 0 ≤ r11v := by simp only [r11v]; split <;> omega
  have hr11_hi : r11v ≤ 43 := by simp only [r11v]; split <;> omega
  -- low (r01) projection via d_low_val
  have h_r1v : (d_r1 r).val = rPlus := d_r1_val r hlo hhi
  have h_high_val : (d_high 95232#i32 r).val = r11v := by show (d_high95232 r).val = r11v; rw [d_high95232_val r h_res_lo h_res_q, h_resv]
  have h_alpha : (Aeneas.Std.I32.wrapping_mul (95232#i32) (2#i32)).val = 190464 := by decide
  have h_mul : (Aeneas.Std.I32.wrapping_mul (d_high 95232#i32 r)
      (Aeneas.Std.I32.wrapping_mul (95232#i32) (2#i32))).val = r11v * 190464 := by
    rw [wrapping_mul_val_noov _ _ (by rw [h_high_val, h_alpha]; nlinarith [hr11_lo, hr11_hi])
          (by rw [h_high_val, h_alpha]; nlinarith [hr11_lo, hr11_hi]), h_high_val, h_alpha]
  have h_low : (decompose_impl_value 95232#i32 r).1.val
      = (rPlus - r11v * 190464) - (if 4190208 < rPlus - r11v * 190464 then 8380417 else 0) := by
    show (d_low 95232#i32 r (d_high 95232#i32 r)).val = _
    rw [d_low_val (95232#i32) r (d_high 95232#i32 r) rPlus (r11v * 190464) h_r1v h_mul
          (by nlinarith [hr11_lo, hr11_hi]) (by nlinarith [hr11_lo, hr11_hi])]
  exact ⟨h_high, h_low⟩

set_option maxHeartbeats 1000000 in
theorem decompose_val_261888 (r : Std.I32) (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < 8380417) :
    let rPlus := r.val + (if r.val < 0 then 8380417 else 0)
    let ceilv := (rPlus + 127) / 128
    let res := (ceilv * 1025 + 2097152) / 4194304
    let r11v := res % 16
    (decompose_impl_value 261888#i32 r).2.val = r11v
    ∧ (decompose_impl_value 261888#i32 r).1.val
        = (rPlus - r11v * 523776) - (if 4190208 < rPlus - r11v * 523776 then 8380417 else 0) := by
  intro rPlus ceilv res r11v
  have hrP_lo : 0 ≤ rPlus := by simp only [rPlus]; split <;> omega
  have hrP_hi : rPlus < 8380417 := by simp only [rPlus]; split <;> omega
  have h_ceilv : (d_ceil r).val = ceilv := d_ceil_val r hlo hhi
  have h_ceil_lo : 0 ≤ (d_ceil r).val := by rw [h_ceilv]; simp only [ceilv]; omega
  have h_ceil_hi : (d_ceil r).val ≤ 65472 := by rw [h_ceilv]; simp only [ceilv]; omega
  have h_resv : (d_res261888 r).val = res := by
    rw [d_res261888_val r h_ceil_lo h_ceil_hi, h_ceilv]
  have h_res_lo : 0 ≤ (d_res261888 r).val := by
    rw [h_resv]; simp only [res]; apply Int.ediv_nonneg _ (by norm_num); nlinarith [h_ceil_lo, h_ceilv]
  have h_res_hi : (d_res261888 r).val ≤ 16 := by
    rw [h_resv]; simp only [res]
    have hb : ceilv * 1025 + 2097152 ≤ 65472 * 1025 + 2097152 := by nlinarith [h_ceil_hi, h_ceilv]
    calc (ceilv * 1025 + 2097152) / 4194304
        ≤ (65472 * 1025 + 2097152) / 4194304 := Int.ediv_le_ediv (by norm_num) hb
      _ = 16 := by norm_num
  have h_res_q : (d_res261888 r).val < 8380417 := by omega
  have h_high : (decompose_impl_value 261888#i32 r).2.val = r11v := by
    show (d_high261888 r).val = r11v
    rw [d_high261888_val r h_res_lo h_res_q, h_resv]
  have hr11_lo : 0 ≤ r11v := by simp only [r11v]; omega
  have hr11_hi : r11v ≤ 15 := by
    simp only [r11v]; have := Int.emod_lt_of_pos res (show (0:Int) < 16 by norm_num); omega
  have h_r1v : (d_r1 r).val = rPlus := d_r1_val r hlo hhi
  have h_high_val : (d_high 261888#i32 r).val = r11v := by show (d_high261888 r).val = r11v; rw [d_high261888_val r h_res_lo h_res_q, h_resv]
  have h_alpha : (Aeneas.Std.I32.wrapping_mul (261888#i32) (2#i32)).val = 523776 := by decide
  have h_mul : (Aeneas.Std.I32.wrapping_mul (d_high 261888#i32 r)
      (Aeneas.Std.I32.wrapping_mul (261888#i32) (2#i32))).val = r11v * 523776 := by
    rw [wrapping_mul_val_noov _ _ (by rw [h_high_val, h_alpha]; nlinarith [hr11_lo, hr11_hi])
          (by rw [h_high_val, h_alpha]; nlinarith [hr11_lo, hr11_hi]), h_high_val, h_alpha]
  have h_low : (decompose_impl_value 261888#i32 r).1.val
      = (rPlus - r11v * 523776) - (if 4190208 < rPlus - r11v * 523776 then 8380417 else 0) := by
    show (d_low 261888#i32 r (d_high 261888#i32 r)).val = _
    rw [d_low_val (261888#i32) r (d_high 261888#i32 r) rPlus (r11v * 523776) h_r1v h_mul
          (by nlinarith [hr11_lo, hr11_hi]) (by nlinarith [hr11_lo, hr11_hi])]
  exact ⟨h_high, h_low⟩

/-! ## Integer identities — opaque-param `_core` (linear omega) + `let`-based wrapper. -/

open libcrux_iot_ml_dsa.Spec.Rounding in
/-- `modPm` uniqueness: the unique rep of `rPlus` mod `m` in `(-m/2, m/2]`. -/
private theorem modPm_unique (rPlus v m : Int) (hm : 0 < m) (hcong : ∃ k, v = rPlus - k * m)
    (hlo : -(m/2) < v) (hhi : v ≤ m/2) (heven : m % 2 = 0) :
    modPm rPlus m = v := by
  unfold modPm
  obtain ⟨k, hk⟩ := hcong
  have hrv : rPlus % m = v % m := by
    rw [hk, Int.sub_emod, Int.mul_emod_left, sub_zero, Int.emod_emod_of_dvd rPlus (dvd_refl m)]
  have hmod_eq : ((rPlus % m) + m) % m = v % m := by
    rw [Int.add_emod_right, Int.emod_emod_of_dvd rPlus (dvd_refl m), hrv]
  rw [hmod_eq]
  by_cases hvpos : 0 ≤ v
  · rw [Int.emod_eq_of_lt hvpos (by omega), if_neg (by omega)]
  · have hvm : v % m = v + m := by
      rw [← Int.add_emod_right v m, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [hvm, if_pos (by omega)]; omega

open libcrux_iot_ml_dsa.Spec.Rounding in
/-- 95232 identity over **opaque** `rPlus/ceilv/res/r11v/r01v` with their linear defining
    facts (every product has a literal coefficient ⇒ `omega` stays linear). -/
private theorem int_identity_95232_core
    (r rPlus ceilv res r11v r01v : Int)
    (h_rP : rPlus = r + (if r < 0 then 8380417 else 0))
    (hrP_lo : 0 ≤ rPlus) (hrP_hi : rPlus < 8380417)
    (hcb1 : 128 * ceilv ≤ rPlus + 127) (hcb2 : rPlus + 127 < 128 * ceilv + 128)
    (hres1 : 16777216 * res ≤ ceilv * 11275 + 8388608)
    (hres2 : ceilv * 11275 + 8388608 < 16777216 * (res + 1))
    (hres_nn : 0 ≤ res) (hres_cap : res ≤ 44)
    (h_r11v : r11v = if 43 < res then 0 else res)
    (h_r01v : r01v = (rPlus - r11v * 190464)
        - (if 4190208 < rPlus - r11v * 190464 then 8380417 else 0)) :
    r11v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).1
    ∧ r01v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).2 := by
  have hQ : (libcrux_iot_ml_dsa.Spec.Parameters.Q : Int) = 8380417 := rfl
  have hdec : libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232
      = (let rP := r % 8380417
         let rP := if rP < 0 then rP + 8380417 else rP
         let r0 := modPm rP 190464
         if rP - r0 = 8380416 then (0, r0 - 1) else ((rP - r0) / 190464, r0)) := by
    unfold libcrux_iot_ml_dsa.Spec.Rounding.decompose
    simp only [libcrux_iot_ml_dsa.Spec.Rounding.Qi, hQ, show (2:Int)*95232 = 190464 from by norm_num,
      show (8380417:Int) - 1 = 8380416 from by norm_num]
  rw [hdec]
  have hrP_eq : (if r % 8380417 < 0 then r % 8380417 + 8380417 else r % 8380417) = rPlus := by
    rw [h_rP]; omega
  simp only [hrP_eq]
  by_cases hbnd : 43 < res
  · have hres44 : res = 44 := by omega
    have hr11v0 : r11v = 0 := by rw [h_r11v, if_pos hbnd]
    have hrP_large : 8285185 ≤ rPlus := by omega
    have hmodpm : modPm rPlus 190464 = rPlus - 8380416 := by
      apply modPm_unique rPlus (rPlus - 8380416) 190464 (by norm_num) ⟨44, by ring⟩
        (by omega) (by omega) (by norm_num)
    simp only [hmodpm]
    rw [if_pos (by omega)]
    refine ⟨hr11v0, ?_⟩
    rw [h_r01v, hr11v0]; rw [if_pos (by omega)]; omega
  · have hr11v : r11v = res := by rw [h_r11v, if_neg (by omega)]
    have hb1 : -95232 < rPlus - res * 190464 := by omega
    have hb2 : rPlus - res * 190464 ≤ 95232 := by omega
    have hmodpm : modPm rPlus 190464 = rPlus - res * 190464 := by
      apply modPm_unique rPlus (rPlus - res * 190464) 190464 (by norm_num) ⟨res, by ring⟩
        (by omega) (by omega) (by norm_num)
    simp only [hmodpm]
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [hr11v]
      have : (rPlus - (rPlus - res * 190464)) / 190464 = res := by
        rw [show rPlus - (rPlus - res * 190464) = res * 190464 from by ring]
        rw [Int.mul_ediv_cancel _ (by norm_num)]
      omega
    · rw [h_r01v, hr11v]; rw [if_neg (by omega)]; omega

open libcrux_iot_ml_dsa.Spec.Rounding in
/-- 95232 identity over the actual `let`-bound div values (thin wrapper deriving the
    linear facts via the `Int.ediv` defining inequalities). -/
theorem decompose_int_identity_95232 (r : Int) (hlo : -(8380417 : Int) ≤ r) (hhi : r < 8380417) :
    let rPlus := r + (if r < 0 then 8380417 else 0)
    let ceilv := (rPlus + 127) / 128
    let res := (ceilv * 11275 + 8388608) / 16777216
    let r11v := (if 43 < res then 0 else res)
    let r01v := (rPlus - r11v * 190464) - (if 4190208 < rPlus - r11v * 190464 then 8380417 else 0)
    r11v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).1
    ∧ r01v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).2 := by
  intro rPlus ceilv res r11v r01v
  have hrP_lo : 0 ≤ rPlus := by simp only [rPlus]; split <;> omega
  have hrP_hi : rPlus < 8380417 := by simp only [rPlus]; split <;> omega
  have hcb1 : 128 * ceilv ≤ rPlus + 127 := by
    simp only [ceilv]; have := Int.ediv_mul_le (rPlus + 127) (show (128:Int) ≠ 0 by norm_num); omega
  have hcb2 : rPlus + 127 < 128 * ceilv + 128 := by
    simp only [ceilv]; have := Int.lt_ediv_add_one_mul_self (rPlus + 127) (show (0:Int) < 128 by norm_num); omega
  have hres1 : 16777216 * res ≤ ceilv * 11275 + 8388608 := by
    simp only [res]; have := Int.ediv_mul_le (ceilv * 11275 + 8388608) (show (16777216:Int) ≠ 0 by norm_num); omega
  have hres2 : ceilv * 11275 + 8388608 < 16777216 * (res + 1) := by
    simp only [res]; have := Int.lt_ediv_add_one_mul_self (ceilv * 11275 + 8388608) (show (0:Int) < 16777216 by norm_num); omega
  have hres_nn : 0 ≤ res := by
    simp only [res]; apply Int.ediv_nonneg _ (by norm_num)
    have : 0 ≤ ceilv := by simp only [ceilv]; omega
    nlinarith [this]
  have hres_cap : res ≤ 44 := by
    have hceil_cap : ceilv ≤ 65472 := by simp only [ceilv]; omega
    simp only [res]
    have hb : ceilv * 11275 + 8388608 ≤ 65472 * 11275 + 8388608 := by nlinarith [hceil_cap]
    calc (ceilv * 11275 + 8388608) / 16777216
        ≤ (65472 * 11275 + 8388608) / 16777216 := Int.ediv_le_ediv (by norm_num) hb
      _ = 44 := by norm_num
  exact int_identity_95232_core r rPlus ceilv res r11v r01v rfl hrP_lo hrP_hi hcb1 hcb2
    hres1 hres2 hres_nn hres_cap rfl rfl

open libcrux_iot_ml_dsa.Spec.Rounding in
private theorem int_identity_261888_core
    (r rPlus ceilv res r11v r01v : Int)
    (h_rP : rPlus = r + (if r < 0 then 8380417 else 0))
    (hrP_lo : 0 ≤ rPlus) (hrP_hi : rPlus < 8380417)
    (hcb1 : 128 * ceilv ≤ rPlus + 127) (hcb2 : rPlus + 127 < 128 * ceilv + 128)
    (hres1 : 4194304 * res ≤ ceilv * 1025 + 2097152)
    (hres2 : ceilv * 1025 + 2097152 < 4194304 * (res + 1))
    (hres_nn : 0 ≤ res) (hres_cap : res ≤ 16)
    (h_r11v : r11v = res % 16)
    (h_r01v : r01v = (rPlus - r11v * 523776)
        - (if 4190208 < rPlus - r11v * 523776 then 8380417 else 0)) :
    r11v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).1
    ∧ r01v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).2 := by
  have hQ : (libcrux_iot_ml_dsa.Spec.Parameters.Q : Int) = 8380417 := rfl
  have hdec : libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888
      = (let rP := r % 8380417
         let rP := if rP < 0 then rP + 8380417 else rP
         let r0 := modPm rP 523776
         if rP - r0 = 8380416 then (0, r0 - 1) else ((rP - r0) / 523776, r0)) := by
    unfold libcrux_iot_ml_dsa.Spec.Rounding.decompose
    simp only [libcrux_iot_ml_dsa.Spec.Rounding.Qi, hQ, show (2:Int)*261888 = 523776 from by norm_num,
      show (8380417:Int) - 1 = 8380416 from by norm_num]
  rw [hdec]
  have hrP_eq : (if r % 8380417 < 0 then r % 8380417 + 8380417 else r % 8380417) = rPlus := by
    rw [h_rP]; omega
  simp only [hrP_eq]
  by_cases hbnd : res = 16
  · have hr11v0 : r11v = 0 := by rw [h_r11v, hbnd]; rfl
    have hrP_large : 8118529 ≤ rPlus := by omega
    have hmodpm : modPm rPlus 523776 = rPlus - 8380416 := by
      apply modPm_unique rPlus (rPlus - 8380416) 523776 (by norm_num) ⟨16, by ring⟩
        (by omega) (by omega) (by norm_num)
    simp only [hmodpm]
    rw [if_pos (by omega)]
    refine ⟨hr11v0, ?_⟩
    rw [h_r01v, hr11v0]; rw [if_pos (by omega)]; omega
  · have hres_lt : res < 16 := by omega
    have hr11v : r11v = res := by rw [h_r11v]; exact Int.emod_eq_of_lt hres_nn (by omega)
    have hb1 : -261888 < rPlus - res * 523776 := by omega
    have hb2 : rPlus - res * 523776 ≤ 261888 := by omega
    have hmodpm : modPm rPlus 523776 = rPlus - res * 523776 := by
      apply modPm_unique rPlus (rPlus - res * 523776) 523776 (by norm_num) ⟨res, by ring⟩
        (by omega) (by omega) (by norm_num)
    simp only [hmodpm]
    rw [if_neg (by omega)]
    refine ⟨?_, ?_⟩
    · rw [hr11v]
      have : (rPlus - (rPlus - res * 523776)) / 523776 = res := by
        rw [show rPlus - (rPlus - res * 523776) = res * 523776 from by ring]
        rw [Int.mul_ediv_cancel _ (by norm_num)]
      omega
    · rw [h_r01v, hr11v]; rw [if_neg (by omega)]; omega

open libcrux_iot_ml_dsa.Spec.Rounding in
theorem decompose_int_identity_261888 (r : Int) (hlo : -(8380417 : Int) ≤ r) (hhi : r < 8380417) :
    let rPlus := r + (if r < 0 then 8380417 else 0)
    let ceilv := (rPlus + 127) / 128
    let res := (ceilv * 1025 + 2097152) / 4194304
    let r11v := res % 16
    let r01v := (rPlus - r11v * 523776) - (if 4190208 < rPlus - r11v * 523776 then 8380417 else 0)
    r11v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).1
    ∧ r01v = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).2 := by
  intro rPlus ceilv res r11v r01v
  have hrP_lo : 0 ≤ rPlus := by simp only [rPlus]; split <;> omega
  have hrP_hi : rPlus < 8380417 := by simp only [rPlus]; split <;> omega
  have hcb1 : 128 * ceilv ≤ rPlus + 127 := by
    simp only [ceilv]; have := Int.ediv_mul_le (rPlus + 127) (show (128:Int) ≠ 0 by norm_num); omega
  have hcb2 : rPlus + 127 < 128 * ceilv + 128 := by
    simp only [ceilv]; have := Int.lt_ediv_add_one_mul_self (rPlus + 127) (show (0:Int) < 128 by norm_num); omega
  have hres1 : 4194304 * res ≤ ceilv * 1025 + 2097152 := by
    simp only [res]; have := Int.ediv_mul_le (ceilv * 1025 + 2097152) (show (4194304:Int) ≠ 0 by norm_num); omega
  have hres2 : ceilv * 1025 + 2097152 < 4194304 * (res + 1) := by
    simp only [res]; have := Int.lt_ediv_add_one_mul_self (ceilv * 1025 + 2097152) (show (0:Int) < 4194304 by norm_num); omega
  have hres_nn : 0 ≤ res := by
    simp only [res]; apply Int.ediv_nonneg _ (by norm_num)
    have : 0 ≤ ceilv := by simp only [ceilv]; omega
    nlinarith [this]
  have hres_cap : res ≤ 16 := by
    have hceil_cap : ceilv ≤ 65472 := by simp only [ceilv]; omega
    simp only [res]
    have hb : ceilv * 1025 + 2097152 ≤ 65472 * 1025 + 2097152 := by nlinarith [hceil_cap]
    calc (ceilv * 1025 + 2097152) / 4194304
        ≤ (65472 * 1025 + 2097152) / 4194304 := Int.ediv_le_ediv (by norm_num) hb
      _ = 16 := by norm_num
  exact int_identity_261888_core r rPlus ceilv res r11v r01v rfl hrP_lo hrP_hi hcb1 hcb2
    hres1 hres2 hres_nn hres_cap rfl rfl

/-! ## `decompose_element_spec` — per-lane Triple (swap: `.1 = spec.2`, `.2 = spec.1`). -/

set_option maxHeartbeats 1000000 in
theorem decompose_element_spec (gamma2 r : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32)
    (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < (8380417 : Int)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element gamma2 r
    ⦃ ⇓ p => ⌜ p.1.val = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r.val gamma2.val).2
             ∧ p.2.val = (libcrux_iot_ml_dsa.Spec.Rounding.decompose r.val gamma2.val).1 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := decompose_impl_value gamma2 r) (decompose_element_eq_ok gamma2 r hg)
  rcases hg with hg | hg <;> subst hg
  · obtain ⟨h_hi, h_lo⟩ := decompose_val_95232 r hlo hhi
    obtain ⟨h_id_hi, h_id_lo⟩ := decompose_int_identity_95232 r.val hlo hhi
    refine ⟨?_, ?_⟩
    · show (decompose_impl_value 95232#i32 r).1.val = _
      rw [h_lo]; exact h_id_lo
    · show (decompose_impl_value 95232#i32 r).2.val = _
      rw [h_hi]; exact h_id_hi
  · obtain ⟨h_hi, h_lo⟩ := decompose_val_261888 r hlo hhi
    obtain ⟨h_id_hi, h_id_lo⟩ := decompose_int_identity_261888 r.val hlo hhi
    refine ⟨?_, ?_⟩
    · show (decompose_impl_value 261888#i32 r).1.val = _
      rw [h_lo]; exact h_id_lo
    · show (decompose_impl_value 261888#i32 r).2.val = _
      rw [h_hi]; exact h_id_hi

/-! ## `decompose_spec` — top-level dual-output rounding keystone. -/

private def decompose_per_elem_P (gamma2 : Std.I32) (x : Std.I32) (p : Std.I32 × Std.I32) : Prop :=
  -(8380417 : Int) ≤ x.val → x.val < (8380417 : Int) →
    p.1.val = (libcrux_iot_ml_dsa.Spec.Rounding.decompose x.val gamma2.val).2
    ∧ p.2.val = (libcrux_iot_ml_dsa.Spec.Rounding.decompose x.val gamma2.val).1

private theorem decompose_per_elem_spec (gamma2 : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) (x : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element gamma2 x
    ⦃ ⇓ p => ⌜ decompose_per_elem_P gamma2 x p ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := decompose_impl_value gamma2 x) (decompose_element_eq_ok gamma2 x hg)
  intro hlo hhi
  obtain ⟨v, hv_eq, hv_P⟩ := triple_exists_ok_l0 (decompose_element_spec gamma2 x hg hlo hhi)
  rw [decompose_element_eq_ok gamma2 x hg] at hv_eq
  rw [Result.ok.inj hv_eq]; exact hv_P

set_option maxHeartbeats 2000000 in
@[spec]
theorem decompose_spec (gamma2 : Std.I32)
    (simd_unit low high : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32)
    (hbound : ∀ j : Nat, j < 8 →
        -(8380417 : Int) ≤ (simd_unit.values.val[j]!).val
          ∧ (simd_unit.values.val[j]!).val < (8380417 : Int)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose gamma2 simd_unit low high
    ⦃ ⇓ p => ⌜ ∀ j : Nat, j < 8 →
        (p.1.values.val[j]!).val
          = (libcrux_iot_ml_dsa.Spec.Rounding.decompose (simd_unit.values.val[j]!).val gamma2.val).2
      ∧ (p.2.values.val[j]!).val
          = (libcrux_iot_ml_dsa.Spec.Rounding.decompose (simd_unit.values.val[j]!).val gamma2.val).1
        ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice low.values)
        = .ok (Aeneas.Std.Array.to_slice low.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice low.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice low.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq low.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_loop
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
              × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) =>
         libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_loop.body
           gamma2 simd_unit p.1 p.2.1 p.2.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
              × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) =>
         src_dual_output_loop_body
           (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element gamma2 x)
           simd_unit.values p.1 p.2.1 p.2.2) := by
    funext p
    obtain ⟨iter1, a1, b1⟩ := p
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_loop.body
    unfold src_dual_output_loop_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok_l0
      (elementwise_src_dual_output_spec
        (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.decompose_element gamma2 x)
        (decompose_per_elem_P gamma2) (decompose_per_elem_spec gamma2 hg)
        simd_unit.values low.values high)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok_l0 (v := ({ values := out.1 }, out.2)) rfl ?_
  intro j hj
  obtain ⟨pj, _h_eq, h_a, h_b, h_P⟩ := h_out_P j hj
  obtain ⟨hb_lo, hb_hi⟩ := hbound j hj
  obtain ⟨h_low, h_high⟩ := h_P hb_lo hb_hi
  show (out.1.val[j]!).val = _ ∧ (out.2.values.val[j]!).val = _
  rw [h_a, h_b]
  exact ⟨h_low, h_high⟩

/-! ## `use_hint` — high-bits range, per-lane, and top-level. -/

/-- `classify`/`declassify` are the identity (`= .ok`). -/
private theorem classify_ok (z : Std.I32) :
    libcrux_secrets.traits.Classify.Blanket.classify z = .ok z := rfl

private theorem declassify_ok (z : Std.I32) :
    libcrux_secrets.traits.Declassify.Blanket.declassify z = .ok z := rfl

open libcrux_iot_ml_dsa.Spec.Rounding in
/-- The decompose **high** value lies in `[0, m-1]` (`m = (q-1)/(2·gamma2)`): 44 for 95232,
    16 for 261888. The single load-bearing arithmetic fact for the `use_hint` bridges. Derived
    from the first conjunct of `decompose_int_identity_*`, whose `r11v` is in range by construction. -/
theorem decompose_high_range (gamma2 : Std.I32) (r : Int)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32)
    (hlo : -(8380417 : Int) ≤ r) (hhi : r < 8380417) :
    0 ≤ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r gamma2.val).1
      ∧ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r gamma2.val).1
          ≤ ((8380417 : Int) - 1) / (2 * gamma2.val) - 1 := by
  rcases hg with hg | hg <;> subst hg
  · -- 95232: m = 44, r11v = if 43 < res then 0 else res, res ∈ [0,44]
    obtain ⟨h_id_hi, _h_id_lo⟩ := decompose_int_identity_95232 r hlo hhi
    have hm : ((8380417 : Int) - 1) / (2 * (95232#i32 : Std.I32).val) - 1 = 43 := by
      norm_num [show (95232#i32 : Std.I32).val = 95232 from rfl]
    show 0 ≤ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).1
      ∧ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 95232).1
          ≤ ((8380417 : Int) - 1) / (2 * (95232#i32 : Std.I32).val) - 1
    rw [← h_id_hi, hm]
    -- r11v = if 43 < res then 0 else res; in both cases 0 ≤ · ≤ 43
    split <;> omega
  · -- 261888: m = 16, r11v = res % 16, res % 16 ∈ [0,15]
    obtain ⟨h_id_hi, _h_id_lo⟩ := decompose_int_identity_261888 r hlo hhi
    have hm : ((8380417 : Int) - 1) / (2 * (261888#i32 : Std.I32).val) - 1 = 15 := by
      norm_num [show (261888#i32 : Std.I32).val = 261888 from rfl]
    show 0 ≤ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).1
      ∧ (libcrux_iot_ml_dsa.Spec.Rounding.decompose r 261888).1
          ≤ ((8380417 : Int) - 1) / (2 * (261888#i32 : Std.I32).val) - 1
    rw [← h_id_hi, hm]
    have hpos : (0 : Int) < 16 := by norm_num
    refine ⟨Int.emod_nonneg _ (by norm_num), ?_⟩
    have := Int.emod_lt_of_pos
      ((((r + (if r < 0 then 8380417 else 0)) + 127) / 128 * 1025 + 2097152) / 4194304) hpos
    omega

/-! ## `use_one_hint_spec` — per-lane equality bridge to `Spec.Rounding.useHint`. -/

open libcrux_iot_ml_dsa.Spec.Rounding in
/-- `core.num.I32.wrapping_add r11 hint = .ok (Aeneas.Std.I32.wrapping_add r11 hint)` (rfl). -/
private theorem core_wrapping_add_ok (x y : Std.I32) :
    CoreModels.core.num.I32.wrapping_add x y = .ok (Aeneas.Std.I32.wrapping_add x y) := rfl

private theorem core_wrapping_sub_ok (x y : Std.I32) :
    CoreModels.core.num.I32.wrapping_sub x y = .ok (Aeneas.Std.I32.wrapping_sub x y) := rfl

set_option maxHeartbeats 2000000 in
theorem use_one_hint_spec (gamma2 r hint : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32)
    (hlo : -(8380417 : Int) ≤ r.val) (hhi : r.val < (8380417 : Int))
    (hh : hint.val = 0 ∨ hint.val = 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint gamma2 r hint
    ⦃ ⇓ z => ⌜ z.val = libcrux_iot_ml_dsa.Spec.Rounding.useHint
        ((hint.val == 1) : Bool) r.val gamma2.val ⌝ ⦄ := by
  -- decompose projections (black-box): r0.val = lowBits, r1.val = highBits.
  obtain ⟨v, hv_eq, h_v_lo, h_v_hi⟩ :=
    triple_exists_ok_l0 (decompose_element_spec gamma2 r hg hlo hhi)
  obtain ⟨v0, v1⟩ := v
  simp only at h_v_lo h_v_hi
  -- high-bits range.
  obtain ⟨h_hi_lo, h_hi_hi⟩ := decompose_high_range gamma2 r.val hg hlo hhi
  -- reduce the prefix (classify / decompose / declassify) of the do-block.
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint
  simp only [classify_ok, declassify_ok, hv_eq, Aeneas.Std.bind_tc_ok]
  -- name the spec projections; `r01 = v0.val = lowBits`, `r11 = v1.val = highBits`.
  set r0s := (libcrux_iot_ml_dsa.Spec.Rounding.decompose r.val gamma2.val).2 with hr0s
  set r1s := (libcrux_iot_ml_dsa.Spec.Rounding.decompose r.val gamma2.val).1 with hr1s
  -- `useHint` reduces with these projections.
  have h_useHint :
      libcrux_iot_ml_dsa.Spec.Rounding.useHint ((hint.val == 1) : Bool) r.val gamma2.val
      = (if (hint.val == 1) = true ∧ r0s > 0 then (r1s + 1) % ((8380417 - 1) / (2 * gamma2.val))
         else if (hint.val == 1) = true ∧ r0s ≤ 0 then
           ((r1s - 1) % ((8380417 - 1) / (2 * gamma2.val))
              + ((8380417 - 1) / (2 * gamma2.val))) % ((8380417 - 1) / (2 * gamma2.val))
         else r1s) := by
    unfold libcrux_iot_ml_dsa.Spec.Rounding.useHint
    simp only [libcrux_iot_ml_dsa.Spec.Rounding.Qi, show ((Q : Int)) = 8380417 from rfl,
      hr0s, hr1s]
  -- impl-comparison bridges (stated before the substs, so `r0s`/`r1s` stay abstract).
  have h_gt : (0#i32 : Std.I32) < v0 ↔ r0s > 0 := by
    rw [Aeneas.Std.IScalar.lt_equiv, ← h_v_lo]; rfl
  have h_v1_43 : (v1 = 43#i32) ↔ (r1s = 43) := by
    rw [← h_v_hi]; constructor
    · intro h; rw [h]; rfl
    · intro h; apply Aeneas.Std.IScalar.eq_of_val_eq; rw [h]; rfl
  have h_v1_0 : (v1 = 0#i32) ↔ (r1s = 0) := by
    rw [← h_v_hi]; constructor
    · intro h; rw [h]; rfl
    · intro h; apply Aeneas.Std.IScalar.eq_of_val_eq; rw [h]; rfl
  rcases hh with hh0 | hh1
  · -- hint.val = 0 ⇒ hint = 0#i32 ⇒ impl returns r11 = v1.val = r1s; useHint bool = false.
    have h_hint_eq : hint = 0#i32 := by
      apply Aeneas.Std.IScalar.eq_of_val_eq; rw [hh0]; rfl
    have h_bool : ((hint.val == 1) : Bool) = false := by rw [hh0]; rfl
    subst h_hint_eq
    apply triple_of_ok_l0 (v := v1) rfl
    rw [h_useHint, h_bool]; simp only [Bool.false_eq_true, false_and, if_false]
    exact h_v_hi
  · -- hint.val = 1 ⇒ hint = 1#i32 ⇒ branch on gamma2 / r01 / r11.
    have h_hint_eq : hint = 1#i32 := by
      apply Aeneas.Std.IScalar.eq_of_val_eq; rw [hh1]; rfl
    have h_bool : ((hint.val == 1) : Bool) = true := by rw [hh1]; rfl
    subst h_hint_eq
    rw [h_useHint, h_bool]
    simp only [true_and]
    rcases hg with hg | hg <;> subst hg
    · -- gamma2 = 95232, m = 44, r1s ∈ [0,43].
      show ⦃ ⌜ True ⌝ ⦄
        (if v0 > 0#i32 then
           (if v1 = 43#i32 then Result.ok 0#i32 else core.num.I32.wrapping_add v1 1#i32)
         else
           (if v1 = 0#i32 then Result.ok 43#i32 else core.num.I32.wrapping_sub v1 1#i32))
        ⦃ ⇓ z => ⌜ z.val = (if r0s > 0 then (r1s + 1) % ((8380417 - 1) / (2 * (95232#i32 : Std.I32).val))
            else if r0s ≤ 0 then
              ((r1s - 1) % ((8380417 - 1) / (2 * (95232#i32 : Std.I32).val))
                + ((8380417 - 1) / (2 * (95232#i32 : Std.I32).val)))
                  % ((8380417 - 1) / (2 * (95232#i32 : Std.I32).val))
            else r1s) ⌝ ⦄
      have hm43 : ((8380417 : Int) - 1) / (2 * (95232#i32 : Std.I32).val) = 44 := by
        norm_num [show (95232#i32 : Std.I32).val = 95232 from rfl]
      have h_r1_lo : 0 ≤ r1s := h_hi_lo
      have h_r1_hi : r1s ≤ 43 := by
        have := h_hi_hi; rw [show ((8380417 : Int) - 1) / (2 * (95232#i32 : Std.I32).val) - 1 = 43
          from by norm_num [show (95232#i32 : Std.I32).val = 95232 from rfl]] at this; exact this
      by_cases hgt : (0#i32 : Std.I32) < v0
      · -- r0s > 0 ⇒ spec (r1s+1)%44.
        have hr0s_pos : r0s > 0 := h_gt.mp hgt
        rw [if_pos hgt, if_pos hr0s_pos, hm43]
        by_cases h43 : v1 = 43#i32
        · rw [if_pos h43]
          have : r1s = 43 := h_v1_43.mp h43
          apply triple_of_ok_l0 (v := 0#i32) rfl
          rw [this]; rfl
        · rw [if_neg h43]
          have hne : r1s ≠ 43 := fun h => h43 (h_v1_43.mpr h)
          apply triple_of_ok_l0 (v := Aeneas.Std.I32.wrapping_add v1 1#i32)
            (core_wrapping_add_ok v1 1#i32)
          rw [wrapping_add_val_noov v1 1#i32 (by rw [h_v_hi]; omega) (by rw [h_v_hi]; omega),
            h_v_hi, show ((1#i32 : Std.I32).val) = 1 from rfl]
          omega
      · -- r0s ≤ 0 ⇒ spec ((r1s-1)%44+44)%44.
        have hr0s_le : r0s ≤ 0 := by
          by_contra hc; exact hgt (h_gt.mpr (by omega))
        rw [if_neg hgt, if_neg (by omega : ¬ r0s > 0), if_pos hr0s_le, hm43]
        by_cases h0 : v1 = 0#i32
        · rw [if_pos h0]
          have : r1s = 0 := h_v1_0.mp h0
          apply triple_of_ok_l0 (v := 43#i32) rfl
          rw [this]; rfl
        · rw [if_neg h0]
          have hne : r1s ≠ 0 := fun h => h0 (h_v1_0.mpr h)
          apply triple_of_ok_l0 (v := Aeneas.Std.I32.wrapping_sub v1 1#i32)
            (core_wrapping_sub_ok v1 1#i32)
          rw [wrapping_sub_val_noov v1 1#i32 (by rw [h_v_hi]; omega) (by rw [h_v_hi]; omega),
            h_v_hi, show ((1#i32 : Std.I32).val) = 1 from rfl]
          omega
    · -- gamma2 = 261888, m = 16, r1s ∈ [0,15].
      show ⦃ ⌜ True ⌝ ⦄
        (if v0 > 0#i32 then
           (core.num.I32.wrapping_add v1 1#i32 >>= fun i1 => Result.ok (i1 &&& 15#i32))
         else
           (core.num.I32.wrapping_sub v1 1#i32 >>= fun i1 => Result.ok (i1 &&& 15#i32)))
        ⦃ ⇓ z => ⌜ z.val = (if r0s > 0 then (r1s + 1) % ((8380417 - 1) / (2 * (261888#i32 : Std.I32).val))
            else if r0s ≤ 0 then
              ((r1s - 1) % ((8380417 - 1) / (2 * (261888#i32 : Std.I32).val))
                + ((8380417 - 1) / (2 * (261888#i32 : Std.I32).val)))
                  % ((8380417 - 1) / (2 * (261888#i32 : Std.I32).val))
            else r1s) ⌝ ⦄
      have hm16 : ((8380417 : Int) - 1) / (2 * (261888#i32 : Std.I32).val) = 16 := by
        norm_num [show (261888#i32 : Std.I32).val = 261888 from rfl]
      have h_r1_lo : 0 ≤ r1s := h_hi_lo
      have h_r1_hi : r1s ≤ 15 := by
        have := h_hi_hi; rw [show ((8380417 : Int) - 1) / (2 * (261888#i32 : Std.I32).val) - 1 = 15
          from by norm_num [show (261888#i32 : Std.I32).val = 261888 from rfl]] at this; exact this
      by_cases hgt : (0#i32 : Std.I32) < v0
      · -- r0s > 0 ⇒ spec (r1s+1)%16. impl (v1+1)&&&15.
        have hr0s_pos : r0s > 0 := h_gt.mp hgt
        rw [if_pos hgt, if_pos hr0s_pos, hm16]
        have h_add : (Aeneas.Std.I32.wrapping_add v1 1#i32).val = r1s + 1 := by
          rw [wrapping_add_val_noov v1 1#i32 (by rw [h_v_hi]; omega) (by rw [h_v_hi]; omega),
            h_v_hi, show ((1#i32 : Std.I32).val) = 1 from rfl]
        rw [core_wrapping_add_ok]; simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_l0 (v := (Aeneas.Std.I32.wrapping_add v1 1#i32) &&& 15#i32) rfl
        rw [show ((Aeneas.Std.I32.wrapping_add v1 1#i32) &&& 15#i32)
            = (⟨(Aeneas.Std.I32.wrapping_add v1 1#i32).bv &&& (15#i32 : Std.I32).bv⟩ : Std.I32) from rfl,
          and_15_val _ (by rw [h_add]; omega) (by rw [h_add]; omega), h_add]
      · -- r0s ≤ 0 ⇒ spec ((r1s-1)%16+16)%16. impl (v1-1)&&&15; r1s=0 special-cased.
        have hr0s_le : r0s ≤ 0 := by
          by_contra hc; exact hgt (h_gt.mpr (by omega))
        rw [if_neg hgt, if_neg (by omega : ¬ r0s > 0), if_pos hr0s_le, hm16]
        have h_sub : (Aeneas.Std.I32.wrapping_sub v1 1#i32).val = r1s - 1 := by
          rw [wrapping_sub_val_noov v1 1#i32 (by rw [h_v_hi]; omega) (by rw [h_v_hi]; omega),
            h_v_hi, show ((1#i32 : Std.I32).val) = 1 from rfl]
        rw [core_wrapping_sub_ok]; simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_l0 (v := (Aeneas.Std.I32.wrapping_sub v1 1#i32) &&& 15#i32) rfl
        rw [show ((Aeneas.Std.I32.wrapping_sub v1 1#i32) &&& 15#i32)
            = (⟨(Aeneas.Std.I32.wrapping_sub v1 1#i32).bv &&& (15#i32 : Std.I32).bv⟩ : Std.I32) from rfl]
        by_cases h0 : r1s = 0
        · -- (v1-1).val = -1 ⇒ and_15_val precondition fails; handle directly.
          have hbv : (Aeneas.Std.I32.wrapping_sub v1 1#i32).bv = BitVec.allOnes 32 := by
            apply BitVec.eq_of_toInt_eq
            show (Aeneas.Std.I32.wrapping_sub v1 1#i32).val = (BitVec.allOnes 32).toInt
            rw [h_sub, h0]; decide
          show ((Aeneas.Std.I32.wrapping_sub v1 1#i32).bv &&& (15#i32 : Std.I32).bv).toInt = _
          rw [hbv, h0]
          rw [show (BitVec.allOnes 32 &&& (15#i32 : Std.I32).bv) = (15 : BitVec 32) from by decide]
          decide
        · -- r1s ∈ [1,15] ⇒ (v1-1).val = r1s-1 ∈ [0,14]; and_15_val applies.
          rw [and_15_val _ (by rw [h_sub]; omega) (by rw [h_sub]; omega), h_sub]
          omega

/-! ## `use_hint_spec` — top-level `@[spec]` per-lane equality keystone. -/

/-- Per-element predicate carrying the precondition→post for `use_hint`'s lanes. -/
private def use_hint_per_elem_P (gamma2 : Std.I32) (src_x acc_x : Std.I32) (z : Std.I32) : Prop :=
  -(8380417 : Int) ≤ src_x.val → src_x.val < (8380417 : Int) →
    (acc_x.val = 0 ∨ acc_x.val = 1) →
      z.val = libcrux_iot_ml_dsa.Spec.Rounding.useHint
        ((acc_x.val == 1) : Bool) src_x.val gamma2.val

/-- `use_one_hint` is total for `gamma2 ∈ {95232, 261888}` (the `| _ => fail` arm is dead);
    the result `.ok` value follows by reducing the do-block prefix and casing on the branches. -/
private theorem use_one_hint_ok_exists (gamma2 src_x acc_x : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    ∃ v, libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint gamma2 src_x acc_x = .ok v := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint
  simp only [classify_ok, declassify_ok, decompose_element_eq_ok gamma2 src_x hg,
    Aeneas.Std.bind_tc_ok]
  obtain ⟨d0, d1, hd⟩ : ∃ a b, decompose_impl_value gamma2 src_x = (a, b) := ⟨_, _, rfl⟩
  rw [hd]
  rcases hg with hg | hg <;> subst hg
  · show ∃ v,
      (if acc_x = 0#i32 then Result.ok d1
       else
         if d0 > 0#i32 then
           (if d1 = 43#i32 then Result.ok 0#i32 else core.num.I32.wrapping_add d1 acc_x)
         else
           (if d1 = 0#i32 then Result.ok 43#i32 else core.num.I32.wrapping_sub d1 acc_x)) = .ok v
    simp only [core_wrapping_add_ok, core_wrapping_sub_ok]
    split_ifs <;> exact ⟨_, rfl⟩
  · show ∃ v,
      (if acc_x = 0#i32 then Result.ok d1
       else
         if d0 > 0#i32 then
           (core.num.I32.wrapping_add d1 acc_x >>= fun i1 => Result.ok (i1 &&& 15#i32))
         else
           (core.num.I32.wrapping_sub d1 acc_x >>= fun i1 => Result.ok (i1 &&& 15#i32))) = .ok v
    simp only [core_wrapping_add_ok, core_wrapping_sub_ok, Aeneas.Std.bind_tc_ok]
    split_ifs <;> exact ⟨_, rfl⟩

private theorem use_hint_per_elem_spec (gamma2 : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) (src_x acc_x : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint gamma2 src_x acc_x
    ⦃ ⇓ z => ⌜ use_hint_per_elem_P gamma2 src_x acc_x z ⌝ ⦄ := by
  obtain ⟨v, hv_eq⟩ := use_one_hint_ok_exists gamma2 src_x acc_x hg
  apply triple_of_ok_l0 (v := v) hv_eq
  unfold use_hint_per_elem_P
  intro hlo hhi hacc
  obtain ⟨z, hz_eq, hz_P⟩ :=
    triple_exists_ok_l0 (use_one_hint_spec gamma2 src_x acc_x hg hlo hhi hacc)
  rw [hv_eq] at hz_eq
  rw [Result.ok.inj hz_eq]; exact hz_P

set_option maxHeartbeats 2000000 in
@[spec]
theorem use_hint_spec (gamma2 : Std.I32)
    (simd_unit hint : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32)
    (hbound : ∀ j : Nat, j < 8 →
        -(8380417 : Int) ≤ (simd_unit.values.val[j]!).val
          ∧ (simd_unit.values.val[j]!).val < (8380417 : Int))
    (hhint : ∀ j : Nat, j < 8 →
        (hint.values.val[j]!).val = 0 ∨ (hint.values.val[j]!).val = 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.use_hint gamma2 simd_unit hint
    ⦃ ⇓ p => ⌜ ∀ j : Nat, j < 8 →
        (p.values.val[j]!).val = libcrux_iot_ml_dsa.Spec.Rounding.useHint
          (((hint.values.val[j]!).val == 1) : Bool)
          (simd_unit.values.val[j]!).val gamma2.val ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.use_hint
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice hint.values)
        = .ok (Aeneas.Std.Array.to_slice hint.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice hint.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice hint.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq hint.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.use_hint_loop
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
         libcrux_iot_ml_dsa.simd.portable.arithmetic.use_hint_loop.body
           gamma2 simd_unit p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
         two_src_single_output_loop_body
           (fun src_x acc_x =>
             libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint gamma2 src_x acc_x)
           simd_unit p.1 p.2) := by
    funext p
    obtain ⟨iter1, a1⟩ := p
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.use_hint_loop.body
    unfold two_src_single_output_loop_body
    simp only [classify_ok, declassify_ok, Aeneas.Std.bind_tc_ok]
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok_l0
      (elementwise_two_src_single_output_spec
        (fun src_x acc_x =>
          libcrux_iot_ml_dsa.simd.portable.arithmetic.use_one_hint gamma2 src_x acc_x)
        (use_hint_per_elem_P gamma2) (use_hint_per_elem_spec gamma2 hg)
        simd_unit hint.values)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok_l0 (v := ({ values := out })) rfl ?_
  intro j hj
  obtain ⟨pj, _h_eq, h_val, h_P⟩ := h_out_P j hj
  obtain ⟨hb_lo, hb_hi⟩ := hbound j hj
  have hacc := hhint j hj
  show (out.val[j]!).val = _
  rw [h_val]
  exact h_P hb_lo hb_hi hacc

/-! ## `compute_hint` — per-lane bit, top-level dual output (count + array). -/

/-- `compute_one_hint` returns exactly `computeHint low high gamma2`, a `{0,1}` bit.
    The impl is total (no decompose); the only no-panic obligation is the checked `-. gamma2`,
    which needs `gamma2 ∈ {95232, 261888}` so `-gamma2` stays in `I32` bounds. -/
theorem compute_one_hint_spec (low high gamma2 : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_one_hint low high gamma2
    ⦃ ⇓ r => ⌜ r.val = libcrux_iot_ml_dsa.Spec.Rounding.computeHint low.val high.val gamma2.val
             ∧ (r.val = 0 ∨ r.val = 1) ⌝ ⦄ := by
  -- The checked negation `-. gamma2` reduces to `.ok gi` with `gi.val = -gamma2.val`.
  obtain ⟨gi, h_neg, h_gi_val⟩ : ∃ gi : Std.I32,
      (-. gamma2 : Result Std.I32) = .ok gi ∧ gi.val = -gamma2.val := by
    rcases hg with hg | hg <;> subst hg
    · exact ⟨(-95232)#i32, by rfl, by decide⟩
    · exact ⟨(-261888)#i32, by rfl, by decide⟩
  have h_g_val : gamma2.val = 95232 ∨ gamma2.val = 261888 := by
    rcases hg with hg | hg <;> subst hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_one_hint
  unfold libcrux_iot_ml_dsa.Spec.Rounding.computeHint
  by_cases h1 : low > gamma2
  · rw [if_pos h1]
    have h1' : low.val > gamma2.val := (Aeneas.Std.IScalar.lt_equiv gamma2 low).mp h1
    apply triple_of_ok_l0 (v := 1#i32) rfl
    exact ⟨by rw [if_pos (Or.inl h1')]; rfl, Or.inr rfl⟩
  · rw [if_neg h1, h_neg]
    simp only [Aeneas.Std.bind_tc_ok]
    have h1' : ¬ low.val > gamma2.val := fun hc =>
      h1 ((Aeneas.Std.IScalar.lt_equiv gamma2 low).mpr hc)
    by_cases h2 : low < gi
    · rw [if_pos h2]
      have h2' : low.val < -gamma2.val := by
        have := (Aeneas.Std.IScalar.lt_equiv low gi).mp h2; rw [h_gi_val] at this; exact this
      apply triple_of_ok_l0 (v := 1#i32) rfl
      exact ⟨by rw [if_pos (Or.inr (Or.inl h2'))]; rfl, Or.inr rfl⟩
    · rw [if_neg h2]
      have h2' : ¬ low.val < -gamma2.val := by
        intro hc; exact h2 ((Aeneas.Std.IScalar.lt_equiv low gi).mpr (by rw [h_gi_val]; exact hc))
      by_cases h3 : low = gi
      · rw [if_pos h3]
        have h3' : low.val = -gamma2.val := by rw [h3, h_gi_val]
        by_cases h4 : high != (0#i32 : Std.I32)
        · rw [if_pos h4]
          have h4' : high.val ≠ 0 := by
            intro hc
            have : high = 0#i32 := Aeneas.Std.IScalar.eq_of_val_eq (by rw [hc]; rfl)
            simp [this] at h4
          apply triple_of_ok_l0 (v := 1#i32) rfl
          exact ⟨by rw [if_pos (Or.inr (Or.inr ⟨h3', h4'⟩))]; rfl, Or.inr rfl⟩
        · rw [if_neg h4]
          have h4' : high.val = 0 := by
            by_contra hc
            exact h4 (by simp only [bne_iff_ne]; intro hh; exact hc (by rw [hh]; rfl))
          apply triple_of_ok_l0 (v := 0#i32) rfl
          refine ⟨?_, Or.inl rfl⟩
          rw [if_neg (by
            rintro (hc | hc | ⟨_, hc⟩)
            · exact h1' hc
            · exact h2' hc
            · exact hc h4')]; rfl
      · rw [if_neg h3]
        have h3' : low.val ≠ -gamma2.val := fun hc =>
          h3 (Aeneas.Std.IScalar.eq_of_val_eq (by rw [h_gi_val]; exact hc))
        apply triple_of_ok_l0 (v := 0#i32) rfl
        refine ⟨?_, Or.inl rfl⟩
        rw [if_neg (by
          rintro (hc | hc | ⟨hc, _⟩)
          · exact h1' hc
          · exact h2' hc
          · exact h3' hc)]; rfl

/-! ## `compute_hint_spec` — top-level dual output: the hint array AND the `1`-bit count. -/

/-- Per-lane predicate for the combinator: the written bit equals the spec `computeHint`. -/
private def compute_hint_per_elem_P (gamma2 : Std.I32) (x y r : Std.I32) : Prop :=
  r.val = libcrux_iot_ml_dsa.Spec.Rounding.computeHint x.val y.val gamma2.val

/-- The per-element spec in the `(r.val ∈ {0,1}) ∧ P` shape required by the combinator. -/
private theorem compute_hint_per_elem_spec (gamma2 : Std.I32)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) (x y : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_one_hint x y gamma2
    ⦃ ⇓ r => ⌜ (r.val = 0 ∨ r.val = 1) ∧ compute_hint_per_elem_P gamma2 x y r ⌝ ⦄ := by
  obtain ⟨v, hv_eq, hv_P, hv_01⟩ := triple_exists_ok_l0 (compute_one_hint_spec x y gamma2 hg)
  apply triple_of_ok_l0 (v := v) hv_eq
  exact ⟨hv_01, hv_P⟩

set_option maxHeartbeats 2000000 in
@[spec]
theorem compute_hint_spec (low high : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (gamma2 : Std.I32)
    (hint : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hg : gamma2 = 95232#i32 ∨ gamma2 = 261888#i32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_hint low high gamma2 hint
    ⦃ ⇓ p => ⌜ (∀ j : Nat, j < 8 →
          (p.2.values.val[j]!).val
            = libcrux_iot_ml_dsa.Spec.Rounding.computeHint
                (low.values.val[j]!).val (high.values.val[j]!).val gamma2.val)
        ∧ p.1.val = ((List.range 8).map (fun j =>
              libcrux_iot_ml_dsa.Spec.Rounding.computeHint
                (low.values.val[j]!).val (high.values.val[j]!).val gamma2.val)).sum ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_hint
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice hint.values)
        = .ok (Aeneas.Std.Array.to_slice hint.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice hint.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice hint.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq hint.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_hint_loop
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray × Std.Usize) =>
         libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_hint_loop.body
           low high gamma2 p.1 p.2.1 p.2.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray × Std.Usize) =>
         two_src_count_output_loop_body
           (fun x y => libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_one_hint x y gamma2)
           low high p.1 p.2.1 p.2.2) := by
    funext p
    obtain ⟨iter1, a1, count1⟩ := p
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_hint_loop.body
    unfold two_src_count_output_loop_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_arr, h_out_count⟩ :=
    triple_exists_ok_l0
      (elementwise_two_src_count_output_spec
        (fun x y => libcrux_iot_ml_dsa.simd.portable.arithmetic.compute_one_hint x y gamma2)
        (compute_hint_per_elem_P gamma2) (compute_hint_per_elem_spec gamma2 hg)
        low high hint.values)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok_l0 (v := (out.2, { values := out.1 })) rfl ?_
  refine ⟨?_, ?_⟩
  · -- hint array: out.1[j] = computeHint low[j] high[j] gamma2.
    intro j hj
    obtain ⟨rj, _h_eq, h_arr_j, _h01_j, h_P_j⟩ := h_out_arr j hj
    show (out.1.val[j]!).val = _
    rw [h_arr_j]; exact h_P_j
  · -- count: out.2 = Σ of the spec bits. The combinator gives out.2 = Σ (out.1[j].val);
    -- rewrite each out.1[j].val = computeHint via the array conjunct.
    show (out.2.val : Int)
        = ((List.range 8).map (fun j =>
            libcrux_iot_ml_dsa.Spec.Rounding.computeHint
              (low.values.val[j]!).val (high.values.val[j]!).val gamma2.val)).sum
    rw [h_out_count]
    have h_map_eq :
        ((List.range 8).map (fun j => (out.1.val[j]!).val))
        = ((List.range 8).map (fun j =>
            libcrux_iot_ml_dsa.Spec.Rounding.computeHint
              (low.values.val[j]!).val (high.values.val[j]!).val gamma2.val)) := by
      apply List.map_congr_left
      intro x hx
      rw [List.mem_range] at hx
      obtain ⟨rj, _h_eq, h_arr_j, _h01_j, h_P_j⟩ := h_out_arr x hx
      show (out.1.val[x]!).val = _
      rw [h_arr_j]; exact h_P_j
    rw [h_map_eq]

end libcrux_iot_ml_dsa.Vector.Portable.Rounding
