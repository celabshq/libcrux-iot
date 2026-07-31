import LibcruxIotMlDsa.Extraction.Funs
import LibcruxIotMlDsa.Spec.Montgomery
import LibcruxIotMlDsa.Spec.Lift
import LibcruxIotMlDsa.Spec.Rounding
import LibcruxIotMlDsa.Util.LoopHelper

/-!
  # `Vector/Portable/Arithmetic.lean` — Layer-0 scalar Montgomery reduction

  `@[spec high]` Triple for the leaf field-arithmetic primitive
  `simd.portable.arithmetic.montgomery_reduce_element`:

  - `get_n_least_significant_bits_eq_ok` — the mask-op closed form (U64 version)
  - `mont_reduce_element_eq_ok` — the do-block reduces to `.ok (mont_reduce_impl_value value)`
  - `mont_reduce_impl_value_val` — bridge to Int / bmod terms
  - `mont_reduce_core` — integer identity: `res·R = value - k·Q`
  - `montgomery_reduce_element_spec` — the final Triple (L0 keystone)
-/

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.Arithmetic
open CoreModels Aeneas Aeneas.Std Std.Do Result ControlFlow
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec.Montgomery
open libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Util.LoopHelper

/-- The Triple `⦃True⦄ x ⦃⇓ r => ⌜P r⌝⦄` closer for `x = .ok v`. -/
private theorem triple_of_ok_l0 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Extract the `.ok` witness from a true-pre Triple — mirror of the SKILL §13.5
    helper, scoped to this file. Lets a downstream proof consume a `@[spec]`
    Triple without reaching into its privates. -/
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

/-! ## `get_n_least_significant_bits` (U64 version) -/

private theorem get_n_least_significant_bits_eq_ok
    (n : Std.U8) (value : Std.U64) (hn : n.val < 64) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits n value
      = .ok ⟨value.bv &&& ((1#64 <<< n.val) - 1#64)⟩ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits
  have hn_lt : n.val < Aeneas.Std.UScalarTy.U64.numBits := hn
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.UScalar.shiftLeft_UScalar,
             Aeneas.Std.UScalar.shiftLeft, hn_lt, reduceIte,
             CoreModels.core.num.U64.wrapping_sub,
             rust_primitives.arithmetic.wrapping_sub_u64,
             Aeneas.Std.bind_tc_ok]
  rfl

/-! ## Closed-form value of the impl -/

def mont_reduce_impl_value (value : Std.I64) : Std.I32 :=
  let i    := Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value
  let i1   : Std.U64 := ⟨i.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  let t    : Std.U64 := ⟨i1.bv * (58728449#u64 : Std.U64).bv⟩
  let i2   : Std.U64 := ⟨t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  let k    := Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 i2
  let i3   := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 k
  let i4q  := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 (8380417#i32 : Std.I32)
  let km   := Aeneas.Std.I64.wrapping_mul i3 i4q
  let c    := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨km.bv.sshiftRight 32⟩ : Std.I64)
  let vh   := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨value.bv.sshiftRight 32⟩ : Std.I64)
  Aeneas.Std.I32.wrapping_sub vh c

theorem mont_reduce_element_eq_ok (value : Std.I64) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
      = .ok (mont_reduce_impl_value value) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element mont_reduce_impl_value
  have h_inv : libcrux_iot_ml_dsa.simd.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R = 58728449#u64 := by
    unfold libcrux_iot_ml_dsa.simd.traits.INVERSE_OF_MODULUS_MOD_MONTGOMERY_R; rfl
  have h_q : libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS = 8380417#i32 := by
    unfold libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS; rfl
  have h_shift : libcrux_iot_ml_dsa.simd.portable.arithmetic.MONTGOMERY_SHIFT = 32#u8 := by
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.MONTGOMERY_SHIFT; rfl
  simp only [libcrux_secrets.traits.Classify.Blanket.classify,
             libcrux_secrets.traits.Declassify.Blanket.declassify,
             libcrux_secrets.I64.Insts.Libcrux_secretsIntCastOps.as_u64,
             libcrux_secrets.I64.Insts.Libcrux_secretsIntCastOps.as_i32,
             libcrux_secrets.U64.Insts.Libcrux_secretsIntCastOps.as_i32,
             libcrux_secrets.I32.Insts.Libcrux_secretsIntCastOps.as_i64,
             Aeneas.Std.bind_tc_ok, Aeneas.Std.lift,
             CoreModels.core.num.I64.wrapping_mul, CoreModels.core.num.I32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_mul_i64, rust_primitives.arithmetic.wrapping_sub_i32,
             h_inv, h_q, h_shift]
  have h_glsb : ∀ (vv : Std.U64),
      libcrux_iot_ml_dsa.simd.portable.arithmetic.get_n_least_significant_bits 32#u8 vv
        = .ok ⟨vv.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩ :=
    fun vv => get_n_least_significant_bits_eq_ok 32#u8 vv (by decide)
  simp only [h_glsb, Aeneas.Std.bind_tc_ok]
  simp only [HShiftRight.hShiftRight, Aeneas.Std.IScalar.shiftRight_UScalar,
             Aeneas.Std.IScalar.shiftRight,
             show (32#u8 : U8).val < Aeneas.Std.IScalarTy.I64.numBits from by decide,
             reduceIte]
  rfl

/-! ## `.val` in Int terms -/

private theorem mont_reduce_impl_value_val
    (value : Std.I64) (hb : value.val.natAbs ≤ 2^55) :
    (mont_reduce_impl_value value).val
      = let v32 := Int.bmod value.val (2^32)
        let k32 := Int.bmod (v32 * 58728449) (2^32)
        let km  := k32 * 8380417
        value.val / (2^32 : Int) - km / (2^32 : Int) := by
  unfold mont_reduce_impl_value
  set v : Int := value.val
  have h_v_abs : |v| ≤ (2^55 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_v32_lb : -(2^31 : Int) ≤ Int.bmod v (2^32) := (Arith.Int.bmod_pow2_bounds 32 v).1
  have h_v32_ub : Int.bmod v (2^32) < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 v).2
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2

  -- i.bv = value.bv  (IScalar.hcast .U64 reinterprets same bits)
  have h_i_bv : (Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv = value.bv := by
    simp only [Aeneas.Std.IScalar.hcast]
    change value.bv.signExtend 64 = value.bv
    exact BitVec.signExtend_eq value.bv

  -- Helper: (value.bv.toNat : Int) % 2^32 = v % 2^32
  have h_bv_val_emod : (value.bv.toNat : Int) % (2^32 : Int) = v % (2^32 : Int) := by
    have hval : v = value.bv.toInt := rfl
    rw [hval]
    simp only [BitVec.toInt_eq_toNat_cond]
    split_ifs <;> push_cast <;> omega

  -- mask.toNat = 2^32 - 1 (for 64-bit; avoid `decide` on large bitvec)
  have h_mask_toNat : ((1#64 <<< (32 : Nat)) - 1#64 : BitVec 64).toNat = 2^32 - 1 := by
    simp

  -- i1.val = v32 % 2^32 (as Nat)
  set i1 : Std.U64 := ⟨(Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv
                        &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  have h_i1_val : i1.val = (v32 % (2^32 : Int)).toNat := by
    change ((Aeneas.Std.IScalar.hcast Aeneas.Std.UScalarTy.U64 value).bv
            &&& ((1#64 <<< (32 : Nat)) - 1#64)).toNat = _
    rw [h_i_bv, BitVec.toNat_and, h_mask_toNat, Nat.and_two_pow_sub_one_eq_mod]
    -- Goal (Nat): value.bv.toNat % 2^32 = (v32 % 2^32 : Int).toNat
    have h_key : (value.bv.toNat : Int) % (2^32 : Int) = v32 % (2^32 : Int) := by
      rw [h_bv_val_emod]; exact Int.bmod_emod.symm
    have hnn : 0 ≤ v32 % (2^32 : Int) := Int.emod_nonneg _ (by decide)
    omega

  -- (i1.val : Int) = v32 % (2^32 : Int)
  have h_i1_val_int : (i1.val : Int) = v32 % (2^32 : Int) := by
    have h_nn : 0 ≤ v32 % (2^32 : Int) := Int.emod_nonneg _ (by decide)
    rw [h_i1_val, Int.toNat_of_nonneg h_nn]

  -- t.val = (i1.val * 58728449) % 2^64
  set t : Std.U64 := ⟨i1.bv * (58728449#u64 : Std.U64).bv⟩
  have h_t_val : t.val = (i1.val * 58728449) % 2^64 := by
    show (i1.bv * (58728449#u64).bv).toNat = _
    rw [BitVec.toNat_mul]; rfl

  -- i2.val = (i1.val * 58728449) % 2^32
  set i2 : Std.U64 := ⟨t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)⟩
  have h_i2_val : i2.val = (i1.val * 58728449) % 2^32 := by
    show (t.bv &&& ((1#64 <<< (32 : Nat)) - 1#64)).toNat = _
    rw [BitVec.toNat_and, h_mask_toNat, Nat.and_two_pow_sub_one_eq_mod]
    have : t.bv.toNat = (i1.val * 58728449) % 2^64 := h_t_val
    omega

  -- k.val = bmod (i2.val : Int) (2^32)
  set k := Aeneas.Std.UScalar.hcast Aeneas.Std.IScalarTy.I32 i2
  have h_k_val : k.val = Int.bmod (i2.val : Int) (2^32) := by
    show (i2.bv.zeroExtend 32).toInt = _
    rw [BitVec.toInt_setWidth]; rfl

  -- k.val = k32
  have h_k_eq_k32 : k.val = k32 := by
    rw [h_k_val, h_i2_val]
    -- Goal: Int.bmod (↑(↑i1 * 58728449 % 2^32)) (2^32) = k32
    have h_cast : ((i1.val * 58728449 % 2 ^ 32 : ℕ) : Int) = (i1.val : Int) * 58728449 % (2^32 : Int) := by
      omega
    rw [h_cast, h_i1_val_int]
    -- Goal: (v32 % 2^32 * 58728449 % 2^32).bmod (2^32) = k32.
    -- `Int.emod_bmod`/`Int.emod_mul_bmod` match the modulus only up to defeq ((2^32 : Int) vs
    -- ↑(2^32 : ℕ)); `rw` matches syntactically and fails here, so chain them in term mode.
    exact (Int.emod_bmod ((v32 % 2^32) * 58728449) (2^32)).trans (Int.emod_mul_bmod v32 (2^32))

  -- i3.val = k.val (sign-extend I32 → I64 preserves value)
  set i3 := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 k
  have h_i3_val : i3.val = k.val := by
    show (k.bv.signExtend 64).toInt = k.bv.toInt
    exact BitVec.toInt_signExtend_of_le (by decide)

  -- i4q.val = 8380417
  set i4q := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 (8380417#i32 : Std.I32)
  have h_i4q_val : i4q.val = 8380417 := by decide

  -- km.val = k.val * 8380417 (no wrap: |k| ≤ 2^31, |k * Q| ≤ 2^31 * Q < 2^63)
  set km := Aeneas.Std.I64.wrapping_mul i3 i4q
  have h_km_val : km.val = k.val * 8380417 := by
    show km.bv.toInt = _
    have h_bv : km.bv = i3.bv * i4q.bv := by
      show (Aeneas.Std.I64.wrapping_mul _ _).bv = _
      simp only [Aeneas.Std.I64.wrapping_mul_bv_eq]
    rw [h_bv, BitVec.toInt_mul]
    show Int.bmod _ _ = _
    rw [show i3.bv.toInt = k.val from h_i3_val, show i4q.bv.toInt = 8380417 from h_i4q_val,
        h_k_eq_k32]
    -- bmod (k32 * 8380417) (2^64) = k32 * 8380417 since |k32 * Q| ≤ 2^31 * Q < 2^63.
    -- Use bmod_pow2_eq_of_inBounds' 64 + norm_num bounds (NO omega on 2⁶³-scale: it trips
    -- the kernel recursion limit; mirrors the final 2^32 step below).
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 64 _ (by decide)
    · -- -2^(64-1) ≤ k32 * 8380417
      have hlb := mul_le_mul_of_nonneg_right h_k32_lb (by norm_num : (0:Int) ≤ 8380417)
      refine le_trans ?_ hlb
      norm_num
    · -- k32 * 8380417 < 2^(64-1)
      have hub := mul_lt_mul_of_pos_right h_k32_ub (by norm_num : (0:Int) < 8380417)
      refine lt_of_lt_of_le hub ?_
      norm_num

  -- c.val = km.val / 2^32
  set c := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨km.bv.sshiftRight 32⟩ : Std.I64)
  have h_c_val : c.val = km.val / (2^32 : Int) := by
    have h_shr : (⟨km.bv.sshiftRight 32⟩ : Std.I64).val = km.val / (2^32 : Int) := by
      show (km.bv.sshiftRight 32).toInt = _
      rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds]
    · exact h_shr
    · rw [h_shr, h_km_val, h_k_eq_k32]
      have h_lb := mul_le_mul_of_nonneg_right h_k32_lb (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^31 : Int) * 8380417 / 2^32 = -4190209 := by norm_num
      have h_pow31 : -(2:Int)^(IScalarTy.I32.numBits-1) = -2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega
    · rw [h_shr, h_km_val, h_k_eq_k32]
      -- bound k32 ≤ 2^31 via le_of_lt (avoids omega on raw 2^31 → kernel deep recursion);
      -- 2^31 * 8380417 / 2^32 = 8380417 / 2 = 4190208 (8380417 odd), same constant.
      have h_mul := mul_le_mul_of_nonneg_right (le_of_lt h_k32_ub) (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : (2^31 : Int) * 8380417 / 2^32 = 4190208 := by norm_num
      have h_pow31 : (2:Int)^(IScalarTy.I32.numBits-1) = 2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega

  -- vh.val = v / 2^32
  set vh := Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I32 (⟨value.bv.sshiftRight 32⟩ : Std.I64)
  have h_vh_val : vh.val = v / (2^32 : Int) := by
    have h_shr : (⟨value.bv.sshiftRight 32⟩ : Std.I64).val = v / (2^32 : Int) := by
      show (value.bv.sshiftRight 32).toInt = _
      rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
    rw [Aeneas.Std.IScalar.val_mod_pow_inBounds]
    · exact h_shr
    · rw [h_shr]
      have h_lb : -(2^55 : Int) ≤ v := le_trans (neg_le_neg h_v_abs) (neg_abs_le v)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^55 : Int) / 2^32 = -8388608 := by norm_num
      have h_pow31 : -(2:Int)^(IScalarTy.I32.numBits-1) = -2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega
    · rw [h_shr]
      have h_ub : v ≤ (2^55 : Int) := le_trans (le_abs_self v) h_v_abs
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^55 : Int) / 2^32 = 8388608 := by norm_num
      have h_pow31 : (2:Int)^(IScalarTy.I32.numBits-1) = 2147483648 := by decide
      rw [h_const] at h_ediv; rw [h_pow31]; omega

  -- Final: wrapping_sub vh c
  show (Aeneas.Std.I32.wrapping_sub vh c).bv.toInt = _
  rw [show (Aeneas.Std.I32.wrapping_sub vh c).bv = vh.bv - c.bv from rfl, BitVec.toInt_sub]
  rw [show vh.bv.toInt = vh.val from rfl, show c.bv.toInt = c.val from rfl]
  rw [h_vh_val, h_c_val, h_km_val, h_k_eq_k32]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_v_div_lb : v / (2^32 : Int) ≥ -8388608 := by
      have h_lb : -(2^55 : Int) ≤ v := le_trans (neg_le_neg h_v_abs) (neg_abs_le v)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_lb
      have h_const : -(2^55 : Int) / 2^32 = -8388608 := by norm_num
      rw [h_const] at h_ediv; omega
    have h_km_div_ub : k32 * 8380417 / (2^32 : Int) ≤ 4190208 := by
      -- k32 ≤ 2^31 via le_of_lt (avoids omega on raw 2^31 → kernel deep recursion);
      -- 2^31 * 8380417 / 2^32 = 8380417 / 2 = 4190208 (8380417 odd), same constant.
      have h_mul := mul_le_mul_of_nonneg_right (le_of_lt h_k32_ub) (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : (2^31 : Int) * 8380417 / 2^32 = 4190208 := by norm_num
      rw [h_const] at h_ediv; omega
    have h31 : (2 : Int)^(32 - 1) = (2147483648 : Int) := by norm_num
    rw [h31]; omega
  · have h_v_div_ub : v / (2^32 : Int) ≤ 8388608 := by
      have h_ub : v ≤ (2^55 : Int) := le_trans (le_abs_self v) h_v_abs
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_ub
      have h_const : (2^55 : Int) / 2^32 = 8388608 := by norm_num
      rw [h_const] at h_ediv; omega
    have h_km_div_lb : k32 * 8380417 / (2^32 : Int) ≥ -4190209 := by
      have h_mul := mul_le_mul_of_nonneg_right h_k32_lb (by decide : (0:Int) ≤ 8380417)
      have h_ediv := Int.ediv_le_ediv (c := 2^32) (by decide) h_mul
      have h_const : -(2^31 : Int) * 8380417 / 2^32 = -4190209 := by norm_num
      rw [h_const] at h_ediv; omega
    have h31 : (2 : Int)^(32 - 1) = (2147483648 : Int) := by norm_num
    rw [h31]; omega

/-! ## Integer core identity -/

private theorem mont_reduce_core
    (v : Int) (hb : v.natAbs ≤ 2^55) :
    let v32 := Int.bmod v (2^32)
    let k32 := Int.bmod (v32 * 58728449) (2^32)
    let km  := k32 * 8380417
    let res := v / (2^32 : Int) - km / (2^32 : Int)
    res * (2^32 : Int) = v - km := by
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  -- (v - km) % 2^32 = 0
  have h_km_mod : (v - km) % (2^32 : Int) = 0 := by
    have h_keystone : (58728449 * 8380417 : Int) % (2^32) = 1 := by decide
    have h_k32_emod : k32 % (2^32 : Int) = (v32 * 58728449) % (2^32 : Int) :=
      Int.bmod_emod
    have h_km_emod : km % (2^32 : Int) = v32 % (2^32 : Int) := by
      change k32 * 8380417 % _ = _
      rw [Int.mul_emod, h_k32_emod, ← Int.mul_emod,
          show v32 * 58728449 * 8380417 = v32 * (58728449 * 8380417) by ring,
          Int.mul_emod, h_keystone, mul_one, Int.emod_emod_of_dvd _ (dvd_refl _)]
    rw [Int.sub_emod,
        show v % (2^32 : Int) = v32 % (2^32 : Int) from Int.bmod_emod.symm,
        ← h_km_emod]; simp
  have h_R_dvd : (2^32 : Int) ∣ (v - km) := Int.dvd_of_emod_eq_zero h_km_mod
  obtain ⟨q, hq⟩ := h_R_dvd
  have h_div_split : v / (2^32 : Int) - km / (2^32 : Int) = (v - km) / (2^32 : Int) :=
    sub_div_of_emod_eq_zero v km (2^32) (by decide) h_km_mod
  have h_vm_div : (v - km) / (2^32 : Int) = q := hq ▸ Int.mul_ediv_cancel_left q (by decide)
  show (v / (2^32 : Int) - km / (2^32 : Int)) * (2^32 : Int) = v - km
  rw [h_div_split, h_vm_div, hq]; ring

/-! ## L0 Triple -/

@[spec high]
theorem montgomery_reduce_element_spec (value : Std.I64) (hb : value.val.natAbs ≤ 2^55) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (value.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 2^24 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := mont_reduce_impl_value value) (mont_reduce_element_eq_ok value)
  rw [mont_reduce_impl_value_val value hb]
  set v : Int := value.val
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  set res := v / (2^32 : Int) - km / (2^32 : Int)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2
  have h_v_abs : |v| ≤ (2^55 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_res_R := mont_reduce_core v hb
  constructor
  · -- Equality clause: (res : Zq) = (v : Zq) * RINV
    show (res : Zq) = (v : Zq) * (RINV : Zq)
    exact mont_reduce_zmod v k32 res h_res_R
  · -- Bound: res.natAbs ≤ 2^24 (with |v| ≤ 2^55, |res| ≤ (2^55 + 2^31·q)/2^32 = 12578816 < 2^24)
    have h_km_abs : |km| ≤ (2^31 : Int) * 8380417 := by
      show |k32 * 8380417| ≤ _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨h_k32_lb, le_of_lt h_k32_ub⟩) (by decide)
    have h_res_abs : |res| ≤ (2^24 : Int) := by
      have h_bound : |res| * (2^32 : Int) ≤ 2^55 + (2^31 : Int) * 8380417 := by
        calc |res| * (2^32 : Int)
            = |res * (2^32 : Int)| := by rw [abs_mul]; simp
          _ = |v - km| := by rw [h_res_R]
          _ ≤ |v| + |km| := abs_sub v km
          _ ≤ 2^55 + (2^31 : Int) * 8380417 := add_le_add h_v_abs h_km_abs
      have h_div_le := (Int.le_ediv_iff_mul_le (by decide : (0:Int) < 2^32)).mpr h_bound
      have h_const : (2^55 + (2^31 : Int) * 8380417) / 2^32 = 12578816 := by norm_num
      rw [h_const] at h_div_le
      exact le_trans h_div_le (by norm_num)
    rw [Int.abs_eq_natAbs] at h_res_abs; exact_mod_cast h_res_abs

/-- Strong variant of `montgomery_reduce_element_spec`: exposes the TIGHT montgomery
    output bound `r.val.natAbs ≤ 12578816` (the true reduce bound), instead of the
    loose `≤ 2^24`. Invoked EXPLICITLY by the inverse-NTT leaves; no `@[spec]` to
    avoid hax_mvcgen ambiguity with the original. -/
theorem montgomery_reduce_element_spec_strong (value : Std.I64) (hb : value.val.natAbs ≤ 2^55) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element value
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (value.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 12578816 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := mont_reduce_impl_value value) (mont_reduce_element_eq_ok value)
  rw [mont_reduce_impl_value_val value hb]
  set v : Int := value.val
  set v32 := Int.bmod v (2^32)
  set k32 := Int.bmod (v32 * 58728449) (2^32)
  set km := k32 * 8380417
  set res := v / (2^32 : Int) - km / (2^32 : Int)
  have h_k32_lb : -(2^31 : Int) ≤ k32 := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).1
  have h_k32_ub : k32 < (2^31 : Int) := (Arith.Int.bmod_pow2_bounds 32 (v32 * 58728449)).2
  have h_v_abs : |v| ≤ (2^55 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hb
  have h_res_R := mont_reduce_core v hb
  constructor
  · -- Equality clause: (res : Zq) = (v : Zq) * RINV
    show (res : Zq) = (v : Zq) * (RINV : Zq)
    exact mont_reduce_zmod v k32 res h_res_R
  · -- Bound: res.natAbs ≤ 12578816 (with |v| ≤ 2^55, |res| ≤ (2^55 + 2^31·q)/2^32 = 12578816)
    have h_km_abs : |km| ≤ (2^31 : Int) * 8380417 := by
      show |k32 * 8380417| ≤ _; rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨h_k32_lb, le_of_lt h_k32_ub⟩) (by decide)
    have h_res_abs : |res| ≤ (12578816 : Int) := by
      have h_bound : |res| * (2^32 : Int) ≤ 2^55 + (2^31 : Int) * 8380417 := by
        calc |res| * (2^32 : Int)
            = |res * (2^32 : Int)| := by rw [abs_mul]; simp
          _ = |v - km| := by rw [h_res_R]
          _ ≤ |v| + |km| := abs_sub v km
          _ ≤ 2^55 + (2^31 : Int) * 8380417 := add_le_add h_v_abs h_km_abs
      have h_div_le := (Int.le_ediv_iff_mul_le (by decide : (0:Int) < 2^32)).mpr h_bound
      have h_const : (2^55 + (2^31 : Int) * 8380417) / 2^32 = 12578816 := by norm_num
      rw [h_const] at h_div_le
      exact h_div_le
    rw [Int.abs_eq_natAbs] at h_res_abs; exact_mod_cast h_res_abs

/-! ## `montgomery_multiply_fe_by_fer` — widen-multiply then reduce

  The impl sign-extends `fe, fer : i32` to `i64`, forms the exact i64 product
  `fe·fer`, and feeds it to the `montgomery_reduce_element` keystone:

      let i  := (fe  : i64)                    -- sign-extend, value-preserving
      let i1 := (fer : i64)
      let i2 := wrapping_mul i i1              -- exact i64 product fe·fer
      montgomery_reduce_element i2

  Under `|fer| ≤ q-1 = 8380416` and the ambient `|fe| ≤ 2^31` (any i32), the
  product `|fe·fer| ≤ 2^31·8380416 < 2^55` is exact (no wrap) and satisfies the
  keystone precondition, so the result lifts to `(fe)·(fer)·R⁻¹` in `Z_q`. -/

/-- Closed form of the do-block at the i64-product level: the impl reduces to
    `montgomery_reduce_element` of the exact (non-wrapped) i64 product. -/
theorem mmfbf_eq_ok (fe fer : Std.I32) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
      = libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_reduce_element
          (Aeneas.Std.I64.wrapping_mul
            (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
            (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer)) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer
  simp only [libcrux_secrets.traits.Classify.Blanket.classify,
             libcrux_secrets.traits.Declassify.Blanket.declassify,
             libcrux_secrets.I32.Insts.Libcrux_secretsIntCastOps.as_i64,
             CoreModels.core.num.I64.wrapping_mul,
             rust_primitives.arithmetic.wrapping_mul_i64,
             Aeneas.Std.bind_tc_ok, Aeneas.Std.lift]

/-- Under `|fer| ≤ 8380416`, the i64 product is exact (no wrap): its `.val` is
    `fe.val * fer.val` (in `Int`). Both casts are sign-extends that preserve
    value, and `|fe·fer| ≤ 2^31·8380416 < 2^63`. Mirrors the keystone's
    `h_km_val`. -/
private theorem mmfbf_product_val
    (fe fer : Std.I32) (hfer : fer.val.natAbs ≤ 8380416) :
    (Aeneas.Std.I64.wrapping_mul
        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
        (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer)).val
      = fe.val * fer.val := by
  -- i32 value bounds: -2^31 ≤ fe.val < 2^31, and |fer.val| ≤ 8380416.
  have h_fe_bounds := fe.hBounds
  have h_red31 : (Aeneas.Std.IScalarTy.I32.numBits - 1) = 31 := by decide
  rw [h_red31] at h_fe_bounds
  have h_fe_abs : |fe.val| ≤ ((2 : Int)^31) :=
    abs_le.mpr ⟨h_fe_bounds.1, le_of_lt h_fe_bounds.2⟩
  have h_fer_abs : |fer.val| ≤ (8380416 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hfer
  -- (cast .I64 x).val = x.val (sign-extend I32 → I64 preserves value).
  have h_fe_cast : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe).val = fe.val := by
    show (fe.bv.signExtend 64).toInt = fe.bv.toInt
    exact BitVec.toInt_signExtend_of_le (by decide)
  have h_fer_cast : (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer).val = fer.val := by
    show (fer.bv.signExtend 64).toInt = fer.bv.toInt
    exact BitVec.toInt_signExtend_of_le (by decide)
  -- |fe.val * fer.val| ≤ 2^31 * 8380416 < 2^63.
  have h_prod_abs : |fe.val * fer.val| ≤ ((2 : Int)^31) * 8380416 := by
    rw [abs_mul]
    calc |fe.val| * |fer.val|
        ≤ ((2 : Int)^31) * |fer.val| :=
          mul_le_mul_of_nonneg_right h_fe_abs (abs_nonneg _)
      _ ≤ ((2 : Int)^31) * 8380416 :=
          mul_le_mul_of_nonneg_left h_fer_abs (by norm_num)
  have h_prod_lb : -((2 : Int)^31 * 8380416) ≤ fe.val * fer.val := (abs_le.mp h_prod_abs).1
  have h_prod_ub : fe.val * fer.val ≤ ((2 : Int)^31 * 8380416) := (abs_le.mp h_prod_abs).2
  -- The wrapping_mul is exact: bmod (fe·fer) (2^64) = fe·fer.
  show (Aeneas.Std.I64.wrapping_mul _ _).bv.toInt = _
  have h_bv : (Aeneas.Std.I64.wrapping_mul
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer)).bv
        = (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe).bv
          * (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer).bv := by
    simp only [Aeneas.Std.I64.wrapping_mul_bv_eq]
  rw [h_bv, BitVec.toInt_mul]
  show Int.bmod _ _ = _
  rw [show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe).bv.toInt = fe.val from h_fe_cast,
      show (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer).bv.toInt = fer.val from h_fer_cast]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 64 _ (by decide)
  · -- -2^(64-1) ≤ fe.val * fer.val
    refine le_trans ?_ h_prod_lb
    norm_num
  · -- fe.val * fer.val < 2^(64-1)
    refine lt_of_le_of_lt h_prod_ub ?_
    norm_num

/-! ## L0 Triple — `montgomery_multiply_fe_by_fer` -/

@[spec high]
theorem montgomery_multiply_fe_by_fer_spec
    (fe fer : Std.I32) (hfer : fer.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (fe.val : Zq) * (fer.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 2^24 ⌝ ⦄ := by
  -- Reduce the impl to a single `montgomery_reduce_element` on the exact product.
  set product : Std.I64 :=
    Aeneas.Std.I64.wrapping_mul
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer) with h_product_def
  have h_product_val : product.val = fe.val * fer.val := mmfbf_product_val fe fer hfer
  -- The keystone precondition: |fe·fer| ≤ 2^31 · 8380416 < 2^55.
  have h_pre : product.val.natAbs ≤ 2^55 := by
    rw [h_product_val, Int.natAbs_mul]
    -- |fe.val| ≤ 2^31 (any i32) and |fer.val| ≤ 8380416.
    have h_fe_bounds := fe.hBounds
    have h_red31 : (Aeneas.Std.IScalarTy.I32.numBits - 1) = 31 := by decide
    rw [h_red31] at h_fe_bounds
    have h_fe_abs : (fe.val.natAbs : Int) ≤ ((2 : Int)^31) := by
      rw [← Int.abs_eq_natAbs]
      exact abs_le.mpr ⟨h_fe_bounds.1, le_of_lt h_fe_bounds.2⟩
    have h_nat_fe : fe.val.natAbs ≤ 2^31 := by exact_mod_cast h_fe_abs
    -- fe.natAbs * fer.natAbs ≤ 2^31 * 8380416 ≤ 2^55.
    have h_mul : fe.val.natAbs * fer.val.natAbs ≤ 2^31 * 8380416 := Nat.mul_le_mul h_nat_fe hfer
    have h_step : (2^31 * 8380416 : Nat) ≤ 2^55 := by norm_num
    exact le_trans h_mul h_step
  -- Extract the keystone's conclusion via `triple_exists_ok_l0`.
  obtain ⟨r0, h_eq_ok, h_lift, h_bound⟩ :=
    triple_exists_ok_l0 (montgomery_reduce_element_spec product h_pre)
  -- The impl reduces to .ok r0; close via triple_of_ok_l0.
  apply triple_of_ok_l0 (v := r0) (by rw [mmfbf_eq_ok]; exact h_eq_ok)
  refine ⟨?_, h_bound⟩
  -- Equality: liftZ_std r0.val = (fe.val·fer.val : Zq)·R⁻¹ = (fe)·(fer)·R⁻¹.
  rw [h_lift, h_product_val]
  show ((fe.val * fer.val : Int) : Zq) * (RINV : Zq)
        = (fe.val : Zq) * (fer.val : Zq) * (RINV : Zq)
  push_cast
  ring

/-- Strong variant of `montgomery_multiply_fe_by_fer_spec`: exposes the TIGHT
    montgomery output bound `r.val.natAbs ≤ 12578816` (instead of `≤ 2^24`), via
    `montgomery_reduce_element_spec_strong`. Invoked EXPLICITLY by the inverse-NTT
    leaves; no `@[spec]` to avoid hax_mvcgen ambiguity with the original. -/
theorem montgomery_multiply_fe_by_fer_spec_strong
    (fe fer : Std.I32) (hfer : fer.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ liftZ_std r.val = (fe.val : Zq) * (fer.val : Zq) * (RINV : Zq)
              ∧ r.val.natAbs ≤ 12578816 ⌝ ⦄ := by
  -- Reduce the impl to a single `montgomery_reduce_element` on the exact product.
  set product : Std.I64 :=
    Aeneas.Std.I64.wrapping_mul
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
      (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer) with h_product_def
  have h_product_val : product.val = fe.val * fer.val := mmfbf_product_val fe fer hfer
  -- The keystone precondition: |fe·fer| ≤ 2^31 · 8380416 < 2^55.
  have h_pre : product.val.natAbs ≤ 2^55 := by
    rw [h_product_val, Int.natAbs_mul]
    -- |fe.val| ≤ 2^31 (any i32) and |fer.val| ≤ 8380416.
    have h_fe_bounds := fe.hBounds
    have h_red31 : (Aeneas.Std.IScalarTy.I32.numBits - 1) = 31 := by decide
    rw [h_red31] at h_fe_bounds
    have h_fe_abs : (fe.val.natAbs : Int) ≤ ((2 : Int)^31) := by
      rw [← Int.abs_eq_natAbs]
      exact abs_le.mpr ⟨h_fe_bounds.1, le_of_lt h_fe_bounds.2⟩
    have h_nat_fe : fe.val.natAbs ≤ 2^31 := by exact_mod_cast h_fe_abs
    -- fe.natAbs * fer.natAbs ≤ 2^31 * 8380416 ≤ 2^55.
    have h_mul : fe.val.natAbs * fer.val.natAbs ≤ 2^31 * 8380416 := Nat.mul_le_mul h_nat_fe hfer
    have h_step : (2^31 * 8380416 : Nat) ≤ 2^55 := by norm_num
    exact le_trans h_mul h_step
  -- Extract the keystone's conclusion via `triple_exists_ok_l0`.
  obtain ⟨r0, h_eq_ok, h_lift, h_bound⟩ :=
    triple_exists_ok_l0 (montgomery_reduce_element_spec_strong product h_pre)
  -- The impl reduces to .ok r0; close via triple_of_ok_l0.
  apply triple_of_ok_l0 (v := r0) (by rw [mmfbf_eq_ok]; exact h_eq_ok)
  refine ⟨?_, h_bound⟩
  -- Equality: liftZ_std r0.val = (fe.val·fer.val : Zq)·R⁻¹ = (fe)·(fer)·R⁻¹.
  rw [h_lift, h_product_val]
  show ((fe.val * fer.val : Int) : Zq) * (RINV : Zq)
        = (fe.val : Zq) * (fer.val : Zq) * (RINV : Zq)
  push_cast
  ring

/-! ## `reduce_element` — centered Barrett reduction (i32, q = 8380417, shift 23)

  The impl computes `fe - ((fe + 2^22) >> 23) * q`, a centered Barrett reduction:

      let i  := 1 <<< 22                     -- 2^22
      let i1 := wrapping_add fe i            -- fe + 2^22
      let q' := i1 >>> 23                     -- (fe + 2^22) / 2^23  (arithmetic shift)
      let i2 := wrapping_mul q' FIELD_MODULUS -- q' * q
      wrapping_sub fe i2                       -- fe - q' * q

  Derived precondition: `|fe| ≤ 2^31 - 2^23`. Binding constraint is the `wrapping_add`
  no-overflow (`fe + 2^22 ≤ 2^31 - 2^22 < 2^31`); this also yields `|quotient| ≤ 255`,
  so `|quotient * q| ≤ 255·q < 2^31` (the `wrapping_mul` no-overflow).

  Derived output bound: `|result| ≤ 6283009`, from the decomposition
  `result = (fe - q'·2^23) + q'·(2^23 - q) = (fe - q'·2^23) + q'·8191` where
  `|fe - q'·2^23| ≤ 2^22` (floor-div remainder) and `|q'·8191| ≤ 255·8191`,
  so `|result| ≤ 2^22 + 255·8191 = 6283009`. -/

/-- Closed-form value computed by the `reduce_element` impl, as an `IScalar.I32`.

    Stages the BV-level result of unfolding `reduce_element` so the Triple proof can
    apply `triple_of_ok_l0`. Mirrors ML-KEM's `barrett_reduce_impl_value`. -/
def reduce_impl_value (fe : Std.I32) : Std.I32 :=
  let i  : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩
  let i1 : Std.I32 := Aeneas.Std.I32.wrapping_add fe i
  let quotient : Std.I32 := ⟨i1.bv.sshiftRight 23⟩
  let i2 : Std.I32 := Aeneas.Std.I32.wrapping_mul quotient (8380417#i32)
  Aeneas.Std.I32.wrapping_sub fe i2

/-- The `do`-block reduces to `Result.ok (reduce_impl_value fe)`. -/
theorem reduce_element_eq_ok (fe : Std.I32) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element fe
      = .ok (reduce_impl_value fe) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element reduce_impl_value
  have h_q : libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS = 8380417#i32 := by
    unfold libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS; rfl
  -- `1#i32 <<< 22#i32` is `IScalar.shiftLeft_IScalar`.
  have h_22_pos : (22#i32 : Std.I32).val ≥ 0 := by decide
  have h_22_lt : (22#i32 : Std.I32).toNat < Aeneas.Std.IScalarTy.I32.numBits := by decide
  -- `i1 >>> 23#i32` is `IScalar.shiftRight_IScalar`.
  have h_23_pos : (23#i32 : Std.I32).val ≥ 0 := by decide
  have h_23_lt : (23#i32 : Std.I32).toNat < Aeneas.Std.IScalarTy.I32.numBits := by decide
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.IScalar.shiftLeft_IScalar,
             Aeneas.Std.IScalar.shiftLeft,
             HShiftRight.hShiftRight, Aeneas.Std.IScalar.shiftRight_IScalar,
             Aeneas.Std.IScalar.shiftRight,
             h_22_pos, h_22_lt, h_23_pos, h_23_lt, reduceIte,
             CoreModels.core.num.I32.wrapping_add,
             CoreModels.core.num.I32.wrapping_mul,
             CoreModels.core.num.I32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_add_i32,
             rust_primitives.arithmetic.wrapping_mul_i32,
             rust_primitives.arithmetic.wrapping_sub_i32,
             Aeneas.Std.bind_tc_ok, h_q]
  rfl

/-- Bridge: `(reduce_impl_value fe).val = fe.val - quotient * 8380417` (as `Int`), where
    `quotient = (fe.val + 2^22) / 2^23`, under `|fe.val| ≤ 2^31 - 2^23`. -/
private theorem reduce_impl_value_val
    (fe : Std.I32) (hb : fe.val.natAbs ≤ 2^31 - 2^23) :
    (reduce_impl_value fe).val
      = fe.val - ((fe.val + (2^22 : Int)) / (2^23 : Int)) * 8380417 := by
  unfold reduce_impl_value
  set v : Int := fe.val with hv_def
  -- |v| ≤ 2^31 - 2^23.
  have h_v_abs : |v| ≤ (2^31 - 2^23 : Int) := by
    rw [Int.abs_eq_natAbs]
    have : (v.natAbs : Int) ≤ ((2^31 - 2^23 : Nat) : Int) := by exact_mod_cast hb
    have h2 : ((2^31 - 2^23 : Nat) : Int) = (2^31 - 2^23 : Int) := by norm_num
    omega
  have h_v_lb : -(2^31 - 2^23 : Int) ≤ v := (abs_le.mp h_v_abs).1
  have h_v_ub : v ≤ (2^31 - 2^23 : Int) := (abs_le.mp h_v_abs).2
  -- i := 1 <<< 22 = 2^22.
  have h_i_val : (⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩ : Std.I32).val = (2^22 : Int) := by decide
  set i : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 22⟩
  -- i1 := wrapping_add fe i. No wrap: -2^31 ≤ v + 2^22 < 2^31.
  set i1 : Std.I32 := Aeneas.Std.I32.wrapping_add fe i
  have h_sum_lb : -(2 : Int)^31 ≤ v + 2^22 := by
    have h_const : -(2 : Int)^31 ≤ -(2^31 - 2^23 : Int) + 2^22 := by norm_num
    omega
  have h_sum_ub : v + 2^22 < (2 : Int)^31 := by
    have h_const : (2^31 - 2^23 : Int) + 2^22 < (2 : Int)^31 := by norm_num
    omega
  have h_i1_val : i1.val = v + 2^22 := by
    show (Aeneas.Std.I32.wrapping_add _ _).val = _
    rw [Aeneas.Std.I32.wrapping_add_val_eq, h_i_val]
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      rw [h_red]; exact h_sum_lb
    · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      rw [h_red]; exact h_sum_ub
  -- quotient := i1 >>> 23 = i1.val / 2^23.
  set quotient : Std.I32 := ⟨i1.bv.sshiftRight 23⟩
  have h_quotient_val : quotient.val = i1.val / (2^23 : Int) := by
    show (i1.bv.sshiftRight 23).toInt = _
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
    have h_pow_nat : ((2^23 : Nat) : Int) = ((2 : Int)^23) := by push_cast
    rw [h_pow_nat]
    show i1.bv.toInt / _ = i1.val / _
    rfl
  -- quotient = (v + 2^22) / 2^23.
  have h_quotient_eq : quotient.val = (v + 2^22) / (2^23 : Int) := by
    rw [h_quotient_val, h_i1_val]
  -- |quotient| ≤ 255 (so the multiply fits): -255 ≤ quotient ≤ 255.
  have h_quotient_bounds : -255 ≤ quotient.val ∧ quotient.val ≤ 255 := by
    rw [h_quotient_eq]
    refine ⟨?_, ?_⟩
    · have h_lb2 : -(2^31 - 2^23 : Int) + 2^22 ≤ v + 2^22 := by omega
      have h := Int.ediv_le_ediv (a := -(2^31 - 2^23 : Int) + 2^22)
                  (b := v + 2^22) (c := (2^23 : Int)) (by norm_num) h_lb2
      have h_const : (-(2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = -255 := by norm_num
      rw [h_const] at h; omega
    · have h_ub2 : v + 2^22 ≤ (2^31 - 2^23 : Int) + 2^22 := by omega
      have h := Int.ediv_le_ediv (a := v + 2^22)
                  (b := (2^31 - 2^23 : Int) + 2^22) (c := (2^23 : Int)) (by norm_num) h_ub2
      have h_const : ((2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = 255 := by norm_num
      rw [h_const] at h; omega
  -- i2 := wrapping_mul quotient 8380417. No wrap: |quotient * q| ≤ 255 * q < 2^31.
  have h_q_lit : (8380417#i32 : Std.I32).val = 8380417 := by decide
  set i2 : Std.I32 := Aeneas.Std.I32.wrapping_mul quotient (8380417#i32)
  have h_i2_val : i2.val = quotient.val * 8380417 := by
    show (Aeneas.Std.I32.wrapping_mul _ _).val = _
    rw [Aeneas.Std.I32.wrapping_mul_val_eq, h_q_lit]
    apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_lb := mul_le_mul_of_nonneg_right h_quotient_bounds.1 (by decide : (0 : Int) ≤ 8380417)
      have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      have h_const : -(2 : Int)^31 ≤ (-255 : Int) * 8380417 := by norm_num
      rw [h_red]; omega
    · have h_ub := mul_le_mul_of_nonneg_right h_quotient_bounds.2 (by decide : (0 : Int) ≤ 8380417)
      have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
      have h_const : (255 : Int) * 8380417 < (2 : Int)^31 := by norm_num
      rw [h_red]; omega
  -- Bound on i2.val for the final wrapping_sub: |i2.val| ≤ 255 * 8380417.
  have h_i2_bounds : -(255 * 8380417 : Int) ≤ i2.val ∧ i2.val ≤ (255 * 8380417 : Int) := by
    rw [h_i2_val]
    constructor
    · have h_lb := mul_le_mul_of_nonneg_right h_quotient_bounds.1 (by decide : (0 : Int) ≤ 8380417)
      have : (-255 : Int) * 8380417 = -(255 * 8380417 : Int) := by ring
      omega
    · exact mul_le_mul_of_nonneg_right h_quotient_bounds.2 (by decide : (0 : Int) ≤ 8380417)
  -- result := wrapping_sub fe i2. No wrap: |v - i2.val| < 2^31.
  -- (|v| ≤ 2^31 - 2^23 and |i2| ≤ 255*q < 2^31; their difference still fits.)
  -- Concrete-numeral bounds on v (for the omega-on-difference steps).
  have h_vlb_lit : (-2139095040 : Int) ≤ v := by
    have h_const : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
    rw [h_const] at h_v_lb; exact h_v_lb
  have h_vub_lit : v ≤ (2139095040 : Int) := by
    have h_const : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
    rw [h_const] at h_v_ub; exact h_v_ub
  have h_q255 : (255 * 8380417 : Int) = 2137006335 := by norm_num
  have h_sub_lb : -(2 : Int)^31 ≤ v - i2.val := by
    have h_i2_ub := h_i2_bounds.2
    have h_pow31 : (2 : Int)^31 = 2147483648 := by norm_num
    rw [h_q255] at h_i2_ub; rw [h_pow31]; omega
  have h_sub_ub : v - i2.val < (2 : Int)^31 := by
    have h_i2_lb := h_i2_bounds.1
    have h_pow31 : (2 : Int)^31 = 2147483648 := by norm_num
    rw [h_q255] at h_i2_lb; rw [h_pow31]; omega
  show (Aeneas.Std.I32.wrapping_sub fe i2).val = _
  rw [Aeneas.Std.I32.wrapping_sub_val_eq, h_i2_val, h_quotient_eq]
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_i2_val, h_quotient_eq] at h_sub_lb; rw [h_red]; exact h_sub_lb
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_i2_val, h_quotient_eq] at h_sub_ub; rw [h_red]; exact h_sub_ub

/-- **Pure `Int`-level core of the centered Barrett reduction.**

    With `quotient = (v + 2^22) / 2^23` and `r = v - quotient·q`, under `|v| ≤ 2^31 - 2^23`:
    `r ≡ v (mod q)` (trivially, the difference is a multiple of q) and `|r| ≤ 6283009`.

    Bound via the decomposition `r = (v - quotient·2^23) + quotient·(2^23 - q)` where
    `2^23 - q = 8191`, `v - quotient·2^23 ∈ [-2^22, 2^22)` (floor-div remainder), and
    `|quotient| ≤ 255`, giving `|r| ≤ 2^22 + 255·8191 = 6283009`. -/
private theorem reduce_element_core
    (v : Int) (hb : v.natAbs ≤ 2^31 - 2^23) :
    let quotient := (v + (2^22 : Int)) / (2^23 : Int)
    let r := v - quotient * 8380417
    (r : Zq) = (v : Zq) ∧ r.natAbs ≤ 6283009 := by
  -- |v| ≤ 2^31 - 2^23.
  have h_v_abs : |v| ≤ (2^31 - 2^23 : Int) := by
    rw [Int.abs_eq_natAbs]
    have : (v.natAbs : Int) ≤ ((2^31 - 2^23 : Nat) : Int) := by exact_mod_cast hb
    have h2 : ((2^31 - 2^23 : Nat) : Int) = (2^31 - 2^23 : Int) := by norm_num
    omega
  have h_v_lb : -(2139095040 : Int) ≤ v := by
    have h_const : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
    have := (abs_le.mp h_v_abs).1; rw [h_const] at this; exact this
  have h_v_ub : v ≤ (2139095040 : Int) := by
    have h_const : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
    have := (abs_le.mp h_v_abs).2; rw [h_const] at this; exact this
  set quotient : Int := (v + (2^22 : Int)) / (2^23 : Int) with hq_def
  set r : Int := v - quotient * 8380417 with hr_def
  refine ⟨?_, ?_⟩
  · -- (r : Zq) = (v : Zq) since r = v - quotient·q and (q : Zq) = 0.
    show ((v - quotient * 8380417 : Int) : Zq) = (v : Zq)
    have h_q_zero : ((8380417 : Int) : Zq) = 0 := by
      show ((8380417 : Int) : ZMod Q) = 0
      rw [show (8380417 : Int) = ((Q : Nat) : Int) from by norm_num]
      push_cast
      exact ZMod.natCast_self Q
    rw [Int.cast_sub, Int.cast_mul, h_q_zero, mul_zero, sub_zero]
  · -- |r| ≤ 6283009 via the decomposition r = (v - quotient·2^23) + quotient·8191.
    -- Floor-div remainder: v + 2^22 - quotient·2^23 ∈ [0, 2^23).
    have h_rem_lb : (0 : Int) ≤ (v + 2^22) - quotient * (2^23 : Int) := by
      have h := Int.emod_nonneg (v + 2^22) (by norm_num : (2^23 : Int) ≠ 0)
      have h_decomp : (v + 2^22) % (2^23 : Int) = (v + 2^22) - quotient * (2^23 : Int) := by
        rw [hq_def, Int.emod_def]; ring
      rw [h_decomp] at h; exact h
    have h_rem_ub : (v + 2^22) - quotient * (2^23 : Int) < (2^23 : Int) := by
      have h := Int.emod_lt_of_pos (v + 2^22) (by norm_num : (0 : Int) < 2^23)
      have h_decomp : (v + 2^22) % (2^23 : Int) = (v + 2^22) - quotient * (2^23 : Int) := by
        rw [hq_def, Int.emod_def]; ring
      rw [h_decomp] at h; exact h
    -- So d := v - quotient·2^23 ∈ [-2^22, 2^22).
    set d : Int := v - quotient * (2^23 : Int) with hd_def
    have h_d_lb : -(2^22 : Int) ≤ d := by
      have : (0 : Int) ≤ d + 2^22 := by rw [hd_def]; linarith [h_rem_lb]
      linarith
    have h_d_ub : d < (2^22 : Int) := by
      have : d + 2^22 < (2^23 : Int) := by rw [hd_def]; linarith [h_rem_ub]
      have h_pow : (2^23 : Int) - 2^22 = 2^22 := by norm_num
      linarith [this, h_pow]
    -- |quotient| ≤ 255.
    have h_quot_bounds : -255 ≤ quotient ∧ quotient ≤ 255 := by
      rw [hq_def]
      refine ⟨?_, ?_⟩
      · have h_31_23 : -(2^31 - 2^23 : Int) = -2139095040 := by norm_num
        have h_lb2 : -(2^31 - 2^23 : Int) + 2^22 ≤ v + 2^22 := by
          rw [h_31_23]; linarith [h_v_lb]
        have h := Int.ediv_le_ediv (a := -(2^31 - 2^23 : Int) + 2^22)
                    (b := v + 2^22) (c := (2^23 : Int)) (by norm_num) h_lb2
        have h_const : (-(2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = -255 := by norm_num
        rw [h_const] at h; omega
      · have h_31_23 : (2^31 - 2^23 : Int) = 2139095040 := by norm_num
        have h_ub2 : v + 2^22 ≤ (2^31 - 2^23 : Int) + 2^22 := by
          rw [h_31_23]; linarith [h_v_ub]
        have h := Int.ediv_le_ediv (a := v + 2^22)
                    (b := (2^31 - 2^23 : Int) + 2^22) (c := (2^23 : Int)) (by norm_num) h_ub2
        have h_const : ((2^31 - 2^23 : Int) + 2^22) / (2^23 : Int) = 255 := by norm_num
        rw [h_const] at h; omega
    -- r = d + quotient·8191  (since 2^23 - q = 8191).
    have h_r_decomp : r = d + quotient * 8191 := by
      rw [hr_def, hd_def]
      have h_2_23 : (2^23 : Int) = 8380417 + 8191 := by norm_num
      have : quotient * (2^23 : Int) = quotient * 8380417 + quotient * 8191 := by
        rw [h_2_23]; ring
      linarith [this]
    -- |r| ≤ 2^22 + 255·8191 = 6283009.
    have h_quot8191_lb : -(255 * 8191 : Int) ≤ quotient * 8191 := by
      have := mul_le_mul_of_nonneg_right h_quot_bounds.1 (by norm_num : (0 : Int) ≤ 8191)
      have h_eq : (-255 : Int) * 8191 = -(255 * 8191 : Int) := by ring
      linarith [this, h_eq]
    have h_quot8191_ub : quotient * 8191 ≤ (255 * 8191 : Int) :=
      mul_le_mul_of_nonneg_right h_quot_bounds.2 (by norm_num : (0 : Int) ≤ 8191)
    have h_r_lb : -(6283009 : Int) ≤ r := by
      rw [h_r_decomp]
      have h_2_22 : -(2^22 : Int) = -4194304 := by norm_num
      have h_255 : (255 * 8191 : Int) = 2088705 := by norm_num
      linarith [h_d_lb, h_quot8191_lb, h_2_22, h_255]
    have h_r_ub : r ≤ (6283009 : Int) := by
      rw [h_r_decomp]
      have h_2_22 : (2^22 : Int) = 4194304 := by norm_num
      have h_255 : (255 * 8191 : Int) = 2088705 := by norm_num
      linarith [h_d_ub, h_quot8191_ub, h_2_22, h_255]
    have h_abs : |r| ≤ (6283009 : Int) := abs_le.mpr ⟨h_r_lb, h_r_ub⟩
    rw [Int.abs_eq_natAbs] at h_abs
    exact_mod_cast h_abs

/-! ## L0 Triple -/

@[spec high]
theorem reduce_element_spec (fe : Std.I32) (h : fe.val.natAbs ≤ 2^31 - 2^23) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element fe
    ⦃ ⇓ r => ⌜ liftZ_std r.val = liftZ_std fe.val
              ∧ r.val.natAbs ≤ 6283009 ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := reduce_impl_value fe) (reduce_element_eq_ok fe)
  rw [reduce_impl_value_val fe h]
  -- Goal: liftZ_std (fe.val - q' * 8380417) = liftZ_std fe.val ∧ (…).natAbs ≤ 6283009.
  have h_core := reduce_element_core fe.val h
  refine ⟨?_, h_core.2⟩
  -- liftZ_std x = (x : Zq); reduce to the core's Zq equality.
  show ((fe.val - ((fe.val + (2^22 : Int)) / (2^23 : Int)) * 8380417 : Int) : Zq)
        = (fe.val : Zq)
  exact h_core.1

/-! ## `shift_left_then_reduce_spec`

    `simd.portable.arithmetic.shift_left_then_reduce SHIFT_BY simd_unit` is an
    8-iter loop applying `reduce_element (simd_unit.values[i] <<< SHIFT_BY)` to
    each lane. STRUCTURALLY IDENTICAL to `montgomery_multiply_by_constant`
    (a single free parameter `SHIFT_BY` carried by the loop, no per-lane guard on
    the operand), so it is proven the same way via `elementwise_unary_spec`.

    The one new ingredient is the signed-left-shift `.val` closed form:
    `shiftLeft_ok` (the in-range `Result.ok` form) + `shiftLeft_shifted_val`
    (the no-overflow `.val = x·2^k` value, pure-`BitVec`); power2round/decompose
    will reuse these. Outputs are CLEAN mod-q, so the post is in `liftZ_std`
    form (residue-preserving): under `hbound`, the signed shift equals
    `x·2^SHIFT_BY` exactly and `reduce_element` preserves the residue. -/

/-- `Slice.len (Array.to_slice (a : CoeffArray)) = 8#usize`. -/
private theorem coeff_slice_len_eq (a : CoeffArray) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (8#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  rw [Aeneas.Std.Slice.len_val]
  show (Aeneas.Std.Array.to_slice a).length = (8#usize : Std.Usize).val
  rw [Aeneas.Std.Array.length_to_slice a]

/-- Signed I32 left shift, `Result.ok` form. Generalizes the literal
    `1#i32 <<< 22#i32` case used inside `reduce_element_eq_ok` to a runtime
    `SHIFT_BY`: `IScalar.shiftLeft_IScalar` discharges `SHIFT_BY.val ≥ 0` and
    `SHIFT_BY.toNat < I32.numBits`, yielding `⟨x.bv.shiftLeft SHIFT_BY.toNat⟩`. -/
theorem shiftLeft_ok (x : Std.I32) (SHIFT_BY : Std.I32)
    (h0 : 0 ≤ SHIFT_BY.val) (h32 : SHIFT_BY.val < 32) :
    (x <<< SHIFT_BY) = .ok ⟨x.bv.shiftLeft SHIFT_BY.toNat⟩ := by
  have h_pos : SHIFT_BY.val ≥ 0 := h0
  have h_lt : SHIFT_BY.toNat < Aeneas.Std.IScalarTy.I32.numBits := by
    show SHIFT_BY.val.toNat < 32; omega
  simp only [HShiftLeft.hShiftLeft, Aeneas.Std.IScalar.shiftLeft_IScalar,
             Aeneas.Std.IScalar.shiftLeft, h_pos, h_lt, reduceIte]

/-- Signed I32 left shift, `.val` closed form under no-overflow (pure `BitVec`).
    `(x.bv.shiftLeft k).toInt = x.val * 2^k` whenever
    `|x.val|·2^k ≤ 2^31 - 2^23` (so `x.val·2^k ∈ [−2^31, 2^31)`, no wrap).
    Mirrors how the `sshiftRight` `.val` lemmas bridge `BitVec.toInt`; here the
    bridge is `x.bv.toNat ≡ x.val (mod 2^32)`, so the unsigned `toInt_shiftLeft`
    form collapses to the signed product after a `bmod` cancellation. -/
theorem shiftLeft_shifted_val (x : Std.I32) (k : Nat)
    (hb : x.val.natAbs * 2 ^ k ≤ 2 ^ 31 - 2 ^ 23) :
    (⟨x.bv.shiftLeft k⟩ : Std.I32).val = x.val * 2 ^ k := by
  show (x.bv.shiftLeft k).toInt = x.val * 2 ^ k
  rw [show x.bv.shiftLeft k = x.bv <<< k from rfl, BitVec.toInt_shiftLeft]
  rw [Nat.shiftLeft_eq, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  -- ↑x.bv.toNat = x.val + 2^32 * q, so the leading `2^32` summand drops under `bmod`.
  have h_decomp : (x.bv.toNat : Int)
      = x.val + (2^32 : Nat) * Int.bdiv (x.bv.toNat : Int) (2^32) := by
    have h := Int.bmod_eq_self_sub_mul_bdiv (x.bv.toNat : Int) (2^32)
    have h_xval : x.val = Int.bmod (x.bv.toNat : Int) (2^32) := by
      show x.bv.toInt = _; rw [BitVec.toInt_eq_toNat_bmod]
    rw [← h_xval] at h; omega
  rw [h_decomp, add_mul, mul_assoc, Int.add_mul_bmod_self_left]
  -- `(x.val * 2^k).bmod 2^32 = x.val * 2^k` from the no-overflow window.
  have h_pow_pos : (0 : Int) < 2 ^ k := by positivity
  have h_abs_bound : |x.val * 2 ^ k| ≤ (2 ^ 31 - 2 ^ 23 : Int) := by
    rw [abs_mul, abs_of_pos h_pow_pos, Int.abs_eq_natAbs]
    calc (x.val.natAbs : Int) * 2 ^ k
        = ((x.val.natAbs * 2 ^ k : Nat) : Int) := by push_cast; ring
      _ ≤ ((2 ^ 31 - 2 ^ 23 : Nat) : Int) := by exact_mod_cast hb
      _ = (2 ^ 31 - 2 ^ 23 : Int) := by norm_num
  have h_lb : -(2 ^ 31 : Int) ≤ x.val * 2 ^ k := by
    have h := (abs_le.mp h_abs_bound).1; norm_num at h ⊢; omega
  have h_ub : x.val * 2 ^ k < (2 ^ 31 : Int) := by
    have h := (abs_le.mp h_abs_bound).2; norm_num at h ⊢; omega
  apply Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_red]; exact h_lb
  · have h_red : ((2 : Int)^(32-1)) = (2 : Int)^31 := by norm_num
    rw [h_red]; exact h_ub

/-- Per-element predicate (guarded form): given the per-lane no-overflow bound,
    the output lifts (residue-preservingly) to `(x·2^SHIFT_BY)` in `Z_q` and
    stays `≤ 6283009` in size. The uniform shift bounds (`h0`/`h32`) are closed
    over by the per-element spec. -/
private def slr_per_elem_P (SHIFT_BY x r : Std.I32) : Prop :=
  x.val.natAbs * 2 ^ SHIFT_BY.toNat ≤ 2 ^ 31 - 2 ^ 23 →
    liftZ_std r.val = liftZ_std x.val * (2 : Zq) ^ SHIFT_BY.toNat
    ∧ r.val.natAbs ≤ 6283009

/-- Per-element Triple: `(x <<< SHIFT_BY) >>= reduce_element` realizes
    `slr_per_elem_P SHIFT_BY x`. The shift always succeeds (given `h0`/`h32`), so
    the program reduces to `reduce_element ⟨x.bv.shiftLeft SHIFT_BY.toNat⟩`; under
    the guarded lane bound, `shiftLeft_shifted_val` exposes its value as `x·2^k`,
    and `reduce_element_spec` gives the residue-preserving post. -/
private theorem slr_per_elem_spec (SHIFT_BY x : Std.I32)
    (h0 : 0 ≤ SHIFT_BY.val) (h32 : SHIFT_BY.val < 32) :
    ⦃ ⌜ True ⌝ ⦄
    (do let i2 ← x <<< SHIFT_BY
        libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element i2)
    ⦃ ⇓ r => ⌜ slr_per_elem_P SHIFT_BY x r ⌝ ⦄ := by
  rw [shiftLeft_ok x SHIFT_BY h0 h32]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [reduce_element_eq_ok]
  refine triple_of_ok_l0 (v := reduce_impl_value ⟨x.bv.shiftLeft SHIFT_BY.toNat⟩) rfl ?_
  show slr_per_elem_P SHIFT_BY x _
  intro hb
  set i2 : Std.I32 := ⟨x.bv.shiftLeft SHIFT_BY.toNat⟩ with hi2
  have h_shl_val : i2.val = x.val * 2 ^ SHIFT_BY.toNat :=
    shiftLeft_shifted_val x SHIFT_BY.toNat hb
  have h_red_pre : i2.val.natAbs ≤ 2 ^ 31 - 2 ^ 23 := by
    rw [h_shl_val]
    have h_abs : (x.val * 2 ^ SHIFT_BY.toNat).natAbs = x.val.natAbs * 2 ^ SHIFT_BY.toNat := by
      rw [Int.natAbs_mul]; congr 1
    rw [h_abs]; exact hb
  obtain ⟨rv, h_red_ok, h_red_P⟩ :=
    triple_exists_ok_l0 (reduce_element_spec i2 h_red_pre)
  rw [reduce_element_eq_ok] at h_red_ok
  have h_eq : reduce_impl_value i2 = rv := Result.ok.inj h_red_ok
  rw [h_eq]
  refine ⟨?_, h_red_P.2⟩
  rw [h_red_P.1, h_shl_val]
  show ((x.val * 2 ^ SHIFT_BY.toNat : Int) : Zq) = (x.val : Zq) * (2 : Zq) ^ SHIFT_BY.toNat
  push_cast; ring

set_option maxHeartbeats 2000000 in
@[spec]
theorem shift_left_then_reduce_spec
    (SHIFT_BY : Std.I32)
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hshift : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 32)
    (hbound : ∀ j, j < 8 →
      (simd_unit.values.val[j]!).val.natAbs * 2 ^ SHIFT_BY.toNat ≤ 2 ^ 31 - 2 ^ 23) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce SHIFT_BY simd_unit
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                liftZ_std (r.values.val[j]!).val
                  = liftZ_std (simd_unit.values.val[j]!).val * (2 : Zq) ^ SHIFT_BY.toNat
              ∧ (r.values.val[j]!).val.natAbs ≤ 6283009 ⌝ ⦄ := by
  obtain ⟨h0, h32⟩ := hshift
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Array.to_slice simd_unit.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq simd_unit.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce_loop
  -- Bridge `shift_left_then_reduce_loop.body SHIFT_BY` to
  -- `unary_loop_body (fun x => (x <<< SHIFT_BY) >>= reduce_element)`. Single index,
  -- free `SHIFT_BY`; `bind_assoc` re-associates the two-bind body, then `rfl`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce_loop.body
          SHIFT_BY p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        unary_loop_body
          (fun x => do let i2 ← x <<< SHIFT_BY
                       libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element i2)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.shift_left_then_reduce_loop.body
    unfold unary_loop_body
    simp only [bind_assoc]
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok_l0
      (elementwise_unary_spec
        (fun x => do let i2 ← x <<< SHIFT_BY
                     libcrux_iot_ml_dsa.simd.portable.arithmetic.reduce_element i2)
        (slr_per_elem_P SHIFT_BY)
        (fun x => slr_per_elem_spec SHIFT_BY x h0 h32)
        simd_unit.values)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok_l0 (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show liftZ_std (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P (hbound j hj)

/-! ## `power2round_element` (DUAL-OUTPUT rounding keystone)

    `simd.portable.arithmetic.power2round_element` is the per-lane Power2Round:
    given a signed `i32` `t` in `[-q, q)`, it computes the canonical `[0, q)` rep
    `t1` (via a sign-mask add of `q`), then splits `t1` into the high part
    `r1 = ⌊(t1 - 1 + 2^12)/2^13⌋` and low part `r0 = t1 - r1·2^13`, returning
    `(r0, r1)` (LOW, HIGH). The clean spec `Spec.Rounding.power2round` returns
    `(r1, r0)` (HIGH, LOW) — the output order is SWAPPED.

    New shift-`.val` infra (reused by `decompose`/`use_hint`):
    - `sshiftRight_val_i32` — signed right shift `.val = x.val / 2^k` (T-division;
      for `x ≥ 0` this is floor; mirrors the inline `BitVec.toInt_sshiftRight` lemmas).
    - `shiftRight_IScalar_ok` / `shiftRight_UScalar_ok` — the `Result.ok` forms for the
      `>>> 31#i32` and `>>> 13#usize` shift mechanics.
    - `shiftLeft_UScalar_ok` — the `Result.ok` form for `1#i32 <<< 12#usize` /
      `t11 <<< 13#usize` (usize-amount); `.val` via the existing
      `shiftLeft_shifted_val`.
    - `power2round_sign_mask_val` — the riskiest fact: the sign mask
      `(t >> 31) & q` is `q` iff `t < 0`, else `0`; proven via the value route
      (`(t >> 31).toInt = t.val / 2^31 ∈ {-1, 0}` ⟹ bv is `allOnes`/`0`),
      kernel-checkable and `bv_decide`-free. -/

/-- Signed right shift `.val` (T-division). For `x ≥ 0` it equals floor division
    (used for `i5 >>> 13` where `i5 ≥ 4095 > 0`). -/
private theorem sshiftRight_val_i32 (x : Std.I32) (k : Nat) :
    (⟨x.bv.sshiftRight k⟩ : Std.I32).val = x.val / (2 ^ k : Int) := by
  show (x.bv.sshiftRight k).toInt = _
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast

/-- `>>> SHIFT#i32` (I32-amount), `Result.ok` form, when `0 ≤ SHIFT < 32`. -/
private theorem shiftRight_IScalar_ok (x SHIFT : Std.I32)
    (h0 : 0 ≤ SHIFT.val) (h32 : SHIFT.toNat < 32) :
    (x >>> SHIFT) = .ok (⟨x.bv.sshiftRight SHIFT.toNat⟩ : Std.I32) := by
  show Aeneas.Std.IScalar.shiftRight_IScalar x SHIFT = _
  unfold Aeneas.Std.IScalar.shiftRight_IScalar Aeneas.Std.IScalar.shiftRight
  rw [if_pos h0, if_pos (show SHIFT.toNat < Aeneas.Std.IScalarTy.I32.numBits from h32)]

/-- `>>> SHIFT#usize` (usize-amount) on an I32, `Result.ok` form, when the value of
    `SHIFT` is `< 32`. -/
private theorem shiftRight_UScalar_ok (x : Std.I32) (SHIFT : Std.Usize)
    (h32 : SHIFT.val < 32) :
    (x >>> SHIFT) = .ok (⟨x.bv.sshiftRight SHIFT.val⟩ : Std.I32) := by
  show Aeneas.Std.IScalar.shiftRight_UScalar x SHIFT = _
  unfold Aeneas.Std.IScalar.shiftRight_UScalar Aeneas.Std.IScalar.shiftRight
  rw [if_pos (show SHIFT.val < Aeneas.Std.IScalarTy.I32.numBits from h32)]

/-- `<<< SHIFT#usize` (usize-amount) on an I32, `Result.ok` form, when the value of
    `SHIFT` is `< 32`. -/
private theorem shiftLeft_UScalar_ok (x : Std.I32) (SHIFT : Std.Usize)
    (h32 : SHIFT.val < 32) :
    (x <<< SHIFT) = .ok (⟨x.bv.shiftLeft SHIFT.val⟩ : Std.I32) := by
  show Aeneas.Std.IScalar.shiftLeft_UScalar x SHIFT = _
  unfold Aeneas.Std.IScalar.shiftLeft_UScalar Aeneas.Std.IScalar.shiftLeft
  rw [if_pos (show SHIFT.val < Aeneas.Std.IScalarTy.I32.numBits from h32)]

/-- I32 `wrapping_add` value, no-overflow form. -/
private theorem wrapping_add_val_noov (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val + y.val) (hub : x.val + y.val < 2 ^ 31) :
    (Aeneas.Std.I32.wrapping_add x y).val = x.val + y.val := by
  rw [Aeneas.Std.I32.wrapping_add_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hlb
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hub

/-- I32 `wrapping_sub` value, no-overflow form. -/
private theorem wrapping_sub_val_noov (x y : Std.I32)
    (hlb : -(2 ^ 31 : Int) ≤ x.val - y.val) (hub : x.val - y.val < 2 ^ 31) :
    (Aeneas.Std.I32.wrapping_sub x y).val = x.val - y.val := by
  rw [Aeneas.Std.I32.wrapping_sub_val_eq]
  apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hlb
  · rw [show ((2 : Int) ^ (32 - 1)) = 2 ^ 31 from by norm_num]; exact hub

/-- The sign-mask `.val`: `(t >> 31) & q` is `q` iff `t < 0`, else `0`.

    Value route (kernel-checkable, `bv_decide`-free): `(t >> 31).toInt = t.val / 2^31`
    which is `-1` (`t < 0`) or `0` (`t ≥ 0`) under the I32 bound `|t.val| < 2^31`; the
    only I32 bitvector with `toInt = -1` is `allOnes` (with `allOnes &&& q = q`) and with
    `toInt = 0` is `0#32` (with `0 &&& q = 0`). -/
private theorem power2round_sign_mask_val (t : Std.I32) :
    (⟨(t.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32).val
      = if t.val < 0 then 8380417 else 0 := by
  have h_bd := Aeneas.Std.IScalar.hBounds t
  have h_lb : -(2 ^ 31 : Int) ≤ t.val := by
    have := h_bd.1
    simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_ub : t.val < (2 ^ 31 : Int) := by
    have := h_bd.2
    simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_shrtoInt : (t.bv.sshiftRight 31).toInt = t.val / (2 ^ 31 : Int) := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  by_cases h : t.val < 0
  · rw [if_pos h]
    have h_div : t.val / (2 ^ 31 : Int) = -1 := by omega
    have h_allones : t.bv.sshiftRight 31 = BitVec.allOnes 32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((t.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv).toInt = _
    rw [h_allones, BitVec.allOnes_and]; decide
  · rw [if_neg h]
    have h_div : t.val / (2 ^ 31 : Int) = 0 := by omega
    have h_zero : t.bv.sshiftRight 31 = 0#32 := by
      apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
    show ((t.bv.sshiftRight 31) &&& (8380417#i32 : Std.I32).bv).toInt = _
    rw [h_zero, BitVec.zero_and]; decide

/-- Closed pure form of `power2round_element` (LOW, HIGH). Mirrors `reduce_impl_value`. -/
def power2round_impl_value (t : Std.I32) : Std.I32 × Std.I32 :=
  let i   : Std.I32 := ⟨t.bv.sshiftRight 31⟩
  let i1  : Std.I32 := ⟨i.bv &&& (8380417#i32 : Std.I32).bv⟩
  let t1  : Std.I32 := Aeneas.Std.I32.wrapping_add t i1
  let i2  : Std.I32 := Aeneas.Std.I32.wrapping_sub t1 (1#i32)
  let i4  : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 12⟩
  let i5  : Std.I32 := Aeneas.Std.I32.wrapping_add i2 i4
  let t11 : Std.I32 := ⟨i5.bv.sshiftRight 13⟩
  let i6  : Std.I32 := ⟨t11.bv.shiftLeft 13⟩
  let t0  : Std.I32 := Aeneas.Std.I32.wrapping_sub t1 i6
  (t0, t11)

set_option maxHeartbeats 1000000 in
/-- The `do`-block reduces to `Result.ok (power2round_impl_value t)`. -/
theorem power2round_element_eq_ok (t : Std.I32) :
    libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element t
      = .ok (power2round_impl_value t) := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element power2round_impl_value
  have h_q : libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS = 8380417#i32 := by
    unfold libcrux_iot_ml_dsa.simd.traits.FIELD_MODULUS; rfl
  have h_d : libcrux_iot_ml_dsa.constants.BITS_IN_LOWER_PART_OF_T = 13#usize := by
    unfold libcrux_iot_ml_dsa.constants.BITS_IN_LOWER_PART_OF_T; rfl
  -- `>>> 31#i32`.
  have h_shr31 : (t >>> (31#i32 : Std.I32)) = .ok (⟨t.bv.sshiftRight 31⟩ : Std.I32) := by
    have h := shiftRight_IScalar_ok t (31#i32 : Std.I32) (by decide) (by decide)
    rw [h]; congr 1
  -- `i3 = BITS - 1` with `.val = 12`.
  obtain ⟨i3', h_i3eq, h_i3val⟩ :
      ∃ i3' : Std.Usize,
        (libcrux_iot_ml_dsa.constants.BITS_IN_LOWER_PART_OF_T - (1#usize : Std.Usize)
          : Result Std.Usize) = .ok i3' ∧ i3'.val = 12 := by
    rw [h_d]
    have hs := Aeneas.Std.Usize.sub_spec
      (x := (13#usize : Std.Usize)) (y := (1#usize : Std.Usize)) (by decide)
    obtain ⟨v', hveq, hPv'⟩ := Aeneas.Std.WP.spec_imp_exists hs
    refine ⟨v', hveq, ?_⟩
    rw [show (13#usize : Std.Usize).val = 13 from rfl,
        show (1#usize : Std.Usize).val = 1 from rfl] at hPv'
    omega
  -- `1#i32 <<< i3'`.
  have h_shl_i3 : ((1#i32 : Std.I32) <<< i3')
      = .ok (⟨(1#i32 : Std.I32).bv.shiftLeft 12⟩ : Std.I32) := by
    have := shiftLeft_UScalar_ok (1#i32 : Std.I32) i3' (by rw [h_i3val]; decide)
    rwa [h_i3val] at this
  -- `i5 >>> 13#usize`.
  have h_shr13 : ∀ x : Std.I32,
      (x >>> libcrux_iot_ml_dsa.constants.BITS_IN_LOWER_PART_OF_T)
        = .ok (⟨x.bv.sshiftRight 13⟩ : Std.I32) := by
    intro x; rw [h_d]
    have := shiftRight_UScalar_ok x (13#usize : Std.Usize) (by decide)
    rwa [show (13#usize : Std.Usize).val = 13 from rfl] at this
  -- `t11 <<< 13#usize`.
  have h_shl13 : ∀ x : Std.I32,
      (x <<< libcrux_iot_ml_dsa.constants.BITS_IN_LOWER_PART_OF_T)
        = .ok (⟨x.bv.shiftLeft 13⟩ : Std.I32) := by
    intro x; rw [h_d]
    have := shiftLeft_UScalar_ok x (13#usize : Std.Usize) (by decide)
    rwa [show (13#usize : Std.Usize).val = 13 from rfl] at this
  -- Chain the do-block.
  rw [h_shr31, h_q]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show (Aeneas.Std.lift (⟨t.bv.sshiftRight 31⟩ &&& (8380417#i32 : Std.I32)) : Result Std.I32)
        = .ok (⟨(⟨t.bv.sshiftRight 31⟩ : Std.I32).bv &&& (8380417#i32 : Std.I32).bv⟩) from rfl]
  simp only [Aeneas.Std.bind_tc_ok, CoreModels.core.num.I32.wrapping_sub,
             CoreModels.core.num.I32.wrapping_add,
             rust_primitives.arithmetic.wrapping_sub_i32,
             rust_primitives.arithmetic.wrapping_add_i32]
  rw [h_i3eq]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [h_shl_i3]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [h_shr13]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [h_shl13]
  simp only [Aeneas.Std.bind_tc_ok]

set_option maxHeartbeats 2000000 in
/-- The component `.val`s of `power2round_impl_value` under the `[-q, q)` precond:
    with `t1v` the canonical `[0, q)` rep, the HIGH output is `⌊(t1v-1+2^12)/2^13⌋`
    and the LOW output is `t1v - HIGH·2^13`. -/
private theorem power2round_impl_value_val (t : Std.I32)
    (hlo : -(8380417 : Int) ≤ t.val) (hhi : t.val < 8380417) :
    let t1v := t.val + (if t.val < 0 then 8380417 else 0)
    (power2round_impl_value t).2.val = (t1v - 1 + 4096) / 8192
    ∧ (power2round_impl_value t).1.val = t1v - ((t1v - 1 + 4096) / 8192) * 8192 := by
  intro t1v
  unfold power2round_impl_value
  have h_i1 :
      (⟨(⟨t.bv.sshiftRight 31⟩ : Std.I32).bv &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32).val
        = if t.val < 0 then 8380417 else 0 := power2round_sign_mask_val t
  have h_t1 :
      (Aeneas.Std.I32.wrapping_add t
        (⟨(⟨t.bv.sshiftRight 31⟩ : Std.I32).bv &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32)).val
        = t1v := by
    rw [wrapping_add_val_noov _ _ (by rw [h_i1]; split <;> omega)
                                  (by rw [h_i1]; split <;> omega), h_i1]
  set t1 : Std.I32 := Aeneas.Std.I32.wrapping_add t
    (⟨(⟨t.bv.sshiftRight 31⟩ : Std.I32).bv &&& (8380417#i32 : Std.I32).bv⟩ : Std.I32) with ht1def
  have h_t1_lo : 0 ≤ t1.val := by rw [h_t1]; simp only [t1v]; split <;> omega
  have h_t1_hi : t1.val < 8380417 := by rw [h_t1]; simp only [t1v]; split <;> omega
  have h_i2 : (Aeneas.Std.I32.wrapping_sub t1 (1#i32)).val = t1.val - 1 := by
    apply wrapping_sub_val_noov <;> rw [show (1#i32 : Std.I32).val = 1 from rfl] <;> omega
  set i2 : Std.I32 := Aeneas.Std.I32.wrapping_sub t1 (1#i32) with hi2def
  have h_i4 : (⟨(1#i32 : Std.I32).bv.shiftLeft 12⟩ : Std.I32).val = 4096 := by decide
  set i4 : Std.I32 := ⟨(1#i32 : Std.I32).bv.shiftLeft 12⟩ with hi4def
  have h_i5 : (Aeneas.Std.I32.wrapping_add i2 i4).val = t1.val - 1 + 4096 := by
    rw [wrapping_add_val_noov i2 i4 (by rw [h_i2, h_i4]; omega) (by rw [h_i2, h_i4]; omega),
        h_i2, h_i4]
  set i5 : Std.I32 := Aeneas.Std.I32.wrapping_add i2 i4 with hi5def
  have h_i5_lo : 0 ≤ i5.val := by rw [h_i5]; omega
  have h_t11 : (⟨i5.bv.sshiftRight 13⟩ : Std.I32).val = i5.val / 8192 := by
    rw [sshiftRight_val_i32]; norm_num
  set t11 : Std.I32 := ⟨i5.bv.sshiftRight 13⟩ with ht11def
  have h_t11_lo : 0 ≤ t11.val := by rw [h_t11]; exact Int.ediv_nonneg h_i5_lo (by norm_num)
  have h_t11_hi : t11.val ≤ 1023 := by
    rw [h_t11]
    have hle : i5.val ≤ 8384511 := by rw [h_i5]; omega
    have h2 := Int.ediv_le_ediv (a := i5.val) (b := 8384511) (c := 8192) (by norm_num) hle
    rw [show (8384511 : Int) / 8192 = 1023 from by norm_num] at h2; exact h2
  have h_i6 : (⟨t11.bv.shiftLeft 13⟩ : Std.I32).val = t11.val * 8192 := by
    rw [show (8192 : Int) = 2 ^ 13 from by norm_num]
    apply shiftLeft_shifted_val t11 13
    have h_na : (t11.val).natAbs ≤ 1023 := by omega
    calc (t11.val).natAbs * 2 ^ 13 ≤ 1023 * 2 ^ 13 := by
          apply Nat.mul_le_mul_right; exact h_na
      _ ≤ 2 ^ 31 - 2 ^ 23 := by norm_num
  set i6 : Std.I32 := ⟨t11.bv.shiftLeft 13⟩ with hi6def
  have h_t0 : (Aeneas.Std.I32.wrapping_sub t1 i6).val = t1.val - i6.val := by
    apply wrapping_sub_val_noov
    · rw [h_i6, h_t11]
      have : 0 ≤ i5.val / 8192 := Int.ediv_nonneg h_i5_lo (by norm_num); omega
    · rw [h_i6]; omega
  refine ⟨?_, ?_⟩
  · show t11.val = (t1v - 1 + 4096) / 8192
    rw [h_t11, h_i5, h_t1]
  · show (Aeneas.Std.I32.wrapping_sub t1 i6).val = t1v - ((t1v - 1 + 4096) / 8192) * 8192
    rw [h_t0, h_i6, h_t11, h_i5, h_t1]

/-- The integer Power2Round identity bridging the impl's `(r0, r1)` (LOW, HIGH)
    closed form to the swap of the clean spec `Spec.Rounding.power2round` (HIGH, LOW). -/
private theorem power2round_int_identity (t : Int)
    (hlo : -(8380417 : Int) ≤ t) (hhi : t < 8380417) :
    let t1v := t + (if t < 0 then 8380417 else 0)
    (t1v - ((t1v - 1 + 4096) / 8192) * 8192
        = (libcrux_iot_ml_dsa.Spec.Rounding.power2round t).2)
    ∧ ((t1v - 1 + 4096) / 8192 = (libcrux_iot_ml_dsa.Spec.Rounding.power2round t).1) := by
  intro t1v
  have hQ : (libcrux_iot_ml_dsa.Spec.Parameters.Q : Int) = 8380417 := rfl
  unfold libcrux_iot_ml_dsa.Spec.Rounding.power2round libcrux_iot_ml_dsa.Spec.Rounding.modPm
  simp only [libcrux_iot_ml_dsa.Spec.Rounding.twoD, libcrux_iot_ml_dsa.Spec.Rounding.Dbits,
             libcrux_iot_ml_dsa.Spec.Rounding.Qi, hQ,
             show ((2 : Int) ^ 13) = 8192 from by norm_num]
  rw [show (if t % 8380417 < 0 then t % 8380417 + 8380417 else t % 8380417) = t1v from by
        simp only [t1v]; omega]
  have h0 : 0 ≤ t1v := by simp only [t1v]; split <;> omega
  have hq : t1v < 8380417 := by simp only [t1v]; split <;> omega
  rw [show ((t1v % 8192) + 8192) % 8192 = t1v % 8192 from by omega]
  constructor <;> omega

set_option maxHeartbeats 2000000 in
/-- Per-element Power2Round Triple: under the `[-q, q)` precond, the LOW output
    matches `(Spec.Rounding.power2round t.val).2` and the HIGH output matches
    `(Spec.Rounding.power2round t.val).1` (note the impl/spec output-order swap). -/
theorem power2round_element_spec (t : Std.I32)
    (hlo : -(libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int) ≤ t.val)
    (hhi : t.val < (libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element t
    ⦃ ⇓ p => ⌜ p.1.val = (libcrux_iot_ml_dsa.Spec.Rounding.power2round t.val).2
             ∧ p.2.val = (libcrux_iot_ml_dsa.Spec.Rounding.power2round t.val).1 ⌝ ⦄ := by
  have h_Qi : (libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int) = 8380417 := rfl
  rw [h_Qi] at hlo hhi
  apply triple_of_ok_l0 (v := power2round_impl_value t) (power2round_element_eq_ok t)
  obtain ⟨h_high, h_low⟩ := power2round_impl_value_val t hlo hhi
  obtain ⟨h_id_low, h_id_high⟩ := power2round_int_identity t.val hlo hhi
  refine ⟨?_, ?_⟩
  · rw [h_low, h_id_low]
  · rw [h_high, h_id_high]

/-! ## `power2round_spec` — top-level dual-output rounding keystone

    `simd.portable.arithmetic.power2round t0 t1` is an 8-iter dual-output loop
    applying `power2round_element` to each lane of `t0`, writing the LOW outputs
    into a fresh LOW poly and the HIGH outputs into the (write-only scratch) `t1`.
    Returns `({values := lows}, highs)` (LOW poly, HIGH poly). Mirrors
    `shift_left_then_reduce_spec` structurally, via `elementwise_dual_output_spec`.
    The `t1` argument's input values are irrelevant (all lanes overwritten). -/

/-- Per-element predicate for the `power2round` loop (guarded by the `[-q, q)`
    per-lane bound; matches `power2round_element_spec`). -/
private def power2round_per_elem_P (x : Std.I32) (p : Std.I32 × Std.I32) : Prop :=
  -(libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int) ≤ x.val →
    x.val < (libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int) →
    p.1.val = (libcrux_iot_ml_dsa.Spec.Rounding.power2round x.val).2
    ∧ p.2.val = (libcrux_iot_ml_dsa.Spec.Rounding.power2round x.val).1

/-- Per-element Triple (always-true pre, guarded post) feeding the loop wrapper. -/
private theorem power2round_per_elem_spec (x : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element x
    ⦃ ⇓ p => ⌜ power2round_per_elem_P x p ⌝ ⦄ := by
  apply triple_of_ok_l0 (v := power2round_impl_value x) (power2round_element_eq_ok x)
  intro hlo hhi
  obtain ⟨v, hv_eq, hv_P⟩ := triple_exists_ok_l0 (power2round_element_spec x hlo hhi)
  rw [power2round_element_eq_ok x] at hv_eq
  rw [Result.ok.inj hv_eq]; exact hv_P

set_option maxHeartbeats 2000000 in
@[spec]
theorem power2round_spec
    (t0 t1 : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hbound : ∀ j : Nat, j < 8 →
        -(libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int) ≤ (t0.values.val[j]!).val
          ∧ (t0.values.val[j]!).val < (libcrux_iot_ml_dsa.Spec.Rounding.Qi : Int)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round t0 t1
    ⦃ ⇓ p => ⌜ ∀ j : Nat, j < 8 →
        (p.1.values.val[j]!).val
          = (libcrux_iot_ml_dsa.Spec.Rounding.power2round (t0.values.val[j]!).val).2
      ∧ (p.2.values.val[j]!).val
          = (libcrux_iot_ml_dsa.Spec.Rounding.power2round (t0.values.val[j]!).val).1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice t0.values)
        = .ok (Aeneas.Std.Array.to_slice t0.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice t0.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice t0.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq t0.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_loop
  -- Bridge `power2round_loop.body` to `dual_output_loop_body power2round_element`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
              × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) =>
         libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_loop.body p.1 p.2.1 p.2.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray
              × libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) =>
         dual_output_loop_body
           libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element p.1 p.2.1 p.2.2) := by
    funext p
    obtain ⟨iter1, a1, b1⟩ := p
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_loop.body
    unfold dual_output_loop_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok_l0
      (elementwise_dual_output_spec
        libcrux_iot_ml_dsa.simd.portable.arithmetic.power2round_element
        power2round_per_elem_P power2round_per_elem_spec t0.values t1)
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

/-! ## `infinity_norm_exceeds` (per-unit) — the signing rejection check.

  The security-critical per-lane check. The Rust per-unit fn computes, for each of
  the 8 coefficients `c`:

      sign       = c >> 31                         -- -1 if c < 0, else 0
      normalized = c - (sign & (2·c))              -- = |c|  (the bug-fixed site)
      result     = result || (normalized >= bound) -- short-circuiting OR

  `normalized = |c|`: when `c ≥ 0`, `sign = 0` so the `& (2·c)` is masked to `0`
  (even if `2·c` overflows!), giving `c`; when `c < 0`, `sign = allOnes` so the mask
  is `2·c` (exact under `c ≥ -2^30`), giving `c - 2·c = -c`. Hence the per-lane
  no-overflow precond is `|c| ≤ 2^30` (only the negative side `c ≥ -2^30` binds;
  the positive overflow at `c = 2^30` is harmless because `sign = 0`).

  This is the impl-bug-#2 site: the per-unit FC was never proven. The post is
  EQUALITY-form: `r = decide (∃ j < 8, bound.val ≤ |c_j|)`. -/

/-- The pure value computed by the per-unit body for one coefficient `c`
    (`normalized` in the Rust). -/
def unit_norm_impl (c : Std.I32) : Std.I32 :=
  let sign : Std.I32 := ⟨c.bv.sshiftRight 31⟩
  let i2 : Std.I32 := Aeneas.Std.I32.wrapping_mul (2#i32) c
  let i3 : Std.I32 := ⟨sign.bv &&& i2.bv⟩
  Aeneas.Std.I32.wrapping_sub c i3

/-- **The bug-fixed identity:** `normalized = |c|` under `|c| ≤ 2^30`. -/
theorem unit_norm_impl_val_abs (c : Std.I32) (hpre : c.val.natAbs ≤ 2^30) :
    (unit_norm_impl c).val = |c.val| := by
  have h_abs30 : |c.val| ≤ (2^30 : Int) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hpre
  have h_lb30 : (-2^30 : Int) ≤ c.val := (abs_le.mp h_abs30).1
  have h_ub30 : c.val ≤ (2^30 : Int) := (abs_le.mp h_abs30).2
  have h_bd := Aeneas.Std.IScalar.hBounds c
  have h_lb : -(2 ^ 31 : Int) ≤ c.val := by
    have := h_bd.1
    simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_ub : c.val < (2 ^ 31 : Int) := by
    have := h_bd.2
    simp only [show Aeneas.Std.IScalarTy.I32.numBits - 1 = 31 from rfl] at this; exact this
  have h_shrtoInt : (c.bv.sshiftRight 31).toInt = c.val / (2 ^ 31 : Int) := by
    rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]; norm_cast
  -- `(sign & 2c).val = if c < 0 then 2c else 0`.
  have h_mask :
      (⟨(c.bv.sshiftRight 31) &&& (Aeneas.Std.I32.wrapping_mul (2#i32) c).bv⟩ : Std.I32).val
        = if c.val < 0 then 2 * c.val else 0 := by
    by_cases hneg : c.val < 0
    · rw [if_pos hneg]
      have h_div : c.val / (2 ^ 31 : Int) = -1 := by omega
      have h_allones : c.bv.sshiftRight 31 = BitVec.allOnes 32 := by
        apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
      show ((c.bv.sshiftRight 31) &&& (Aeneas.Std.I32.wrapping_mul (2#i32) c).bv).toInt = _
      rw [h_allones, BitVec.allOnes_and]
      show (Aeneas.Std.I32.wrapping_mul (2#i32) c).val = 2 * c.val
      rw [Aeneas.Std.I32.wrapping_mul_val_eq]
      show Int.bmod ((2#i32 : Std.I32).val * c.val) (2^32) = _
      rw [show (2#i32 : Std.I32).val = 2 from rfl]
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
      · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega
      · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega
    · rw [if_neg hneg]
      have h_div : c.val / (2 ^ 31 : Int) = 0 := by omega
      have h_zero : c.bv.sshiftRight 31 = 0#32 := by
        apply BitVec.eq_of_toInt_eq; rw [h_shrtoInt, h_div]; decide
      show ((c.bv.sshiftRight 31) &&& (Aeneas.Std.I32.wrapping_mul (2#i32) c).bv).toInt = _
      rw [h_zero, BitVec.zero_and]; decide
  unfold unit_norm_impl
  show (Aeneas.Std.I32.wrapping_sub c
        (⟨(⟨c.bv.sshiftRight 31⟩ : Std.I32).bv
          &&& (Aeneas.Std.I32.wrapping_mul (2#i32) c).bv⟩ : Std.I32)).val = _
  rw [Aeneas.Std.I32.wrapping_sub_val_eq,
      show (⟨(⟨c.bv.sshiftRight 31⟩ : Std.I32).bv
              &&& (Aeneas.Std.I32.wrapping_mul (2#i32) c).bv⟩ : Std.I32).val
            = if c.val < 0 then 2 * c.val else 0 from h_mask]
  by_cases hneg : c.val < 0
  · rw [if_pos hneg, abs_of_neg hneg, show c.val - 2 * c.val = -c.val from by ring]
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega
    · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega
  · rw [if_neg hneg, abs_of_nonneg (by omega), show c.val - 0 = c.val from by ring]
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega
    · rw [show ((2:Int)^(32-1)) = 2^31 from by norm_num]; omega

/-! ### Per-unit Bool-accumulator loop. -/

/-- Pure-prop holds helpers for the Bool-accumulator invariant. -/
private theorem pure_prop_holds_inf {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_inf {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-- The whole per-coefficient chunk (computation + short-circuiting `if`) reduces to
    `.ok (cont (iter1, if result then true else unit_norm_impl c >= bound))`. -/
theorem inf_chunk_if_eq (c bound : Std.I32) (result : Bool)
    (iter1 : CoreModels.core.ops.range.Range Std.Usize) :
    (do
      let sign ← c >>> 31#i32
      let i1 ← libcrux_secrets.traits.Classify.Blanket.classify 2#i32
      let i2 ← CoreModels.core.num.I32.wrapping_mul i1 c
      let i3 ← Aeneas.Std.lift (sign &&& i2)
      let normalized ← CoreModels.core.num.I32.wrapping_sub c i3
      if result
      then ok (ControlFlow.cont (iter1, true))
      else
        let i4 ← libcrux_secrets.traits.Declassify.Blanket.declassify normalized
        ok (ControlFlow.cont (iter1, i4 >= bound)) :
      Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool))
    = .ok (ControlFlow.cont (iter1, if result then true else (unit_norm_impl c >= bound))) := by
  unfold unit_norm_impl
  have h_shr31 : (c >>> (31#i32 : Std.I32)) = .ok (⟨c.bv.sshiftRight 31⟩ : Std.I32) := by
    have h := shiftRight_IScalar_ok c (31#i32 : Std.I32) (by decide) (by decide)
    rw [h]; congr 1
  rw [h_shr31]
  simp only [libcrux_secrets.traits.Classify.Blanket.classify,
             libcrux_secrets.traits.Declassify.Blanket.declassify,
             CoreModels.core.num.I32.wrapping_mul, CoreModels.core.num.I32.wrapping_sub,
             rust_primitives.arithmetic.wrapping_mul_i32,
             rust_primitives.arithmetic.wrapping_sub_i32,
             Aeneas.Std.bind_tc_ok, Aeneas.Std.lift]
  cases result <;> rfl

/-- The per-unit loop body (the `infinity_norm_exceeds_loop.body` shape on the raw
    8-element coefficient array `a`). -/
def inf_body (a : CoeffArray) (bound : Std.I32)
    (iter : CoreModels.core.ops.range.Range Std.Usize) (result : Bool) :
    Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool) := do
  let (o, iter1) ←
    CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
      CoreModels.core.Usize.Insts.CoreIterRangeStep iter
  match o with
  | CoreModels.core.option.Option.None => ok (ControlFlow.done result)
  | CoreModels.core.option.Option.Some i =>
    let coefficient ← Aeneas.Std.Array.index_usize a i
    let sign ← coefficient >>> 31#i32
    let i1 ← libcrux_secrets.traits.Classify.Blanket.classify 2#i32
    let i2 ← CoreModels.core.num.I32.wrapping_mul i1 coefficient
    let i3 ← Aeneas.Std.lift (sign &&& i2)
    let normalized ← CoreModels.core.num.I32.wrapping_sub coefficient i3
    if result
    then ok (ControlFlow.cont (iter1, true))
    else
      let i4 ← libcrux_secrets.traits.Declassify.Blanket.declassify normalized
      ok (ControlFlow.cont (iter1, i4 >= bound))

/-- The per-unit loop invariant: `result = decide(∃ j < k, bound ≤ |a[j]|)`. -/
def inf_inv (a : CoeffArray) (bound : Std.I32) :
    Std.Usize → Bool → Result Prop :=
  fun k result => pure
    (result = decide (∃ j : Nat, j < k.val ∧ (bound.val : Int) ≤ |(a.val[j]!).val|))

/-- Per-iteration step post for the per-unit loop. -/
def inf_step_post (a : CoeffArray) (bound : Std.I32) (k : Std.Usize)
    (r : ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool) : Prop :=
  match r with
  | .cont (iter', result') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inf_inv a bound iter'.start result').holds
  | .done y => (inf_inv a bound 8#usize y).holds

/-- Invariant extension at the `Some` step: `decide(∃ j < k+1, P j)` from
    `decide(∃ j < k, P j)` and the freshly-tested `P k = (bound ≤ |a[k]|)`. -/
private theorem inf_extend (a : CoeffArray) (bound : Std.I32)
    (k : Nat) (hk : k < 8) (result : Bool)
    (hpre_k : (a.val[k]!).val.natAbs ≤ 2^30)
    (h_res : result = decide (∃ j : Nat, j < k ∧ (bound.val : Int) ≤ |(a.val[j]!).val|)) :
    (if result then true else (unit_norm_impl (a.val[k]!) >= bound))
      = decide (∃ j : Nat, j < k + 1 ∧ (bound.val : Int) ≤ |(a.val[j]!).val|) := by
  -- the per-lane Bool test equals `decide (bound.val ≤ |a[k]|)`.
  have h_norm : (unit_norm_impl (a.val[k]!)).val = |(a.val[k]!).val| :=
    unit_norm_impl_val_abs (a.val[k]!) hpre_k
  have h_test : ((unit_norm_impl (a.val[k]!) >= bound) : Bool)
      = decide ((bound.val : Int) ≤ |(a.val[k]!).val|) := by
    show decide (bound ≤ unit_norm_impl (a.val[k]!)) = _
    rw [decide_eq_decide]
    show ((bound.val : Int) ≤ (unit_norm_impl (a.val[k]!)).val) ↔ _
    rw [h_norm]
  rw [h_test, h_res]
  -- `(if decide P then true else decide Q) = decide (P ∨ Q)`, then prove the iff.
  rw [show ∀ (P Q : Prop) [Decidable P] [Decidable Q],
        (if decide P then true else decide Q) = decide (P ∨ Q) from by
        intro P Q _ _; by_cases h : P <;> simp [h]]
  rw [decide_eq_decide]
  constructor
  · rintro (⟨j, hj, hjb⟩ | hk')
    · exact ⟨j, by omega, hjb⟩
    · exact ⟨k, by omega, hk'⟩
  · rintro ⟨j, hj, hjb⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · exact Or.inl ⟨j, h, hjb⟩
    · subst h; exact Or.inr hjb

set_option maxHeartbeats 4000000 in
/-- Per-iteration step lemma for the per-unit OR-loop. -/
theorem inf_step_lemma
    (a : CoeffArray) (bound : Std.I32)
    (hpre : ∀ j : Nat, j < 8 → (a.val[j]!).val.natAbs ≤ 2^30)
    (result : Bool) (k : Std.Usize)
    (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (inf_inv a bound k result).holds) :
    ⦃ ⌜ True ⌝ ⦄
    inf_body a bound { start := k, «end» := 8#usize } result
    ⦃ ⇓ r => ⌜ inf_step_post a bound k r ⌝ ⦄ := by
  have h_8 : (8#usize : Std.Usize).val = 8 := rfl
  have h_a_len : a.length = 8 := CoeffArray_length a
  have h_res : result = decide (∃ j : Nat, j < k.val ∧ (bound.val : Int) ≤ |(a.val[j]!).val|) :=
    of_pure_prop_holds_inf h_inv
  unfold inf_body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- `Some k` branch.
    have hk_8 : k.val < 8 := by rw [h_8] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k 8#usize h_lt
    set c : Std.I32 := a.val[k.val]! with hc_def
    have h_idx : Aeneas.Std.Array.index_usize a k = .ok c :=
      array_index_usize_ok_eq a k (by rw [h_a_len]; exact hk_8)
    set new_res : Bool :=
      if result then true else (unit_norm_impl c >= bound) with hnr_def
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done result) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool))
          | CoreModels.core.option.Option.Some i =>
            let coefficient ← Aeneas.Std.Array.index_usize a i
            let sign ← coefficient >>> 31#i32
            let i1 ← libcrux_secrets.traits.Classify.Blanket.classify 2#i32
            let i2 ← CoreModels.core.num.I32.wrapping_mul i1 coefficient
            let i3 ← Aeneas.Std.lift (sign &&& i2)
            let normalized ← CoreModels.core.num.I32.wrapping_sub coefficient i3
            if result
            then ok (ControlFlow.cont (iter1, true))
            else
              let i4 ← libcrux_secrets.traits.Declassify.Blanket.declassify normalized
              ok (ControlFlow.cont (iter1, i4 >= bound)))
        = .ok (ControlFlow.cont
            (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_res)) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [inf_chunk_if_eq c bound result
            ({ start := s, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)]
    apply triple_of_ok_l0 h_body
    show inf_step_post a bound k
      (.cont (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize), new_res))
    unfold inf_step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (inf_inv a bound s new_res).holds
    apply pure_prop_holds_inf
    show new_res = decide (∃ j : Nat, j < s.val ∧ (bound.val : Int) ≤ |(a.val[j]!).val|)
    rw [hs_val, hnr_def, hc_def]
    exact inf_extend a bound k.val hk_8 result (hpre k.val hk_8) h_res
  · -- `None` branch.
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h_8] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k 8#usize hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | CoreModels.core.option.Option.None =>
              (Result.ok (ControlFlow.done result) :
                Result (ControlFlow ((CoreModels.core.ops.range.Range Std.Usize) × Bool) Bool))
          | CoreModels.core.option.Option.Some i =>
            let coefficient ← Aeneas.Std.Array.index_usize a i
            let sign ← coefficient >>> 31#i32
            let i1 ← libcrux_secrets.traits.Classify.Blanket.classify 2#i32
            let i2 ← CoreModels.core.num.I32.wrapping_mul i1 coefficient
            let i3 ← Aeneas.Std.lift (sign &&& i2)
            let normalized ← CoreModels.core.num.I32.wrapping_sub coefficient i3
            if result
            then ok (ControlFlow.cont (iter1, true))
            else
              let i4 ← libcrux_secrets.traits.Declassify.Blanket.declassify normalized
              ok (ControlFlow.cont (iter1, i4 >= bound)))
        = .ok (ControlFlow.done result) := by
      conv_lhs =>
        rw [show
          (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              CoreModels.core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                CoreModels.core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_l0 h_body
    show inf_step_post a bound k (.done result)
    unfold inf_step_post
    show (inf_inv a bound 8#usize result).holds
    apply pure_prop_holds_inf
    show result = decide (∃ j : Nat, j < 8 ∧ (bound.val : Int) ≤ |(a.val[j]!).val|)
    rw [h_res, hk_eq]

/-! ### Per-unit FC. -/

set_option maxHeartbeats 2000000 in
/-- **`infinity_norm_exceeds` per-unit FC** (the impl-bug-#2 site). Returns `true`
    iff some of the 8 coefficients has `bound ≤ |coefficient|`. EQUALITY-form post.
    Per-lane no-overflow precond: `|values[j]| ≤ 2^30`. -/
theorem infinity_norm_exceeds_unit_spec
    (simd_unit : simd.portable.vector_type.Coefficients) (bound : Std.I32)
    (hpre : ∀ j : Nat, j < 8 → (simd_unit.values.val[j]!).val.natAbs ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.infinity_norm_exceeds simd_unit bound
    ⦃ ⇓ r => ⌜ r = decide (∃ j : Nat, j < 8
                  ∧ (bound.val : Int) ≤ |(simd_unit.values.val[j]!).val|) ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.infinity_norm_exceeds
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Array.to_slice simd_unit.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq simd_unit.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.infinity_norm_exceeds_loop
  -- Bridge the extracted body to `inf_body`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × Bool) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.infinity_norm_exceeds_loop.body
          simd_unit.values bound p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × Bool) =>
        inf_body simd_unit.values bound p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, result1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.infinity_norm_exceeds_loop.body inf_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_holds⟩ :=
    triple_exists_ok_l0
      (Util.LoopSpecs.loop_range_spec_usize
        (fun p => inf_body simd_unit.values bound p.1 p.2)
        false 0#usize 8#usize
        (inf_inv simd_unit.values bound)
        (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
        (by
          apply pure_prop_holds_inf
          show (false : Bool)
            = decide (∃ j : Nat, j < 0
                ∧ (bound.val : Int) ≤ |(simd_unit.values.val[j]!).val|)
          symm; rw [decide_eq_false_iff_not]; rintro ⟨j, hj, _⟩; exact absurd hj (Nat.not_lt_zero j))
        (by
          intro acc k _h_ge h_le hinv
          have h_step := inf_step_lemma simd_unit.values bound hpre acc k h_le hinv
          apply Std.Do.Triple.of_entails_right _ h_step
          rw [PostCond.entails_noThrow]
          intro r hh
          rcases r with ⟨iter', acc'⟩ | y
          · have hP : inf_step_post simd_unit.values bound k (.cont (iter', acc')) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [inf_step_post] using hP
          · have hP : inf_step_post simd_unit.values bound k (.done y) := by
              simpa [Std.Do.SPred.down_pure] using hh
            simpa [inf_step_post] using hP))
  rw [h_out_eq]
  apply triple_of_ok_l0 (v := out) rfl
  have h_final : out = decide (∃ j : Nat, j < 8
      ∧ (bound.val : Int) ≤ |(simd_unit.values.val[j]!).val|) :=
    of_pure_prop_holds_inf h_out_holds
  rw [h_final]

end libcrux_iot_ml_dsa.Vector.Portable.Arithmetic
