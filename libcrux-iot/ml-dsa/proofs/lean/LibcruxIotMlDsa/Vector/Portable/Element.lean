/-
  # `Vector/Portable/Element.lean` — Layer-1 elementwise `Coefficients` ops (ML-DSA)

  ML-DSA analogue of ml-kem's
  `LibcruxIotMlKem/Vector/Portable/Arithmetic/Element.lean` (`add_spec`/`sub_spec`).

  - **`add_spec`** — `simd.portable.arithmetic.add` folds
    `core.num.I32.wrapping_add` over the 8 `Std.I32` lanes of the
    `Coefficients.values` array. Under the per-lane no-overflow bound
    `|lhs[j] + rhs[j]| ≤ 2^31 - 1`, the wrap is the identity and the output
    equals the exact integer sum.
  - **`subtract_spec`** — same, with `wrapping_sub` / `-`.

  Both instantiate `Util.LoopHelper.elementwise_binary_spec` with a per-element
  Triple, then post-process to the equality-form post on `Coefficients`.
-/
import LibcruxIotMlDsa.Util.LoopHelper
import LibcruxIotMlDsa.Util.SliceSpecs
import LibcruxIotMlDsa.Vector.Portable.Arithmetic

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_dsa.Vector.Portable.Element
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_dsa.Util.LoopHelper libcrux_iot_ml_dsa.Util.LoopSpecs
  libcrux_iot_ml_dsa.Util.SliceSpecs
open libcrux_iot_ml_dsa.Spec.Lift libcrux_iot_ml_dsa.Spec.Montgomery
  libcrux_iot_ml_dsa.Spec.Parameters

/-! ## Local Triple ↔ Result.ok bridges. -/

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

/-- `Slice.len (Array.to_slice (a : CoeffArray)) = 8#usize`. -/
private theorem coeff_slice_len_eq (a : CoeffArray) :
    Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice a) = (8#usize : Std.Usize) := by
  apply Std.UScalar.eq_of_val_eq
  rw [Aeneas.Std.Slice.len_val]
  show (Aeneas.Std.Array.to_slice a).length = (8#usize : Std.Usize).val
  rw [Aeneas.Std.Array.length_to_slice a]

/-! ## `add_spec`

    `simd.portable.arithmetic.add lhs rhs` is an 8-iter loop calling
    `core.num.I32.wrapping_add lhs.values[i] rhs.values[i]` and writing the
    result back. Under the per-element no-overflow bound
    `|lhs.val + rhs.val| ≤ 2^31 - 1`, `Int.bmod _ (2^32)` is the identity. -/

/-- Per-element predicate (guarded form): given the no-overflow bound on
    `x + y`, the output value equals the sum and is in range. -/
private def add_per_elem_P (x y r : Std.I32) : Prop :=
  ((x.val + y.val : Int)).natAbs ≤ 2 ^ 31 - 1 →
    r.val = x.val + y.val ∧ r.val.natAbs ≤ 2 ^ 31 - 1

/-- Per-element Triple: `core.num.I32.wrapping_add x y` reduces to
    `.ok (Std.I32.wrapping_add x y)`, whose `.val` is `Int.bmod (x.val + y.val) (2^32)`.
    Under the no-overflow bound, `Int.bmod` is the identity. -/
private theorem add_per_elem_spec (x y : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I32.wrapping_add x y
    ⦃ ⇓ r => ⌜ add_per_elem_P x y r ⌝ ⦄ := by
  have h_ok :
      CoreModels.core.num.I32.wrapping_add x y
        = .ok (Aeneas.Std.I32.wrapping_add x y) := by
    unfold CoreModels.core.num.I32.wrapping_add
    unfold rust_primitives.arithmetic.wrapping_add_i32
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show add_per_elem_P x y (Aeneas.Std.I32.wrapping_add x y)
  unfold add_per_elem_P
  intro hb
  have h_val := Aeneas.Std.I32.wrapping_add_val_eq x y
  have h_lb : -(2 ^ 31 : Int) ≤ x.val + y.val := by
    have h_abs : ((x.val + y.val : Int)).natAbs ≤ 2 ^ 31 - 1 := hb
    omega
  have h_ub : x.val + y.val < (2 ^ 31 : Int) := by
    have h_abs : ((x.val + y.val : Int)).natAbs ≤ 2 ^ 31 - 1 := hb
    omega
  have h_bmod : Int.bmod (x.val + y.val) (2 ^ 32) = x.val + y.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_const : -((2 : Int) ^ (32 - 1)) ≤ -(2 ^ 31 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 31 : Int) ≤ (2 : Int) ^ (32 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact hb

@[spec]
theorem add_spec
    (lhs rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hpre : ∀ j : Nat, j < 8 →
      ((lhs.values.val[j]!).val + (rhs.values.val[j]!).val : Int).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                (r.values.val[j]!).val
                  = (lhs.values.val[j]!).val + (rhs.values.val[j]!).val
              ∧ (r.values.val[j]!).val.natAbs ≤ 2 ^ 31 - 1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.add
  -- `lift (Array.to_slice lhs.values) = .ok (Array.to_slice lhs.values)`.
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Array.to_slice lhs.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- `core.slice.Slice.len s = .ok (Slice.len s)`.
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice lhs.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  -- The derived bound `Slice.len (to_slice lhs.values)` is `8#usize`.
  rw [coeff_slice_len_eq lhs.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.add_loop
  -- Bridge `add_loop.body rhs` to `binary_loop_body wrapping_add rhs`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.add_loop.body rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        binary_loop_body CoreModels.core.num.I32.wrapping_add rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.add_loop.body
    unfold binary_loop_body
    rfl
  rw [h_body_eq]
  -- Extract the loop output `out` and its per-index post; the whole `do`
  -- reduces to `.ok { values := out }`.
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok
      (elementwise_binary_spec
        CoreModels.core.num.I32.wrapping_add
        add_per_elem_P
        add_per_elem_spec
        lhs.values rhs)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## `subtract_spec`

    `simd.portable.arithmetic.subtract lhs rhs` is an 8-iter loop calling
    `core.num.I32.wrapping_sub lhs.values[i] rhs.values[i]`. Same structure
    as `add_spec` but with `-`. -/

/-- Per-element predicate (guarded form): given the no-overflow bound on
    `x - y`, the output value equals the difference and is in range. -/
private def sub_per_elem_P (x y r : Std.I32) : Prop :=
  ((x.val - y.val : Int)).natAbs ≤ 2 ^ 31 - 1 →
    r.val = x.val - y.val ∧ r.val.natAbs ≤ 2 ^ 31 - 1

/-- Per-element Triple: `core.num.I32.wrapping_sub x y` reduces to
    `.ok (Std.I32.wrapping_sub x y)`, whose `.val` is `Int.bmod (x.val - y.val) (2^32)`.
    Under the no-overflow bound, `Int.bmod` is the identity. -/
private theorem sub_per_elem_spec (x y : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I32.wrapping_sub x y
    ⦃ ⇓ r => ⌜ sub_per_elem_P x y r ⌝ ⦄ := by
  have h_ok :
      CoreModels.core.num.I32.wrapping_sub x y
        = .ok (Aeneas.Std.I32.wrapping_sub x y) := by
    unfold CoreModels.core.num.I32.wrapping_sub
    unfold rust_primitives.arithmetic.wrapping_sub_i32
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show sub_per_elem_P x y (Aeneas.Std.I32.wrapping_sub x y)
  unfold sub_per_elem_P
  intro hb
  have h_val := Aeneas.Std.I32.wrapping_sub_val_eq x y
  have h_lb : -(2 ^ 31 : Int) ≤ x.val - y.val := by
    have h_abs : ((x.val - y.val : Int)).natAbs ≤ 2 ^ 31 - 1 := hb
    omega
  have h_ub : x.val - y.val < (2 ^ 31 : Int) := by
    have h_abs : ((x.val - y.val : Int)).natAbs ≤ 2 ^ 31 - 1 := hb
    omega
  have h_bmod : Int.bmod (x.val - y.val) (2 ^ 32) = x.val - y.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 32 _ (by decide)
    · have h_const : -((2 : Int) ^ (32 - 1)) ≤ -(2 ^ 31 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 31 : Int) ≤ (2 : Int) ^ (32 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact hb

@[spec]
theorem subtract_spec
    (lhs rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hpre : ∀ j : Nat, j < 8 →
      ((lhs.values.val[j]!).val - (rhs.values.val[j]!).val : Int).natAbs ≤ 2 ^ 31 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.subtract lhs rhs
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                (r.values.val[j]!).val
                  = (lhs.values.val[j]!).val - (rhs.values.val[j]!).val
              ∧ (r.values.val[j]!).val.natAbs ≤ 2 ^ 31 - 1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.subtract
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Array.to_slice lhs.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice lhs.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq lhs.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.subtract_loop
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.subtract_loop.body rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        binary_loop_body CoreModels.core.num.I32.wrapping_sub rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.subtract_loop.body
    unfold binary_loop_body
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok
      (elementwise_binary_spec
        CoreModels.core.num.I32.wrapping_sub
        sub_per_elem_P
        sub_per_elem_spec
        lhs.values rhs)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## `montgomery_multiply_spec`

    `simd.portable.arithmetic.montgomery_multiply lhs rhs` is an 8-iter loop
    calling `montgomery_multiply_fe_by_fer lhs.values[i] rhs.values[i]` and
    writing back. Under the per-lane bound `|rhs[j]| ≤ q-1 = 8380416`, each lane
    lifts to `(lhs[j]) · (rhs[j]) · R⁻¹` in `Z_q` and stays `≤ 2^24` in size. -/

/-- Per-element predicate (guarded form): given the bound on `fer` (the `rhs`
    lane), the output lifts to `(fe)·(fer)·R⁻¹` and is `≤ 2^24` in size. -/
private def mmul_per_elem_P (fe fer r : Std.I32) : Prop :=
  fer.val.natAbs ≤ 8380416 →
    liftZ_std r.val = (fe.val : Zq) * (fer.val : Zq) * (RINV : Zq)
      ∧ r.val.natAbs ≤ 2 ^ 24

/-- Per-element Triple: under the `fer` bound, strengthen the leaf
    `montgomery_multiply_fe_by_fer_spec` post to the guarded `P`; when the bound
    fails the post is vacuous, but the op is still total (`mmfbf_eq_ok`). -/
private theorem mmul_per_elem_spec (fe fer : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer fe fer
    ⦃ ⇓ r => ⌜ mmul_per_elem_P fe fer r ⌝ ⦄ := by
  by_cases hfer : fer.val.natAbs ≤ 8380416
  · -- Guard TRUE: extract the leaf spec's `.ok` witness + post, re-close with `P`.
    obtain ⟨r0, h_eq_ok, h_lift, h_bound⟩ :=
      triple_exists_ok
        (libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec
          fe fer hfer)
    refine triple_of_ok (v := r0) h_eq_ok ?_
    intro _
    exact ⟨h_lift, h_bound⟩
  · -- Guard FALSE: post antecedent (`fer ≤ q-1`) is false, so `P` holds
    -- vacuously. The op is total regardless of the bound: `mmfbf_eq_ok` reduces
    -- it to `montgomery_reduce_element`, and `mont_reduce_element_eq_ok` shows
    -- that is unconditionally `.ok` (no `2^55` precondition needed).
    refine triple_of_ok
      (v := libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.mont_reduce_impl_value
        (Aeneas.Std.I64.wrapping_mul
          (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fe)
          (Aeneas.Std.IScalar.cast Aeneas.Std.IScalarTy.I64 fer)))
      (by
        rw [libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.mmfbf_eq_ok,
            libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.mont_reduce_element_eq_ok]) ?_
    intro hbad
    exact absurd hbad hfer

@[spec]
theorem montgomery_multiply_spec
    (lhs rhs : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (hpre : ∀ j : Nat, j < 8 → (rhs.values.val[j]!).val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply lhs rhs
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                liftZ_std (r.values.val[j]!).val
                  = ((lhs.values.val[j]!).val : Zq) * ((rhs.values.val[j]!).val : Zq) * (RINV : Zq)
              ∧ (r.values.val[j]!).val.natAbs ≤ 2 ^ 24 ⌝ ⦄ := by
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Array.to_slice lhs.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice lhs.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice lhs.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq lhs.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_loop
  -- Bridge `montgomery_multiply_loop.body rhs` to
  -- `binary_loop_body montgomery_multiply_fe_by_fer rhs`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_loop.body rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        binary_loop_body
          libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_loop.body
    unfold binary_loop_body
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok
      (elementwise_binary_spec
        libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer
        mmul_per_elem_P
        mmul_per_elem_spec
        lhs.values rhs)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show liftZ_std (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## `montgomery_multiply_by_constant_spec`

    `simd.portable.arithmetic.montgomery_multiply_by_constant simd_unit c` is an
    8-iter loop calling `montgomery_multiply_fe_by_fer simd_unit.values[i] c` and
    writing back. UNLIKE `montgomery_multiply`, the second operand is a single
    free constant `c` carried by the loop; the top-level bound `hc` applies to it
    once, so no per-lane guard is needed. Each lane lifts to `(x)·(c)·R⁻¹` in
    `Z_q` and stays `≤ 2^24` in size. -/

/-- Per-element predicate (unguarded): the output lifts to `(x)·(c)·R⁻¹` and is
    `≤ 2^24` in size. The `c` bound `hc` is closed over by the leaf spec. -/
private def mmul_by_const_per_elem_P (c x r : Std.I32) : Prop :=
  liftZ_std r.val = (x.val : Zq) * (c.val : Zq) * (RINV : Zq)
    ∧ r.val.natAbs ≤ 2 ^ 24

@[spec]
theorem montgomery_multiply_by_constant_spec
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) (c : Std.I32)
    (hc : c.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant simd_unit c
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                liftZ_std (r.values.val[j]!).val
                  = ((simd_unit.values.val[j]!).val : Zq) * (c.val : Zq) * (RINV : Zq)
              ∧ (r.values.val[j]!).val.natAbs ≤ 2 ^ 24 ⌝ ⦄ := by
  -- Per-element spec: the leaf `montgomery_multiply_fe_by_fer_spec x c hc` IS the
  -- per-element post verbatim (`P := mmul_by_const_per_elem_P c`); `hc` is closed
  -- over, so no guard or entailment massaging is needed.
  have per_elem_spec : ∀ x : Std.I32,
      ⦃ ⌜ True ⌝ ⦄
      libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c
      ⦃ ⇓ r => ⌜ mmul_by_const_per_elem_P c x r ⌝ ⦄ :=
    fun x =>
      libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec x c hc
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Array.to_slice simd_unit.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq simd_unit.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop
  -- Bridge `montgomery_multiply_by_constant_loop.body c` to
  -- `unary_loop_body (fun x => montgomery_multiply_fe_by_fer x c)`. Single index,
  -- free `c` — plain `rfl` after unfolding both bodies and `mmfbf`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop.body
          c p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        unary_loop_body
          (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop.body
    unfold unary_loop_body
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok
      (elementwise_unary_spec
        (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
        (mmul_by_const_per_elem_P c)
        per_elem_spec
        simd_unit.values)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show liftZ_std (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P

/-- Strong variant of `mmul_by_const_per_elem_P`: tight montgomery output bound
    `r.val.natAbs ≤ 12578816` instead of `≤ 2^24`. -/
private def mmul_by_const_per_elem_P_strong (c x r : Std.I32) : Prop :=
  liftZ_std r.val = (x.val : Zq) * (c.val : Zq) * (RINV : Zq)
    ∧ r.val.natAbs ≤ 12578816

/-- Strong variant of `montgomery_multiply_by_constant_spec`: exposes the TIGHT
    montgomery output bound `≤ 12578816` (instead of `≤ 2^24`) on every lane, via
    `montgomery_multiply_fe_by_fer_spec_strong`. Invoked EXPLICITLY by the
    inverse-NTT cross-unit leaf; no `@[spec]` to avoid hax_mvcgen ambiguity. -/
theorem montgomery_multiply_by_constant_spec_strong
    (simd_unit : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) (c : Std.I32)
    (hc : c.val.natAbs ≤ 8380416) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant simd_unit c
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 →
                liftZ_std (r.values.val[j]!).val
                  = ((simd_unit.values.val[j]!).val : Zq) * (c.val : Zq) * (RINV : Zq)
              ∧ (r.values.val[j]!).val.natAbs ≤ 12578816 ⌝ ⦄ := by
  -- Per-element spec: the leaf `montgomery_multiply_fe_by_fer_spec_strong x c hc` IS the
  -- per-element post verbatim (`P := mmul_by_const_per_elem_P_strong c`); `hc` is closed
  -- over, so no guard or entailment massaging is needed.
  have per_elem_spec : ∀ x : Std.I32,
      ⦃ ⌜ True ⌝ ⦄
      libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c
      ⦃ ⇓ r => ⌜ mmul_by_const_per_elem_P_strong c x r ⌝ ⦄ :=
    fun x =>
      libcrux_iot_ml_dsa.Vector.Portable.Arithmetic.montgomery_multiply_fe_by_fer_spec_strong x c hc
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant
  rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Array.to_slice simd_unit.values) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [show CoreModels.core.slice.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)
        = .ok (Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice simd_unit.values)) from rfl]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [coeff_slice_len_eq simd_unit.values]
  unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop
  -- Bridge `montgomery_multiply_by_constant_loop.body c` to
  -- `unary_loop_body (fun x => montgomery_multiply_fe_by_fer x c)`. Single index,
  -- free `c` — plain `rfl` after unfolding both bodies and `mmfbf`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop.body
          c p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize) × CoeffArray) =>
        unary_loop_body
          (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, a1⟩
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_by_constant_loop.body
    unfold unary_loop_body
    unfold libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer
    rfl
  rw [h_body_eq]
  obtain ⟨out, h_out_eq, h_out_P⟩ :=
    triple_exists_ok
      (elementwise_unary_spec
        (fun x => libcrux_iot_ml_dsa.simd.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
        (mmul_by_const_per_elem_P_strong c)
        per_elem_spec
        simd_unit.values)
  rw [h_out_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  refine triple_of_ok (v := { values := out }) rfl ?_
  intro j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := h_out_P j hj
  show liftZ_std (out.val[j]!).val = _ ∧ _
  rw [h_acc]
  exact h_P


/-! ## Per-unit (`Coefficients`-level) convert FCs.

    `zero` / `to_coefficient_array` / `from_coefficient_array` are the elementwise
    primitives the poly-layer `zero` / `to_i32_array` / `from_i32_array` loops call
    per SIMD unit. Each reduces to a trivial slice/`Array.repeat` manipulation;
    `declassify_ref`/`classify` are identities (`Extraction/Missing.lean`). -/

/-- **`zero` unit.** `simd.portable.vector_type.zero = ok { values := repeat 8 (classify 0) }`;
    `classify` is identity, so every lane is `0`. -/
theorem zero_unit_spec :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.vector_type.zero
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 → (r.values.val[j]!).val = 0 ⌝ ⦄ := by
  have h_ok : libcrux_iot_ml_dsa.simd.portable.vector_type.zero
      = .ok { values := Array.repeat 8#usize (0#i32 : Std.I32) } := by
    unfold libcrux_iot_ml_dsa.simd.portable.vector_type.zero
    unfold libcrux_secrets.traits.Classify.Blanket.classify
    rfl
  refine triple_of_ok (v := { values := Array.repeat 8#usize (0#i32 : Std.I32) }) h_ok ?_
  intro j hj
  show ((Array.repeat 8#usize (0#i32 : Std.I32)).val[j]!).val = 0
  rw [Array.repeat_val, List.getElem!_eq_getElem?_getD, List.getElem?_replicate]
  simp [hj]

/-- **`to_coefficient_array` unit.** `declassify_ref value.values` is identity, then
    `copy_from_slice out (to_slice value.values)` returns the source slice (lengths
    both `8`). Result slice's lanes equal `value`'s lanes. The precond `hout` (out
    length `8`) is what the impl's `copy_from_slice` genuinely needs. -/
theorem to_coefficient_array_spec
    (value : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) (out : Slice Std.I32)
    (hout : out.val.length = 8) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.vector_type.to_coefficient_array value out
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 → (r.val[j]!).val = (value.values.val[j]!).val ⌝ ⦄ := by
  have h_ok : libcrux_iot_ml_dsa.simd.portable.vector_type.to_coefficient_array value out
      = .ok (Aeneas.Std.Array.to_slice value.values) := by
    unfold libcrux_iot_ml_dsa.simd.portable.vector_type.to_coefficient_array
    unfold libcrux_secrets.SharedAT.Insts.Libcrux_secretsTraitsDeclassifyRefSharedAT.declassify_ref
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice value.values)
          = .ok (Aeneas.Std.Array.to_slice value.values) from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    unfold CoreModels.core.slice.Slice.copy_from_slice
    have h1 : Aeneas.Std.Slice.len out
        = Aeneas.Std.Slice.len (Aeneas.Std.Array.to_slice value.values) := by
      apply Std.UScalar.eq_of_val_eq
      rw [Aeneas.Std.Slice.len_val, Aeneas.Std.Slice.len_val,
          Aeneas.Std.Array.length_to_slice]
      show out.val.length = (8 : Nat)
      rw [hout]
    rw [if_pos h1]
  refine triple_of_ok (v := Aeneas.Std.Array.to_slice value.values) h_ok ?_
  intro j hj
  show ((Aeneas.Std.Array.to_slice value.values).val[j]!).val = _
  rfl

/-- **`from_coefficient_array` unit.** Indexes `array[0..8]` into `out.values` (via
    `to_slice_mut` + `copy_from_slice` + write-back). Result unit's lanes equal the
    first `8` lanes of `array`. The precond `harr` (`array` length `8`) is the
    in-bounds requirement of the `array[0..8]` index. -/
theorem from_coefficient_array_spec
    (array : Slice Std.I32)
    (out : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)
    (harr : 8 ≤ array.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_dsa.simd.portable.vector_type.from_coefficient_array array out
    ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 8 → (r.values.val[j]!).val = (array.val[j]!).val ⌝ ⦄ := by
  obtain ⟨r, h_ok, h_P⟩ :
      ∃ r, libcrux_iot_ml_dsa.simd.portable.vector_type.from_coefficient_array array out = .ok r
        ∧ ∀ j : Nat, j < 8 → (r.values.val[j]!).val = (array.val[j]!).val := by
    unfold libcrux_iot_ml_dsa.simd.portable.vector_type.from_coefficient_array
    rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice_mut out.values)
          = .ok (Aeneas.Std.Array.to_slice_mut out.values) from rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show simd.traits.COEFFICIENTS_IN_SIMD_UNIT = 8#usize by
          simp [simd.traits.COEFFICIENTS_IN_SIMD_UNIT]]
    have hsp_len : (Aeneas.Std.Array.to_slice_mut out.values).1.val.length = 8 :=
      out.values.property
    have hback_eq : (Aeneas.Std.Array.to_slice_mut out.values).2 = out.values.from_slice := rfl
    rcases hp : out.values.to_slice_mut with ⟨sp, back⟩
    -- Collapse the literal pair-destructuring `let (s, back) := (sp, back)`.
    show ∃ r, (do
        let s1 ← core.Slice.Insts.CoreOpsIndexIndex.index
                (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice Std.I32) array
                { start := 0#usize, «end» := 8#usize }
        let s2 ← CoreModels.core.slice.Slice.copy_from_slice core.I32.Insts.CoreMarkerCopy sp s1
        Result.ok ({ values := back s2 }
          : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients)) = .ok r
        ∧ ∀ j : Nat, j < 8 → (r.values.val[j]!).val = (array.val[j]!).val
    obtain ⟨s1, hs1_eq, hs1_val, hs1_len⟩ :=
      triple_exists_ok
        (core_models_Slice_Insts_index_RangeUsize_spec array
          { start := 0#usize, «end» := 8#usize } (by decide) (by exact harr))
    rw [hs1_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    have hsp_len8 : sp.val.length = 8 := by
      rw [show sp = (out.values.to_slice_mut).1 from by rw [hp], hsp_len]
    have hs1_len8 : s1.val.length = 8 := by rw [hs1_len]; rfl
    obtain ⟨s2, hs2_eq, hs2_val⟩ :=
      triple_exists_ok
        (core_models_slice_Slice_copy_from_slice_spec core.I32.Insts.CoreMarkerCopy sp s1
          (by rw [hsp_len8, hs1_len8]))
    rw [hs2_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    refine ⟨_, rfl, ?_⟩
    intro j hj
    show (back s2).val[j]!.val = _
    have hback : back = out.values.from_slice := by
      rw [show back = (out.values.to_slice_mut).2 from by rw [hp], hback_eq]
    rw [hback]
    have hfrom : (out.values.from_slice s2).val = s2.val := by
      rw [Aeneas.Std.Array.from_slice_val]; rw [hs2_val, hs1_len8]; rfl
    rw [hfrom, hs2_val, hs1_val]
    show ((List.slice 0 8 array.val)[j]!).val = _
    congr 1
    unfold List.slice
    simp only [List.drop_zero]
    rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_take_of_lt hj]
  exact triple_of_ok h_ok h_P

end libcrux_iot_ml_dsa.Vector.Portable.Element
