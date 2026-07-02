/-
  # `Equivalence/L1_VectorElementOps.lean` — Layer 1 elementwise PortableVector Triples.

  Layer-1 Triples for the per-element-of-PortableVector ops. Each L1.x
  Triple proves that running the loop produces an output vector where
  every element satisfies the corresponding L0.x per-element post:

  - **L1.3 `barrett_reduce_spec`** — instantiates `elementwise_unary_spec`
    with `barrett_reduce_element_spec` from L0.2.
  - **L1.4 `montgomery_multiply_by_constant_spec`** — instantiates
    `elementwise_unary_spec` with `montgomery_multiply_fe_by_fer_spec`
    (L0.4), post-processed to expose `(r * 2^16) % 3329 = (x * c) % 3329`.
  - **L1.5 `cond_subtract_3329_spec`** — uses a conditional-body
    variant `elementwise_cond_unary_spec` (the else-branch returns
    the input vec unchanged, so the canonical `unary_loop_body`
    shape doesn't apply).
  - **L1.6 `negate_spec`** — instantiates `elementwise_unary_spec`
    with `core.num.I16.wrapping_neg` (per-element `.bv = -x.bv`).

  L1.1, L1.2, L1.7-L1.10 will follow the same pattern (instantiate the
  per-element L0.x Triple via `elementwise_unary_spec` / its
  conditional / binary variants).
-/
import LibcruxIotMlKem.Vector.Portable.Arithmetic.LoopHelper
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element
open libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper

/-! ## L1.1 — `add_spec`

    The Vector.Portable.Arithmetic.add impl is a 16-iter loop that
    calls `core.num.I16.wrapping_add lhs[i] rhs[i]` and writes
    the result back to `lhs[i]`. Under the per-element no-overflow
    bound `|lhs.val + rhs.val| ≤ 2^15 - 1`, the wrap is the identity
    and `(wrapping_add lhs rhs).val = lhs.val + rhs.val`. -/

/-- Per-element predicate (guarded form): given the no-overflow bound
    on `x + y`, the output value equals the sum and is in range. -/
private def add_per_elem_P (x y r : Std.I16) : Prop :=
  ((x.val + y.val : Int)).natAbs ≤ 2 ^ 15 - 1 →
    r.val = x.val + y.val ∧ r.val.natAbs ≤ 2 ^ 15 - 1

/-- Per-element Triple: `core.num.I16.wrapping_add x y` reduces
    to `.ok (Std.I16.wrapping_add x y)`, whose `.val` is the bmod of
    `x.val + y.val` mod `2^16`. Under the no-overflow bound,
    `Int.bmod` is the identity. -/
private theorem add_per_elem_spec (x y : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I16.wrapping_add x y
    ⦃ ⇓ r => ⌜ add_per_elem_P x y r ⌝ ⦄ := by
  have h_ok :
      CoreModels.core.num.I16.wrapping_add x y
        = .ok (Aeneas.Std.I16.wrapping_add x y) := by
    unfold CoreModels.core.num.I16.wrapping_add
    unfold rust_primitives.arithmetic.wrapping_add_i16
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show add_per_elem_P x y (Aeneas.Std.I16.wrapping_add x y)
  unfold add_per_elem_P
  intro hb
  have h_val := Aeneas.Std.I16.wrapping_add_val_eq x y
  have h_lb : -(2 ^ 15 : Int) ≤ x.val + y.val := by
    have h_abs : ((x.val + y.val : Int)).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_ub : x.val + y.val < (2 ^ 15 : Int) := by
    have h_abs : ((x.val + y.val : Int)).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_bmod : Int.bmod (x.val + y.val) (2 ^ 16) = x.val + y.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact hb

@[spec]
theorem add_spec
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val + (rhs.elements.val[i]!).val : Int).natAbs ≤ 2 ^ 15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).val
                  = (lhs.elements.val[i]!).val + (rhs.elements.val[i]!).val
              ∧ (r.elements.val[i]!).val.natAbs ≤ 2 ^ 15 - 1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.add
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.add_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge `add_loop.body rhs` to
  -- `binary_loop_body CoreModels.core.num.I16.wrapping_add rhs`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.add_loop.body rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        binary_loop_body CoreModels.core.num.I16.wrapping_add rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.add_loop.body
    unfold binary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_binary_spec
      CoreModels.core.num.I16.wrapping_add
      add_per_elem_P
      add_per_elem_spec
      lhs rhs)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## L1.2 — `sub_spec`

    The Vector.Portable.Arithmetic.sub impl is a 16-iter loop that
    calls `core.num.I16.wrapping_sub lhs[i] rhs[i]`. Same
    structure as `add_spec` but with `-` instead of `+`. -/

/-- Per-element predicate (guarded form): given the no-overflow bound
    on `x - y`, the output value equals the difference and is in range. -/
private def sub_per_elem_P (x y r : Std.I16) : Prop :=
  ((x.val - y.val : Int)).natAbs ≤ 2 ^ 15 - 1 →
    r.val = x.val - y.val ∧ r.val.natAbs ≤ 2 ^ 15 - 1

/-- Per-element Triple: `core.num.I16.wrapping_sub x y` reduces
    to `.ok (Std.I16.wrapping_sub x y)`, whose `.val` is the bmod of
    `x.val - y.val` mod `2^16`. Under the no-overflow bound,
    `Int.bmod` is the identity. -/
private theorem sub_per_elem_spec (x y : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I16.wrapping_sub x y
    ⦃ ⇓ r => ⌜ sub_per_elem_P x y r ⌝ ⦄ := by
  have h_ok :
      CoreModels.core.num.I16.wrapping_sub x y
        = .ok (Aeneas.Std.I16.wrapping_sub x y) := by
    unfold CoreModels.core.num.I16.wrapping_sub
    unfold rust_primitives.arithmetic.wrapping_sub_i16
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show sub_per_elem_P x y (Aeneas.Std.I16.wrapping_sub x y)
  unfold sub_per_elem_P
  intro hb
  have h_val := Aeneas.Std.I16.wrapping_sub_val_eq x y
  have h_lb : -(2 ^ 15 : Int) ≤ x.val - y.val := by
    have h_abs : ((x.val - y.val : Int)).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_ub : x.val - y.val < (2 ^ 15 : Int) := by
    have h_abs : ((x.val - y.val : Int)).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_bmod : Int.bmod (x.val - y.val) (2 ^ 16) = x.val - y.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  refine ⟨?_, ?_⟩
  · rw [h_val, h_bmod]
  · rw [h_val, h_bmod]; exact hb

@[spec]
theorem sub_spec
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val - (rhs.elements.val[i]!).val : Int).natAbs ≤ 2 ^ 15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.sub lhs rhs
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).val
                  = (lhs.elements.val[i]!).val - (rhs.elements.val[i]!).val
              ∧ (r.elements.val[i]!).val.natAbs ≤ 2 ^ 15 - 1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.sub
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.sub_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.sub_loop.body rhs p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        binary_loop_body CoreModels.core.num.I16.wrapping_sub rhs p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.sub_loop.body
    unfold binary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_binary_spec
      CoreModels.core.num.I16.wrapping_sub
      sub_per_elem_P
      sub_per_elem_spec
      lhs rhs)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## L1.3 — `barrett_reduce_spec`

    Implements the upstream `Vector.Portable.Arithmetic.barrett_reduce`
    correctness theorem. The impl is a 16-iteration
    `for i in 0..16` loop that calls L0.2 `barrett_reduce_element` on each
    element. The post asserts each output element is congruent to its
    input mod 3329 and bounded in absolute value by 3328.

    F* pre: `∀ i < 16, is_i16b 32767 vec.elements[i]`
    F* post: `∀ i < 16, is_i16b 3328 r.elements[i]
                     ∧ v r.elements[i] % 3329 = v vec.elements[i] % 3329` -/

/-- Per-element predicate threading the L0.2 bound precondition into
    an implication. -/
private def barrett_per_elem_P (x y : Std.I16) : Prop :=
  x.val.natAbs ≤ 32767 →
    libcrux_iot_ml_kem.Spec.ModularArith.modq_eq y.val x.val 3329
      ∧ y.val.natAbs ≤ 1664

/-- Per-element Triple: an unconditional Triple over
    `barrett_reduce_element` with the guarded post. The function is
    total (see `barrett_reduce_element_eq_ok`); the in-bounds case
    invokes the L0.2 `barrett_reduce_element_spec`. -/
private theorem barrett_per_elem_spec (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element x
    ⦃ ⇓ r => ⌜ barrett_per_elem_P x r ⌝ ⦄ := by
  -- The function is total: it returns `.ok (barrett_reduce_impl_value x)`
  -- unconditionally (`barrett_reduce_element_eq_ok`). Reduce the Triple
  -- to a pure goal via that .ok equation.
  have h_ok := barrett_reduce_element_eq_ok x
  rw [show libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element x
        = .ok (barrett_reduce_impl_value x) from h_ok]
  -- Triple shape: ⦃True⦄ .ok v ⦃⇓ r => ⌜barrett_per_elem_P x r⌝⦄.
  simp only [Std.Do.Triple, WP.wp]
  intro _
  -- Goal: barrett_per_elem_P x (barrett_reduce_impl_value x)
  show barrett_per_elem_P x (barrett_reduce_impl_value x)
  unfold barrett_per_elem_P
  intro hb
  -- Now use the L0.2 spec.
  have hT := barrett_reduce_element_spec x hb
  -- hT : ⦃True⦄ barrett_reduce_element x ⦃⇓ r => ⌜...⌝⦄
  -- Reduce to the .ok form via h_ok.
  rw [h_ok] at hT
  -- hT : ⦃True⦄ .ok (barrett_reduce_impl_value x) ⦃⇓ r => ⌜...⌝⦄
  -- Extract the post-condition.
  simp only [Std.Do.Triple, WP.wp] at hT
  exact hT trivial

@[spec]
theorem barrett_reduce_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bounds : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
                (r.elements.val[i]!).val (vec.elements.val[i]!).val 3329
              ∧ (r.elements.val[i]!).val.natAbs ≤ 1664 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Replace `barrett_reduce_loop.body` with `unary_loop_body
  -- barrett_reduce_element`. Both have identical definitions modulo
  -- the per_elem variable, so funext is trivial.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop.body p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce_element
      barrett_per_elem_P
      barrett_per_elem_spec
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  -- hh : ∀ i < 16, ∃ ri, barrett_reduce_element (vec[i]) = .ok ri
  --        ∧ r.elements[i]! = ri ∧ barrett_per_elem_P (vec[i]) ri
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (h_bounds j hj)

/-! ## L1.4 — `montgomery_multiply_by_constant_spec`

    The Vector.Portable.Arithmetic.montgomery_multiply_by_constant impl
    is a 16-iteration loop that calls L0.4's `montgomery_multiply_fe_by_fer`
    on each element (the constant `c` is captured by the body lambda).

    Conversion from L0.4's `modq_eq r (fe*c*169) 3329` to L1.4's
    `(r*2^16) % 3329 = (fe*c) % 3329`: multiply both sides by 2^16,
    and use `169 * 65536 ≡ 1 (mod 3329)` (which is the Montgomery
    inversion identity at this q). -/

/-- Per-element predicate (unconditional form): the L0.4 bound +
    the L1.4-shaped Montgomery congruence. -/
private def montgomery_per_elem_P (c x y : Std.I16) : Prop :=
  y.val.natAbs ≤ 3328
    ∧ (y.val * (2 ^ 16 : Int)) % 3329 = (x.val * c.val) % 3329

/-- Per-element Triple: invokes the L0.4 spec under the captured `hc`,
    then weakens the post via the Montgomery-inversion identity
    `169 * 2^16 ≡ 1 (mod 3329)`. -/
private theorem montgomery_per_elem_spec
    (c : Std.I16) (hc : c.val.natAbs ≤ 1664) (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c
    ⦃ ⇓ r => ⌜ montgomery_per_elem_P c x r ⌝ ⦄ := by
  -- Invoke L0.4 and weaken its post to the L1.4-shaped form.
  apply Std.Do.Triple.of_entails_right _ (montgomery_multiply_fe_by_fer_spec x c hc)
  rw [PostCond.entails_noThrow]
  intro r hh
  have h_inner : r.val.natAbs ≤ 3328
                  ∧ libcrux_iot_ml_kem.Spec.ModularArith.modq_eq r.val (x.val * c.val * 169) 3329 := by
    simpa [Std.Do.SPred.down_pure] using hh
  obtain ⟨h_bd, h_mod⟩ := h_inner
  show montgomery_per_elem_P c x r
  unfold montgomery_per_elem_P
  refine ⟨h_bd, ?_⟩
  -- From `modq_eq r (x * c * 169) 3329`, derive `(r * 2^16) % 3329 = (x * c) % 3329`.
  unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_mod
  -- h_mod : (r.val - x.val * c.val * 169) % 3329 = 0
  -- Goal:   (r.val * 2^16) % 3329 = (x.val * c.val) % 3329
  have h_dvd : (3329 : Int) ∣ (r.val - x.val * c.val * 169) :=
    Int.dvd_of_emod_eq_zero h_mod
  -- 3329 ∣ (r*2^16 - x*c*169*2^16) (multiply prev by 2^16).
  have h_dvd2 : (3329 : Int)
                  ∣ (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int)) := by
    have h_eq : (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int))
                = (r.val - x.val * c.val * 169) * (2 ^ 16 : Int) := by ring
    rw [h_eq]; exact Dvd.dvd.mul_right h_dvd _
  -- 169 * 65536 = 11075584 = 3329 * 3327 + 1, so 169 * 2^16 - 1 = 3329 * 3327.
  have h_inv : (169 : Int) * (2 ^ 16 : Int) - 1 = 3329 * 3327 := by decide
  have h_dvd3 : (3329 : Int)
                  ∣ (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val) := by
    have h_eq : (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val)
                = (x.val * c.val) * ((169 : Int) * (2 ^ 16 : Int) - 1) := by ring
    rw [h_eq, h_inv]
    exact ⟨(x.val * c.val) * 3327, by ring⟩
  have h_dvd4 : (3329 : Int) ∣ (r.val * (2 ^ 16 : Int) - x.val * c.val) := by
    have h_sum : (r.val * (2 ^ 16 : Int) - x.val * c.val)
                = (r.val * (2 ^ 16 : Int) - x.val * c.val * 169 * (2 ^ 16 : Int))
                  + (x.val * c.val * 169 * (2 ^ 16 : Int) - x.val * c.val) := by ring
    rw [h_sum]; exact dvd_add h_dvd2 h_dvd3
  -- (a - b) % q = 0  ⇒  a % q = b % q.
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
  exact Int.emod_eq_zero_of_dvd h_dvd4

@[spec]
theorem montgomery_multiply_by_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              (r.elements.val[i]!).val.natAbs ≤ 3328
              ∧ ((r.elements.val[i]!).val * (2 ^ 16 : Int)) % 3329
                 = ((vec.elements.val[i]!).val * c.val) % 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge the impl's body shape (captured-c) to `unary_loop_body
  -- (λ x => montgomery_multiply_fe_by_fer x c)`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop.body
          c p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          (fun x => libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      (fun x => libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_fe_by_fer x c)
      (montgomery_per_elem_P c)
      (fun x => montgomery_per_elem_spec c hc x)
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.6 — `negate_spec`

    The Vector.Portable.Arithmetic.negate impl is a 16-iter loop
    calling `core.num.I16.wrapping_neg` on each element. The
    per-element op is the missing-stub `wrapping_sub 0 x`. -/

/-- Per-element predicate: `.bv = -x.bv`. -/
private def negate_per_elem_P (x y : Std.I16) : Prop :=
  y.bv = -x.bv

/-- Per-element Triple: `wrapping_neg x = .ok (wrapping_sub 0 x)` and
    `(wrapping_sub 0 x).bv = 0 - x.bv = -x.bv`. -/
private theorem negate_per_elem_spec (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I16.wrapping_neg x
    ⦃ ⇓ r => ⌜ negate_per_elem_P x r ⌝ ⦄ := by
  -- The missing-stub def: `wrapping_neg x = wrapping_sub_i16 0 x = .ok (I16.wrapping_sub 0 x)`.
  have h_ok :
      CoreModels.core.num.I16.wrapping_neg x = .ok (Aeneas.Std.I16.wrapping_sub (0#i16) x) := by
    unfold CoreModels.core.num.I16.wrapping_neg
    unfold rust_primitives.arithmetic.wrapping_sub_i16
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show negate_per_elem_P x (Aeneas.Std.I16.wrapping_sub (0#i16) x)
  unfold negate_per_elem_P
  -- (wrapping_sub 0 x).bv = 0.bv - x.bv = -x.bv.
  rw [Aeneas.Std.I16.wrapping_sub_bv_eq]
  -- (0#i16).bv = 0 (BitVec definitional); reduce LHS to `0 - x.bv` then
  -- apply BitVec.zero_sub. Use simp to normalize the `IScalarTy.I16.numBits`
  -- vs `16` type-level reduction (per SKILL §5.1.1).
  simp only [show (0#i16 : Std.I16).bv = (0 : BitVec 16) from rfl]
  exact BitVec.zero_sub x.bv

@[spec]
theorem negate_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              (r.elements.val[i]!).bv = -(vec.elements.val[i]!).bv ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge body to `unary_loop_body CoreModels.core.num.I16.wrapping_neg`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop.body p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body CoreModels.core.num.I16.wrapping_neg p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.negate_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      CoreModels.core.num.I16.wrapping_neg
      negate_per_elem_P
      negate_per_elem_spec
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.5 — `cond_subtract_3329_spec`

    The Vector.Portable.Arithmetic.cond_subtract_3329 impl is a
    16-iter loop where each iter conditionally subtracts 3329 from
    the element (if `x ≥ 3329`) or passes through unchanged. The
    canonical `unary_loop_body` macro doesn't fit because the
    else-branch returns the input `vec` unchanged (no `Array.update`).

    Plan-B: prove from first principles via `loop_range_spec_usize`,
    mirroring `elementwise_unary_spec`'s shape (2-conjunct invariant,
    body-reduction-to-Result-equation, step lemma) with the
    conditional branching inlined. -/

namespace CondSubtract3329

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

private theorem triple_of_ok_l1
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem of_pure_prop_holds_l1 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow,
    PredTrans.apply] at h
  exact h trivial

private theorem pure_prop_holds_l1 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]; intro _; exact h

/-- Per-element invariant for `cond_subtract_3329`. -/
private def cond_inv
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize →
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector →
    Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
        (((input.elements.val[j]!).val ≥ 3329 ∧
            (acc.elements.val[j]!) = Std.I16.wrapping_sub (input.elements.val[j]!) 3329#i16)
          ∨ ((input.elements.val[j]!).val < 3329 ∧
              acc.elements.val[j]! = input.elements.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.elements.val[j]! = input.elements.val[j]!))

/-- Per-iteration post as a top-level def (avoids inline match issue
    with `loop_range_spec_usize`'s named match constants — see SKILL
    §13 / the analogous `unary_step_post` in PortableVector.lean). -/
private def cond_step_post
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize)
        × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (cond_inv input iter'.start acc').holds
  | .done y => (cond_inv input 16#usize y).holds

set_option maxHeartbeats 8000000 in
private theorem cond_step
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (cond_inv input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ cond_step_post input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l1 h_inv
  have h_acc_len : acc.elements.length = 16 := PortableVector_elements_length acc
  have h_16 : (16#usize : Std.Usize).val = 16 := rfl
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some i = k branch.
    have hk_16 : k.val < 16 := by rw [h_16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc.elements k = .ok (acc.elements.val[k.val]!) :=
      array_index_usize_ok_eq acc.elements k (by rw [h_acc_len]; exact hk_16)
    -- declassify x = .ok x.
    have h_decl :
        libcrux_secrets.traits.Declassify.Blanket.declassify (acc.elements.val[k.val]!)
          = .ok (acc.elements.val[k.val]!) := rfl
    -- Two sub-cases for the ≥3329 branch.
    set xk : Std.I16 := acc.elements.val[k.val]! with hxk_def
    -- The key element at index k.
    have h_acc_xk : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
      h_acc_undone k.val (Nat.le_refl _) hk_16
    by_cases h_ge : xk.val ≥ 3329
    · -- ≥ 3329: write back wrapping_sub.
      have h_ge_lit : xk ≥ 3329#i16 := by
        -- `≥` on I16 is `.val ≥ .val`.
        change (3329#i16 : Std.I16).val ≤ xk.val
        have : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [this]; exact h_ge
      have h_decide : decide (xk ≥ 3329#i16) = true := decide_eq_true h_ge_lit
      -- wrapping_sub xk 3329#i16 reduces to .ok (Std.I16.wrapping_sub xk 3329#i16).
      have h_wsub :
          CoreModels.core.num.I16.wrapping_sub xk 3329#i16
            = .ok (Std.I16.wrapping_sub xk 3329#i16) := by
        unfold CoreModels.core.num.I16.wrapping_sub
        unfold rust_primitives.arithmetic.wrapping_sub_i16
        rfl
      have h_upd :
          Aeneas.Std.Array.update acc.elements k (Std.I16.wrapping_sub xk 3329#i16)
            = .ok (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)) :=
        array_update_ok_eq acc.elements k _ (by rw [h_acc_len]; exact hk_16)
      have h_body :
          (do
            let (o, iter1) ←
              core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
            match o with
            | core.option.Option.None =>
                (Result.ok (ControlFlow.done acc) :
                  Result (ControlFlow
                    ((CoreModels.core.ops.range.Range Std.Usize)
                      × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
            | core.option.Option.Some i =>
              let i1 ← Aeneas.Std.Array.index_usize acc.elements i
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← core.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize),
               { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) })) := by
        conv_lhs =>
          rw [show
            (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
              = (CoreModels.core.iter.range.IteratorRange.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : CoreModels.core.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_pos h_ge_lit]
        rw [h_wsub]
        simp only [bind_tc_ok]
        rw [h_upd]
        rfl
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) }))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k: invariant carries over (set at index k, j ≠ k).
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
                = (acc.elements)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
                = acc.elements.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
          have h_old := h_acc_done j hj_lt_k
          rcases h_old with ⟨h_in_ge, h_acc_eq⟩ | ⟨h_in_lt, h_acc_eq⟩
          · left; refine ⟨h_in_ge, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
          · right; refine ⟨h_in_lt, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
        · -- j = k.val: use the just-set element.
          subst hj_eq_k
          have h_lt'' : k.val < acc.elements.length := by rw [h_acc_len]; exact hk_16
          have h_set_eq :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc.elements k k.val _ ⟨rfl, h_lt''⟩
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          left
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; exact h_ge
          · rw [h_set_eq_val, ← h_acc_xk]
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
              = (acc.elements)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
        have h_set_eq_val :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
              = acc.elements.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        rw [h_set_eq_val]
        exact h_acc_undone j h_ge' hj_lt
    · -- < 3329: pass through unchanged.
      have h_not_ge : ¬ (3329#i16 : Std.I16).val ≤ xk.val := by
        have h_eq : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [h_eq]; exact h_ge
      have h_not_ge' : ¬ (xk ≥ 3329#i16) := h_not_ge
      have h_body :
          (do
            let (o, iter1) ←
              core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
            match o with
            | core.option.Option.None =>
                (Result.ok (ControlFlow.done acc) :
                  Result (ControlFlow
                    ((CoreModels.core.ops.range.Range Std.Usize)
                      × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
            | core.option.Option.Some i =>
              let i1 ← Aeneas.Std.Array.index_usize acc.elements i
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← core.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize),
               acc)) := by
        conv_lhs =>
          rw [show
            (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
              = (CoreModels.core.iter.range.IteratorRange.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : CoreModels.core.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_neg h_not_ge']
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    acc))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · exact h_acc_done j hj_lt_k
        · subst hj_eq_k
          right
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; show xk.val < 3329
            push Not at h_ge; exact h_ge
          · exact h_acc_xk
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ge' : k.val ≤ j := by omega
        exact h_acc_undone j h_ge' hj_lt
  · -- None branch.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h_16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize)
                    × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc.elements i
            let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
            if i2 >= 3329#i16
            then
              let i3 ← core.num.I16.wrapping_sub i1 3329#i16
              let a ← Aeneas.Std.Array.update acc.elements i i3
              ok (cont (iter1, { elements := a }))
            else ok (cont (iter1, acc)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_l1 h_body
    show cond_step_post input k (.done acc)
    unfold cond_step_post
    apply pure_prop_holds_l1
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_16] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_16] at hj_ge; exact hj_ge

end CondSubtract3329

@[spec]
theorem cond_subtract_3329_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bounds : ∀ i : Nat, i < 16 → 0 ≤ (vec.elements.val[i]!).val
                                  ∧ (vec.elements.val[i]!).val < 2 * 3329) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
              0 ≤ (r.elements.val[i]!).val
              ∧ (r.elements.val[i]!).val < 3329
              ∧ (r.elements.val[i]!).val % 3329 = (vec.elements.val[i]!).val % 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, vec1) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
          iter1 vec1)
      vec 0#usize 16#usize
      (CondSubtract3329.cond_inv vec)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (CondSubtract3329.pure_prop_holds_l1 ⟨
        fun j hj => by
          have h0 : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done, _h_undone⟩ := CondSubtract3329.of_pure_prop_holds_l1 h
    intro j hj
    -- Per-element: derive 0 ≤ r[j] < 3329 and r[j] % 3329 = vec[j] % 3329.
    obtain ⟨h_vec_ge, h_vec_lt⟩ := h_bounds j hj
    have h_done_j := h_done j (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hj)
    -- Pinned x := vec[j] (since the inv carries `input := vec`).
    set xj : Std.I16 := vec.elements.val[j]! with hxj_def
    rcases h_done_j with ⟨h_ge, h_eq⟩ | ⟨h_lt, h_eq⟩
    · -- ≥ 3329 branch: r[j] = wrapping_sub xj 3329.
      -- (wrapping_sub xj 3329).val = xj.val - 3329, since 3329 ≤ xj.val < 6658.
      have h_wsub_val :
          (Std.I16.wrapping_sub xj (3329#i16 : Std.I16)).val = xj.val - 3329 := by
        rw [Std.I16.wrapping_sub_val_eq]
        -- bmod xj.val - 3329 by 2^16 = xj.val - 3329 when in range
        have h_diff_lb : -(2^15 : Int) ≤ xj.val - 3329 := by
          have h_xj_lb : (0 : Int) ≤ xj.val := h_vec_ge
          have : -(2^15 : Int) ≤ -3329 := by decide
          grind
        have h_diff_ub : xj.val - 3329 < (2^15 : Int) := by
          have h_xj_ub : xj.val < 2 * 3329 := h_vec_lt
          have h_step : (2 * 3329 - 3329 : Int) < (2^15 : Int) := by decide
          grind
        have h_3329_val : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [h_3329_val]
        apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
        · have h_const : -((2 : Int)^(16-1)) ≤ -(2^15 : Int) := by decide
          exact le_trans h_const h_diff_lb
        · have h_const : (2^15 : Int) ≤ (2 : Int)^(16-1) := by decide
          exact lt_of_lt_of_le h_diff_ub h_const
      refine ⟨?_, ?_, ?_⟩
      · -- 0 ≤ xj.val - 3329 (since xj.val ≥ 3329).
        rw [h_eq, h_wsub_val]
        have : (0 : Int) ≤ xj.val - 3329 := by grind
        exact this
      · -- xj.val - 3329 < 3329 (since xj.val < 2 * 3329).
        rw [h_eq, h_wsub_val]
        have : xj.val - 3329 < (3329 : Int) := by grind
        exact this
      · rw [h_eq, h_wsub_val]
        -- (xj.val - 3329) % 3329 = xj.val % 3329 (subtracting a multiple of 3329).
        have : (xj.val - 3329) % 3329 = xj.val % 3329 := by
          have h := Int.sub_emod xj.val 3329 3329
          rw [h]
          have h_self : (3329 : Int) % 3329 = 0 := by decide
          rw [h_self]
          simp [Int.emod_emod_of_dvd]
        exact this
    · -- < 3329 branch: r[j] = xj.
      refine ⟨?_, ?_, ?_⟩
      · rw [h_eq]; exact h_vec_ge
      · rw [h_eq]; exact h_lt
      · rw [h_eq]
  · intro acc k h_ge h_le hinv
    have h_step := CondSubtract3329.cond_step vec acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : CondSubtract3329.cond_step_post vec k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [CondSubtract3329.cond_step_post] using hP
    · have hP : CondSubtract3329.cond_step_post vec k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [CondSubtract3329.cond_step_post] using hP

/-! ## L1.7 — `multiply_by_constant_spec`

    The Vector.Portable.Arithmetic.multiply_by_constant impl is a
    16-iteration loop that calls `core.num.I16.wrapping_mul`
    on each element, with the constant `c` captured by the body
    lambda (same structure as L1.4's `montgomery_multiply_by_constant`).
    Under the per-element no-overflow bound
    `|x.val * c.val| ≤ 2^15 - 1`, the wrap is a no-op and
    `(wrapping_mul x c).val = x.val * c.val`. -/

/-- Per-element predicate (guarded form): given the no-overflow bound
    on `x * c`, the output value equals the product and is in range. -/
private def multiply_by_constant_per_elem_P (c x y : Std.I16) : Prop :=
  (x.val * c.val : Int).natAbs ≤ 2 ^ 15 - 1 →
    y.val = x.val * c.val ∧ y.val.natAbs ≤ 2 ^ 15 - 1

/-- Per-element Triple: `core.num.I16.wrapping_mul x c` reduces
    to `.ok (Std.I16.wrapping_mul x c)`, whose `.val` is the bmod of
    `x.val * c.val` mod `2^16`. Under the no-overflow bound,
    `Int.bmod` is the identity. -/
private theorem multiply_by_constant_per_elem_spec
    (c : Std.I16) (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.I16.wrapping_mul x c
    ⦃ ⇓ r => ⌜ multiply_by_constant_per_elem_P c x r ⌝ ⦄ := by
  -- Reduce `wrapping_mul` to `.ok (Std.I16.wrapping_mul x c)`.
  have h_ok :
      CoreModels.core.num.I16.wrapping_mul x c
        = .ok (Aeneas.Std.I16.wrapping_mul x c) := by
    unfold CoreModels.core.num.I16.wrapping_mul
    unfold rust_primitives.arithmetic.wrapping_mul_i16
    rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show multiply_by_constant_per_elem_P c x (Aeneas.Std.I16.wrapping_mul x c)
  unfold multiply_by_constant_per_elem_P
  intro hb
  -- `(wrapping_mul x c).val = Int.bmod (x.val * c.val) (2^16)`.
  have h_val := Aeneas.Std.I16.wrapping_mul_val_eq x c
  -- Under `|x*c| ≤ 2^15 - 1`, Int.bmod is the identity.
  -- omega handles `Int.natAbs ≤ N → -N ≤ a ∧ a ≤ N` directly.
  have h_lb : -(2 ^ 15 : Int) ≤ x.val * c.val := by
    have h_abs : (x.val * c.val : Int).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_ub : x.val * c.val < (2 ^ 15 : Int) := by
    have h_abs : (x.val * c.val : Int).natAbs ≤ 2 ^ 15 - 1 := hb
    omega
  have h_bmod : Int.bmod (x.val * c.val) (2 ^ 16) = x.val * c.val := by
    apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
    · have h_const : -((2 : Int) ^ (16 - 1)) ≤ -(2 ^ 15 : Int) := by decide
      exact le_trans h_const h_lb
    · have h_const : (2 ^ 15 : Int) ≤ (2 : Int) ^ (16 - 1) := by decide
      exact lt_of_lt_of_le h_ub h_const
  -- Combine.
  refine ⟨?_, ?_⟩
  · -- (wrapping_mul x c).val = x.val * c.val
    rw [h_val, h_bmod]
  · -- (wrapping_mul x c).val.natAbs ≤ 2^15 - 1
    rw [h_val, h_bmod]; exact hb

@[spec]
theorem multiply_by_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hpre : ∀ i : Nat, i < 16 →
      ((vec.elements.val[i]!).val * c.val : Int).natAbs ≤ 2 ^ 15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).val = (vec.elements.val[i]!).val * c.val
              ∧ (r.elements.val[i]!).val.natAbs ≤ 2 ^ 15 - 1 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge `multiply_by_constant_loop.body c` to `unary_loop_body
  -- (fun x => core.num.I16.wrapping_mul x c)`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant_loop.body
          c p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          (fun x => core.num.I16.wrapping_mul x c)
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      (fun x => core.num.I16.wrapping_mul x c)
      (multiply_by_constant_per_elem_P c)
      (fun x => multiply_by_constant_per_elem_spec c x)
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (hpre j hj)

/-! ## L1.8 — `bitwise_and_with_constant_spec`

    The Vector.Portable.Arithmetic.bitwise_and_with_constant impl is a
    16-iter loop where each iter computes `i1 &&& c` via the
    `lift`-then-bv operation. The per-element op is pure
    (no `Result`-level branching beyond `.ok`), so the Triple closes by
    direct reduction. -/

/-- Per-element predicate: `.bv = x.bv &&& c.bv`. -/
private def bitwise_and_per_elem_P (c x y : Std.I16) : Prop :=
  y.bv = x.bv &&& c.bv

/-- Per-element Triple: `lift (x &&& c)` reduces to `.ok (x &&& c)`,
    whose `.bv` is `x.bv &&& c.bv` by definition of `IScalar.and`. -/
private theorem bitwise_and_per_elem_spec (c : Std.I16) (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    lift (x &&& c)
    ⦃ ⇓ r => ⌜ bitwise_and_per_elem_P c x r ⌝ ⦄ := by
  -- `lift v = .ok v`, definitionally.
  have h_ok : (lift (x &&& c) : Result Std.I16) = .ok (x &&& c) := rfl
  rw [h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show bitwise_and_per_elem_P c x (x &&& c)
  unfold bitwise_and_per_elem_P
  -- `(x &&& c).bv = x.bv &&& c.bv` by definition of `IScalar.and`.
  rfl

@[spec]
theorem bitwise_and_with_constant_spec
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv = (vec.elements.val[i]!).bv &&& c.bv ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant_loop.body
          c p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          (fun x => lift (x &&& c))
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant_loop.body
    unfold unary_loop_body
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      (fun x => lift (x &&& c))
      (bitwise_and_per_elem_P c)
      (fun x => bitwise_and_per_elem_spec c x)
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.9 — `shift_right_spec`

    The Vector.Portable.Arithmetic.shift_right impl is a 16-iter loop
    where each body lifts the captured `SHIFT_BY : I32` to `U32` via
    `IScalar.hcast`, then `>>>`-shifts the i-th lane. The per-element
    op is `i2 >>> (IScalar.hcast .U32 SHIFT_BY)` =
    `IScalar.shiftRight_UScalar i2 _`. The body's structure differs
    from `unary_loop_body` in that the `lift (IScalar.hcast …)`
    statement is the first do-binding (before `index_usize`); but since
    `lift v = .ok v` is a pure no-op with no side effects, swapping
    the order is `rfl` after a `simp only [lift]`. -/

/-- Per-element predicate: `.bv = x.bv.sshiftRight SHIFT_BY.val.toNat`. -/
private def shift_right_per_elem_P (SHIFT_BY : Std.I32) (x y : Std.I16) : Prop :=
  y.bv = x.bv.sshiftRight SHIFT_BY.val.toNat

/-- Per-element Triple: `x >>> (IScalar.hcast .U32 SHIFT_BY)` reduces
    via `IScalar.shiftRight_UScalar_bv_eq` to
    `.ok ⟨x.bv.sshiftRight (hcast SHIFT_BY).val⟩`; the hcast preserves
    the value when `0 ≤ SHIFT_BY.val < 2^32`, so its `.val = SHIFT_BY.val.toNat`. -/
private theorem shift_right_per_elem_spec
    (SHIFT_BY : Std.I32) (hs : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 16) (x : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    (x >>> (IScalar.hcast .U32 SHIFT_BY) : Result Std.I16)
    ⦃ ⇓ r => ⌜ shift_right_per_elem_P SHIFT_BY x r ⌝ ⦄ := by
  -- `x >>> u` unfolds to `IScalar.shiftRight_UScalar x u`.
  show ⦃ ⌜ True ⌝ ⦄
        Aeneas.Std.IScalar.shiftRight_UScalar x (IScalar.hcast .U32 SHIFT_BY)
        ⦃ ⇓ r => ⌜ shift_right_per_elem_P SHIFT_BY x r ⌝ ⦄
  -- `(hcast .U32 SHIFT_BY).val ≤ 32` needs to be derived from `SHIFT_BY.val < 16`.
  obtain ⟨hs_nn, hs_lt⟩ := hs
  -- `(hcast .U32 SHIFT_BY).val = SHIFT_BY.val.toNat`. Use the in-bounds
  -- spec for `hcast`: under `0 ≤ SHIFT_BY.val ≤ U32.max`, hcast preserves value.
  have h_max : SHIFT_BY.val ≤ Aeneas.Std.UScalar.max .U32 := by
    -- scalar_tac knows UScalar.max .U32 = 4294967295 (via max_eq simp).
    scalar_tac
  have h_hcast_spec := Aeneas.Std.IScalar.hcast_inBounds_spec .U32 SHIFT_BY ⟨hs_nn, h_max⟩
  -- The `lift` post-only spec is `spec (lift v) p`, and `lift v = .ok v`,
  -- so `spec_ok` collapses it to `p v` directly.
  have h_eq_int : ((IScalar.hcast .U32 SHIFT_BY : Std.U32).val : Int) = SHIFT_BY.val := by
    -- h_hcast_spec : spec (lift (hcast .U32 SHIFT_BY)) (fun y => y.val = SHIFT_BY.val)
    -- Reduce lift → .ok, then spec_ok.
    have h_ok_lift : (lift (Aeneas.Std.IScalar.hcast .U32 SHIFT_BY)
                      : Result Std.U32)
                    = .ok (Aeneas.Std.IScalar.hcast .U32 SHIFT_BY) := rfl
    rw [h_ok_lift] at h_hcast_spec
    rw [Aeneas.Std.WP.spec_ok] at h_hcast_spec
    exact h_hcast_spec
  -- Bridge: `((n : Nat) : Int) = SHIFT_BY.val` and `0 ≤ SHIFT_BY.val` → `n = SHIFT_BY.val.toNat`.
  have h_hcast_val : (IScalar.hcast .U32 SHIFT_BY : Std.U32).val = SHIFT_BY.val.toNat := by
    have h_inj : ((IScalar.hcast .U32 SHIFT_BY : Std.U32).val : Int).toNat
                  = SHIFT_BY.val.toNat := by rw [h_eq_int]
    simpa using h_inj
  -- Now invoke `IScalar.shiftRight_UScalar_bv_eq`.
  have h_lt_numBits : (IScalar.hcast .U32 SHIFT_BY : Std.U32).val
                        < Aeneas.Std.IScalarTy.I16.numBits := by
    rw [h_hcast_val]
    have h_red : (Aeneas.Std.IScalarTy.I16.numBits : Nat) = 16 := by decide
    rw [h_red]
    -- `SHIFT_BY.val.toNat < 16` since `SHIFT_BY.val < 16` and `0 ≤ SHIFT_BY.val`.
    have h_le : (SHIFT_BY.val.toNat : Int) = SHIFT_BY.val := Int.toNat_of_nonneg hs_nn
    omega
  have h_sr := IScalar.shiftRight_UScalar_bv_eq x (IScalar.hcast .U32 SHIFT_BY) h_lt_numBits
  rw [h_sr]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show shift_right_per_elem_P SHIFT_BY x ⟨x.bv.sshiftRight (IScalar.hcast .U32 SHIFT_BY : Std.U32).val⟩
  unfold shift_right_per_elem_P
  show (⟨x.bv.sshiftRight (IScalar.hcast .U32 SHIFT_BY : Std.U32).val⟩ : Std.I16).bv
        = x.bv.sshiftRight SHIFT_BY.val.toNat
  show x.bv.sshiftRight (IScalar.hcast .U32 SHIFT_BY : Std.U32).val
        = x.bv.sshiftRight SHIFT_BY.val.toNat
  rw [h_hcast_val]

@[spec]
theorem shift_right_spec
    (SHIFT_BY : Std.I32) (hs : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 16)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right SHIFT_BY vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv =
                  (vec.elements.val[i]!).bv.sshiftRight SHIFT_BY.val.toNat ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right_loop
  have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                  = (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
  rw [h_field]
  -- Bridge `shift_right_loop.body SHIFT_BY` to
  -- `unary_loop_body (fun x => x >>> (IScalar.hcast .U32 SHIFT_BY))`.
  -- The two body shapes differ in that the impl computes the hcast
  -- *before* the index_usize. Since `lift v = .ok v` is pure,
  -- the bind chain reorders by `bind_tc_ok` rewriting.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right_loop.body
          SHIFT_BY p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        unary_loop_body
          (fun x => x >>> (IScalar.hcast .U32 SHIFT_BY))
          p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right_loop.body
    unfold unary_loop_body
    -- After unfolding, the impl body has `let i1 ← lift (hcast …); let i2 ← index; let i3 ← i2 >>> i1`,
    -- and `unary_loop_body` has `let i1 ← index; let vi ← (i1 >>> hcast …); …`.
    -- `lift v = .ok v` is definitional; reduce the leading `lift` bind.
    rfl
  rw [h_body_eq]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_unary_spec
      (fun x => x >>> (IScalar.hcast .U32 SHIFT_BY))
      (shift_right_per_elem_P SHIFT_BY)
      (fun x => shift_right_per_elem_spec SHIFT_BY hs x)
      vec)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P

/-! ## L1.10 — `reducing_from_i32_array_spec`

    The Vector.Portable.Arithmetic.reducing_from_i32_array impl is a
    16-iteration loop that reads `array[i] : I32`, runs L0.3
    `montgomery_reduce_element` (I32 → I16), and writes the result to
    `out.elements[i] : I16`. Differs from the unary family in that the
    input/output types differ — uses the `io_loop_*` macro family from
    `Util/PortableVector.lean`. -/

/-- Per-element predicate (guarded form): under the L0.3 precondition
    `|x| ≤ 3328 * 2^16`, the output satisfies the L1.10-shaped bound
    and Montgomery congruence. -/
private def reducing_per_elem_P (x : Std.I32) (y : Std.I16) : Prop :=
  x.val.natAbs ≤ 3328 * 2 ^ 16 →
    y.val.natAbs ≤ 3328 + 1665
    ∧ libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
        (y.val * (2 ^ 16 : Int)) x.val 3329

/-- Per-element Triple: `montgomery_reduce_element` is total (returns
    `.ok` unconditionally via `mont_reduce_element_eq_ok`); under the
    L0.3 precondition `|x| ≤ 3328 * 2^16`, the post-weakening to L1.10's
    Montgomery congruence uses the same identity as L1.4
    (`169 * 2^16 ≡ 1 (mod 3329)`). -/
private theorem reducing_per_elem_spec (x : Std.I32) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element x
    ⦃ ⇓ r => ⌜ reducing_per_elem_P x r ⌝ ⦄ := by
  -- Reduce to the .ok form via the totality theorem.
  have h_ok := mont_reduce_element_eq_ok x
  rw [show libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element x
        = .ok (mont_reduce_impl_value x) from h_ok]
  simp only [Std.Do.Triple, WP.wp]
  intro _
  show reducing_per_elem_P x (mont_reduce_impl_value x)
  unfold reducing_per_elem_P
  intro hb
  -- Now invoke L0.3 under hb to extract the post.
  have hT := montgomery_reduce_element_spec x hb
  rw [h_ok] at hT
  simp only [Std.Do.Triple, WP.wp] at hT
  have h_inner := hT trivial
  obtain ⟨h_weak, _h_tight, h_modq⟩ := h_inner
  refine ⟨h_weak, ?_⟩
  -- Convert L0.3's `modq_eq r.val (x.val * 169) 3329` to
  -- `modq_eq (r.val * 2^16) x.val 3329` (same algebra as L1.4).
  unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_modq ⊢
  have h_dvd : (3329 : Int) ∣ ((mont_reduce_impl_value x).val - x.val * 169) :=
    Int.dvd_of_emod_eq_zero h_modq
  have h_dvd2 : (3329 : Int)
                  ∣ ((mont_reduce_impl_value x).val * (2 ^ 16 : Int)
                      - x.val * 169 * (2 ^ 16 : Int)) := by
    have h_eq2 : ((mont_reduce_impl_value x).val * (2 ^ 16 : Int)
                    - x.val * 169 * (2 ^ 16 : Int))
                = ((mont_reduce_impl_value x).val - x.val * 169) * (2 ^ 16 : Int) := by ring
    rw [h_eq2]; exact Dvd.dvd.mul_right h_dvd _
  have h_inv : (169 : Int) * (2 ^ 16 : Int) - 1 = 3329 * 3327 := by decide
  have h_dvd3 : (3329 : Int)
                  ∣ (x.val * 169 * (2 ^ 16 : Int) - x.val) := by
    have h_eq3 : (x.val * 169 * (2 ^ 16 : Int) - x.val)
                = x.val * ((169 : Int) * (2 ^ 16 : Int) - 1) := by ring
    rw [h_eq3, h_inv]
    exact ⟨x.val * 3327, by ring⟩
  have h_dvd4 : (3329 : Int)
                  ∣ ((mont_reduce_impl_value x).val * (2 ^ 16 : Int) - x.val) := by
    have h_sum : ((mont_reduce_impl_value x).val * (2 ^ 16 : Int) - x.val)
                = ((mont_reduce_impl_value x).val * (2 ^ 16 : Int)
                    - x.val * 169 * (2 ^ 16 : Int))
                  + (x.val * 169 * (2 ^ 16 : Int) - x.val) := by ring
    rw [h_sum]; exact dvd_add h_dvd2 h_dvd3
  exact Int.emod_eq_zero_of_dvd h_dvd4

@[spec]
theorem reducing_from_i32_array_spec
    (array : Aeneas.Std.Slice Std.I32)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_len : array.val.length = 16)
    (hpre : ∀ i : Nat, i < 16 → (array.val[i]!).val.natAbs ≤ 3328 * 2 ^ 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array array out
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).val.natAbs ≤ 3328 + 1665
              ∧ libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
                  ((r.elements.val[i]!).val * (2 ^ 16 : Int))
                  (array.val[i]!).val 3329 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array_loop
  -- Bridge `reducing_from_i32_array_loop.body array` to `io_loop_body`.
  have h_body_eq :
      (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array_loop.body
          array p.1 p.2)
      = (fun (p : (CoreModels.core.ops.range.Range Std.Usize)
            × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) =>
        io_loop_body
          libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element
          array p.1 p.2) := by
    funext p
    rcases p with ⟨iter1, vec1⟩
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array_loop.body
    unfold io_loop_body
    rfl
  rw [h_body_eq]
  have h_len_ge : 16 ≤ array.val.length := by rw [h_len]
  apply Std.Do.Triple.of_entails_right _
    (elementwise_io_spec
      libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_reduce_element
      reducing_per_elem_P
      reducing_per_elem_spec
      array out h_len_ge)
  rw [PostCond.entails_noThrow]
  intro r hh j hj
  obtain ⟨rj, _h_eq, h_acc, h_P⟩ := hh j hj
  rw [h_acc]
  exact h_P (hpre j hj)

end libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element
/-! ### Extracted from FCTargets.lean (§vector_arith_hi). -/

namespace libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element
open libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L1 — chunk-level vector ops (10 theorems). -/

/-! ### L1.1 — `add` on 16-lane PortableVector chunks.

    Proof sketch:
    1. Bridge `add_pure_val_eq`: `(FieldElement.add_pure a b).val.val
       = (a.val.val + b.val.val) % 3329`. Mirrors `Canonical_add_pure`'s
       trace through the hacspec U32-widen + add + mod q + U16-narrow body.
    2. Bridge `lift_fe_add_pure_eq`: under the no-overflow bound on
       `a.val + b.val` (Int), the `lift_fe` of any i16 carrying that
       sum equals `FieldElement.add_pure (lift_fe a) (lift_fe b)`. Both
       sides reduce to `feOfZMod ((a.val + b.val : Int) : ZMod 3329)`
       via canonical-FE round-trip + `ZMod.natCast_mod`.
    3. Main: extract `add_spec` via `triple_exists_ok_fc` to get
       per-element `r[i].val = lhs[i].val + rhs[i].val ∧ bound`.
       Apply `triple_of_ok_fc` to close monadic shell. Reduce array
       equality to `List.ext_get!` + per-index, then apply Bridge 2. -/

/-- Local helper (mirrors `Spec.Pure.uscalar_rem_ok_U32` which is
    file-private). Establishes that U32 modular remainder by a non-zero
    divisor is always `.ok`, and exposes the underlying value. -/
theorem uscalar_rem_ok_U32_local (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Bridge lemma: the `.val.val` of `FieldElement.add_pure` is the
    impl's U16 modular-reduced sum. Proof structure mirrors
    `Canonical_add_pure` in `Spec.Pure.lean` — chain through the U32
    do-block via `add_equiv` + `uscalar_rem_ok_U32_local` + the U16
    narrowing cast. Pure-projection side lemma, NOT panic-freedom. -/
theorem add_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b).val.val
      = (a.val.val + b.val.val) % 3329 := by
  have hadd :
      hacspec_ml_kem.parameters.FieldElement.add a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.add at hadd
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hadd
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae hadd; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hadd
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local z m hmod_ne
    rw [hw_eq] at hadd; simp only [Aeneas.Std.bind_tc_ok] at hadd
    unfold hacspec_ml_kem.parameters.FieldElement.new at hadd
    simp at hadd
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hadd]
    show (Std.UScalar.cast .U16 w).val = (a.val.val + b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- Canonical-FE round-trip: a canonical `FieldElement` (i.e.
    `fe.val.val < 3329`) is recovered exactly by `feOfZMod ∘ zmodOfFE`.
    The forward direction `zmodOfFE_feOfZMod` lives in `Spec.lean`;
    this lemma is the canonicity-constrained converse, used to bridge
    `FieldElement.add_pure (lift_fe a) (lift_fe b)` (canonical by
    `Canonical_add_pure`) to its `feOfZMod`-image normal form. -/
theorem feOfZMod_zmodOfFE_of_canonical
    (fe : hacspec_ml_kem.parameters.FieldElement)
    (h : fe.val.val < 3329) :
    feOfZMod (zmodOfFE fe) = fe := by
  unfold feOfZMod zmodOfFE
  -- Goal: ⟨⟨BitVec.ofNat 16 ((fe.val.val : ZMod 3329)).val⟩⟩ = fe.
  -- ZMod.val_natCast_of_lt: ((fe.val.val : ZMod 3329)).val = fe.val.val
  -- given fe.val.val < 3329.
  have hzval : ((fe.val.val : ZMod 3329)).val = fe.val.val :=
    ZMod.val_natCast_of_lt h
  rw [hzval]
  -- Goal: ⟨⟨BitVec.ofNat 16 fe.val.val⟩⟩ = fe
  -- Both have the same .val.val (= fe.val.val < 65536), so the BV's match.
  have hfeval : fe.val.val < 2 ^ 16 := by
    have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
    omega
  have hfebv : BitVec.ofNat 16 fe.val.val = fe.val.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show fe.val.val % 2 ^ 16 = fe.val.bv.toNat
    rw [Nat.mod_eq_of_lt hfeval]
    rfl
  show ({ val := ⟨BitVec.ofNat 16 fe.val.val⟩ } :
          hacspec_ml_kem.parameters.FieldElement) = fe
  rw [hfebv]

/-- Helper: `(lift_fe x).val.val = ((x.val : Int) : ZMod 3329).val`. -/
theorem lift_fe_val_val (x : Std.I16) :
    (lift_fe x).val.val = (((x.val : Int) : ZMod 3329)).val := by
  unfold lift_fe i16_to_spec_fe_plain feOfZMod
  show (BitVec.ofNat 16 (((x.val : Int) : ZMod 3329)).val).toNat
        = (((x.val : Int) : ZMod 3329)).val
  rw [BitVec.toNat_ofNat]
  have h_lt : (((x.val : Int) : ZMod 3329)).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le (ZMod.val_lt _) (by decide)
  exact Nat.mod_eq_of_lt h_lt

/-- Bridge lemma: under the no-overflow bound on `a.val + b.val`
    (Int, |·| ≤ 2^15-1), any `r : Std.I16` carrying that sum lifts to
    `FieldElement.add_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val + b.val : Int) : ZMod 3329)`. The LHS is direct
    from `lift_fe`'s definition. The RHS uses `add_pure_val_eq` plus
    canonical round-trip — the result is canonical by
    `Canonical_add_pure`, so equals `feOfZMod (zmodOfFE …)`, and the
    `zmodOfFE`-projection reduces by `ZMod.natCast_mod` to the desired
    cast sum. -/
theorem lift_fe_add_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val + b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (lift_fe a) (lift_fe b) := by
  -- LHS reduction: lift_fe r = feOfZMod ((r.val : Int) : ZMod 3329)
  --                           = feOfZMod ((a.val + b.val : Int) : ZMod 3329).
  have h_lhs : lift_fe r
      = feOfZMod (((a.val + b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  -- RHS reduction: FieldElement.add_pure (lift_fe a) (lift_fe b)
  --                  = feOfZMod (zmodOfFE …) (canonical round-trip)
  --                  = feOfZMod ((a.val + b.val : Int) : ZMod 3329).
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure
      (lift_fe a) (lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- zmodOfFE s = ((a.val + b.val : Int) : ZMod 3329).
  have h_zmod_s : zmodOfFE s = (((a.val + b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    -- (s.val.val : ZMod 3329) with s.val.val = ((lift_fe a).val.val + (lift_fe b).val.val) % 3329
    rw [add_pure_val_eq]
    -- Goal: ((((lift_fe a).val.val + (lift_fe b).val.val) % 3329 : Nat) : ZMod 3329)
    --        = ((a.val + b.val : Int) : ZMod 3329).
    rw [ZMod.natCast_mod]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    -- Goal: (((a.val : Int) : ZMod 3329).val : ZMod 3329)
    --       + (((b.val : Int) : ZMod 3329).val : ZMod 3329)
    --     = ((a.val + b.val : Int) : ZMod 3329).
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.1 — `add` on 16-lane PortableVector chunks. -/
@[spec high]
theorem add_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val + (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.add lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_add_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec lhs rhs hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_add_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            ((Std.Array.make 16#usize (lhs.elements.val.map lift_fe)
              (by simp)).val[i]!)
            ((Std.Array.make 16#usize (rhs.elements.val.map lift_fe)
              (by simp)).val[i]!))
  -- 3. Show both lists have length 16 and per-index entries match.
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    -- LHS at i: lift_fe (r0.elements.val[i]).
    -- RHS at i: add_pure (lift_fe lhs[i]) (lift_fe rhs[i]).
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    -- Rewrite LHS.
    rw [List.getElem_map]
    -- Rewrite RHS.
    rw [List.getElem_map, List.getElem_range]
    -- Indexing into Std.Array.make.
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          ((lhs.elements.val.map lift_fe)[i]!)
          ((rhs.elements.val.map lift_fe)[i]!)
    -- Express `r0.elements.val[i]` as `r0.elements.val[i]!`
    -- (same value when i < length).
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    -- Express `(lhs.elements.val.map lift_fe)[i]!` as `lift_fe (lhs.val[i]!)`.
    have h_lhs_len : lhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
    have h_rhs_len : rhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
    have h_map_lhs :
        (lhs.elements.val.map lift_fe)[i]! = lift_fe (lhs.elements.val[i]!) := by
      have hi_lhs : i < lhs.elements.val.length := by rw [h_lhs_len]; exact hi
      rw [getElem!_pos (lhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_lhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos lhs.elements.val i hi_lhs]
    have h_map_rhs :
        (rhs.elements.val.map lift_fe)[i]! = lift_fe (rhs.elements.val[i]!) := by
      have hi_rhs : i < rhs.elements.val.length := by rw [h_rhs_len]; exact hi
      rw [getElem!_pos (rhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_rhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos rhs.elements.val i hi_rhs]
    rw [h_map_lhs, h_map_rhs]
    -- Apply the bridge lemma with the per-element value equation.
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_add_pure_eq
      (lhs.elements.val[i]!) (rhs.elements.val[i]!) (r0.elements.val[i]!)
      h_val

/-- Canonicity of `lift_fe`: every `feOfZMod`-image is canonical
    (its `.val.val < 3329`). Used by `lift_fe_sub_pure_eq` to discharge
    `sub_eq_ok`'s canonicity preconditions. Pure-projection side lemma. -/
theorem Canonical_lift_fe (x : Std.I16) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical (lift_fe x) := by
  unfold libcrux_iot_ml_kem.Spec.Pure.Canonical
  unfold lift_fe i16_to_spec_fe_plain feOfZMod
  -- Goal: (BitVec.ofNat 16 ((x.val : Int) : ZMod 3329).val).toNat
  --         < parameters.FIELD_MODULUS.val
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (BitVec.ofNat 16 (((x.val : Int) : ZMod 3329)).val).toNat < 3329
  rw [BitVec.toNat_ofNat]
  have h_lt : (((x.val : Int) : ZMod 3329)).val < 3329 := ZMod.val_lt _
  have h_le : (((x.val : Int) : ZMod 3329)).val < 2 ^ 16 :=
    Nat.lt_of_lt_of_le h_lt (by decide)
  rw [Nat.mod_eq_of_lt h_le]
  exact h_lt

/-- Every lane of `lift_poly self` is canonical (as a hacspec FE), since each
    lane is a `lift_fe` image and `lift_fe` produces canonical FEs via
    `feOfZMod`. Used by L6.1 FC close to feed `poly_barrett_reduce_pure_id_of_canonical`. -/
theorem lift_poly_lanes_canonical
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ∀ k : Nat, k < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical ((lift_poly self).val[k]!) := by
  intro k hk
  -- (lift_poly self).val = (List.range 256).map (fun j => lift_fe …).
  unfold lift_poly
  show libcrux_iot_ml_kem.Spec.Pure.Canonical
        (((List.range 256).map (fun j =>
            lift_fe (self.coefficients.val[j / 16]!).elements.val[j % 16]!))[k]!)
  have h_len : ((List.range 256).map (fun j =>
      lift_fe (self.coefficients.val[j / 16]!).elements.val[j % 16]!)).length = 256 := by
    simp
  rw [getElem!_pos _ k (by rw [h_len]; exact hk)]
  rw [List.getElem_map, List.getElem_range]
  exact Canonical_lift_fe _

/-- Bridge lemma: the `.val.val` of `FieldElement.sub_pure` (under
    canonicity of both operands) is the impl's U16 modular-reduced
    difference: `(a.val.val + 3329 - b.val.val) % 3329`. Mirrors
    `add_pure_val_eq`'s trace through the U32 do-block; the impl's
    `sub` body is `(self.val + q - other.val) % q` (`x + q` widens
    safely under `b` canonical, then `s - y ≥ 0` since
    `s = x + q ≥ q > y`, then `% q`, then narrow U16). -/
theorem sub_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.Spec.Pure.Canonical a)
    (hb : libcrux_iot_ml_kem.Spec.Pure.Canonical b) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a b).val.val
      = (a.val.val + 3329 - b.val.val) % 3329 := by
  have hsub :
      hacspec_ml_kem.parameters.FieldElement.sub a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_eq_ok a b ha hb
  have ha' : a.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at ha
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at ha; simpa using ha
  have hb' : b.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hb
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at hb; simpa using hb
  unfold hacspec_ml_kem.parameters.FieldElement.sub at hsub
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hsub
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae hsub; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hsub
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2 hsub; simp at hae2
      -- hae2 : y.val ≤ s.val ∧ s.val = u.val + y.val ∧ u.bv = s.bv - y.bv
      obtain ⟨_hyle, hsuy, _⟩ := hae2
      simp only [Aeneas.Std.bind_tc_ok] at hsub
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local u q hq_ne
      rw [hw_eq] at hsub; simp only [Aeneas.Std.bind_tc_ok] at hsub
      unfold hacspec_ml_kem.parameters.FieldElement.new at hsub
      simp at hsub
      have hwbnd : w.val < 3329 := by
        rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
      have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
        apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
        simp [Aeneas.Std.UScalarTy.numBits]; omega
      rw [← hsub]
      show (Std.UScalar.cast .U16 w).val = (a.val.val + 3329 - b.val.val) % 3329
      rw [hwcast, hwval, hqval]
      -- Goal: u.val % 3329 = (a.val.val + 3329 - b.val.val) % 3329
      -- From hsuy : s.val = u.val + y.val and hsval : s.val = x.val + q.val
      -- and hxval, hqval, hyval, hb', we get u.val = a.val.val + 3329 - b.val.val.
      have hu_eq : u.val = a.val.val + 3329 - b.val.val := by
        have h1 : s.val = u.val + y.val := hsuy
        rw [hsval, hxval, hqval, hyval] at h1
        omega
      rw [hu_eq]
    | fail e =>
      rw [hsy] at hae2; simp at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- Bridge lemma: the `.val.val` of `FieldElement.mul_pure` is the
    impl's U16 modular-reduced product: `(a.val.val * b.val.val) % 3329`.
    Mirrors `add_pure_val_eq`'s trace through the U32 do-block; the
    impl's `mul` body is `(self.val * other.val) % q` (`x * y` widens
    safely to U32 since `a.val * b.val ≤ (2^16-1)² < 2^32`, then `% q`,
    then narrow U16). Unconditional (no canonicity needed). -/
theorem mul_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b).val.val
      = (a.val.val * b.val.val) % 3329 := by
  have hmul :
      hacspec_ml_kem.parameters.FieldElement.mul a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.mul at hmul
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32_local z m hmod_ne
    rw [hw_eq] at hmul; simp only [Aeneas.Std.bind_tc_ok] at hmul
    unfold hacspec_ml_kem.parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val = (a.val.val * b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail _ =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Aeneas.Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- Bridge lemma: under the no-overflow bound on `a.val - b.val` (Int,
    |·| ≤ 2^15-1), any `r : Std.I16` carrying that difference lifts to
    `FieldElement.sub_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val - b.val : Int) : ZMod 3329)`. The RHS uses
    `sub_pure_val_eq` plus canonical round-trip — the result is
    canonical by `Canonical_sub_pure`, and the `zmodOfFE`-projection
    reduces the inner `(a.val.val + 3329 - b.val.val) % 3329` to
    `(a.val - b.val : Int) : ZMod 3329` via `ZMod.natCast_mod` plus
    integer reasoning. -/
theorem lift_fe_sub_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val - b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          (lift_fe a) (lift_fe b) := by
  have h_lhs : lift_fe r
      = feOfZMod (((a.val - b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_sub_pure
      (lift_fe a) (lift_fe b) (Canonical_lift_fe a) (Canonical_lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((a.val - b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [sub_pure_val_eq _ _ (Canonical_lift_fe a) (Canonical_lift_fe b)]
    -- Goal: (((lift_fe a).val.val + 3329 - (lift_fe b).val.val) % 3329 : Nat) : ZMod 3329
    --       = ((a.val - b.val : Int) : ZMod 3329)
    rw [ZMod.natCast_mod]
    -- Step: lift the Nat-subtraction expression through Nat→ZMod cast using
    -- a cast-equality. Since (lift_fe b).val.val ≤ (lift_fe a).val.val + 3329
    -- (b canonical), Nat subtraction agrees with Int subtraction.
    have hb_lt : (lift_fe b).val.val < 3329 := by
      have h_cb := Canonical_lift_fe b
      unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cb
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS at h_cb; simpa using h_cb
    have h_le : (lift_fe b).val.val ≤ (lift_fe a).val.val + 3329 := by omega
    -- (Nat-cast into ZMod) of the Nat sub equals (Int-cast into ZMod) of the Int sub.
    have h_zmod_eq :
        (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : ZMod 3329)
          = ((((lift_fe a).val.val : Int) + 3329 - ((lift_fe b).val.val : Int) : Int)
                : ZMod 3329) := by
      have h_int_eq :
          (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : Int)
            = ((lift_fe a).val.val : Int) + 3329 - ((lift_fe b).val.val : Int) := by
        omega
      have h_route :
          (((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : ZMod 3329)
            = ((((lift_fe a).val.val + 3329 - (lift_fe b).val.val : Nat) : Int)
                : ZMod 3329) := by
        rfl
      rw [h_route, h_int_eq]
    rw [h_zmod_eq]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    -- Goal after push_cast: ((a.val : Int) : ZMod 3329) + 0 - ((b.val : Int) : ZMod 3329)
    --                       = ((a.val - b.val : Int) : ZMod 3329)
    -- (push_cast collapses `(3329 : ZMod 3329)` to `0` via ZMod.natCast_self.)
    ring
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- Bridge lemma: under the no-overflow bound on `a.val * b.val` (Int,
    |·| ≤ 2^15-1), any `r : Std.I16` carrying that product lifts to
    `FieldElement.mul_pure (lift_fe a) (lift_fe b)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((a.val * b.val : Int) : ZMod 3329)`. The RHS uses
    `mul_pure_val_eq` plus canonical round-trip — the result is
    canonical by `Canonical_mul_pure`. Unconditional in canonicity. -/
theorem lift_fe_mul_pure_eq
    (a b r : Std.I16) (hrv : r.val = a.val * b.val) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe a) (lift_fe b) := by
  have h_lhs : lift_fe r
      = feOfZMod (((a.val * b.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe a) (lift_fe b) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe a) (lift_fe b)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((a.val * b.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [mul_pure_val_eq]
    rw [ZMod.natCast_mod]
    push_cast
    rw [lift_fe_val_val a, lift_fe_val_val b]
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.2 — `sub` on 16-lane PortableVector chunks. -/
@[spec high]
theorem sub_fc
    (lhs rhs : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      ((lhs.elements.val[i]!).val - (rhs.elements.val[i]!).val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.sub lhs rhs
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_sub_pure (lift_chunk lhs) (lift_chunk rhs) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.sub_spec lhs rhs hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_sub_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
            ((Std.Array.make 16#usize (lhs.elements.val.map lift_fe)
              (by simp)).val[i]!)
            ((Std.Array.make 16#usize (rhs.elements.val.map lift_fe)
              (by simp)).val[i]!))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          ((lhs.elements.val.map lift_fe)[i]!)
          ((rhs.elements.val.map lift_fe)[i]!)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_lhs_len : lhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length lhs
    have h_rhs_len : rhs.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length rhs
    have h_map_lhs :
        (lhs.elements.val.map lift_fe)[i]! = lift_fe (lhs.elements.val[i]!) := by
      have hi_lhs : i < lhs.elements.val.length := by rw [h_lhs_len]; exact hi
      rw [getElem!_pos (lhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_lhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos lhs.elements.val i hi_lhs]
    have h_map_rhs :
        (rhs.elements.val.map lift_fe)[i]! = lift_fe (rhs.elements.val[i]!) := by
      have hi_rhs : i < rhs.elements.val.length := by rw [h_rhs_len]; exact hi
      rw [getElem!_pos (rhs.elements.val.map lift_fe) i (by
        simp [List.length_map, h_rhs_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos rhs.elements.val i hi_rhs]
    rw [h_map_lhs, h_map_rhs]
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_sub_pure_eq
      (lhs.elements.val[i]!) (rhs.elements.val[i]!) (r0.elements.val[i]!)
      h_val

/-- Per-element bridge for `barrett_reduce_fc`: under `modq_eq r vec 3329`,
    the lift of `r` equals the spec-side `Spec.barrett_pure` applied to
    the lift of `vec`. Combines `lift_fe_eq_of_modq` with
    `barrett_pure_lift_fe` (which collapses the canonical round-trip on
    `lift_fe` images to identity). -/
theorem lift_fe_barrett_pure_eq
    (a r : Std.I16)
    (h : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq r.val a.val 3329) :
    lift_fe r = Spec.barrett_pure (lift_fe a) := by
  rw [barrett_pure_lift_fe]
  exact lift_fe_eq_of_modq r a h

/-- L1.3 — `barrett_reduce` on a chunk. The output lanes are the **centered
    Barrett representatives** `|r[i]| ≤ 1664 = ⌊3329/2⌋` (the tight bound the tail
    poly ops need for the L7 uniqueness guarantee). -/
@[spec high]
theorem barrett_reduce_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      (vec.elements.val[i]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce vec
    ⦃ ⇓ r => ⌜ (∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 1664)
                ∧ lift_chunk r = Spec.chunk_barrett_reduce_pure (lift_chunk vec) ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact: modq_eq r[i] vec[i] 3329 ∧ |r[i]| ≤ 1664.
  have h_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.barrett_reduce_spec vec hpre
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨?_, ?_⟩
  · -- Bound conjunct: the centered `r[i].natAbs ≤ 1664` from the per-element spec.
    intro i hi
    exact (h_per i hi).2
  · -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
    unfold lift_chunk Spec.chunk_barrett_reduce_pure
    apply Subtype.ext
    show r0.elements.val.map lift_fe
        = (List.range 16).map (fun i =>
            Spec.barrett_pure
              ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
                (by simp)).val[i]!))
    have h_r0_len : r0.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
    apply List.ext_getElem
    · simp [List.length_map, List.length_range, h_r0_len]
    · intro i hi1 hi2
      have hi : i < 16 := by
        have : i < (r0.elements.val.map lift_fe).length := hi1
        simp [List.length_map, h_r0_len] at this; exact this
      rw [List.getElem_map]
      rw [List.getElem_map, List.getElem_range]
      show lift_fe r0.elements.val[i]
        = Spec.barrett_pure ((vec.elements.val.map lift_fe)[i]!)
      have h_r0_get_eq : r0.elements.val[i]
          = r0.elements.val[i]! := by
        have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
        rw [getElem!_pos r0.elements.val i hi_r0]
      rw [h_r0_get_eq]
      have h_vec_len : vec.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
      have h_map_vec :
          (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
        have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
        rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
          simp [List.length_map, h_vec_len]; exact hi)]
        rw [List.getElem_map]
        rw [getElem!_pos vec.elements.val i hi_vec]
      rw [h_map_vec]
      obtain ⟨h_modq, _h_bnd⟩ := h_per i hi
      exact lift_fe_barrett_pure_eq
        (vec.elements.val[i]!) (r0.elements.val[i]!) h_modq

/-- Per-element bridge for `montgomery_multiply_by_constant_fc`: from the
    legacy L1.4 congruence `(r * 2^16) ≡ (a * c) (mod 3329)`, derive the
    FC equation
    `lift_fe_mont r = Spec.montgomery_multiply_fe_by_fer_pure (lift_fe a) (lift_fe_mont c)`.

    Algebra: the goal (after unfolding via `mmfbf_pure_lift_fe_lift_fe_mont`
    and `lift_fe_mont`/`i16_to_spec_fe_mont`) is the `ZMod 3329` equation
    `r * 169 = a * (c * 169) * 169`. From the legacy hypothesis
    `r * 2^16 = a * c` in `ZMod 3329`, multiply both sides by `169 * 169`
    and use the Montgomery-inversion identity `2^16 * 169 = 1` in `ZMod 3329`
    to collapse one factor on the LHS. -/
theorem lift_fe_mont_mmfbf_pure_eq
    (a c r : Std.I16)
    (h : (r.val * (2 ^ 16 : Int)) % 3329 = (a.val * c.val) % 3329) :
    lift_fe_mont r
      = Spec.montgomery_multiply_fe_by_fer_pure (lift_fe a) (lift_fe_mont c) := by
  rw [mmfbf_pure_lift_fe_lift_fe_mont]
  unfold lift_fe_mont i16_to_spec_fe_mont
  congr 1
  -- Goal: (r.val : ZMod 3329) * 169 = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169
  have h_modq : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
                  (r.val * (2 ^ 16 : Int)) (a.val * c.val) 3329 := by
    unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
    rw [Int.sub_emod, h]; simp
  have h_zmod : ((r.val * (2 ^ 16 : Int) : Int) : ZMod 3329)
              = ((a.val * c.val : Int) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h_modq
  push_cast at h_zmod
  -- After push_cast: h_zmod : (r.val : ZMod 3329) * 2285 = (a.val : ZMod 3329) * (c.val : ZMod 3329)
  -- (Lean reduces `2^16` to its canonical residue `2285` in ZMod 3329.)
  -- Goal: (r.val : ZMod 3329) * 169 = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169
  -- Normalize: 2285 * 169 = 386165 = 3329 * 116 + 1, so 2285 * 169 ≡ 1 (mod 3329).
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  calc (r.val : ZMod 3329) * 169
      = (r.val : ZMod 3329) * ((2285 : ZMod 3329) * 169) * 169 := by rw [h_inv]; ring
    _ = ((r.val : ZMod 3329) * 2285) * 169 * 169 := by ring
    _ = ((a.val : ZMod 3329) * (c.val : ZMod 3329)) * 169 * 169 := by rw [h_zmod]
    _ = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) * 169 := by ring

/-- Per-element bridge for the `montgomery_multiply_by_constant`-then-other
    chain used by `subtract_reduce_fc`: from the legacy L1.4 congruence
    `(r * 2^16) ≡ (a * c) (mod 3329)`, derive the *plain*-domain FC
    equation `lift_fe r = mul_pure (lift_fe a) (lift_fe_mont c)`.

    This is the sibling of `lift_fe_mont_mmfbf_pure_eq` for callers that
    feed the Mont-multiplied lane into a subsequent `sub`/`negate` (which
    consume `lift_fe`, not `lift_fe_mont`). The algebra reduces to the
    ZMod q equation `r = a * (c * 169)`, again using the Montgomery
    inversion identity `2^16 * 169 ≡ 1 (mod q)`. -/
theorem lift_fe_mont_mul_pure_eq
    (a c r : Std.I16)
    (h : (r.val * (2 ^ 16 : Int)) % 3329 = (a.val * c.val) % 3329) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe a) (lift_fe_mont c) := by
  -- Both sides equal `feOfZMod ((a.val : ZMod q) * ((c.val : ZMod q) * 169))`.
  -- LHS: `lift_fe r = feOfZMod ((r.val : ZMod q))`.
  -- RHS: round-trip via Canonical_mul_pure + mul_pure_val_eq.
  have h_lhs_zmod : (r.val : ZMod 3329) = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) := by
    have h_modq : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
                    (r.val * (2 ^ 16 : Int)) (a.val * c.val) 3329 := by
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
      rw [Int.sub_emod, h]; simp
    have h_zmod : ((r.val * (2 ^ 16 : Int) : Int) : ZMod 3329)
                = ((a.val * c.val : Int) : ZMod 3329) :=
      modq_eq_cast_zmod _ _ h_modq
    push_cast at h_zmod
    -- h_zmod : (r.val : ZMod 3329) * 2285 = (a.val : ZMod 3329) * (c.val : ZMod 3329)
    have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
    calc (r.val : ZMod 3329)
        = (r.val : ZMod 3329) * ((2285 : ZMod 3329) * 169) := by rw [h_inv]; ring
      _ = ((r.val : ZMod 3329) * 2285) * 169 := by ring
      _ = ((a.val : ZMod 3329) * (c.val : ZMod 3329)) * 169 := by rw [h_zmod]
      _ = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) := by ring
  have h_lhs : lift_fe r
      = feOfZMod ((a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169)) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [h_lhs_zmod]
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe a) (lift_fe_mont c) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe a) (lift_fe_mont c)
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169) := by
    unfold zmodOfFE
    rw [mul_pure_val_eq]
    rw [ZMod.natCast_mod]
    push_cast
    -- Goal: ((lift_fe a).val.val : ZMod 3329) * ((lift_fe_mont c).val.val : ZMod 3329)
    --     = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169)
    rw [lift_fe_val_val a]
    -- LHS: ((a.val : ZMod 3329)) * ((lift_fe_mont c).val.val : ZMod 3329) = ...
    rw [ZMod.natCast_zmod_val]
    -- Now need: (a.val : ZMod 3329) * ((lift_fe_mont c).val.val : ZMod 3329)
    --        = (a.val : ZMod 3329) * ((c.val : ZMod 3329) * 169)
    -- Suffices to show: ((lift_fe_mont c).val.val : ZMod 3329) = (c.val : ZMod 3329) * 169.
    have h_mont_val : ((lift_fe_mont c).val.val : ZMod 3329)
        = (c.val : ZMod 3329) * 169 := by
      unfold lift_fe_mont i16_to_spec_fe_mont
      -- (lift_fe_mont c).val.val = (feOfZMod ((c.val : ZMod 3329) * 169)).val.val.
      -- Apply ZMod.natCast_zmod_val + zmodOfFE_feOfZMod.
      have h_step : zmodOfFE (feOfZMod ((c.val : ZMod 3329) * 169))
          = (c.val : ZMod 3329) * 169 := zmodOfFE_feOfZMod _
      -- zmodOfFE x = (x.val.val : ZMod 3329) (by defn).
      have h_unfold : zmodOfFE (feOfZMod ((c.val : ZMod 3329) * 169))
          = ((feOfZMod ((c.val : ZMod 3329) * 169)).val.val : ZMod 3329) := rfl
      rw [h_unfold] at h_step
      exact h_step
    rw [h_mont_val]
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.4 — `montgomery_multiply_by_constant` on a chunk.
    Each lane: `vec[i] · c / R`. The lift uses `lift_chunk_mont` on
    the output (the result is in Mont domain). -/
@[spec high]
theorem montgomery_multiply_by_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hvec : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767)
    (hc : c.val.natAbs ≤ 1664) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk_mont r
                = Spec.chunk_montgomery_multiply_by_constant_pure
                    (lift_chunk vec) (lift_fe_mont c) ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact: |r[i]| ≤ 3328 ∧ (r[i]*2^16) ≡ vec[i]*c (mod 3329).
  have h_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec vec c hc
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe_mont equality.
  unfold lift_chunk_mont Spec.chunk_montgomery_multiply_by_constant_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe_mont
      = (List.range 16).map (fun i =>
          Spec.montgomery_multiply_fe_by_fer_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!)
            (lift_fe_mont c))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe_mont).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe_mont r0.elements.val[i]
      = Spec.montgomery_multiply_fe_by_fer_pure
          ((vec.elements.val.map lift_fe)[i]!) (lift_fe_mont c)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    obtain ⟨_h_bnd, h_mod⟩ := h_per i hi
    exact lift_fe_mont_mmfbf_pure_eq
      (vec.elements.val[i]!) c (r0.elements.val[i]!)
      h_mod

/-! ### L1.5 — `cond_subtract_3329` private loop machinery.

    The legacy `libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.cond_subtract_3329_spec` requires
    `0 ≤ vec[i] < 2*3329` as a precondition (it's load-bearing for the
    OUTER bound `r[i] < 3329`). The FC statement here uses NO
    precondition — we only need `lift_chunk r = lift_chunk vec`, i.e.
    mod-3329 equivalence per lane. The mod-3329 equivalence holds for
    BOTH branches of the conditional WITHOUT any precondition:

      - `vec[i] ≥ 3329` branch: `r[i] = wrapping_sub vec[i] 3329`.
        Since `vec[i] ∈ [3329, 32767]` (signed), `vec[i] - 3329 ∈ [0, 29438]`
        fits I16, so `r[i].val = vec[i].val - 3329 ≡ vec[i].val (mod 3329)`.
      - `vec[i] < 3329` branch: `r[i] = vec[i]`, trivially mod-3329 equivalent.

    Below we reproduce a stripped-down copy of the CondSubtract3329 loop machinery
    (private to FCTargets) yielding just the per-element disjunction. The
    full proof closely mirrors `Equivalence.CondSubtract3329.cond_step`; comments are
    abbreviated since the structure is verbatim.
-/

namespace CondSubtract3329FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

theorem triple_of_ok_l1
    {α : Type} {x : Result α} {v : α} {P : α → Prop}
    (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply, hp]

theorem of_pure_prop_holds_l1 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow,
    PredTrans.apply] at h
  exact h trivial

theorem pure_prop_holds_l1 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow,
    PredTrans.apply]
  intro _; exact h

/-- Per-element invariant for `cond_subtract_3329` (FCTargets-local copy
    of `Equivalence.CondSubtract3329.cond_inv`; precondition-free). -/
def cond_inv
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize →
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector →
    Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
        (((input.elements.val[j]!).val ≥ 3329 ∧
            (acc.elements.val[j]!) = Std.I16.wrapping_sub (input.elements.val[j]!) 3329#i16)
          ∨ ((input.elements.val[j]!).val < 3329 ∧
              acc.elements.val[j]! = input.elements.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.elements.val[j]! = input.elements.val[j]!))

def cond_step_post
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize)
        × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (cond_inv input iter'.start acc').holds
  | .done y => (cond_inv input 16#usize y).holds

set_option maxHeartbeats 8000000 in
theorem cond_step
    (input : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (cond_inv input k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ cond_step_post input k r ⌝ ⦄ := by
  obtain ⟨h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l1 h_inv
  have h_acc_len : acc.elements.length = 16 := PortableVector_elements_length acc
  have h_16 : (16#usize : Std.Usize).val = 16 := rfl
  unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · have hk_16 : k.val < 16 := by rw [h_16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    have h_idx :
        Aeneas.Std.Array.index_usize acc.elements k = .ok (acc.elements.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.elements k (by rw [h_acc_len]; exact hk_16)
    set xk : Std.I16 := acc.elements.val[k.val]! with hxk_def
    have h_acc_xk : acc.elements.val[k.val]! = input.elements.val[k.val]! :=
      h_acc_undone k.val (Nat.le_refl _) hk_16
    by_cases h_ge : xk.val ≥ 3329
    · have h_ge_lit : xk ≥ 3329#i16 := by
        change (3329#i16 : Std.I16).val ≤ xk.val
        have : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [this]; exact h_ge
      have h_wsub :
          CoreModels.core.num.I16.wrapping_sub xk 3329#i16
            = .ok (Std.I16.wrapping_sub xk 3329#i16) := by
        unfold CoreModels.core.num.I16.wrapping_sub
        unfold rust_primitives.arithmetic.wrapping_sub_i16
        rfl
      have h_upd :
          Aeneas.Std.Array.update acc.elements k (Std.I16.wrapping_sub xk 3329#i16)
            = .ok (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)) :=
        array_update_ok_eq acc.elements k _ (by rw [h_acc_len]; exact hk_16)
      have h_body :
          (do
            let (o, iter1) ←
              core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
            match o with
            | core.option.Option.None =>
                (Result.ok (ControlFlow.done acc) :
                  Result (ControlFlow
                    ((CoreModels.core.ops.range.Range Std.Usize)
                      × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
            | core.option.Option.Some i =>
              let i1 ← Aeneas.Std.Array.index_usize acc.elements i
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← CoreModels.core.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize),
               { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) })) := by
        conv_lhs =>
          rw [show
            (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
              = (CoreModels.core.iter.range.IteratorRange.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : CoreModels.core.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_pos h_ge_lit]
        rw [h_wsub]
        simp only [bind_tc_ok]
        rw [h_upd]
        rfl
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    { elements := acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16) }))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
                = (acc.elements)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
                = acc.elements.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
          have h_old := h_acc_done j hj_lt_k
          rcases h_old with ⟨h_in_ge, h_acc_eq⟩ | ⟨h_in_lt, h_acc_eq⟩
          · left; refine ⟨h_in_ge, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
          · right; refine ⟨h_in_lt, ?_⟩; rw [h_set_eq_val]; exact h_acc_eq
        · subst hj_eq_k
          have h_lt'' : k.val < acc.elements.length := by rw [h_acc_len]; exact hk_16
          have h_set_eq :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq acc.elements k k.val _ ⟨rfl, h_lt''⟩
          have h_set_eq_val :
              (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[k.val]!
                = Std.I16.wrapping_sub xk 3329#i16 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
          left
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; exact h_ge
          · rw [h_set_eq_val, ← h_acc_xk]
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16))[j]!
              = (acc.elements)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.elements k j _ h_ne
        have h_set_eq_val :
            (acc.elements.set k (Std.I16.wrapping_sub xk 3329#i16)).val[j]!
              = acc.elements.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        rw [h_set_eq_val]
        exact h_acc_undone j h_ge' hj_lt
    · have h_not_ge : ¬ (3329#i16 : Std.I16).val ≤ xk.val := by
        have h_eq : (3329#i16 : Std.I16).val = 3329 := by decide
        rw [h_eq]; exact h_ge
      have h_not_ge' : ¬ (xk ≥ 3329#i16) := h_not_ge
      have h_body :
          (do
            let (o, iter1) ←
              core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
            match o with
            | core.option.Option.None =>
                (Result.ok (ControlFlow.done acc) :
                  Result (ControlFlow
                    ((CoreModels.core.ops.range.Range Std.Usize)
                      × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
            | core.option.Option.Some i =>
              let i1 ← Aeneas.Std.Array.index_usize acc.elements i
              let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
              if i2 >= 3329#i16
              then
                let i3 ← CoreModels.core.num.I16.wrapping_sub i1 3329#i16
                let a ← Aeneas.Std.Array.update acc.elements i i3
                ok (cont (iter1, { elements := a }))
              else ok (cont (iter1, acc)))
          = .ok (cont
              (({ start := s, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize),
               acc)) := by
        conv_lhs =>
          rw [show
            (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
              = (CoreModels.core.iter.range.IteratorRange.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := 16#usize }
                    : CoreModels.core.ops.range.Range Std.Usize))
            from rfl]
        rw [h_iter_some]
        simp only [bind_tc_ok]
        rw [h_idx]
        simp only [bind_tc_ok]
        rw [show libcrux_secrets.traits.Declassify.Blanket.declassify xk = .ok xk from rfl]
        simp only [bind_tc_ok]
        rw [if_neg h_not_ge']
      apply triple_of_ok_l1 h_body
      show cond_step_post input k
            (.cont (({ start := s, «end» := 16#usize }
                       : CoreModels.core.ops.range.Range Std.Usize),
                    acc))
      unfold cond_step_post
      refine ⟨h_lt, rfl, hs_val, ?_⟩
      apply pure_prop_holds_l1
      refine ⟨?_, ?_⟩
      · intro j hj
        rw [hs_val] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · exact h_acc_done j hj_lt_k
        · subst hj_eq_k
          right
          refine ⟨?_, ?_⟩
          · rw [← h_acc_xk]; show xk.val < 3329
            push Not at h_ge; exact h_ge
          · exact h_acc_xk
      · intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ge' : k.val ≤ j := by omega
        exact h_acc_undone j h_ge' hj_lt
  · have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h_16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        (do
          let (o, iter1) ←
            core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize)
          match o with
          | core.option.Option.None =>
              (Result.ok (ControlFlow.done acc) :
                Result (ControlFlow
                  ((CoreModels.core.ops.range.Range Std.Usize)
                    × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
          | core.option.Option.Some i =>
            let i1 ← Aeneas.Std.Array.index_usize acc.elements i
            let i2 ← libcrux_secrets.traits.Declassify.Blanket.declassify i1
            if i2 >= 3329#i16
            then
              let i3 ← CoreModels.core.num.I16.wrapping_sub i1 3329#i16
              let a ← Aeneas.Std.Array.update acc.elements i i3
              ok (cont (iter1, { elements := a }))
            else ok (cont (iter1, acc)))
        = .ok (done acc) := by
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 16#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 16#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    apply triple_of_ok_l1 h_body
    show cond_step_post input k (.done acc)
    unfold cond_step_post
    apply pure_prop_holds_l1
    refine ⟨?_, ?_⟩
    · intro j hj
      apply h_acc_done j
      rw [hk_eq]; rw [h_16] at hj; exact hj
    · intro j hj_ge hj_lt
      apply h_acc_undone j _ hj_lt
      rw [hk_eq]; rw [h_16] at hj_ge; exact hj_ge

end CondSubtract3329FC

/-- L1.5 — `cond_subtract_3329` on a chunk.
    NO HACSPEC EQUIVALENT — the impl conditionally subtracts q to
    rebalance ranges; spec-side this is identity in `ZMod 3329`. The
    spec target we land against is the identity at the FE-array level.

    No precondition required: the mod-3329 equivalence holds in BOTH
    branches of the conditional unconditionally (see `CondSubtract3329FC` namespace
    above for the precondition-free invariant). -/
@[spec high]
theorem cond_subtract_3329_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
    ⦃ ⇓ r => ⌜ lift_chunk r = lift_chunk vec ⌝ ⦄ := by
  -- 1. Run the loop-spec machinery to get the per-element disjunction.
  have h_disj :
      ⦃ ⌜ True ⌝ ⦄
      libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329 vec
      ⦃ ⇓ r => ⌜ ∀ j : Nat, j < 16 →
                ((vec.elements.val[j]!).val ≥ 3329 ∧
                    (r.elements.val[j]!)
                      = Std.I16.wrapping_sub (vec.elements.val[j]!) 3329#i16)
                ∨ ((vec.elements.val[j]!).val < 3329 ∧
                    r.elements.val[j]! = vec.elements.val[j]!) ⌝ ⦄ := by
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329
    unfold libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop
    have h_field : libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
                    = (16#usize : Std.Usize) := by
      unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR; rfl
    rw [h_field]
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun (iter1, vec1) =>
          libcrux_iot_ml_kem.vector.portable.arithmetic.cond_subtract_3329_loop.body
            iter1 vec1)
        vec 0#usize 16#usize
        (CondSubtract3329FC.cond_inv vec)
        (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
        (CondSubtract3329FC.pure_prop_holds_l1 ⟨
          fun j hj => by
            have h0 : (0#usize : Std.Usize).val = 0 := rfl
            rw [h0] at hj; exact absurd hj (Nat.not_lt_zero j),
          fun _ _ _ => rfl⟩)
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r h
      obtain ⟨h_done, _h_undone⟩ := CondSubtract3329FC.of_pure_prop_holds_l1 h
      intro j hj
      exact h_done j (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hj)
    · -- Step lemma.
      intro acc k h_ge h_le hinv
      have h_step := CondSubtract3329FC.cond_step vec acc k h_le hinv
      apply Std.Do.Triple.of_entails_right _ h_step
      rw [PostCond.entails_noThrow]
      intro r hh
      rcases r with ⟨iter', acc'⟩ | y
      · have hP : CondSubtract3329FC.cond_step_post vec k (.cont (iter', acc')) := by
          simpa [Std.Do.SPred.down_pure] using hh
        simpa [CondSubtract3329FC.cond_step_post] using hP
      · have hP : CondSubtract3329FC.cond_step_post vec k (.done y) := by
          simpa [Std.Do.SPred.down_pure] using hh
        simpa [CondSubtract3329FC.cond_step_post] using hP
  -- 2. Apply h_disj and convert per-lane disjunction to lift_fe equality.
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_disj
  apply triple_of_ok_fc (v := r0) h_eq
  -- 3. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk
  apply Subtype.ext
  show r0.elements.val.map lift_fe = vec.elements.val.map lift_fe
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  have h_vec_len : vec.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
  apply List.ext_getElem
  · simp [List.length_map, h_r0_len, h_vec_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map, List.getElem_map]
    -- Goal: lift_fe r0.elements.val[i] = lift_fe vec.elements.val[i].
    have h_r0_get : r0.elements.val[i] = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    have h_vec_get : vec.elements.val[i] = vec.elements.val[i]! := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_r0_get, h_vec_get]
    -- Apply per-lane disjunction.
    rcases h_per i hi with ⟨h_ge, h_eq_lane⟩ | ⟨h_lt, h_eq_lane⟩
    · -- ≥ 3329 branch: r0[i] = wrapping_sub vec[i] 3329, derive mod-3329 equality.
      rw [h_eq_lane]
      -- Goal: lift_fe (wrapping_sub vec[i] 3329) = lift_fe vec[i].
      set xi : Std.I16 := vec.elements.val[i]! with hxi
      -- Use modq_eq on (wrapping_sub xi 3329).val vs xi.val.
      apply lift_fe_eq_of_modq
      -- Need: modq_eq (wrapping_sub xi 3329).val xi.val 3329.
      -- (wrapping_sub xi 3329).val = bmod (xi.val - 3329) (2^16). Since
      -- xi.val ≥ 3329 and xi.val < 2^15, we have xi.val - 3329 ∈ [0, 2^15 - 3329],
      -- which is in I16 range, so bmod = xi.val - 3329.
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
      rw [Std.I16.wrapping_sub_val_eq]
      have hxi_ub : xi.val < 2^15 := by
        have h := xi.hBounds
        simp [Aeneas.Std.IScalarTy.numBits] at h
        omega
      have h3329 : (3329#i16 : Std.I16).val = 3329 := by decide
      rw [h3329]
      have hxi_lb_diff : (-(2:Int)^(16-1)) ≤ xi.val - 3329 := by
        have h1 : (3329 : Int) ≤ xi.val := h_ge
        have h2 : -(2:Int)^(16-1) ≤ 0 := by decide
        have h3 : (0 : Int) ≤ xi.val - 3329 := by omega
        omega
      have hxi_ub_diff : xi.val - 3329 < (2:Int)^(16-1) := by
        have h1 : xi.val < (2:Int)^15 := by exact_mod_cast hxi_ub
        have h2 : (2:Int)^(16-1) = (2:Int)^15 := by decide
        omega
      rw [Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
            hxi_lb_diff hxi_ub_diff]
      -- Goal: (xi.val - 3329 - xi.val) % 3329 = 0.
      have : xi.val - 3329 - xi.val = -3329 := by ring
      rw [this]
      decide
    · -- < 3329 branch: r0[i] = vec[i], trivially mod-3329 equivalent.
      rw [h_eq_lane]

/-- Local helper (mirrors `Spec.Pure.uscalar_rem_ok_U16` which is
    file-private). Establishes that U16 modular remainder by a non-zero
    divisor is always `.ok`, and exposes the underlying value. Needed
    by `neg_pure_val_eq`, whose `% q` step is at U16 width (no widening). -/
theorem uscalar_rem_ok_U16_local (z m : Std.U16) (hm : m.val ≠ 0) :
    ∃ w : Std.U16, (z % m : Result Std.U16) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U16) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

/-- Bridge lemma: under canonicity of the operand, the `.val.val` of
    `FieldElement.neg_pure` is the impl's U16 modular-reduced negation
    `(3329 - a.val.val) % 3329`. Mirrors `sub_pure_val_eq`'s trace, but
    the impl's `neg` body is `(q - self.val) % q` operated entirely at
    U16 width (NO widening to U32); panic-impossibility of `q - self.val`
    is precisely `Canonical a` (i.e. `a.val.val < q`). -/
theorem neg_pure_val_eq
    (a : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.Spec.Pure.Canonical a) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure a).val.val
      = (3329 - a.val.val) % 3329 := by
  have hneg :
      hacspec_ml_kem.parameters.FieldElement.neg a
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure a) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_eq_ok a ha
  have ha' : a.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at ha
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at ha; simpa using ha
  unfold hacspec_ml_kem.parameters.FieldElement.neg at hneg
  have hA := a.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA
  have hqval : (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16).val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.sub_equiv (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16) a.val
  cases hqa :
      ((hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16) - a.val : Result Std.U16) with
  | ok i =>
    rw [hqa] at hae hneg; simp at hae
    obtain ⟨_hale, hival, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hneg
    have hq_ne : (hacspec_ml_kem.parameters.FIELD_MODULUS : Std.U16).val ≠ 0 := by
      rw [hqval]; decide
    obtain ⟨w, hw_eq, hwval⟩ :=
      uscalar_rem_ok_U16_local i hacspec_ml_kem.parameters.FIELD_MODULUS hq_ne
    rw [hw_eq] at hneg; simp only [Aeneas.Std.bind_tc_ok] at hneg
    unfold hacspec_ml_kem.parameters.FieldElement.new at hneg
    simp at hneg
    rw [← hneg]
    -- Goal: w.val = (3329 - a.val.val) % 3329.
    rw [hwval, hqval]
    -- Goal: i.val % 3329 = (3329 - a.val.val) % 3329.
    -- From hival : i.val + a.val.val = 3329, so i.val = 3329 - a.val.val.
    have hi_eq : i.val = 3329 - a.val.val := by
      rw [hqval] at hival; omega
    rw [hi_eq]
  | fail e =>
    rw [hqa] at hae; simp at hae
    rw [hqval] at hae
    omega
  | div => rw [hqa] at hae; exact hae.elim

/-- Bridge lemma: under the no-overflow bound on `-a.val` (i.e.
    `a.val.natAbs ≤ 2^15 - 1`, equivalently `a.val ∈ [-(2^15 - 1), 2^15 - 1]`,
    which EXCLUDES the boundary `-2^15`), any `r : Std.I16` carrying that
    negation lifts to `FieldElement.neg_pure (lift_fe a)`.

    Pure-projection content: both sides reduce to
    `feOfZMod ((-a.val : Int) : ZMod 3329)`. The LHS is direct from
    `lift_fe`'s definition. The RHS uses `neg_pure_val_eq` plus canonical
    round-trip — the result is canonical by `Canonical_neg_pure` (which
    needs `Canonical_lift_fe`), and the `zmodOfFE`-projection reduces
    the inner `(3329 - (lift_fe a).val.val) % 3329` to `((-a.val : Int)
    : ZMod 3329)` via `ZMod.natCast_mod` plus integer reasoning.

    Boundary excluded: at `a.val = -2^15 = -32768`, both sides would
    diverge — `Int.bmod (-a.val) 2^16 = -32768`, but
    `(-((-32768 : Int) : ZMod 3329)).val = 2807 ≠ 522`. The `hbnd`
    precondition rules out this case. -/
theorem lift_fe_neg_pure_eq
    (a r : Std.I16)
    (hbnd : a.val.natAbs ≤ 2^15 - 1)
    (hrv : r.val = -a.val) :
    lift_fe r
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe a) := by
  -- LHS reduction.
  have h_lhs : lift_fe r = feOfZMod (((-a.val : Int)) : ZMod 3329) := by
    unfold lift_fe i16_to_spec_fe_plain
    rw [hrv]
  -- RHS reduction.
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure (lift_fe a) with hs_def
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_neg_pure
      (lift_fe a) (Canonical_lift_fe a)
    show s.val.val < 3329
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  have h_zmod_s : zmodOfFE s = (((-a.val : Int)) : ZMod 3329) := by
    unfold zmodOfFE
    rw [neg_pure_val_eq _ (Canonical_lift_fe a)]
    -- Goal: ((3329 - (lift_fe a).val.val) % 3329 : Nat) : ZMod 3329
    --       = ((-a.val : Int) : ZMod 3329)
    rw [ZMod.natCast_mod]
    -- (lift_fe a).val.val < 3329, so 3329 - (lift_fe a).val.val ≤ 3329.
    have ha_lt : (lift_fe a).val.val < 3329 := by
      have h_ca := Canonical_lift_fe a
      unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_ca
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS at h_ca; simpa using h_ca
    -- Cast the Nat-sub through Int-sub: 3329 - (lift_fe a).val.val (Nat) =
    -- 3329 - (lift_fe a).val.val (Int) since the former is ≥ 0.
    have h_zmod_eq :
        (((3329 - (lift_fe a).val.val : Nat)) : ZMod 3329)
          = ((((3329 : Int) - ((lift_fe a).val.val : Int)) : Int) : ZMod 3329) := by
      have h_int_eq :
          (((3329 - (lift_fe a).val.val : Nat)) : Int)
            = (3329 : Int) - ((lift_fe a).val.val : Int) := by
        omega
      have h_route :
          (((3329 - (lift_fe a).val.val : Nat)) : ZMod 3329)
            = ((((3329 - (lift_fe a).val.val : Nat)) : Int) : ZMod 3329) := by
        rfl
      rw [h_route, h_int_eq]
    rw [h_zmod_eq]
    push_cast
    rw [lift_fe_val_val a]
    rw [ZMod.natCast_zmod_val]
    -- After push_cast: 0 - ((a.val : Int) : ZMod 3329) = ((-a.val : Int) : ZMod 3329)
    -- (3329 collapses to 0 via ZMod.natCast_self).
    ring
  rw [h_lhs, ← h_round_trip, h_zmod_s]

/-- L1.6 — `negate` on a chunk.

    **Precondition** `hpre` mirrors the upstream F* spec `negate_pre`
    from `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:684`
    (`forall i. is_intb (pow2 15 - 1) (v ${vec}[i])`), i.e. every lane
    is strictly within `[-(2^15 - 1), 2^15 - 1]` — equivalently the
    natAbs is `≤ 2^15 - 1`.

    **Why this is the canonical bound**: the impl's `negate` is
    pointwise `core.num.I16.wrapping_neg`, which lowers to
    `wrapping_sub 0 vec[i]`. The lane-level value reduces to
    `Int.bmod (-vec[i].val) 2^16`. For the FC equation
    `(r[i].val : ZMod 3329) = -(vec[i].val : ZMod 3329)` to hold we
    need `Int.bmod (-vec[i].val) 2^16 = -vec[i].val` (no boundary flip);
    `bmod_pow2_eq_of_inBounds'` requires `-vec[i].val ∈ [-2^15, 2^15)`,
    i.e. `vec[i].val ∈ (-2^15, 2^15]`. Combined with the impl's
    `vec[i].val ∈ [-2^15, 2^15)` carrier we get `vec[i].val.natAbs
    ≤ 2^15 - 1` — exactly `negate_pre`. The excluded value `-2^15`
    would yield a real divergence: `2^16 mod 3329 = 2645 ≠ 0`, so
    bmod's two-valued identification of `-2^15` and `2^15` does NOT
    collapse mod 3329.

    **Callers**: every real caller of `negate` (in
    `serialize::compress_then_serialize_*`) feeds inputs that are
    barrett-reduced (so `|x| ≤ 1664 < 2^15 - 1`) or subtracted from
    barrett-reduced operands (so `|x| ≤ 6656 < 2^15 - 1`); the bound
    is trivially satisfied at every call site. -/
@[spec high]
theorem negate_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hpre : ∀ i : Nat, i < 16 →
      (vec.elements.val[i]!).val.natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.negate vec
    ⦃ ⇓ r => ⌜ lift_chunk r = Spec.chunk_neg_pure (lift_chunk vec) ⌝ ⦄ := by
  -- 1. Extract per-element BV-equation from legacy `negate_spec`.
  have h_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.negate_spec vec
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_neg_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
          ((vec.elements.val.map lift_fe)[i]!)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    -- 3. Convert per-lane BV-equation to val-equation, then apply bridge.
    set xi : Std.I16 := vec.elements.val[i]! with hxi
    set ri : Std.I16 := r0.elements.val[i]! with hri
    -- From negate_spec: ri.bv = -xi.bv.
    have h_bv : ri.bv = -xi.bv := h_per i hi
    -- From this BV equality + I16.bv_toInt_eq: ri.val = (-xi.bv).toInt.
    -- The cleanest route: bridge through `Std.I16.wrapping_sub 0 xi`,
    -- whose `.bv = 0 - xi.bv = -xi.bv` matches `ri.bv`, then use
    -- `wrapping_sub_val_eq` to get `Int.bmod (0 - xi.val) (2^16)`.
    have h_wsub_bv : (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv = -xi.bv := by
      rw [Aeneas.Std.I16.wrapping_sub_bv_eq]
      simp only [show (0#i16 : Std.I16).bv = (0 : BitVec 16) from rfl]
      exact BitVec.zero_sub xi.bv
    -- Convert BV equality to val equality: ri.val = (-xi.bv).toInt =
    -- (Std.I16.wrapping_sub 0 xi).val = Int.bmod (0 - xi.val) (2^16) = -xi.val
    -- (last step under hpre via bmod_pow2_eq_of_inBounds').
    have h_ri_val : ri.val = -xi.val := by
      have h_step1 : ri.val = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val := by
        have h_toInt :
            (ri.bv).toInt = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt := by
          rw [h_bv, h_wsub_bv]
        have h_lhs : (ri.bv).toInt = ri.val := Aeneas.Std.I16.bv_toInt_eq ri
        have h_rhs : (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt
            = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val :=
          Aeneas.Std.I16.bv_toInt_eq _
        rw [h_lhs, h_rhs] at h_toInt
        exact h_toInt
      rw [h_step1]
      rw [Aeneas.Std.I16.wrapping_sub_val_eq]
      have h0 : (0#i16 : Std.I16).val = 0 := by decide
      rw [h0]
      -- Goal: Int.bmod (0 - xi.val) (2^16) = -xi.val.
      have h_diff : (0 : Int) - xi.val = -xi.val := by ring
      rw [h_diff]
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
        have h_pow : -((2 : Int) ^ (16 - 1)) = -(2^15 : Int) := by decide
        rw [h_pow]
        omega
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
        have h_pow : ((2 : Int) ^ (16 - 1)) = (2^15 : Int) := by decide
        rw [h_pow]
        omega
    -- 4. Apply the bridge lemma.
    have h_abs : xi.val.natAbs ≤ 2^15 - 1 := hpre i hi
    exact lift_fe_neg_pure_eq xi ri h_abs h_ri_val

/-- L1.7 — `multiply_by_constant` (plain) on a chunk.

    **Precondition note**: the legacy `libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.multiply_by_constant_spec`
    requires the per-element product bound `|vec[i] * c| ≤ 2^15 - 1`.
    The aggregate `|vec[i]| ≤ 32767 ∧ |c| ≤ 1664` does NOT imply that
    product bound (it allows `32767 * 1664 ≫ 32767`), so we carry
    `hpre_prod` as an additional caller obligation. Callers downstream
    in the NTT pipeline reliably satisfy this — Mont-domain inputs are
    already `|vec[i]| ≤ 3328 + 1665` after a `montgomery_reduce`, and
    the product with `|c| ≤ 1664` is well inside i32 with the per-lane
    bound easily verified. The `hvec` / `hc` are kept for API
    consistency with `montgomery_multiply_by_constant_fc`. -/
@[spec high]
theorem multiply_by_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16)
    (hvec : ∀ i : Nat, i < 16 → (vec.elements.val[i]!).val.natAbs ≤ 32767)
    (hc : c.val.natAbs ≤ 1664)
    (hpre_prod : ∀ i : Nat, i < 16 →
      ((vec.elements.val[i]!).val * c.val : Int).natAbs ≤ 2^15 - 1) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant vec c
    ⦃ ⇓ r => ⌜ lift_chunk r
                = Spec.chunk_multiply_by_constant_pure
                    (lift_chunk vec) (lift_fe c) ⌝ ⦄ := by
  -- 1. Extract per-element value-equation from legacy bounds Triple.
  have h_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.multiply_by_constant_spec vec c hpre_prod
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  -- 2. Reduce array equality to list equality, then to per-index lift_fe equality.
  unfold lift_chunk Spec.chunk_multiply_by_constant_pure
  apply Subtype.ext
  show r0.elements.val.map lift_fe
      = (List.range 16).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((Std.Array.make 16#usize (vec.elements.val.map lift_fe)
              (by simp)).val[i]!)
            (lift_fe c))
  have h_r0_len : r0.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, h_r0_len]
  · intro i hi1 hi2
    have hi : i < 16 := by
      have : i < (r0.elements.val.map lift_fe).length := hi1
      simp [List.length_map, h_r0_len] at this; exact this
    rw [List.getElem_map]
    rw [List.getElem_map, List.getElem_range]
    show lift_fe r0.elements.val[i]
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((vec.elements.val.map lift_fe)[i]!) (lift_fe c)
    have h_r0_get_eq : r0.elements.val[i]
        = r0.elements.val[i]! := by
      have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
      rw [getElem!_pos r0.elements.val i hi_r0]
    rw [h_r0_get_eq]
    have h_vec_len : vec.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length vec
    have h_map_vec :
        (vec.elements.val.map lift_fe)[i]! = lift_fe (vec.elements.val[i]!) := by
      have hi_vec : i < vec.elements.val.length := by rw [h_vec_len]; exact hi
      rw [getElem!_pos (vec.elements.val.map lift_fe) i (by
        simp [List.length_map, h_vec_len]; exact hi)]
      rw [List.getElem_map]
      rw [getElem!_pos vec.elements.val i hi_vec]
    rw [h_map_vec]
    obtain ⟨h_val, _h_bnd⟩ := h_per i hi
    exact lift_fe_mul_pure_eq
      (vec.elements.val[i]!) c (r0.elements.val[i]!)
      h_val

/-- L1.8 — `bitwise_and_with_constant` on a chunk.

    the upstream F* spec
    `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:720`
    (`bitwise_and_with_constant_constant_post`), the canonical FC
    statement for this bit-level op is the per-lane BV-equality
    `result == map_array (fun x -> x &. c) vec`. This is the
    "FE-level lift" formulation is NOT meaningful here because
    `lift_fe` projects through `mod 3329`, discarding the bit pattern
    that `&.` depends on (the FE equation would require lift_chunk to
    preserve bit info, which it cannot without losing the ring
    semantics). The canonical FC equation is therefore at the I16-BV
    level — equality-form, equality-strong, just at the correct
    abstraction layer for a bit-level op.

    The §0.5 `Spec.chunk_bitwise_and_with_constant_pure` stub remains
    in place as documentation but is NOT used in the FC equation
    below (the canonical post is the upstream F*-aligned BV-equality). -/
@[spec high]
theorem bitwise_and_with_constant_fc
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (c : Std.I16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.bitwise_and_with_constant vec c
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv = (vec.elements.val[i]!).bv &&& c.bv ⌝ ⦄ :=
  libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.bitwise_and_with_constant_spec vec c

/-- L1.9 — `shift_right` on a chunk.

    the upstream F* spec
    `libcrux-ml-kem-proofs/libcrux-ml-kem/src/vector/traits.rs:731`
    (`shift_right_post`), the canonical FC statement for this bit-level
    op is the per-lane BV-equality
    `result == map_array (fun x -> x >>! shift_by) vec` (where `>>!`
    is signed right shift on i16). Same reasoning as `bitwise_and_with_constant_fc`:
    the I16-BV level is the correct abstraction; lift_fe would discard
    the bit pattern that `>>!` depends on.

    The legacy `libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.shift_right_spec` uses `0 ≤ SHIFT_BY.val ∧
    SHIFT_BY.val < 16` (the same range as the upstream F* `requires
    SHIFT_BY >= 0 && SHIFT_BY < 16` on the trait). We adopt the same
    precondition shape. -/
@[spec high]
theorem shift_right_fc
    (SHIFT_BY : Std.I32)
    (vec : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hs : 0 ≤ SHIFT_BY.val ∧ SHIFT_BY.val < 16) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.shift_right SHIFT_BY vec
    ⦃ ⇓ r => ⌜ ∀ i : Nat, i < 16 →
                (r.elements.val[i]!).bv =
                  (vec.elements.val[i]!).bv.sshiftRight SHIFT_BY.val.toNat ⌝ ⦄ :=
  libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.shift_right_spec SHIFT_BY hs vec

/-- Per-element bridge for `reducing_from_i32_array_fc`: from the legacy
    L1.10 congruence `(r * 2^16) ≡ x (mod 3329)`, derive the FC equation
    `lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int x.val)`.

    Algebra: the goal (after unfolding via `mont_reduce_pure_lift_fe_int`
    and `lift_fe_mont`/`i16_to_spec_fe_mont`) is the `ZMod 3329` equation
    `r * 169 = x * 169 * 169`. From the legacy hypothesis `r * 2^16 = x`
    in `ZMod 3329`, multiply both sides by `169 * 169` and use the
    Montgomery-inversion identity `2^16 * 169 ≡ 1 (mod 3329)`
    (numerically `2285 * 169 = 1` in `ZMod 3329`) to collapse one factor
    on the LHS. -/
theorem lift_fe_mont_mont_reduce_pure_eq
    (x : Std.I32) (r : Std.I16)
    (h : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
            (r.val * (2 ^ 16 : Int)) x.val 3329) :
    lift_fe_mont r = Spec.mont_reduce_pure (lift_fe_int x.val) := by
  rw [mont_reduce_pure_lift_fe_int]
  unfold lift_fe_mont i16_to_spec_fe_mont
  congr 1
  -- Goal: (r.val : ZMod 3329) * 169 = (x.val : ZMod 3329) * 169 * 169
  have h_zmod : ((r.val * (2 ^ 16 : Int) : Int) : ZMod 3329)
              = ((x.val : Int) : ZMod 3329) :=
    modq_eq_cast_zmod _ _ h
  push_cast at h_zmod
  -- h_zmod : (r.val : ZMod 3329) * 2285 = (x.val : ZMod 3329)
  -- Goal: (r.val : ZMod 3329) * 169 = (x.val : ZMod 3329) * 169 * 169
  have h_inv : ((2285 : ZMod 3329)) * 169 = 1 := by decide
  calc (r.val : ZMod 3329) * 169
      = (r.val : ZMod 3329) * ((2285 : ZMod 3329) * 169) * 169 := by rw [h_inv]; ring
    _ = ((r.val : ZMod 3329) * 2285) * 169 * 169 := by ring
    _ = (x.val : ZMod 3329) * 169 * 169 := by rw [h_zmod]

/-- L1.10 — `reducing_from_i32_array` on a chunk.
    Composes `montgomery_reduce_element` across 16 lanes.

    POST additionally exposes the per-lane I16 bound `|r[i]| ≤ 4993`
    (= 3328 + 1665) coming from `libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.reducing_from_i32_array_spec`.
    Used by L6.7 to thread a bound through to L7.1 Stage 3, where
    `add_standard_error_reduce_fc` consumes `|self[k][ℓ]| ≤ 32767`
    via `4993 ≤ 32767`. -/
@[spec high]
theorem reducing_from_i32_array_fc
    (array : Slice Std.I32)
    (out : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hlen : array.length = 16)
    (hbound : ∀ i : Nat, i < 16 →
      (array.val[i]!).val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array array out
    ⦃ ⇓ r => ⌜ lift_chunk_mont r = Spec.chunk_reducing_from_i32_array_pure array
                ∧ (∀ i : Nat, i < 16 → (r.elements.val[i]!).val.natAbs ≤ 4993) ⌝ ⦄ := by
  -- 1. Extract per-element legacy fact:
  --    |r[i]| ≤ 3328+1665 ∧ (r[i]*2^16) ≡ array[i] (mod 3329).
  have hpre' : ∀ i : Nat, i < 16 → (array.val[i]!).val.natAbs ≤ 3328 * 2 ^ 16 := by
    intro i hi
    have h := hbound i hi
    rwa [show (3328 * 2 ^ 16 : Nat) = 2 ^ 16 * 3328 from by decide]
  have hlen' : array.val.length = 16 := hlen
  have h_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.reducing_from_i32_array_spec array out hlen' hpre'
  obtain ⟨r0, h_eq, h_per⟩ := triple_exists_ok_fc h_legacy
  apply triple_of_ok_fc (v := r0) h_eq
  refine ⟨?_, ?_⟩
  · -- (a) Existing FC equation: lift_chunk_mont r = Spec.chunk_reducing_from_i32_array_pure array.
    -- Reduce array equality to list equality, then to per-index lift_fe_mont equality.
    unfold lift_chunk_mont Spec.chunk_reducing_from_i32_array_pure
    apply Subtype.ext
    show r0.elements.val.map lift_fe_mont
        = (List.range 16).map (fun i =>
            Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val))
    have h_r0_len : r0.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length r0
    apply List.ext_getElem
    · simp [List.length_map, List.length_range, h_r0_len]
    · intro i hi1 hi2
      have hi : i < 16 := by
        have : i < (r0.elements.val.map lift_fe_mont).length := hi1
        simp [List.length_map, h_r0_len] at this; exact this
      rw [List.getElem_map]
      rw [List.getElem_map, List.getElem_range]
      show lift_fe_mont r0.elements.val[i]
        = Spec.mont_reduce_pure (lift_fe_int (array.val[i]!).val)
      have h_r0_get_eq : r0.elements.val[i]
          = r0.elements.val[i]! := by
        have hi_r0 : i < r0.elements.val.length := by rw [h_r0_len]; exact hi
        rw [getElem!_pos r0.elements.val i hi_r0]
      rw [h_r0_get_eq]
      obtain ⟨_h_bnd, h_modq⟩ := h_per i hi
      exact lift_fe_mont_mont_reduce_pure_eq
        (array.val[i]!) (r0.elements.val[i]!) h_modq
  · -- (b) Per-lane I16 bound `|r[i]| ≤ 4993` from the legacy spec's first conjunct.
    intro i hi
    exact (h_per i hi).1


end libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element