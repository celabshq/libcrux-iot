/-
  # `Polynomial/PolyOpsFc.lean` — FC theorems for §L6.{2,4,5,6,7}.

  Houses reducing_from_i32_array_fc, subtract_reduce_fc, and the
  add_*_error_reduce_fc family. Lives separately from PolyOps.lean
  (and from PolyOpsFcBarrett.lean which holds §L6.1) to keep the
  layering acyclic.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Spec.Pure
import LibcruxIotMlKem.Spec.ModularArith
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Extraction.Funs
import HacspecMlKem.Extraction.Funs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


/-! ### Extracted from FCTargets.lean (§poly_l6_rest). -/

namespace libcrux_iot_ml_kem.Polynomial.PolyOpsFc
open libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

namespace ReducingFromI32ArrayFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator (the mutable `b` poly). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `subtract_reduce_fc`.
    * (a) Chunks `j < k`: FC equation `lift_chunk acc[j] = chunk_subtract_reduce_pure
          (lift_chunk self[j]) (lift_chunk b_init[j])`.
    * (b) Chunks `k ≤ j < 16`: `acc[j] = b_init[j]` (unchanged).
    * (c) Chunks `j < k`: per-lane `|acc[j][m]| ≤ 1664` — the Barrett-reduced
          output bound, carried so the top-level L7.4 POST can state the impl
          output in canonical form (no output `lift`). -/
def inv
    (self b_init : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.coefficients.val[j]!)
        = Spec.chunk_subtract_reduce_pure
            (lift_chunk (self.coefficients.val[j]!))
            (lift_chunk (b_init.coefficients.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = b_init.coefficients.val[j]!)
    ∧ (∀ j : Nat, j < k.val → ∀ m : Nat, m < 16 →
        ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (self b_init : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv self b_init iter'.start acc').holds
  | .done y => (inv self b_init 16#usize y).holds

end ReducingFromI32ArrayFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `subtract_reduce`. Given a valid loop
    state `(acc, k)` with `k.val < 16`, applies the fused
    `mont_mul(1441) + sub + negate + barrett` chain to chunk `k.val` of
    `acc`, recording the FC equation `lift_chunk acc'[k.val] =
    chunk_subtract_reduce_pure (lift_chunk self[k.val]) (lift_chunk
    b_init[k.val])` while preserving chunks `j ≠ k.val`. -/
theorem subtract_reduce_step_lemma_fc
    (self b_init : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_b_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((b_init.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (acc : ReducingFromI32ArrayFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (ReducingFromI32ArrayFC.inv self b_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) self
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ ReducingFromI32ArrayFC.step_post self b_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_self_coef_len : self.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_done⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `index_mut_usize b.coefficients k` → `(t, set_back) = (acc.coefs[k], acc.coefs.set k)`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.coefficients.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.coefficients k
        (by rw [h_coef_len]; exact hk_16)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.coefficients k
        = .ok (t, acc.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (1a) `t = b_init.coefficients[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = b_init.coefficients.val[k.val]! := by
      show acc.coefficients.val[k.val]! = b_init.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_b_bnd k.val hk_16 ℓ hℓ
    -- (2) `mont_mul(t, 1441#i16)` → `t1`. Pre: |1441| ≤ 1664 ✓; |t| ≤ 32767 ✓.
    have h_c1441_bnd : ((1441#i16 : Std.I16).val.natAbs) ≤ 1664 := by decide
    obtain ⟨t1, h_t1_eq, h_t1_lift_mont⟩ :=
      triple_exists_ok_fc
        (montgomery_multiply_by_constant_fc t (1441#i16) h_t_bnd h_c1441_bnd)
    -- Also pull the legacy per-element fact for the bound and value.
    have h_t1_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec
        t (1441#i16) h_c1441_bnd
    obtain ⟨t1', h_t1_eq', h_t1_per⟩ := triple_exists_ok_fc h_t1_spec
    have h_t1_same : t1 = t1' := by
      have := h_t1_eq.symm.trans h_t1_eq'
      cases this; rfl
    subst h_t1_same
    have h_t1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t1.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).1
    have h_t1_modq : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val * (2 ^ 16 : Int)) % 3329
          = ((t.elements.val[ℓ]!).val * (1441#i16 : Std.I16).val) % 3329 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).2
    -- (3) `a = acc.coefficients.set k t1` (after applying index_mut_back).
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha_def
    -- (4) `index_mut_usize a k` → `(t2, set_back2) = (a[k], a.set k)`.
    have h_a_len : a.length = 16 := by simp [ha_def, h_coef_len]
    have h_a_k : a.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
          ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
    have h_idx_t2 : Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a k
        (by rw [h_a_len]; exact hk_16)
    have h_imt_t2 : Aeneas.Std.Array.index_mut_usize a k = .ok (t1, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t2]; rw [h_a_k]; rfl
    -- (5) `index_usize self.coefficients k` → `t3 = self.coefs[k]`.
    set t3 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      self.coefficients.val[k.val]! with ht3_def
    have h_idx_t3 : Aeneas.Std.Array.index_usize self.coefficients k = .ok t3 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq self.coefficients k
        (by rw [h_self_coef_len]; exact hk_16)
    have h_t3_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t3.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ; exact h_self_bnd k.val hk_16 ℓ hℓ
    -- (6) `sub t1 t3` → `t4`. Pre: |t1[ℓ] - t3[ℓ]| ≤ 32767.
    --   |t1| ≤ 3328, |t3| ≤ 29439, so |t1 - t3| ≤ 3328 + 29439 = 32767 ✓.
    have h_sub_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val - (t3.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t1 := h_t1_bnd ℓ hℓ
      have hb_t3 := h_t3_bnd ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_abs_sub : ((t1.elements.val[ℓ]!).val
            - (t3.elements.val[ℓ]!).val : Int).natAbs
          ≤ ((t1.elements.val[ℓ]!).val : Int).natAbs
            + ((t3.elements.val[ℓ]!).val : Int).natAbs :=
        Int.natAbs_sub_le _ _
      omega
    obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
      triple_exists_ok_fc (sub_fc t1 t3 h_sub_bnd)
    -- Pull legacy per-element value: t4[ℓ].val = t1[ℓ].val - t3[ℓ].val.
    have h_t4_spec := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.sub_spec t1 t3 h_sub_bnd
    obtain ⟨t4', h_t4_eq', h_t4_per⟩ := triple_exists_ok_fc h_t4_spec
    have h_t4_same : t4 = t4' := by
      have := h_t4_eq.symm.trans h_t4_eq'
      cases this; rfl
    subst h_t4_same
    have h_t4_val : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val
          = (t1.elements.val[ℓ]!).val - (t3.elements.val[ℓ]!).val := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).1
    have h_t4_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).2
    -- (7) `a1 = a.set k t4`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t4 with ha1_def
    have h_a1_len : a1.length = 16 := by simp [ha1_def, h_a_len]
    have h_a1_k : a1.val[k.val]! = t4 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t4
          ⟨rfl, by rw [h_a_len]; exact hk_16⟩
    -- (8) `index_mut_usize a1 k` → `(t5, set_back3) = (t4, a1.set k)`.
    have h_idx_t5 : Aeneas.Std.Array.index_usize a1 k = .ok (a1.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a1 k
        (by rw [h_a1_len]; exact hk_16)
    have h_imt_t5 : Aeneas.Std.Array.index_mut_usize a1 k = .ok (t4, a1.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t5]; rw [h_a1_k]; rfl
    -- (9) `negate t4` → `t6`. Pre: |t4[ℓ]| ≤ 32767 ≤ 2^15-1 ✓.
    have h_neg_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val.natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have h_b := h_t4_bnd ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]; exact h_b
    obtain ⟨t6, h_t6_eq, h_t6_lift⟩ :=
      triple_exists_ok_fc (negate_fc t4 h_neg_bnd)
    -- Pull legacy per-element BV fact for t6.
    have h_t6_spec := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.negate_spec t4
    obtain ⟨t6', h_t6_eq', h_t6_per⟩ := triple_exists_ok_fc h_t6_spec
    have h_t6_same : t6 = t6' := by
      have := h_t6_eq.symm.trans h_t6_eq'
      cases this; rfl
    subst h_t6_same
    -- We need a bound on t6 for barrett's pre.  Derive from negate_spec's BV
    -- equality combined with h_t4_bnd: t6.val = -t4.val (under |t4| ≤ 2^15-1).
    have h_t6_val : ∀ ℓ : Nat, ℓ < 16 →
        (t6.elements.val[ℓ]!).val = -(t4.elements.val[ℓ]!).val := by
      intro ℓ hℓ
      set xi : Std.I16 := t4.elements.val[ℓ]! with hxi
      set ri : Std.I16 := t6.elements.val[ℓ]! with hri
      have h_bv : ri.bv = -xi.bv := h_t6_per ℓ hℓ
      have h_wsub_bv :
          (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv = -xi.bv := by
        rw [Aeneas.Std.I16.wrapping_sub_bv_eq]
        simp only [show (0#i16 : Std.I16).bv = (0 : BitVec 16) from rfl]
        exact BitVec.zero_sub xi.bv
      have h_step1 : ri.val = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val := by
        have h_toInt : (ri.bv).toInt
            = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt := by
          rw [h_bv, h_wsub_bv]
        have h_lhs : (ri.bv).toInt = ri.val := Aeneas.Std.I16.bv_toInt_eq ri
        have h_rhs : (Aeneas.Std.I16.wrapping_sub (0#i16) xi).bv.toInt
            = (Aeneas.Std.I16.wrapping_sub (0#i16) xi).val :=
          Aeneas.Std.I16.bv_toInt_eq _
        rw [h_lhs, h_rhs] at h_toInt
        exact h_toInt
      rw [h_step1, Aeneas.Std.I16.wrapping_sub_val_eq]
      have h0 : (0#i16 : Std.I16).val = 0 := by decide
      rw [h0]
      have h_diff : (0 : Int) - xi.val = -xi.val := by ring
      rw [h_diff]
      apply Aeneas.Arith.Int.bmod_pow2_eq_of_inBounds' 16 _ (by decide)
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := h_neg_bnd ℓ hℓ
        have h_pow : -((2 : Int) ^ (16 - 1)) = -(2^15 : Int) := by decide
        rw [h_pow]
        omega
      · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := h_neg_bnd ℓ hℓ
        have h_pow : ((2 : Int) ^ (16 - 1)) = (2^15 : Int) := by decide
        rw [h_pow]
        omega
    have h_t6_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t6.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      have hv := h_t6_val ℓ hℓ
      have hb := h_t4_bnd ℓ hℓ
      have h_abs : ((-(t4.elements.val[ℓ]!).val : Int)).natAbs
          = ((t4.elements.val[ℓ]!).val : Int).natAbs := Int.natAbs_neg _
      rw [hv, h_abs]; exact hb
    -- (10) `a2 = a1.set k t6`.
    set a2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set k t6 with ha2_def
    have h_a2_len : a2.length = 16 := by simp [ha2_def, h_a1_len]
    have h_a2_k : a2.val[k.val]! = t6 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq a1 k k.val t6
          ⟨rfl, by rw [h_a1_len]; exact hk_16⟩
    -- (11) `index_mut_usize a2 k` → `(t7, set_back4) = (t6, a2.set k)`.
    have h_idx_t7 : Aeneas.Std.Array.index_usize a2 k = .ok (a2.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a2 k
        (by rw [h_a2_len]; exact hk_16)
    have h_imt_t7 : Aeneas.Std.Array.index_mut_usize a2 k = .ok (t6, a2.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t7]; rw [h_a2_k]; rfl
    -- (12) `barrett_reduce t6` → `t8`. Pre: |t6[ℓ]| ≤ 32767 ✓.
    obtain ⟨t8, h_t8_eq, h_t8_post⟩ :=
      triple_exists_ok_fc (barrett_reduce_fc t6 h_t6_bnd)
    obtain ⟨h_t8_bnd, h_t8_lift⟩ := h_t8_post
    -- (13) Compose acc' = `{ coefficients := a2.set k t8 }`.
    set a3 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a2.set k t8 with ha3_def
    set acc' : ReducingFromI32ArrayFC.Acc := { coefficients := a3 } with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
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
      simp only [Aeneas.Std.bind_tc_ok]
      -- The body is now sequentially: index_mut acc k → mont_mul → index_mut → index_usize self k
      --   → sub → index_mut → negate → index_mut → barrett. Discharge each.
      show (do
              let (t', index_mut_back) ←
                Aeneas.Std.Array.index_mut_usize acc.coefficients k
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
                  t' (1441#i16)
              let (t2', index_mut_back1) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back t1') k
              let t3' ← Aeneas.Std.Array.index_usize self.coefficients k
              let t4' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.sub
                  t2' t3'
              let (t5', index_mut_back2) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back1 t4') k
              let t6' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.negate t5'
              let (t7', index_mut_back3) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back2 t6') k
              let t8' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t7'
              .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back3 t8' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t2]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t3]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t5]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t6_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t7]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t8_eq]
      rfl
    apply triple_of_ok_fc h_body
    show ReducingFromI32ArrayFC.step_post self b_init k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold ReducingFromI32ArrayFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (ReducingFromI32ArrayFC.inv self b_init s acc').holds
    -- Invariant at (s, acc'). acc'.coefficients = a3 = ((acc.coefs.set k t1).set k t4).set k t6).set k t8.
    -- Equivalently: only chunk k changes, to t8.
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.coefficients.val[j]!)
            = Spec.chunk_subtract_reduce_pure
                (lift_chunk (self.coefficients.val[j]!))
                (lift_chunk (b_init.coefficients.val[j]!)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.coefficients.val[j]! = b_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < s.val → ∀ m : Nat, m < 16 →
            ((acc'.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) j < s.val → FC equation at chunk j.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk (((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all four sets.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : (((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!)
              = ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (((acc.coefficients.set k t1).set k t4).set k t6) k j t8 h_ne
          have h_set2 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set3 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set4 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3, h_set4]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: chunk j = t8, need lift_chunk t8 = chunk_subtract_reduce_pure ....
          subst hj_eq_k
          have h_set_eq : ((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[k.val]!
              = t8 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                (((acc.coefficients.set k t1).set k t4).set k t6) k k.val t8
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          -- Goal: lift_chunk t8 = chunk_subtract_reduce_pure (lift_chunk self[k]) (lift_chunk b_init[k]).
          -- We'll prove this by chaining: lift_chunk t8 = lift_chunk t6 (barrett identity) =
          --   chunk_neg (lift_chunk t4) = chunk_neg (chunk_sub (lift_chunk t1) (lift_chunk t3)).
          -- Then expand: lift_fe t1[ℓ] = mul_pure(lift_fe t[ℓ], lift_fe_mont 1441),
          -- and t[ℓ] = b_init[k][ℓ], t3[ℓ] = self[k][ℓ].
          -- The final identity reduces to: neg_pure(sub_pure(mul_pure b z) self) = sub_pure self (mul_pure b z).
          rw [h_t8_lift]
          -- t8_lift: lift_chunk t8 = chunk_barrett_reduce_pure (lift_chunk t6).
          show Spec.chunk_barrett_reduce_pure (lift_chunk t6)
              = Spec.chunk_subtract_reduce_pure
                  (lift_chunk (self.coefficients.val[k.val]!))
                  (lift_chunk (b_init.coefficients.val[k.val]!))
          -- Need a pointwise lane equation showing the four-stage chain on lane ℓ
          -- equals: barrett(neg(t1[ℓ] - self[ℓ])) ≡ self[ℓ] - mul_pure(b[ℓ], lift_fe_mont 1441) in ZMod q.
          unfold Spec.chunk_barrett_reduce_pure Spec.chunk_subtract_reduce_pure
          apply Subtype.ext
          -- Goal now: .val of LHS = .val of RHS. The .val of Std.Array.make is the list.
          change (List.range 16).map (fun i =>
              Spec.barrett_pure ((lift_chunk t6).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                ((lift_chunk (self.coefficients.val[k.val]!)).val[ℓ]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk (b_init.coefficients.val[k.val]!)).val[ℓ]!)
                  (lift_fe_mont (1441#i16))))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            -- LHS: Spec.barrett_pure ((lift_chunk t6).val[ℓ]!).
            -- RHS: sub_pure (self[k][ℓ]) (mul_pure b[k][ℓ] (lift_fe_mont 1441)).
            -- Step A: ((lift_chunk t6).val[ℓ]!) = lift_fe (t6.elements.val[ℓ]!).
            have h_t6_elems_len : t6.elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length t6
            have h_lc_t6 : ((lift_chunk t6).val[ℓ]!) = lift_fe (t6.elements.val[ℓ]!) := by
              unfold lift_chunk
              show ((t6.elements.val.map lift_fe)[ℓ]!) = _
              have h_len : (t6.elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_t6_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos t6.elements.val ℓ (by rw [h_t6_elems_len]; exact hℓ)]
            rw [h_lc_t6]
            -- Step B: barrett_pure (lift_fe t6[ℓ]) = lift_fe t6[ℓ] (canonical identity).
            rw [barrett_pure_lift_fe]
            -- Step C: lift_fe t6[ℓ] = -(lift_fe t4[ℓ]) in FE  ⟺  ZMod equation.
            -- Use h_t6_val: t6.val[ℓ] = -t4.val[ℓ] (Int).  Use h_t4_val: t4.val[ℓ] = t1.val[ℓ] - t3.val[ℓ].
            -- So t6.val[ℓ] = -(t1.val[ℓ] - t3.val[ℓ]) = t3.val[ℓ] - t1.val[ℓ].
            -- Then lift_fe t6 = (t3.val - t1.val : ZMod q).
            -- RHS: sub_pure self[k][ℓ] (mul_pure b_init[k][ℓ] (lift_fe_mont 1441)).
            --   = self[k][ℓ] - b_init[k][ℓ] * (1441 * 169) in ZMod q.
            -- Since self[k][ℓ] = t3.val and t1 satisfies t1.val ≡ t.val * 1441 * 169 ≡ b_init[k].val * 1441 * 169 in ZMod q,
            --   lift_fe t6 = t3.val - t1.val ≡ self[k][ℓ] - b[k][ℓ] * 1441 * 169  ✓.
            -- Let me build this step by step.
            -- (i) lift_fe t6[ℓ] = sub_pure (lift_fe t3[ℓ]) (lift_fe t1[ℓ])
            have hv6 := h_t6_val ℓ hℓ
            have hv4 := h_t4_val ℓ hℓ
            have h_t6_val_eq : (t6.elements.val[ℓ]!).val
                = (t3.elements.val[ℓ]!).val - (t1.elements.val[ℓ]!).val := by
              rw [hv6, hv4]; ring
            have h_sub_bnd_local :
                ((t3.elements.val[ℓ]!).val - (t1.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
              have h_bt1 := h_t1_bnd ℓ hℓ
              have h_bt3 := h_t3_bnd ℓ hℓ
              have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
              rw [h_p2]
              have h_abs_sub :
                  ((t3.elements.val[ℓ]!).val - (t1.elements.val[ℓ]!).val : Int).natAbs
                  ≤ ((t3.elements.val[ℓ]!).val : Int).natAbs
                    + ((t1.elements.val[ℓ]!).val : Int).natAbs :=
                Int.natAbs_sub_le _ _
              omega
            have h_lift_t6 :
                lift_fe (t6.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                      (lift_fe (t3.elements.val[ℓ]!)) (lift_fe (t1.elements.val[ℓ]!)) :=
              lift_fe_sub_pure_eq _ _ _ h_t6_val_eq
            rw [h_lift_t6]
            -- (ii) lift_fe t1[ℓ] = mul_pure (lift_fe t[ℓ]) (lift_fe_mont 1441).
            have h_lift_t1 :
                lift_fe (t1.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)) :=
              lift_fe_mont_mul_pure_eq _ _ _ (h_t1_modq ℓ hℓ)
            rw [h_lift_t1]
            -- (iii) Now goal:
            --   sub_pure (lift_fe t3[ℓ]) (mul_pure (lift_fe t[ℓ]) (lift_fe_mont 1441))
            --     = sub_pure ((lift_chunk self[k]).val[ℓ]!) (mul_pure ((lift_chunk b_init[k]).val[ℓ]!) (lift_fe_mont 1441)).
            -- t3 = self[k]; t = b_init[k]; lift_chunk x .val[ℓ]! = lift_fe (x.elements.val[ℓ]!).
            have h_self_elems_len : (self.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_b_elems_len : (b_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_lc_self : ((lift_chunk (self.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((self.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((self.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((self.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_self_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (self.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_self_elems_len]; exact hℓ)]
            have h_lc_b : ((lift_chunk (b_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((b_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((b_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((b_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_b_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (b_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_b_elems_len]; exact hℓ)]
            rw [h_lc_self, h_lc_b]
            -- t3 = self[k], t = b_init[k] (since t = acc[k] = b_init[k] by h_t_eq).
            -- Rewrite t3 and t to their respective self[k] and b_init[k] definitions
            -- to match the RHS.
            show libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (lift_fe (t3.elements.val[ℓ]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)))
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (lift_fe ((self.coefficients.val[k.val]!).elements.val[ℓ]!))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe ((b_init.coefficients.val[k.val]!).elements.val[ℓ]!))
                    (lift_fe_mont (1441#i16)))
            rw [show t3 = self.coefficients.val[k.val]! from ht3_def,
                show t = b_init.coefficients.val[k.val]! from h_t_eq]
      · -- (b) s.val ≤ j < 16 → acc'.coefs[j] = b_init.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!
            = b_init.coefficients.val[j]!
        have h_set1 : (((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!)
            = ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              (((acc.coefficients.set k t1).set k t4).set k t6) k j t8 h_ne
        have h_set2 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
        have h_set3 : (((acc.coefficients.set k t1).set k t4).val[j]!)
            = ((acc.coefficients.set k t1).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              (acc.coefficients.set k t1) k j t4 h_ne
        have h_set4 : ((acc.coefficients.set k t1).val[j]!)
            = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        rw [h_set1, h_set2, h_set3, h_set4]
        exact h_acc_undone j h_ge' hj_lt
      · -- (c) j < s.val → per-lane Barrett bound on acc'.coefs[j].
        intro j hj m hm
        rw [hs_val] at hj
        show ((((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!).elements.val[m]!).val.natAbs ≤ 1664
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all four sets — reuse the incoming bound.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : (((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[j]!)
              = ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (((acc.coefficients.set k t1).set k t4).set k t6) k j t8 h_ne
          have h_set2 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set3 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set4 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3, h_set4]
          exact h_acc_bnd_done j hj_lt_k m hm
        · -- j = k.val: chunk j = t8, the Barrett-reduced output (|·| ≤ 1664).
          subst hj_eq_k
          have h_set_eq : (((((acc.coefficients.set k t1).set k t4).set k t6).set k t8).val[k.val]!)
              = t8 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                (((acc.coefficients.set k t1).set k t4).set k t6) k k.val t8
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          exact h_t8_bnd m hm
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
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
    apply triple_of_ok_fc h_body
    show ReducingFromI32ArrayFC.step_post self b_init k (.done acc)
    unfold ReducingFromI32ArrayFC.step_post
    show (ReducingFromI32ArrayFC.inv self b_init 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
          lift_chunk (acc.coefficients.val[j]!)
            = Spec.chunk_subtract_reduce_pure
                (lift_chunk (self.coefficients.val[j]!))
                (lift_chunk (b_init.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.coefficients.val[j]! = b_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj m hm; rw [h16] at hj
        exact h_acc_bnd_done j (by rw [hk_eq]; exact hj) m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.2 — `subtract_reduce`: per-chunk `negate(mont_mul(b, 1441) - self)`
    then barrett. Equivalent in ZMod q to pointwise `self - 512 · b`
    (C.4 commute: `1441 · R⁻¹ ≡ 512 mod q`), NOT to hacspec's `self - b`.

    Spec target: custom `Spec.subtract_reduce_pure` modeling the
    fused-Mont impl behavior (see §0.5). Mirrors the L6.4/5/6
    `Spec.add_*_reduce_pure` pattern.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_self_bnd`: per-lane `|self[k][ℓ]| ≤ 29439` (drives `sub`'s overflow bound).
    - `h_b_bnd`: per-lane `|b[k][ℓ]| ≤ 32767` (consumed by `mont_mul`'s
      legacy precondition; the impl's later `sub` then uses `|t1| ≤ 3328` from
      mont's output bound). -/
@[spec]
theorem subtract_reduce_fc
    (self b : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_b_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((b.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self b
    ⦃ ⇓ p => ⌜ lift_poly p
                = Spec.subtract_reduce_pure (lift_poly self) (lift_poly b)
              ∧ (∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
                  ((p.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce
  -- Resolve `VECTORS_IN_RING_ELEMENT = .ok 16#usize`.
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, b1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.subtract_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self iter1 b1)
      (β := ReducingFromI32ArrayFC.Acc)
      b
      0#usize 16#usize
      (ReducingFromI32ArrayFC.inv self b)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- No chunks done yet.
          intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · -- All chunks unchanged (goal trivializes since acc = b).
          intro _ _ _; trivial
        · -- No output bounds to prove yet.
          intro j hj; exact absurd hj (Nat.not_lt_zero j))
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (ReducingFromI32ArrayFC.inv self b 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.coefficients.val[j]!)
              = Spec.chunk_subtract_reduce_pure
                  (lift_chunk (self.coefficients.val[j]!))
                  (lift_chunk (b.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.coefficients.val[j]! = b.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((r.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             ReducingFromI32ArrayFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    -- Split the conjunctive postcondition: lift equation, then the Barrett bound.
    refine ⟨?_, fun j hj m hm => h_bnd j hj m hm⟩
    -- Build chunks_arr matching the Spec definition, then apply
    -- flatten_chunks_eq_lift_poly_fc.
    unfold Spec.subtract_reduce_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_subtract_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly b) k)))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_subtract_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly b) k)))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc self k hk, chunk_at_lift_poly_fc b k hk]
      exact (h_done k hk).symm
    have h_final := flatten_chunks_eq_lift_poly_fc r chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma application.
    intro acc k _h_ge h_le hinv
    have h_step :=
      subtract_reduce_step_lemma_fc self b h_self_bnd h_b_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : ReducingFromI32ArrayFC.step_post self b k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [ReducingFromI32ArrayFC.step_post] using hP
    · have hP : ReducingFromI32ArrayFC.step_post self b k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [ReducingFromI32ArrayFC.step_post] using hP

/-! ### L6.3 — `add_to_ring_element` (DOCUMENTED, NO STANDALONE FC).

    The impl-side `PolynomialRingElement.add_to_ring_element` is NOT
    a standalone exported op at the impl extraction layer: the impl
    fuses "add then reduce" into the `add_*_reduce` family
    (`add_error_reduce`, `add_standard_error_reduce`,
    `add_message_error_reduce`).

    The hacspec target `polynomial.add_to_ring_element` is exercised
    indirectly through the matrix-level FCs (L7.1 / L7.3 use it
    inside `multiply_matrix_by_column` and `add_polynomials`); we do
    NOT land a separate `add_to_ring_element_fc` Triple here, but we
    DO land per-component `add_*_reduce_fc` Triples below (L6.4/5/6)
    that cover the impl-side calls. -/

/-! ### L6.4.A — Loop scaffolding for `add_error_reduce_fc`. -/

namespace AddErrorReduceFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator (the mutable `self` poly). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `add_error_reduce_fc`.
    * (a) Chunks `j < k`: FC equation `lift_chunk acc[j] =
          chunk_add_error_reduce_pure (lift_chunk self_init[j]) (lift_chunk error[j])`.
    * (b) Chunks `k ≤ j < 16`: `acc[j] = self_init[j]` (unchanged). -/
def inv
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.coefficients.val[j]!)
        = Spec.chunk_add_error_reduce_pure
            (lift_chunk (self_init.coefficients.val[j]!))
            (lift_chunk (error.coefficients.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = self_init.coefficients.val[j]!)
    ∧ (∀ j : Nat, j < k.val → ∀ m : Nat, m < 16 →
        ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv self_init error iter'.start acc').holds
  | .done y => (inv self_init error 16#usize y).holds

end AddErrorReduceFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `add_error_reduce`. Given a valid loop
    state `(acc, k)` with `k.val < 16`, applies the
    `mont_mul(1441) + add(error[k]) + barrett` chain to chunk `k.val` of
    `acc`, recording the FC equation `lift_chunk acc'[k.val] =
    chunk_add_error_reduce_pure (lift_chunk self_init[k.val]) (lift_chunk
    error[k.val])` while preserving chunks `j ≠ k.val`. -/
theorem add_error_reduce_step_lemma_fc
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self_init.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((error.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (acc : AddErrorReduceFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (AddErrorReduceFC.inv self_init error k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) error
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ AddErrorReduceFC.step_post self_init error k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_error_coef_len : error.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_done⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `index_mut_usize acc.coefficients k` → `(t, set_back) = (acc.coefs[k], acc.coefs.set k)`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.coefficients.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.coefficients k
        (by rw [h_coef_len]; exact hk_16)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.coefficients k
        = .ok (t, acc.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (1a) `t = self_init.coefficients[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = self_init.coefficients.val[k.val]! := by
      show acc.coefficients.val[k.val]! = self_init.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_self_bnd k.val hk_16 ℓ hℓ
    -- (2) `mont_mul(t, 1441#i16)` → `t1`. Pre: |1441| ≤ 1664 ✓; |t| ≤ 32767 ✓.
    have h_c1441_bnd : ((1441#i16 : Std.I16).val.natAbs) ≤ 1664 := by decide
    obtain ⟨t1, h_t1_eq, h_t1_lift_mont⟩ :=
      triple_exists_ok_fc
        (montgomery_multiply_by_constant_fc t (1441#i16) h_t_bnd h_c1441_bnd)
    -- Also pull the legacy per-element fact for the bound and value.
    have h_t1_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec
        t (1441#i16) h_c1441_bnd
    obtain ⟨t1', h_t1_eq', h_t1_per⟩ := triple_exists_ok_fc h_t1_spec
    have h_t1_same : t1 = t1' := by
      have := h_t1_eq.symm.trans h_t1_eq'
      cases this; rfl
    subst h_t1_same
    have h_t1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t1.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).1
    have h_t1_modq : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val * (2 ^ 16 : Int)) % 3329
          = ((t.elements.val[ℓ]!).val * (1441#i16 : Std.I16).val) % 3329 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).2
    -- (3) `a = acc.coefficients.set k t1`.
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha_def
    -- (4) `index_mut_usize a k` → `(t2, set_back2) = (a[k], a.set k) = (t1, a.set k)`.
    have h_a_len : a.length = 16 := by simp [ha_def, h_coef_len]
    have h_a_k : a.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
          ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
    have h_idx_t2 : Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a k
        (by rw [h_a_len]; exact hk_16)
    have h_imt_t2 : Aeneas.Std.Array.index_mut_usize a k = .ok (t1, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t2]; rw [h_a_k]; rfl
    -- (5) `index_usize error.coefficients k` → `t3 = error.coefs[k]`.
    set t3 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      error.coefficients.val[k.val]! with ht3_def
    have h_idx_t3 : Aeneas.Std.Array.index_usize error.coefficients k = .ok t3 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq error.coefficients k
        (by rw [h_error_coef_len]; exact hk_16)
    have h_t3_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t3.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ; exact h_error_bnd k.val hk_16 ℓ hℓ
    -- (6) `add t1 t3` → `t4`. Pre: |t1[ℓ] + t3[ℓ]| ≤ 32767.
    --   |t1| ≤ 3328, |t3| ≤ 29439, so |t1 + t3| ≤ 3328 + 29439 = 32767 ✓.
    have h_add_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val + (t3.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t1 := h_t1_bnd ℓ hℓ
      have hb_t3 := h_t3_bnd ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_abs_add : ((t1.elements.val[ℓ]!).val
            + (t3.elements.val[ℓ]!).val : Int).natAbs
          ≤ ((t1.elements.val[ℓ]!).val : Int).natAbs
            + ((t3.elements.val[ℓ]!).val : Int).natAbs :=
        Int.natAbs_add_le _ _
      omega
    obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
      triple_exists_ok_fc (add_fc t1 t3 h_add_bnd)
    -- Pull legacy per-element value: t4[ℓ].val = t1[ℓ].val + t3[ℓ].val.
    have h_t4_spec := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec t1 t3 h_add_bnd
    obtain ⟨t4', h_t4_eq', h_t4_per⟩ := triple_exists_ok_fc h_t4_spec
    have h_t4_same : t4 = t4' := by
      have := h_t4_eq.symm.trans h_t4_eq'
      cases this; rfl
    subst h_t4_same
    have h_t4_val : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val
          = (t1.elements.val[ℓ]!).val + (t3.elements.val[ℓ]!).val := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).1
    have h_t4_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).2
    -- (7) `a1 = a.set k t4`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t4 with ha1_def
    have h_a1_len : a1.length = 16 := by simp [ha1_def, h_a_len]
    have h_a1_k : a1.val[k.val]! = t4 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t4
          ⟨rfl, by rw [h_a_len]; exact hk_16⟩
    -- (8) `index_mut_usize a1 k` → `(t5, set_back3) = (t4, a1.set k)`.
    have h_idx_t5 : Aeneas.Std.Array.index_usize a1 k = .ok (a1.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a1 k
        (by rw [h_a1_len]; exact hk_16)
    have h_imt_t5 : Aeneas.Std.Array.index_mut_usize a1 k = .ok (t4, a1.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t5]; rw [h_a1_k]; rfl
    -- (9) `barrett_reduce t4` → `t6`. Pre: |t4[ℓ]| ≤ 32767 ✓.
    obtain ⟨t6, h_t6_eq, h_t6_post⟩ :=
      triple_exists_ok_fc (barrett_reduce_fc t4 h_t4_bnd)
    obtain ⟨h_t6_bnd, h_t6_lift⟩ := h_t6_post
    -- (10) Compose acc' = `{ coefficients := a1.set k t6 }`.
    set a2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set k t6 with ha2_def
    set acc' : AddErrorReduceFC.Acc := { coefficients := a2 } with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
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
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
              let (t', index_mut_back) ←
                Aeneas.Std.Array.index_mut_usize acc.coefficients k
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
                  t' (1441#i16)
              let (t2', index_mut_back1) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back t1') k
              let t3' ← Aeneas.Std.Array.index_usize error.coefficients k
              let t4' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.add t2' t3'
              let (t5', index_mut_back2) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back1 t4') k
              let t6' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t5'
              .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back2 t6' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t2]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t3]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t5]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t6_eq]
      rfl
    apply triple_of_ok_fc h_body
    show AddErrorReduceFC.step_post self_init error k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold AddErrorReduceFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (AddErrorReduceFC.inv self_init error s acc').holds
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.coefficients.val[j]!)
            = Spec.chunk_add_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.coefficients.val[j]! = self_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < s.val → ∀ m : Nat, m < 16 →
            ((acc'.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) j < s.val → FC equation at chunk j.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: chunk j = t6, need lift_chunk t6 = chunk_add_error_reduce_pure ....
          subst hj_eq_k
          have h_set_eq : ((((acc.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          -- Goal: lift_chunk t6 = chunk_add_error_reduce_pure
          --   (lift_chunk self_init[k]) (lift_chunk error[k]).
          rw [h_t6_lift]
          -- Now: chunk_barrett_reduce_pure (lift_chunk t4) =
          --   chunk_add_error_reduce_pure (lift_chunk self_init[k]) (lift_chunk error[k]).
          show Spec.chunk_barrett_reduce_pure (lift_chunk t4)
              = Spec.chunk_add_error_reduce_pure
                  (lift_chunk (self_init.coefficients.val[k.val]!))
                  (lift_chunk (error.coefficients.val[k.val]!))
          unfold Spec.chunk_barrett_reduce_pure Spec.chunk_add_error_reduce_pure
          apply Subtype.ext
          change (List.range 16).map (fun i =>
              Spec.barrett_pure ((lift_chunk t4).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                  (lift_fe_mont (1441#i16)))
                ((lift_chunk (error.coefficients.val[k.val]!)).val[ℓ]!))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            -- LHS: Spec.barrett_pure ((lift_chunk t4).val[ℓ]!).
            -- Step A: ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!).
            have h_t4_elems_len : t4.elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length t4
            have h_lc_t4 : ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!) := by
              unfold lift_chunk
              show ((t4.elements.val.map lift_fe)[ℓ]!) = _
              have h_len : (t4.elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_t4_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos t4.elements.val ℓ (by rw [h_t4_elems_len]; exact hℓ)]
            rw [h_lc_t4]
            -- Step B: barrett_pure (lift_fe t4[ℓ]) = lift_fe t4[ℓ].
            rw [barrett_pure_lift_fe]
            -- Step C: lift_fe t4[ℓ] = add_pure (lift_fe t1[ℓ]) (lift_fe t3[ℓ]).
            have hv4 := h_t4_val ℓ hℓ
            have h_lift_t4 :
                lift_fe (t4.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (lift_fe (t1.elements.val[ℓ]!)) (lift_fe (t3.elements.val[ℓ]!)) :=
              lift_fe_add_pure_eq _ _ _ hv4
            rw [h_lift_t4]
            -- Step D: lift_fe t1[ℓ] = mul_pure (lift_fe t[ℓ]) (lift_fe_mont 1441).
            have h_lift_t1 :
                lift_fe (t1.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)) :=
              lift_fe_mont_mul_pure_eq _ _ _ (h_t1_modq ℓ hℓ)
            rw [h_lift_t1]
            -- Step E: rewrite t and t3 to self_init[k] and error[k] images.
            have h_self_elems_len :
                (self_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_err_elems_len :
                (error.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_lc_self : ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((self_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((self_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_self_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (self_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_self_elems_len]; exact hℓ)]
            have h_lc_err : ((lift_chunk (error.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((error.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((error.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((error.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_err_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (error.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_err_elems_len]; exact hℓ)]
            rw [h_lc_self, h_lc_err]
            show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)))
                  (lift_fe (t3.elements.val[ℓ]!))
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!))
                    (lift_fe_mont (1441#i16)))
                  (lift_fe ((error.coefficients.val[k.val]!).elements.val[ℓ]!))
            rw [show t = self_init.coefficients.val[k.val]! from h_t_eq,
                show t3 = error.coefficients.val[k.val]! from ht3_def]
      · -- (b) s.val ≤ j < 16 → acc'.coefs[j] = self_init.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = self_init.coefficients.val[j]!
        have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
        have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
            = ((acc.coefficients.set k t1).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              (acc.coefficients.set k t1) k j t4 h_ne
        have h_set3 : ((acc.coefficients.set k t1).val[j]!)
            = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        rw [h_set1, h_set2, h_set3]
        exact h_acc_undone j h_ge' hj_lt
      · -- (c) j < s.val → per-lane Barrett bound on acc'.coefs[j].
        intro j hj m hm
        rw [hs_val] at hj
        show (((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!).elements.val[m]!).val.natAbs ≤ 1664
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets — reuse the incoming bound.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_bnd_done j hj_lt_k m hm
        · -- j = k.val: chunk j = t6, the Barrett-reduced output (|·| ≤ 1664).
          subst hj_eq_k
          have h_set_eq : ((((acc.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          exact h_t6_bnd m hm
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
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
    apply triple_of_ok_fc h_body
    show AddErrorReduceFC.step_post self_init error k (.done acc)
    unfold AddErrorReduceFC.step_post
    show (AddErrorReduceFC.inv self_init error 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
          lift_chunk (acc.coefficients.val[j]!)
            = Spec.chunk_add_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.coefficients.val[j]! = self_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj m hm; rw [h16] at hj
        exact h_acc_bnd_done j (by rw [hk_eq]; exact hj) m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.4 — `add_error_reduce`: `self · (R/128) + error` then barrett.
    Returns `(re, scratch)` tuple; we project on `re`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_self_bnd`: per-lane `|self[k][ℓ]| ≤ 32767` (consumed by `mont_mul`'s
      legacy precondition; the impl's later `add` then uses `|t1| ≤ 3328` from
      mont's output bound).
    - `h_error_bnd`: per-lane `|error[k][ℓ]| ≤ 29439` (drives `add`'s overflow
      bound: |t1| + |error| ≤ 3328 + 29439 = 32767). -/
@[spec]
theorem add_error_reduce_fc
    (self error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((error.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self error
    ⦃ ⇓ p => ⌜ lift_poly p = Spec.add_error_reduce_pure (lift_poly self) (lift_poly error)
              ∧ (∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
                  ((p.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
  -- Resolve `VECTORS_IN_RING_ELEMENT = .ok 16#usize`.
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, self1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error iter1 self1)
      (β := AddErrorReduceFC.Acc)
      self
      0#usize 16#usize
      (AddErrorReduceFC.inv self error)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial
        · intro j hj; exact absurd hj (Nat.not_lt_zero j))
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (AddErrorReduceFC.inv self error 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.coefficients.val[j]!)
              = Spec.chunk_add_error_reduce_pure
                  (lift_chunk (self.coefficients.val[j]!))
                  (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.coefficients.val[j]! = self.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((r.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             AddErrorReduceFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    -- Split the conjunctive postcondition: lift equation, then the Barrett bound.
    refine ⟨?_, fun j hj m hm => h_bnd j hj m hm⟩
    -- Build chunks_arr matching the Spec definition, then apply
    -- flatten_chunks_eq_lift_poly_fc.
    unfold Spec.add_error_reduce_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_add_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly error) k)))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_add_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly error) k)))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc self k hk, chunk_at_lift_poly_fc error k hk]
      exact (h_done k hk).symm
    have h_final := flatten_chunks_eq_lift_poly_fc r chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step entailment: per-iteration step lemma.
    intro acc k _h_ge h_le hinv
    have h_step :=
      add_error_reduce_step_lemma_fc self error h_self_bnd h_error_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : AddErrorReduceFC.step_post self error k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddErrorReduceFC.step_post] using hP
    · have hP : AddErrorReduceFC.step_post self error k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddErrorReduceFC.step_post] using hP

/-! ### L6.5.A — Loop scaffolding for `add_standard_error_reduce_fc`. -/

namespace AddStandardErrorReduceFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator (the mutable `self` poly). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `add_standard_error_reduce_fc`.
    * (a) Chunks `j < k`: FC equation `lift_chunk acc[j] =
          chunk_add_standard_error_reduce_pure (lift_chunk self_init[j])
            (lift_chunk error[j])`.
    * (b) Chunks `k ≤ j < 16`: `acc[j] = self_init[j]` (unchanged).
    * (c) Chunks `j < k`: per-lane `|acc[j][m]| ≤ 1664` — the Barrett-reduced
          output bound, carried so the top-level L7.1 POST can state the impl
          output in canonical form (no output `lift`). -/
def inv
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.coefficients.val[j]!)
        = Spec.chunk_add_standard_error_reduce_pure
            (lift_chunk (self_init.coefficients.val[j]!))
            (lift_chunk (error.coefficients.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = self_init.coefficients.val[j]!)
    ∧ (∀ j : Nat, j < k.val → ∀ m : Nat, m < 16 →
        ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv self_init error iter'.start acc').holds
  | .done y => (inv self_init error 16#usize y).holds

end AddStandardErrorReduceFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `add_standard_error_reduce`. Given a
    valid loop state `(acc, k)` with `k.val < 16`, applies the
    `mont_mul(1353) + add(error[k]) + barrett` chain (via the
    `to_standard_domain` wrapper) to chunk `k.val` of `acc`, recording the
    FC equation `lift_chunk acc'[k.val] =
    chunk_add_standard_error_reduce_pure (lift_chunk self_init[k.val])
    (lift_chunk error[k.val])` while preserving chunks `j ≠ k.val`. -/
theorem add_standard_error_reduce_step_lemma_fc
    (self_init error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self_init.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((error.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (acc : AddStandardErrorReduceFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (AddStandardErrorReduceFC.inv self_init error k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) error
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ AddStandardErrorReduceFC.step_post self_init error k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_error_coef_len : error.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_RR_unfold :
      libcrux_iot_ml_kem.vector.traits.MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
        = (1353#i16 : Std.I16) := by
    unfold libcrux_iot_ml_kem.vector.traits.MONTGOMERY_R_SQUARED_MOD_FIELD_MODULUS
    rfl
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_done⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `index_mut_usize acc.coefficients k` → `(t, set_back) = (acc.coefs[k], acc.coefs.set k)`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.coefficients.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.coefficients k
        (by rw [h_coef_len]; exact hk_16)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.coefficients k
        = .ok (t, acc.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (1a) `t = self_init.coefficients[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = self_init.coefficients.val[k.val]! := by
      show acc.coefficients.val[k.val]! = self_init.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_self_bnd k.val hk_16 ℓ hℓ
    -- (2) `mont_mul(t, 1353#i16)` → `t1`. Pre: |1353| ≤ 1664 ✓; |t| ≤ 32767 ✓.
    have h_c1353_bnd : ((1353#i16 : Std.I16).val.natAbs) ≤ 1664 := by decide
    obtain ⟨t1, h_t1_eq, h_t1_lift_mont⟩ :=
      triple_exists_ok_fc
        (montgomery_multiply_by_constant_fc t (1353#i16) h_t_bnd h_c1353_bnd)
    -- Also pull the legacy per-element fact for the bound and value.
    have h_t1_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec
        t (1353#i16) h_c1353_bnd
    obtain ⟨t1', h_t1_eq', h_t1_per⟩ := triple_exists_ok_fc h_t1_spec
    have h_t1_same : t1 = t1' := by
      have := h_t1_eq.symm.trans h_t1_eq'
      cases this; rfl
    subst h_t1_same
    have h_t1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t1.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).1
    have h_t1_modq : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val * (2 ^ 16 : Int)) % 3329
          = ((t.elements.val[ℓ]!).val * (1353#i16 : Std.I16).val) % 3329 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).2
    -- (3) `a = acc.coefficients.set k t1`.
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha_def
    -- (4) `index_mut_usize a k` → `(t2, set_back2) = (a[k], a.set k) = (t1, a.set k)`.
    have h_a_len : a.length = 16 := by simp [ha_def, h_coef_len]
    have h_a_k : a.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
          ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
    have h_idx_t2 : Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a k
        (by rw [h_a_len]; exact hk_16)
    have h_imt_t2 : Aeneas.Std.Array.index_mut_usize a k = .ok (t1, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t2]; rw [h_a_k]; rfl
    -- (5) `index_usize error.coefficients k` → `t3 = error.coefs[k]`.
    set t3 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      error.coefficients.val[k.val]! with ht3_def
    have h_idx_t3 : Aeneas.Std.Array.index_usize error.coefficients k = .ok t3 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq error.coefficients k
        (by rw [h_error_coef_len]; exact hk_16)
    have h_t3_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t3.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ; exact h_error_bnd k.val hk_16 ℓ hℓ
    -- (6) `add t1 t3` → `t4`. Pre: |t1[ℓ] + t3[ℓ]| ≤ 32767.
    --   |t1| ≤ 3328, |t3| ≤ 29439, so |t1 + t3| ≤ 3328 + 29439 = 32767 ✓.
    have h_add_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val + (t3.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t1 := h_t1_bnd ℓ hℓ
      have hb_t3 := h_t3_bnd ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_abs_add : ((t1.elements.val[ℓ]!).val
            + (t3.elements.val[ℓ]!).val : Int).natAbs
          ≤ ((t1.elements.val[ℓ]!).val : Int).natAbs
            + ((t3.elements.val[ℓ]!).val : Int).natAbs :=
        Int.natAbs_add_le _ _
      omega
    obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
      triple_exists_ok_fc (add_fc t1 t3 h_add_bnd)
    -- Pull legacy per-element value: t4[ℓ].val = t1[ℓ].val + t3[ℓ].val.
    have h_t4_spec := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec t1 t3 h_add_bnd
    obtain ⟨t4', h_t4_eq', h_t4_per⟩ := triple_exists_ok_fc h_t4_spec
    have h_t4_same : t4 = t4' := by
      have := h_t4_eq.symm.trans h_t4_eq'
      cases this; rfl
    subst h_t4_same
    have h_t4_val : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val
          = (t1.elements.val[ℓ]!).val + (t3.elements.val[ℓ]!).val := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).1
    have h_t4_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).2
    -- (7) `a1 = a.set k t4`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t4 with ha1_def
    have h_a1_len : a1.length = 16 := by simp [ha1_def, h_a_len]
    have h_a1_k : a1.val[k.val]! = t4 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t4
          ⟨rfl, by rw [h_a_len]; exact hk_16⟩
    -- (8) `index_mut_usize a1 k` → `(t5, set_back3) = (t4, a1.set k)`.
    have h_idx_t5 : Aeneas.Std.Array.index_usize a1 k = .ok (a1.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a1 k
        (by rw [h_a1_len]; exact hk_16)
    have h_imt_t5 : Aeneas.Std.Array.index_mut_usize a1 k = .ok (t4, a1.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t5]; rw [h_a1_k]; rfl
    -- (9) `barrett_reduce t4` → `t6`. Pre: |t4[ℓ]| ≤ 32767 ✓.
    obtain ⟨t6, h_t6_eq, h_t6_post⟩ :=
      triple_exists_ok_fc (barrett_reduce_fc t4 h_t4_bnd)
    obtain ⟨h_t6_bnd, h_t6_lift⟩ := h_t6_post
    -- (10) Compose acc' = `{ coefficients := a1.set k t6 }`.
    set a2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set k t6 with ha2_def
    set acc' : AddStandardErrorReduceFC.Acc := { coefficients := a2 } with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
      simp only [libcrux_iot_ml_kem.vector.traits.to_standard_domain, h_RR_unfold]
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
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
              let (t', index_mut_back) ←
                Aeneas.Std.Array.index_mut_usize acc.coefficients k
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
                  t' (1353#i16)
              let (t2', index_mut_back1) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back t1') k
              let t3' ← Aeneas.Std.Array.index_usize error.coefficients k
              let t4' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.add t2' t3'
              let (t5', index_mut_back2) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back1 t4') k
              let t6' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t5'
              .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back2 t6' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t2]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t3]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t5]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t6_eq]
      rfl
    apply triple_of_ok_fc h_body
    show AddStandardErrorReduceFC.step_post self_init error k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold AddStandardErrorReduceFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (AddStandardErrorReduceFC.inv self_init error s acc').holds
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.coefficients.val[j]!)
            = Spec.chunk_add_standard_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.coefficients.val[j]! = self_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < s.val → ∀ m : Nat, m < 16 →
            ((acc'.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) j < s.val → FC equation at chunk j.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: chunk j = t6, need lift_chunk t6 = chunk_add_standard_error_reduce_pure ....
          subst hj_eq_k
          have h_set_eq : ((((acc.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          -- Goal: lift_chunk t6 = chunk_add_standard_error_reduce_pure
          --   (lift_chunk self_init[k]) (lift_chunk error[k]).
          rw [h_t6_lift]
          -- Now: chunk_barrett_reduce_pure (lift_chunk t4) =
          --   chunk_add_standard_error_reduce_pure (lift_chunk self_init[k]) (lift_chunk error[k]).
          show Spec.chunk_barrett_reduce_pure (lift_chunk t4)
              = Spec.chunk_add_standard_error_reduce_pure
                  (lift_chunk (self_init.coefficients.val[k.val]!))
                  (lift_chunk (error.coefficients.val[k.val]!))
          unfold Spec.chunk_barrett_reduce_pure Spec.chunk_add_standard_error_reduce_pure
          apply Subtype.ext
          change (List.range 16).map (fun i =>
              Spec.barrett_pure ((lift_chunk t4).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                  (lift_fe_mont (1353#i16)))
                ((lift_chunk (error.coefficients.val[k.val]!)).val[ℓ]!))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            -- LHS: Spec.barrett_pure ((lift_chunk t4).val[ℓ]!).
            -- Step A: ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!).
            have h_t4_elems_len : t4.elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length t4
            have h_lc_t4 : ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!) := by
              unfold lift_chunk
              show ((t4.elements.val.map lift_fe)[ℓ]!) = _
              have h_len : (t4.elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_t4_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos t4.elements.val ℓ (by rw [h_t4_elems_len]; exact hℓ)]
            rw [h_lc_t4]
            -- Step B: barrett_pure (lift_fe t4[ℓ]) = lift_fe t4[ℓ].
            rw [barrett_pure_lift_fe]
            -- Step C: lift_fe t4[ℓ] = add_pure (lift_fe t1[ℓ]) (lift_fe t3[ℓ]).
            have hv4 := h_t4_val ℓ hℓ
            have h_lift_t4 :
                lift_fe (t4.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (lift_fe (t1.elements.val[ℓ]!)) (lift_fe (t3.elements.val[ℓ]!)) :=
              lift_fe_add_pure_eq _ _ _ hv4
            rw [h_lift_t4]
            -- Step D: lift_fe t1[ℓ] = mul_pure (lift_fe t[ℓ]) (lift_fe_mont 1353).
            have h_lift_t1 :
                lift_fe (t1.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1353#i16)) :=
              lift_fe_mont_mul_pure_eq _ _ _ (h_t1_modq ℓ hℓ)
            rw [h_lift_t1]
            -- Step E: rewrite t and t3 to self_init[k] and error[k] images.
            have h_self_elems_len :
                (self_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_err_elems_len :
                (error.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_lc_self : ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((self_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((self_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_self_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (self_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_self_elems_len]; exact hℓ)]
            have h_lc_err : ((lift_chunk (error.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((error.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((error.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((error.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_err_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (error.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_err_elems_len]; exact hℓ)]
            rw [h_lc_self, h_lc_err]
            show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1353#i16)))
                  (lift_fe (t3.elements.val[ℓ]!))
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!))
                    (lift_fe_mont (1353#i16)))
                  (lift_fe ((error.coefficients.val[k.val]!).elements.val[ℓ]!))
            rw [show t = self_init.coefficients.val[k.val]! from h_t_eq,
                show t3 = error.coefficients.val[k.val]! from ht3_def]
      · -- (b) s.val ≤ j < 16 → acc'.coefs[j] = self_init.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = self_init.coefficients.val[j]!
        have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
        have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
            = ((acc.coefficients.set k t1).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              (acc.coefficients.set k t1) k j t4 h_ne
        have h_set3 : ((acc.coefficients.set k t1).val[j]!)
            = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        rw [h_set1, h_set2, h_set3]
        exact h_acc_undone j h_ge' hj_lt
      · -- (c) j < s.val → per-lane Barrett bound on acc'.coefs[j].
        intro j hj m hm
        rw [hs_val] at hj
        show (((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!).elements.val[m]!).val.natAbs ≤ 1664
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets — reuse the incoming bound.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_bnd_done j hj_lt_k m hm
        · -- j = k.val: chunk j = t6, the Barrett-reduced output (|·| ≤ 1664).
          subst hj_eq_k
          have h_set_eq : ((((acc.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          exact h_t6_bnd m hm
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
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
    apply triple_of_ok_fc h_body
    show AddStandardErrorReduceFC.step_post self_init error k (.done acc)
    unfold AddStandardErrorReduceFC.step_post
    show (AddStandardErrorReduceFC.inv self_init error 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
          lift_chunk (acc.coefficients.val[j]!)
            = Spec.chunk_add_standard_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.coefficients.val[j]! = self_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((acc.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj m hm; rw [h16] at hj
        exact h_acc_bnd_done j (by rw [hk_eq]; exact hj) m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.5 — `add_standard_error_reduce`: `self · R² + error` then barrett.
    Used to take an inverse-NTT result back to "standard domain".

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_self_bnd`: per-lane `|self[k][ℓ]| ≤ 32767` (consumed by `mont_mul`'s
      legacy precondition; the impl's later `add` then uses `|t1| ≤ 3328` from
      mont's output bound).
    - `h_error_bnd`: per-lane `|error[k][ℓ]| ≤ 29439` (drives `add`'s overflow
      bound: |t1| + |error| ≤ 3328 + 29439 = 32767). -/
@[spec]
theorem add_standard_error_reduce_fc
    (self error : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((error.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self error
    ⦃ ⇓ p => ⌜ lift_poly p
                = Spec.add_standard_error_reduce_pure (lift_poly self) (lift_poly error)
              ∧ (∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
                  ((p.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
  -- Resolve `VECTORS_IN_RING_ELEMENT = .ok 16#usize`.
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, self1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) error iter1 self1)
      (β := AddStandardErrorReduceFC.Acc)
      self
      0#usize 16#usize
      (AddStandardErrorReduceFC.inv self error)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial
        · intro j hj; exact absurd hj (Nat.not_lt_zero j))
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (AddStandardErrorReduceFC.inv self error 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.coefficients.val[j]!)
              = Spec.chunk_add_standard_error_reduce_pure
                  (lift_chunk (self.coefficients.val[j]!))
                  (lift_chunk (error.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.coefficients.val[j]! = self.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((r.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             AddStandardErrorReduceFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    -- Split the conjunctive postcondition: lift equation, then the Barrett bound.
    refine ⟨?_, fun j hj m hm => h_bnd j hj m hm⟩
    -- Build chunks_arr matching the Spec definition, then apply
    -- flatten_chunks_eq_lift_poly_fc.
    unfold Spec.add_standard_error_reduce_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_add_standard_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly error) k)))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_add_standard_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly error) k)))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc self k hk, chunk_at_lift_poly_fc error k hk]
      exact (h_done k hk).symm
    have h_final := flatten_chunks_eq_lift_poly_fc r chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step entailment: per-iteration step lemma.
    intro acc k _h_ge h_le hinv
    have h_step :=
      add_standard_error_reduce_step_lemma_fc self error h_self_bnd h_error_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : AddStandardErrorReduceFC.step_post self error k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddStandardErrorReduceFC.step_post] using hP
    · have hP : AddStandardErrorReduceFC.step_post self error k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddStandardErrorReduceFC.step_post] using hP

/-! ### L6.6.A — Loop scaffolding for `add_message_error_reduce_fc`.

    Unlike L6.4/L6.5 (single-poly Acc), this loop carries a 2-tuple
    `(result_acc, scratch)` because the impl reads/writes both per
    iteration. The FC equation lives entirely on `result_acc`; `scratch`
    is unconstrained at iteration boundaries (`scratch_15 = self[15] +
    message[15]` at exit, but the FC theorem only projects `p.1`). -/

namespace AddMessageErrorReduceFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator: `(result, scratch)`. -/
abbrev Acc :=
  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    × libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `add_message_error_reduce_fc`.
    * (a) Chunks `j < k`: FC equation on `acc.1` against
          `chunk_add_message_error_reduce_pure (self_init[j]) (message_init[j]) (result_init[j])`.
    * (b) Chunks `k ≤ j < 16`: `acc.1[j] = result_init[j]` (unchanged).
    The `scratch` component `acc.2` is unconstrained. -/
def inv
    (self_init message_init result_init :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.1.coefficients.val[j]!)
        = Spec.chunk_add_message_error_reduce_pure
            (lift_chunk (self_init.coefficients.val[j]!))
            (lift_chunk (message_init.coefficients.val[j]!))
            (lift_chunk (result_init.coefficients.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.1.coefficients.val[j]! = result_init.coefficients.val[j]!)
    ∧ (∀ j : Nat, j < k.val → ∀ m : Nat, m < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (self_init message_init result_init :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv self_init message_init result_init iter'.start acc').holds
  | .done y => (inv self_init message_init result_init 16#usize y).holds

end AddMessageErrorReduceFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `add_message_error_reduce`. Given a
    valid loop state `((result_acc, _scratch_acc), k)` with `k.val < 16`,
    applies the `mont_mul(1441) + add(self+message) + barrett` chain to
    chunk `k.val` of `result_acc`, recording the FC equation
    `lift_chunk acc'.1[k.val] =
      chunk_add_message_error_reduce_pure
        (lift_chunk self_init[k.val])
        (lift_chunk message_init[k.val])
        (lift_chunk result_init[k.val])`
    while preserving chunks `j ≠ k.val`. The scratch slot is overwritten
    each iteration with `self[k] + message[k]` and remains unconstrained
    by the invariant. -/
theorem add_message_error_reduce_step_lemma_fc
    (self_init message_init result_init :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_result_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((result_init.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_sum_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      (((self_init.coefficients.val[chunk]!).elements.val[ℓ]!).val
        + ((message_init.coefficients.val[chunk]!).elements.val[ℓ]!).val
            : Int).natAbs ≤ 29439)
    (acc : AddMessageErrorReduceFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (AddMessageErrorReduceFC.inv self_init message_init result_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) self_init message_init
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ AddMessageErrorReduceFC.step_post self_init message_init result_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_self_coef_len : self_init.coefficients.length = 16 :=
    Std.Array.length_eq _
  have h_msg_coef_len : message_init.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd_done⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `index_mut_usize acc.1.coefficients k` → `(t, set_back) =
    --     (acc.1.coefs[k], acc.1.coefs.set k)`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.1.coefficients.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.1.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.1.coefficients k
        (by rw [h_coef_len]; exact hk_16)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.1.coefficients k
        = .ok (t, acc.1.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (1a) `t = result_init.coefficients[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = result_init.coefficients.val[k.val]! := by
      show acc.1.coefficients.val[k.val]! = result_init.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_result_bnd k.val hk_16 ℓ hℓ
    -- (2) `mont_mul(t, 1441#i16)` → `t1`. Pre: |1441| ≤ 1664 ✓; |t| ≤ 32767 ✓.
    have h_c1441_bnd : ((1441#i16 : Std.I16).val.natAbs) ≤ 1664 := by decide
    obtain ⟨t1, h_t1_eq, h_t1_lift_mont⟩ :=
      triple_exists_ok_fc
        (montgomery_multiply_by_constant_fc t (1441#i16) h_t_bnd h_c1441_bnd)
    have h_t1_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec
        t (1441#i16) h_c1441_bnd
    obtain ⟨t1', h_t1_eq', h_t1_per⟩ := triple_exists_ok_fc h_t1_spec
    have h_t1_same : t1 = t1' := by
      have := h_t1_eq.symm.trans h_t1_eq'
      cases this; rfl
    subst h_t1_same
    have h_t1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t1.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).1
    have h_t1_modq : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val * (2 ^ 16 : Int)) % 3329
          = ((t.elements.val[ℓ]!).val * (1441#i16 : Std.I16).val) % 3329 := by
      intro ℓ hℓ; exact (h_t1_per ℓ hℓ).2
    -- (3) `scratch1 = self_init.coefs[k]`.
    set scratch1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      self_init.coefficients.val[k.val]! with hscratch1_def
    have h_idx_scratch1 : Aeneas.Std.Array.index_usize self_init.coefficients k
        = .ok scratch1 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq self_init.coefficients k
        (by rw [h_self_coef_len]; exact hk_16)
    -- (4) `t2 = message_init.coefs[k]`.
    set t2 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      message_init.coefficients.val[k.val]! with ht2_def
    have h_idx_t2 : Aeneas.Std.Array.index_usize message_init.coefficients k = .ok t2 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq message_init.coefficients k
        (by rw [h_msg_coef_len]; exact hk_16)
    -- (5) `add scratch1 t2 = scratch2`. Pre: |scratch1 + t2| ≤ 32767;
    --     from `h_sum_bnd` ≤ 29439 ≤ 32767.
    have h_scratch2_pre : ∀ ℓ : Nat, ℓ < 16 →
        ((scratch1.elements.val[ℓ]!).val + (t2.elements.val[ℓ]!).val : Int).natAbs
          ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_sum := h_sum_bnd k.val hk_16 ℓ hℓ
      show (((self_init.coefficients.val[k.val]!).elements.val[ℓ]!).val
              + ((message_init.coefficients.val[k.val]!).elements.val[ℓ]!).val
              : Int).natAbs ≤ 32767
      omega
    obtain ⟨scratch2, h_scratch2_eq, h_scratch2_lift⟩ :=
      triple_exists_ok_fc (add_fc scratch1 t2 h_scratch2_pre)
    have h_scratch2_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec scratch1 t2 h_scratch2_pre
    obtain ⟨scratch2', h_scratch2_eq', h_scratch2_per⟩ := triple_exists_ok_fc h_scratch2_spec
    have h_scratch2_same : scratch2 = scratch2' := by
      have := h_scratch2_eq.symm.trans h_scratch2_eq'
      cases this; rfl
    subst h_scratch2_same
    have h_scratch2_val : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val
          = (scratch1.elements.val[ℓ]!).val + (t2.elements.val[ℓ]!).val := by
      intro ℓ hℓ; exact (h_scratch2_per ℓ hℓ).1
    have h_scratch2_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_scratch2_val ℓ hℓ]
      exact h_sum_bnd k.val hk_16 ℓ hℓ
    -- (6) `a = acc.1.coefficients.set k t1`.
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.1.coefficients.set k t1 with ha_def
    have h_a_len : a.length = 16 := by simp [ha_def, h_coef_len]
    have h_a_k : a.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc.1.coefficients k k.val t1
          ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
    -- (7) `index_mut_usize a k` → `(t3, _) = (t1, a.set k)`.
    have h_idx_t3 : Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a k
        (by rw [h_a_len]; exact hk_16)
    have h_imt_t3 : Aeneas.Std.Array.index_mut_usize a k = .ok (t1, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t3]; rw [h_a_k]; rfl
    -- (8) `add t1 scratch2 = t4`. Pre: |t1 + scratch2| ≤ 32767;
    --     |t1| ≤ 3328, |scratch2| ≤ 29439 ⇒ |t1 + scratch2| ≤ 32767 ✓.
    have h_t4_pre : ∀ ℓ : Nat, ℓ < 16 →
        ((t1.elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs
          ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t1 := h_t1_bnd ℓ hℓ
      have hb_s2 := h_scratch2_bnd ℓ hℓ
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_abs_add : ((t1.elements.val[ℓ]!).val
            + (scratch2.elements.val[ℓ]!).val : Int).natAbs
          ≤ ((t1.elements.val[ℓ]!).val : Int).natAbs
            + ((scratch2.elements.val[ℓ]!).val : Int).natAbs :=
        Int.natAbs_add_le _ _
      omega
    obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
      triple_exists_ok_fc (add_fc t1 scratch2 h_t4_pre)
    have h_t4_spec := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec t1 scratch2 h_t4_pre
    obtain ⟨t4', h_t4_eq', h_t4_per⟩ := triple_exists_ok_fc h_t4_spec
    have h_t4_same : t4 = t4' := by
      have := h_t4_eq.symm.trans h_t4_eq'
      cases this; rfl
    subst h_t4_same
    have h_t4_val : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val
          = (t1.elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).1
    have h_t4_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t4.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ; exact (h_t4_per ℓ hℓ).2
    -- (9) `a1 = a.set k t4`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t4 with ha1_def
    have h_a1_len : a1.length = 16 := by simp [ha1_def, h_a_len]
    have h_a1_k : a1.val[k.val]! = t4 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t4
          ⟨rfl, by rw [h_a_len]; exact hk_16⟩
    -- (10) `index_mut_usize a1 k` → `(t5, _) = (t4, a1.set k)`.
    have h_idx_t5 : Aeneas.Std.Array.index_usize a1 k = .ok (a1.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a1 k
        (by rw [h_a1_len]; exact hk_16)
    have h_imt_t5 : Aeneas.Std.Array.index_mut_usize a1 k = .ok (t4, a1.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t5]; rw [h_a1_k]; rfl
    -- (11) `barrett_reduce t4 = t6`. Pre: |t4[ℓ]| ≤ 32767 ✓.
    obtain ⟨t6, h_t6_eq, h_t6_post⟩ :=
      triple_exists_ok_fc (barrett_reduce_fc t4 h_t4_bnd)
    obtain ⟨h_t6_bnd, h_t6_lift⟩ := h_t6_post
    -- (12) Compose acc'.1 = `{ coefficients := a1.set k t6 }`, acc'.2 = scratch2.
    set a2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set k t6 with ha2_def
    set acc1' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      { coefficients := a2 } with hacc1'_def
    set acc' : AddMessageErrorReduceFC.Acc := (acc1', scratch2) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self_init message_init
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
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
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
              let (t', index_mut_back) ←
                Aeneas.Std.Array.index_mut_usize acc.1.coefficients k
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
                  t' (1441#i16)
              let scratch1' ← Aeneas.Std.Array.index_usize self_init.coefficients k
              let t2' ← Aeneas.Std.Array.index_usize message_init.coefficients k
              let scratch2' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.add scratch1' t2'
              let (t3', index_mut_back1) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back t1') k
              let t4' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.add t3' scratch2'
              let (t5', index_mut_back2) ←
                Aeneas.Std.Array.index_mut_usize (index_mut_back1 t4') k
              let t6' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t5'
              .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back2 t6' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
                        scratch2')))
            = _
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_scratch1]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_t2]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_scratch2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t3]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t5]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t6_eq]
      rfl
    apply triple_of_ok_fc h_body
    show AddMessageErrorReduceFC.step_post self_init message_init result_init k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold AddMessageErrorReduceFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (AddMessageErrorReduceFC.inv self_init message_init result_init s acc').holds
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.1.coefficients.val[j]!)
            = Spec.chunk_add_message_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (message_init.coefficients.val[j]!))
                (lift_chunk (result_init.coefficients.val[j]!)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.1.coefficients.val[j]! = result_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < s.val → ∀ m : Nat, m < 16 →
            ((acc'.1.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) j < s.val → FC equation at chunk j.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.1.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.1.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.1.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.1.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.1.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.1.coefficients.set k t1).val[j]!)
              = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: chunk j = t6. Need:
          --   lift_chunk t6 = chunk_add_message_error_reduce_pure
          --     (lift_chunk self_init[k]) (lift_chunk message_init[k])
          --     (lift_chunk result_init[k]).
          subst hj_eq_k
          have h_set_eq : ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.1.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          rw [h_t6_lift]
          show Spec.chunk_barrett_reduce_pure (lift_chunk t4)
              = Spec.chunk_add_message_error_reduce_pure
                  (lift_chunk (self_init.coefficients.val[k.val]!))
                  (lift_chunk (message_init.coefficients.val[k.val]!))
                  (lift_chunk (result_init.coefficients.val[k.val]!))
          unfold Spec.chunk_barrett_reduce_pure Spec.chunk_add_message_error_reduce_pure
          apply Subtype.ext
          change (List.range 16).map (fun i =>
              Spec.barrett_pure ((lift_chunk t4).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk (result_init.coefficients.val[k.val]!)).val[ℓ]!)
                  (lift_fe_mont (1441#i16)))
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                  ((lift_chunk (message_init.coefficients.val[k.val]!)).val[ℓ]!)))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            -- LHS: Spec.barrett_pure ((lift_chunk t4).val[ℓ]!).
            -- Step A: ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!).
            have h_t4_elems_len : t4.elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length t4
            have h_lc_t4 : ((lift_chunk t4).val[ℓ]!) = lift_fe (t4.elements.val[ℓ]!) := by
              unfold lift_chunk
              show ((t4.elements.val.map lift_fe)[ℓ]!) = _
              have h_len : (t4.elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_t4_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos t4.elements.val ℓ (by rw [h_t4_elems_len]; exact hℓ)]
            rw [h_lc_t4]
            -- Step B: barrett_pure (lift_fe t4[ℓ]) = lift_fe t4[ℓ].
            rw [barrett_pure_lift_fe]
            -- Step C: lift_fe t4[ℓ] = add_pure (lift_fe t1[ℓ]) (lift_fe scratch2[ℓ]).
            have hv4 := h_t4_val ℓ hℓ
            have h_lift_t4 :
                lift_fe (t4.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (lift_fe (t1.elements.val[ℓ]!))
                      (lift_fe (scratch2.elements.val[ℓ]!)) :=
              lift_fe_add_pure_eq _ _ _ hv4
            rw [h_lift_t4]
            -- Step D: lift_fe t1[ℓ] = mul_pure (lift_fe t[ℓ]) (lift_fe_mont 1441).
            have h_lift_t1 :
                lift_fe (t1.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)) :=
              lift_fe_mont_mul_pure_eq _ _ _ (h_t1_modq ℓ hℓ)
            rw [h_lift_t1]
            -- Step E: lift_fe scratch2[ℓ] = add_pure (lift_fe scratch1[ℓ]) (lift_fe t2[ℓ]).
            have hv_s2 := h_scratch2_val ℓ hℓ
            have h_lift_s2 :
                lift_fe (scratch2.elements.val[ℓ]!)
                  = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (lift_fe (scratch1.elements.val[ℓ]!))
                      (lift_fe (t2.elements.val[ℓ]!)) :=
              lift_fe_add_pure_eq _ _ _ hv_s2
            rw [h_lift_s2]
            -- Step F: rewrite t, scratch1, t2 to result_init[k], self_init[k],
            -- message_init[k] images via lift_chunk projection.
            have h_result_elems_len :
                (result_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_self_elems_len :
                (self_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_msg_elems_len :
                (message_init.coefficients.val[k.val]!).elements.val.length = 16 :=
              libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
            have h_lc_result : ((lift_chunk (result_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((result_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((result_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((result_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_result_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (result_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_result_elems_len]; exact hℓ)]
            have h_lc_self : ((lift_chunk (self_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((self_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((self_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_self_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (self_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_self_elems_len]; exact hℓ)]
            have h_lc_msg : ((lift_chunk (message_init.coefficients.val[k.val]!)).val[ℓ]!)
                = lift_fe ((message_init.coefficients.val[k.val]!).elements.val[ℓ]!) := by
              unfold lift_chunk
              show (((message_init.coefficients.val[k.val]!).elements.val.map lift_fe)[ℓ]!) = _
              have h_len :
                  ((message_init.coefficients.val[k.val]!).elements.val.map lift_fe).length = 16 := by
                rw [List.length_map]; exact h_msg_elems_len
              rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
              rw [List.getElem_map]
              rw [getElem!_pos (message_init.coefficients.val[k.val]!).elements.val ℓ
                (by rw [h_msg_elems_len]; exact hℓ)]
            rw [h_lc_result, h_lc_self, h_lc_msg]
            show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe (t.elements.val[ℓ]!)) (lift_fe_mont (1441#i16)))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (lift_fe (scratch1.elements.val[ℓ]!))
                    (lift_fe (t2.elements.val[ℓ]!)))
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (lift_fe ((result_init.coefficients.val[k.val]!).elements.val[ℓ]!))
                    (lift_fe_mont (1441#i16)))
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (lift_fe ((self_init.coefficients.val[k.val]!).elements.val[ℓ]!))
                    (lift_fe ((message_init.coefficients.val[k.val]!).elements.val[ℓ]!)))
            rw [show t = result_init.coefficients.val[k.val]! from h_t_eq,
                show scratch1 = self_init.coefficients.val[k.val]! from hscratch1_def,
                show t2 = message_init.coefficients.val[k.val]! from ht2_def]
      · -- (b) s.val ≤ j < 16 → acc'.1.coefs[j] = result_init.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = result_init.coefficients.val[j]!
        have h_set1 : ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!)
            = (((acc.1.coefficients.set k t1).set k t4).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              ((acc.1.coefficients.set k t1).set k t4) k j t6 h_ne
        have h_set2 : (((acc.1.coefficients.set k t1).set k t4).val[j]!)
            = ((acc.1.coefficients.set k t1).val[j]!) := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne
              (acc.1.coefficients.set k t1) k j t4 h_ne
        have h_set3 : ((acc.1.coefficients.set k t1).val[j]!)
            = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients k j t1 h_ne
        rw [h_set1, h_set2, h_set3]
        exact h_acc_undone j h_ge' hj_lt
      · -- (c) j < s.val → per-lane Barrett bound on acc'.1.coefs[j].
        intro j hj m hm
        rw [hs_val] at hj
        show (((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!).elements.val[m]!).val.natAbs ≤ 1664
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged through all three sets — reuse the incoming bound.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set1 : ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[j]!)
              = (((acc.1.coefficients.set k t1).set k t4).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                ((acc.1.coefficients.set k t1).set k t4) k j t6 h_ne
          have h_set2 : (((acc.1.coefficients.set k t1).set k t4).val[j]!)
              = ((acc.1.coefficients.set k t1).val[j]!) := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne
                (acc.1.coefficients.set k t1) k j t4 h_ne
          have h_set3 : ((acc.1.coefficients.set k t1).val[j]!)
              = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients k j t1 h_ne
          rw [h_set1, h_set2, h_set3]
          exact h_acc_bnd_done j hj_lt_k m hm
        · -- j = k.val: chunk j = t6, the Barrett-reduced output (|·| ≤ 1664).
          subst hj_eq_k
          have h_set_eq : ((((acc.1.coefficients.set k t1).set k t4).set k t6).val[k.val]!)
              = t6 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq
                ((acc.1.coefficients.set k t1).set k t4) k k.val t6
                ⟨rfl, by simp; exact hk_16⟩
          rw [h_set_eq]
          exact h_t6_bnd m hm
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self_init message_init
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
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
    apply triple_of_ok_fc h_body
    show AddMessageErrorReduceFC.step_post self_init message_init result_init k (.done acc)
    unfold AddMessageErrorReduceFC.step_post
    show (AddMessageErrorReduceFC.inv self_init message_init result_init 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
          lift_chunk (acc.1.coefficients.val[j]!)
            = Spec.chunk_add_message_error_reduce_pure
                (lift_chunk (self_init.coefficients.val[j]!))
                (lift_chunk (message_init.coefficients.val[j]!))
                (lift_chunk (result_init.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.1.coefficients.val[j]! = result_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((acc.1.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj m hm; rw [h16] at hj
        exact h_acc_bnd_done j (by rw [hk_eq]; exact hj) m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.6 — `add_message_error_reduce`: combines `self · (R/128)` with
    `result + message` then barrett. Returns `(re, scratch)` tuple; we
    project on `re`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_result_bnd`: per-lane `|result[k][ℓ]| ≤ 32767` (consumed by
      `mont_mul`'s legacy precondition).
    - `h_sum_bnd`: per-lane `|self[k][ℓ] + message[k][ℓ]| ≤ 29439` (drives
      both `add`s: first `self + message` directly; then `t1 + scratch2`
      with |t1| ≤ 3328 + |scratch2| ≤ 29439 = 32767). -/
@[spec]
theorem add_message_error_reduce_fc
    (self message result : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_result_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((result.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (h_sum_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      (((self.coefficients.val[chunk]!).elements.val[ℓ]!).val
        + ((message.coefficients.val[chunk]!).elements.val[ℓ]!).val
            : Int).natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self message result scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1
                = Spec.add_message_error_reduce_pure
                    (lift_poly self) (lift_poly message) (lift_poly result)
              ∧ (∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
                  ((p.1.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_message_error_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) self message
          iter1 acc1.1 acc1.2)
      (β := AddMessageErrorReduceFC.Acc)
      (result, scratch)
      0#usize 16#usize
      (AddMessageErrorReduceFC.inv self message result)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial
        · intro j hj; exact absurd hj (Nat.not_lt_zero j))
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (AddMessageErrorReduceFC.inv self message result 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.1.coefficients.val[j]!)
              = Spec.chunk_add_message_error_reduce_pure
                  (lift_chunk (self.coefficients.val[j]!))
                  (lift_chunk (message.coefficients.val[j]!))
                  (lift_chunk (result.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.1.coefficients.val[j]! = result.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ m : Nat, m < 16 →
            ((r.1.coefficients.val[j]!).elements.val[m]!).val.natAbs ≤ 1664) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             AddMessageErrorReduceFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    -- Split the conjunctive postcondition: lift equation, then the Barrett bound.
    refine ⟨?_, fun j hj m hm => h_bnd j hj m hm⟩
    unfold Spec.add_message_error_reduce_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_add_message_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly message) k)
          (Spec.chunk_at (lift_poly result) k)))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.1.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_add_message_error_reduce_pure
          (Spec.chunk_at (lift_poly self) k)
          (Spec.chunk_at (lift_poly message) k)
          (Spec.chunk_at (lift_poly result) k)))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc self k hk, chunk_at_lift_poly_fc message k hk,
          chunk_at_lift_poly_fc result k hk]
      exact (h_done k hk).symm
    have h_final := flatten_chunks_eq_lift_poly_fc r.1 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step entailment.
    intro acc k _h_ge h_le hinv
    have h_step :=
      add_message_error_reduce_step_lemma_fc self message result
        h_result_bnd h_sum_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : AddMessageErrorReduceFC.step_post self message result k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddMessageErrorReduceFC.step_post] using hP
    · have hP : AddMessageErrorReduceFC.step_post self message result k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AddMessageErrorReduceFC.step_post] using hP

namespace SubtractReduceFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator (the mutable `out` poly). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `poly_reducing_from_i32_array_fc` (per-lane).
    * (a) Chunks `j < k`, lanes `ℓ < 16`: per-lane mont equality
          `lift_fe_mont acc[j][ℓ] = Spec.mont_reduce_pure (lift_fe_int a[16*j+ℓ])`.
    * (b) Chunks `k ≤ j < 16`: `acc[j] = out_init[j]` (unchanged).
    * (c) Chunks `j < k`, lanes `ℓ < 16`: per-lane I16 bound
          `|acc[j][ℓ]| ≤ 4993`, propagated from
          `reducing_from_i32_array_fc`'s strengthened POST. Used by L6.5
          (`add_standard_error_reduce_fc`) via `4993 ≤ 32767`.
    Using a per-lane invariant avoids reasoning about sub-slice
    equality at the chunk level (`lift_chunk_mont` vs sub-slice
    `Spec.chunk_reducing_from_i32_array_pure`). -/
def inv (a : Slice Std.I32) (out_init : Acc) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
      lift_fe_mont ((acc.coefficients.val[j]!).elements.val[ℓ]!)
        = Spec.mont_reduce_pure (lift_fe_int (a.val[16 * j + ℓ]!).val))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = out_init.coefficients.val[j]!)
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post (a : Slice Std.I32) (out_init : Acc) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv a out_init iter'.start acc').holds
  | .done y => (inv a out_init 16#usize y).holds

end SubtractReduceFC

/-- Sub-slice extraction `.ok`-form. Given a slice `a` and a range
    `[start, end] ⊆ [0, a.length]`, the `core_models`-level slice index
    succeeds with `s.val = a.val.slice start.val end.val` and
    `s.val.length = end.val - start.val`. -/
theorem slice_index_range_ok_eq_fc
    {T : Type} (a : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ a.val.length) :
    ∃ s : Slice T,
      core.Slice.Insts.CoreOpsIndexIndex.index
        (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T)
        a r = .ok s
      ∧ s.val = a.val.slice r.start.val r.end.val
      ∧ s.val.length = r.end.val - r.start.val := by
  have hT := libcrux_iot_ml_kem.Util.SliceSpecs.core_models_Slice_Insts_index_RangeUsize_spec
              (T := T) a r h0 h1
  obtain ⟨s, h_eq, h_post⟩ := triple_exists_ok_fc hT
  exact ⟨s, h_eq, h_post.1, h_post.2⟩

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `poly.reducing_from_i32_array`.
    Given a valid loop state `(acc, k)` with `k.val < 16`, the impl:
    (i) extracts the sub-slice `s = a[16k..16(k+1)]`,
    (ii) overwrites chunk `k` of `acc` with
         `vector.reducing_from_i32_array s _` (the prior chunk value is
         discarded by the vector op),
    yielding the per-lane mont equality
    `lift_fe_mont acc'[k][ℓ] = Spec.mont_reduce_pure (lift_fe_int a[16k+ℓ])`
    for all ℓ, while preserving chunks `j ≠ k`. -/
theorem poly_reducing_from_i32_array_step_lemma_fc
    (a : Slice Std.I32) (out_init : SubtractReduceFC.Acc)
    (hlen : a.length = 256)
    (hbound : ∀ i : Nat, i < 256 → (a.val[i]!).val.natAbs ≤ 2^16 * 3328)
    (acc : SubtractReduceFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (SubtractReduceFC.inv a out_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) a
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ SubtractReduceFC.step_post a out_init k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_a_len : a.val.length = 256 := hlen
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some i = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s_iter, hs_val, h_iter_some⟩ :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) i1 := k * 16.
    have hi1_max : k.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum]
      have h1 : k.val * 16 ≤ 15 * 16 := Nat.mul_le_mul_right 16 hk_15
      have : (15 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, hi1_eq, hi1_val⟩ := usize_mul_ok_eq_fc k 16#usize hi1_max
    have hi1_val_eq : i1.val = 16 * k.val := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi1_val, hum]; omega
    -- (2) i2 := k + 1.
    have hi2_max : k.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hk_15 : k.val ≤ 15 := by omega
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hum]
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i2, hi2_eq, hi2_val⟩ := usize_add_ok_eq_fc k 1#usize hi2_max
    have hi2_val_eq : i2.val = k.val + 1 := by
      have hum : (1#usize : Std.Usize).val = 1 := rfl
      rw [hi2_val, hum]
    -- (3) i3 := i2 * 16.
    have hi3_max : i2.val * (16#usize : Std.Usize).val ≤ Std.Usize.max := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hum, hi2_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : (k.val + 1) * 16 ≤ 16 * 16 := Nat.mul_le_mul_right 16 this
      have : (16 * 16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i3, hi3_eq, hi3_val⟩ := usize_mul_ok_eq_fc i2 16#usize hi3_max
    have hi3_val_eq : i3.val = 16 * (k.val + 1) := by
      have hum : (16#usize : Std.Usize).val = 16 := rfl
      rw [hi3_val, hi2_val_eq, hum]; omega
    -- (4) Sub-slice extraction.
    have h0_le : i1.val ≤ i3.val := by rw [hi1_val_eq, hi3_val_eq]; omega
    have hi3_le : i3.val ≤ a.val.length := by
      rw [h_a_len, hi3_val_eq]
      have : k.val + 1 ≤ 16 := by omega
      have h1 : 16 * (k.val + 1) ≤ 16 * 16 := Nat.mul_le_mul_left _ this
      omega
    obtain ⟨s, h_s_eq, h_s_val, h_s_len⟩ :=
      slice_index_range_ok_eq_fc a { start := i1, «end» := i3 } h0_le hi3_le
    have h_s_len16 : s.length = 16 := by
      show s.val.length = 16
      rw [h_s_len]
      show i3.val - i1.val = 16
      rw [hi3_val_eq, hi1_val_eq]; omega
    -- (4a) Per-lane lookup: s.val[ℓ]! = a.val[16*k + ℓ]!.
    have h_s_lane : ∀ ℓ : Nat, ℓ < 16 →
        s.val[ℓ]! = a.val[16 * k.val + ℓ]! := by
      intro ℓ hℓ
      rw [h_s_val]
      have h_idx_lt : i1.val + ℓ < i3.val := by
        rw [hi1_val_eq, hi3_val_eq]; omega
      have h_end_le : i3.val ≤ a.val.length := hi3_le
      have h_bnd : i3.val ≤ a.val.length ∧ i1.val + ℓ < i3.val := ⟨h_end_le, h_idx_lt⟩
      rw [List.getElem!_slice i1.val i3.val ℓ a.val h_bnd]
      rw [hi1_val_eq]
    -- (4b) Per-lane bound for the sub-slice (consumed by `reducing_from_i32_array_fc`).
    have h_s_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (s.val[ℓ]!).val.natAbs ≤ 2^16 * 3328 := by
      intro ℓ hℓ
      rw [h_s_lane ℓ hℓ]
      apply hbound (16 * k.val + ℓ)
      have : k.val ≤ 15 := by omega
      have : 16 * k.val ≤ 16 * 15 := Nat.mul_le_mul_left 16 this
      omega
    -- (5) `index_mut_usize acc.coefficients k` → `(t, set_back) = (acc.coefs[k], acc.coefs.set k)`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.coefficients.val[k.val]! with ht_def
    have h_idx_t : Aeneas.Std.Array.index_usize acc.coefficients k = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.coefficients k
        (by rw [h_coef_len]; exact hk_16)
    have h_imt_t : Aeneas.Std.Array.index_mut_usize acc.coefficients k
        = .ok (t, acc.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_t]; rfl
    -- (6) Apply `reducing_from_i32_array_fc` to get `t1` with the chunk FC equation
    -- AND the per-lane I16 bound `|t1.elements[ℓ]| ≤ 4993` (used by L6.7's
    -- strengthened POST conjunct (c) at chunk k).
    obtain ⟨t1, h_t1_eq, h_t1_lift, h_t1_bnd⟩ :=
      triple_exists_ok_fc (reducing_from_i32_array_fc s t h_s_len16 h_s_bnd)
    -- (7) Compose `a1 := acc.coefficients.set k t1`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha1_def
    have h_a1_len : a1.length = 16 := by simp [ha1_def, h_coef_len]
    have h_a1_k : a1.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
          ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
    -- (8) Compose acc'.
    set acc' : SubtractReduceFC.Acc := { coefficients := a1 } with hacc'_def
    -- (9) Body equation.
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) a
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
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
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let i1' ← (k * 16#usize : Result Std.Usize)
              let i2' ← k + 1#usize
              let i3' ← i2' * 16#usize
              let s' ←
                core.Slice.Insts.CoreOpsIndexIndex.index
                  (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
                    Std.I32) a { start := i1', «end» := i3' }
              let (t', index_mut_back) ←
                Aeneas.Std.Array.index_mut_usize acc.coefficients k
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array s' t'
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back t1' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            : Result (ControlFlow _ _))
            = _
      rw [hi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [hi3_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_s_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_t]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let t1' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.reducing_from_i32_array s t
              .ok (ControlFlow.cont (({ start := s_iter, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := acc.coefficients.set k t1' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            : Result _)
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_fc h_body
    show SubtractReduceFC.step_post a out_init k
      (.cont (({ start := s_iter, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold SubtractReduceFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (SubtractReduceFC.inv a out_init s_iter acc').holds
    have h_inv_pure :
        (∀ j : Nat, j < s_iter.val → ∀ ℓ : Nat, ℓ < 16 →
          lift_fe_mont ((acc'.coefficients.val[j]!).elements.val[ℓ]!)
            = Spec.mont_reduce_pure (lift_fe_int (a.val[16 * j + ℓ]!).val))
        ∧ (∀ j : Nat, s_iter.val ≤ j → j < 16 →
            acc'.coefficients.val[j]! = out_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < s_iter.val → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) j < s_iter.val = k+1 → per-lane FC.
        intro j hj ℓ hℓ
        rw [hs_val] at hj
        show lift_fe_mont
              (((acc.coefficients.set k t1).val[j]!).elements.val[ℓ]!)
            = Spec.mont_reduce_pure (lift_fe_int (a.val[16 * j + ℓ]!).val)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk unchanged.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set]
          exact h_acc_done j hj_lt_k ℓ hℓ
        · -- j = k.val: chunk = t1; pull per-lane FC out of `h_t1_lift`.
          subst hj_eq_k
          have h_set_eq : ((acc.coefficients.set k t1).val[k.val]!) = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq]
          -- Extract per-lane via `lift_chunk_mont t1 = Spec.chunk_reducing_from_i32_array_pure s`.
          have h_t1_elems_len : t1.elements.val.length = 16 :=
            libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length t1
          -- From `lift_chunk_mont`'s .val list form and Subtype.ext on the chunk eq.
          have h_chunk_val :
              t1.elements.val.map lift_fe_mont
                = (List.range 16).map (fun i =>
                    Spec.mont_reduce_pure (lift_fe_int (s.val[i]!).val)) := by
            have h_unfold : (lift_chunk_mont t1).val
                  = (Spec.chunk_reducing_from_i32_array_pure s).val := by
              rw [h_t1_lift]
            unfold lift_chunk_mont Spec.chunk_reducing_from_i32_array_pure at h_unfold
            exact h_unfold
          -- Use `getElem!` form to dodge motive-not-type-correct issues.
          have h_lhs_get :
              (t1.elements.val.map lift_fe_mont)[ℓ]!
                = lift_fe_mont (t1.elements.val[ℓ]!) := by
            have h_len : (t1.elements.val.map lift_fe_mont).length = 16 := by
              rw [List.length_map]; exact h_t1_elems_len
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map]
            congr 1
            rw [getElem!_pos t1.elements.val ℓ (by rw [h_t1_elems_len]; exact hℓ)]
          have h_rhs_get :
              ((List.range 16).map (fun i =>
                Spec.mont_reduce_pure (lift_fe_int (s.val[i]!).val)))[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val) := by
            have h_len : ((List.range 16).map (fun i =>
                Spec.mont_reduce_pure (lift_fe_int (s.val[i]!).val))).length = 16 := by
              simp
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range]
          have h_lane :
              lift_fe_mont (t1.elements.val[ℓ]!)
                = Spec.mont_reduce_pure (lift_fe_int (s.val[ℓ]!).val) := by
            rw [← h_lhs_get, h_chunk_val, h_rhs_get]
          rw [h_lane]
          -- Substitute s.val[ℓ]! = a.val[16*k.val + ℓ]!.
          rw [h_s_lane ℓ hℓ]
      · -- (b) s_iter.val ≤ j < 16 → acc'.coefs[j] = out_init.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((acc.coefficients.set k t1).val[j]!)
            = out_init.coefficients.val[j]!
        have h_set : ((acc.coefficients.set k t1).val[j]!)
            = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        rw [h_set]
        exact h_acc_undone j h_ge' hj_lt
      · -- (c) j < s_iter.val = k+1 → per-lane I16 bound `|acc'[j][ℓ]| ≤ 4993`.
        intro j hj ℓ hℓ
        rw [hs_val] at hj
        show ((((acc.coefficients.set k t1).val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993)
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk unchanged, bound inherited from (c) at step k.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set]
          exact h_acc_bnd j hj_lt_k ℓ hℓ
        · -- j = k.val: chunk = t1; bound comes from `h_t1_bnd`.
          subst hj_eq_k
          have h_set_eq : ((acc.coefficients.set k t1).val[k.val]!) = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq]
          exact h_t1_bnd ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) a
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
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
    apply triple_of_ok_fc h_body
    show SubtractReduceFC.step_post a out_init k (.done acc)
    unfold SubtractReduceFC.step_post
    show (SubtractReduceFC.inv a out_init 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
          lift_fe_mont ((acc.coefficients.val[j]!).elements.val[ℓ]!)
            = Spec.mont_reduce_pure (lift_fe_int (a.val[16 * j + ℓ]!).val))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.coefficients.val[j]! = out_init.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j hj ℓ hℓ; rw [h16] at hj
        apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj ℓ hℓ; rw [h16] at hj
        apply h_acc_bnd j _ ℓ hℓ; rw [hk_eq]; exact hj
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.7 — poly-level `reducing_from_i32_array`. Returns a fresh poly
    from an `i32` slice via 16 chunkwise `reducing_from_i32_array` calls.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `hlen`: `a.length = 256` (the impl reads `a[16k..16(k+1)]` for k ∈ 0..16).
    - `hbound`: per-lane `|a[i]| ≤ 2^16 * 3328` (consumed by the chunk-level
      `reducing_from_i32_array_fc` precondition). -/
@[spec]
theorem poly_reducing_from_i32_array_fc
    (a : Slice Std.I32)
    (out : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (hlen : a.length = 256)
    (hbound : ∀ i : Nat, i < 256 → (a.val[i]!).val.natAbs ≤ 2^16 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
      (vectortraitsOperationsInst := portable_ops_inst) a out
    ⦃ ⇓ p => ⌜ lift_poly_mont p = Spec.poly_reducing_from_i32_array_pure a
                ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
                    ((p.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, out1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) a iter1 out1)
      (β := SubtractReduceFC.Acc)
      out
      0#usize 16#usize
      (SubtractReduceFC.inv a out)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial
        · intro j hj; exact absurd hj (Nat.not_lt_zero j))
      ?_)
  · -- Post entailment: at k=16, invariant gives per-lane FC for all 256 indices,
    -- AND the per-lane I16 bound `|r[j][ℓ]| ≤ 4993` for all j < 16.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (SubtractReduceFC.inv a out 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
            lift_fe_mont ((r.coefficients.val[j]!).elements.val[ℓ]!)
              = Spec.mont_reduce_pure (lift_fe_int (a.val[16 * j + ℓ]!).val))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.coefficients.val[j]! = out.coefficients.val[j]!)
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val → ∀ ℓ : Nat, ℓ < 16 →
            ((r.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4993) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             SubtractReduceFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone, h_bnd⟩ := h_inv
    refine ⟨?_, ?_⟩
    · -- Goal: `lift_poly_mont r = Spec.poly_reducing_from_i32_array_pure a`.
      -- Both sides are 256-lane `Std.Array.make` constructions; reduce to
      -- list equality via `Subtype.ext` and per-index via `List.ext_getElem`.
      unfold lift_poly_mont Spec.poly_reducing_from_i32_array_pure
      apply Subtype.ext
      show (List.range 256).map (fun j =>
              lift_fe_mont (r.coefficients.val[j / 16]!).elements.val[j % 16]!)
          = (List.range 256).map (fun i =>
              Spec.mont_reduce_pure (lift_fe_int (a.val[i]!).val))
      apply List.ext_getElem
      · simp
      · intro j hj1 _hj2
        have hj : j < 256 := by
          have : j < ((List.range 256).map (fun j' =>
              lift_fe_mont (r.coefficients.val[j' / 16]!).elements.val[j' % 16]!)).length := hj1
          simpa using this
        have h_div_lt : j / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hj
        have h_mod_lt : j % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
        have h_decomp : 16 * (j / 16) + j % 16 = j := by
          have := Nat.div_add_mod j 16
          omega
        have h16' : (16#usize : Std.Usize).val = 16 := rfl
        have h_inv_at := h_done (j / 16) (by rw [h16']; exact h_div_lt) (j % 16) h_mod_lt
        simp only [List.getElem_map, List.getElem_range]
        rw [h_inv_at, h_decomp]
    · -- Goal: per-lane I16 bound for all j < 16, ℓ < 16.
      intro j hj ℓ hℓ
      have h16' : (16#usize : Std.Usize).val = 16 := rfl
      exact h_bnd j (by rw [h16']; exact hj) ℓ hℓ
  · -- Step entailment: per-iteration step lemma.
    intro acc k _h_ge h_le hinv
    have h_step :=
      poly_reducing_from_i32_array_step_lemma_fc a out hlen hbound acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : SubtractReduceFC.step_post a out k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [SubtractReduceFC.step_post] using hP
    · have hP : SubtractReduceFC.step_post a out k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [SubtractReduceFC.step_post] using hP


end libcrux_iot_ml_kem.Polynomial.PolyOpsFc