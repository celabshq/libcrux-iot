/-
  # `Polynomial/PolyOpsFcBarrett.lean` — FC theorems for `polynomial.rs` ops.

  Houses the §L6.{1,2,4,5,6,7} FC obligations from the original
  `FCTargets.lean`. Lives separately from `Polynomial/PolyOps.lean`
  to break a dependency cycle (the existing `PolyOps.lean` is imported
  by `Polynomial/NttDrivers.lean`, while the FC theorems here depend
  on `Polynomial/NttDrivers.lean` and feed into `Ntt.lean`'s
  `ntt_binomially_sampled_ring_element_fc`).
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Spec.Pure
import LibcruxIotMlKem.Spec.ModularArith
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Extraction.Funs
import HacspecMlKem.Extraction.Funs

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


/-! ### Extracted from FCTargets.lean (§poly_l6_1). -/

namespace libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett
open libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L6 — poly-level ops (6 theorems). -/

/-! ### L6.1.A — Loop scaffolding for `poly_barrett_reduce_fc`.

    FC invariant for the 16-iter chunk-loop. Each iteration `i ∈ 0..16`
    applies `barrett_reduce` to chunk `i` of `self`, leaving chunks
    `j ≠ i` untouched. The chunk-level closure for chunk `i` is
      `lift_chunk acc'[i] = Spec.chunk_barrett_reduce_pure
                              (lift_chunk self[i])`
    where `Spec.chunk_barrett_reduce_pure` lifts `Spec.barrett_pure`
    pointwise across 16 lanes. -/

namespace BarrettReduceFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Step-local accumulator (the mutable poly being barrett-reduced). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `poly_barrett_reduce_fc`.
    * (a) Chunks `j < k`: FC equation `lift_chunk acc[j] =
          chunk_barrett_reduce_pure (lift_chunk self[j])`.
    * (b) Chunks `k ≤ j < 16`: `acc[j] = self[j]` (unchanged). -/
def inv
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.coefficients.val[j]!)
        = Spec.chunk_barrett_reduce_pure
            (lift_chunk (self.coefficients.val[j]!)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.coefficients.val[j]! = self.coefficients.val[j]!))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv self iter'.start acc').holds
  | .done y => (inv self 16#usize y).holds

end BarrettReduceFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for `poly_barrett_reduce`. Given a valid
    loop state `(acc, k)` with `k.val < 16`, applies `barrett_reduce` to
    chunk `k.val` of `acc`, recording the FC equation
    `lift_chunk acc'[k.val] = chunk_barrett_reduce_pure
                                (lift_chunk self[k.val])`
    while preserving chunks `j ≠ k.val`. -/
theorem poly_barrett_reduce_step_lemma_fc
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767)
    (acc : BarrettReduceFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (BarrettReduceFC.inv self k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc
    ⦃ ⇓ r => ⌜ BarrettReduceFC.step_post self k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
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
    -- (1a) `t = self.coefficients[k]` (via h_acc_undone at j=k).
    have h_t_eq : t = self.coefficients.val[k.val]! := by
      show acc.coefficients.val[k.val]! = self.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_bnd k.val hk_16 ℓ hℓ
    -- (2) `barrett_reduce t` → `t1`. Pre: |t[ℓ]| ≤ 32767 ✓.
    obtain ⟨t1, h_t1_eq, h_t1_post⟩ :=
      triple_exists_ok_fc (barrett_reduce_fc t h_t_bnd)
    obtain ⟨_h_t1_bnd, h_t1_lift⟩ := h_t1_post
    -- (3) Compose acc' = `{ coefficients := acc.coefs.set k t1 }`.
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.coefficients.set k t1 with ha_def
    set acc' : BarrettReduceFC.Acc := { coefficients := a } with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
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
                libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce t'
              .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back t1' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_imt_t]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_fc h_body
    show BarrettReduceFC.step_post self k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold BarrettReduceFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (BarrettReduceFC.inv self s acc').holds
    -- Invariant at (s, acc'): only chunk k changes (to t1).
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.coefficients.val[j]!)
            = Spec.chunk_barrett_reduce_pure
                (lift_chunk (self.coefficients.val[j]!)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.coefficients.val[j]! = self.coefficients.val[j]!) := by
      refine ⟨?_, ?_⟩
      · -- (a) j < s.val → FC equation at chunk j.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((acc.coefficients.set k t1).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j unchanged.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set : ((acc.coefficients.set k t1).val[j]!)
              = acc.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
          rw [h_set]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: chunk j = t1.
          subst hj_eq_k
          have h_set : ((acc.coefficients.set k t1).val[k.val]!) = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set]
          -- Goal: lift_chunk t1 = chunk_barrett_reduce_pure (lift_chunk self[k]).
          -- From h_t1_lift: lift_chunk t1 = chunk_barrett_reduce_pure (lift_chunk t).
          -- And t = self.coefficients[k] (h_t_eq).
          rw [h_t1_lift, h_t_eq]
      · -- (b) s.val ≤ j < 16 → acc'.coefs[j] = self.coefs[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        show ((acc.coefficients.set k t1).val[j]!) = self.coefficients.val[j]!
        have h_set : ((acc.coefficients.set k t1).val[j]!)
            = acc.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.coefficients k j t1 h_ne
        rw [h_set]
        exact h_acc_undone j h_ge' hj_lt
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
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
    show BarrettReduceFC.step_post self k (.done acc)
    unfold BarrettReduceFC.step_post
    show (BarrettReduceFC.inv self 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
          lift_chunk (acc.coefficients.val[j]!)
            = Spec.chunk_barrett_reduce_pure
                (lift_chunk (self.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.coefficients.val[j]! = self.coefficients.val[j]!) := by
      refine ⟨?_, ?_⟩
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L6.1 — `poly_barrett_reduce`: 16-chunk loop applying `barrett_reduce`
    per chunk. Spec target: hacspec `polynomial.poly_barrett_reduce`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_bnd`: per-lane `|self[chunk][ℓ]| ≤ 32767` (consumed by
      `barrett_reduce_fc`'s legacy precondition).

    Proof sketch:
    1. Unfold `VECTORS_IN_RING_ELEMENT = .ok 16#usize`.
    2. Apply `loop_range_spec_usize` with invariant `BarrettReduceFC.inv`.
    3. Per-iter step lemma (above) closes the body via `barrett_reduce_fc`.
    4. Post-entailment: at `k=16`, each chunk satisfies the FC equation
       `lift_chunk r.coefs[k] = chunk_barrett_reduce_pure (lift_chunk self.coefs[k])`.
       Build `chunks_arr` from this and use `flatten_chunks_eq_lift_poly_fc` to
       get `flatten_chunks chunks_arr = lift_poly r`. Then bridge to the
       hacspec post via `poly_barrett_reduce_eq_ok` (canonical lanes: `barrett_pure`
       is identity on `lift_fe` images, so the pure projection coincides with
       `flatten_chunks chunks_arr` pointwise). -/
@[spec]
theorem poly_barrett_reduce_fc
    (self : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((self.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce
      (vectortraitsOperationsInst := portable_ops_inst) self
    ⦃ ⇓ p => ⌜ hacspec_ml_kem.polynomial.poly_barrett_reduce (lift_poly self)
                = .ok (lift_poly p) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce
  -- Resolve `VECTORS_IN_RING_ELEMENT = .ok 16#usize`.
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  rw [h_vre]; simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.poly_barrett_reduce_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) iter1 acc1)
      (β := BarrettReduceFC.Acc)
      self
      0#usize 16#usize
      (BarrettReduceFC.inv self)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_⟩
        · -- No chunks done yet.
          intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · -- All chunks unchanged (acc = self) — but goal trivializes since acc = self
          -- and the second conjunct's body is `acc.coefs[j]! = self.coefs[j]!` which is rfl.
          intro _ _ _; trivial)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (BarrettReduceFC.inv self 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.coefficients.val[j]!)
              = Spec.chunk_barrett_reduce_pure
                  (lift_chunk (self.coefficients.val[j]!)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.coefficients.val[j]! = self.coefficients.val[j]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             BarrettReduceFC.inv] using h_inv_holds
    obtain ⟨h_done, _h_undone⟩ := h_inv
    -- Build chunks_arr matching `chunk_barrett_reduce_pure (chunk_at (lift_poly self) k)`,
    -- then apply `flatten_chunks_eq_lift_poly_fc` to get `flatten_chunks chunks_arr = lift_poly r`.
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_barrett_reduce_pure
          (Spec.chunk_at (lift_poly self) k)))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_barrett_reduce_pure
          (Spec.chunk_at (lift_poly self) k)))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc self k hk]
      exact (h_done k hk).symm
    have h_flat := flatten_chunks_eq_lift_poly_fc r chunks_arr h_chunks_len h_chunks_get
    -- Bridge to hacspec via `poly_barrett_reduce_eq_ok` + canonical-identity.
    rw [libcrux_iot_ml_kem.Spec.Pure.polynomial.poly_barrett_reduce_eq_ok]
    rw [libcrux_iot_ml_kem.Spec.Pure.polynomial.poly_barrett_reduce_pure_id_of_canonical
          (lift_poly self) (lift_poly_lanes_canonical self)]
    -- Goal: .ok (lift_poly self) = .ok (lift_poly r). Reduce via congrArg.
    congr 1
    -- Goal: lift_poly self = lift_poly r. Chain through flatten_chunks.
    rw [← h_flat]
    -- Goal: lift_poly self = flatten_chunks chunks_arr.
    apply Subtype.ext
    unfold Spec.flatten_chunks lift_poly
    show (List.range 256).map (fun j =>
            lift_fe (self.coefficients.val[j / 16]!).elements.val[j % 16]!)
        = (List.range 256).map (fun j => (chunks_arr.val[j / 16]!).val[j % 16]!)
    apply List.ext_getElem
    · simp
    · intro j hj1 _hj2
      have hj : j < 256 := by
        have : j < ((List.range 256).map _).length := hj1
        simpa using this
      have h_div_lt : j / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hj
      have h_mod_lt : j % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      -- Pull chunks_arr.val[j/16]! through the definition (Std.Array.make's .val[!]).
      have h_chunks_at :
          chunks_arr.val[j / 16]!
            = Spec.chunk_barrett_reduce_pure
                (Spec.chunk_at (lift_poly self) (j / 16)) := by
        rw [getElem!_pos chunks_arr.val (j / 16) (by rw [h_chunks_len]; exact h_div_lt)]
        show ((List.range 16).map (fun k =>
            Spec.chunk_barrett_reduce_pure
              (Spec.chunk_at (lift_poly self) k)))[j / 16]'_ = _
        rw [List.getElem_map, List.getElem_range]
      rw [h_chunks_at]
      -- Unfold chunk_barrett_reduce_pure: lane-wise barrett_pure.
      unfold Spec.chunk_barrett_reduce_pure
      -- The Std.Array.make's .val is the underlying list directly.
      show lift_fe (self.coefficients.val[j / 16]!).elements.val[j % 16]!
          = (((List.range 16).map (fun i =>
              Spec.barrett_pure ((Spec.chunk_at (lift_poly self) (j / 16)).val[i]!)))[j % 16]!)
      rw [getElem!_pos ((List.range 16).map (fun i =>
            Spec.barrett_pure ((Spec.chunk_at (lift_poly self) (j / 16)).val[i]!)))
          (j % 16) (by simp; exact h_mod_lt)]
      rw [List.getElem_map, List.getElem_range]
      -- chunk_at (lift_poly self) (j/16) = lift_chunk (self.coefs[j/16]!).
      rw [chunk_at_lift_poly_fc self (j / 16) h_div_lt]
      -- (lift_chunk x).val[j%16]! = lift_fe (x.elements.val[j%16]!).
      have h_self_elems_len : (self.coefficients.val[j / 16]!).elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
      have h_lc_self : ((lift_chunk (self.coefficients.val[j / 16]!)).val[j % 16]!)
          = lift_fe ((self.coefficients.val[j / 16]!).elements.val[j % 16]!) := by
        unfold lift_chunk
        show (((self.coefficients.val[j / 16]!).elements.val.map lift_fe)[j % 16]!) = _
        have h_len :
            ((self.coefficients.val[j / 16]!).elements.val.map lift_fe).length = 16 := by
          rw [List.length_map]; exact h_self_elems_len
        rw [getElem!_pos ((self.coefficients.val[j / 16]!).elements.val.map lift_fe)
            (j % 16) (by rw [h_len]; exact h_mod_lt)]
        rw [List.getElem_map]
        rw [getElem!_pos (self.coefficients.val[j / 16]!).elements.val (j % 16)
          (by rw [h_self_elems_len]; exact h_mod_lt)]
      rw [h_lc_self]
      rw [barrett_pure_lift_fe]
  · -- Step lemma application.
    intro acc k _h_ge h_le hinv
    have h_step := poly_barrett_reduce_step_lemma_fc self h_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : BarrettReduceFC.step_post self k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [BarrettReduceFC.step_post] using hP
    · have hP : BarrettReduceFC.step_post self k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [BarrettReduceFC.step_post] using hP


end libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett