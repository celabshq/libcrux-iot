/-
  # `Ntt.lean` — extracted from `FCTargets.lean` §ntt.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Ntt
open libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L3 — NTT driver loops (5 theorems). -/

/-! ### L3.0 — Helpers for the layer-N driver loops.

    `ZETAS_bound`, `polynomial.zeta_eq_ok_fc`, `polynomial.zeta_fc`
    expose the impl `polynomial.zeta` as a deterministic `.ok` value
    + Mont-domain bound. The chunk/flatten identities
    (`Spec.chunk_at_lift_poly`, `Spec.flatten_chunks_eq_lift_poly`)
    bridge `lift_poly` ↔ `Spec.chunk_at`/`Spec.flatten_chunks`. -/

unseal libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R in
theorem ZETAS_bound :
    ∀ i : Nat, i < 128 →
      ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i]!).val.natAbs
        ≤ 1664 := by
  intro i hi
  interval_cases i <;> decide

/-- Pure-projection: `polynomial.zeta i` reduces to the array lookup. -/
theorem polynomial.zeta_eq_ok_fc
    (i : Std.Usize) (hi : i.val < 128) :
    libcrux_iot_ml_kem.polynomial.zeta i
      = .ok ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!) := by
  unfold libcrux_iot_ml_kem.polynomial.zeta
  exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq
    libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R i (by
      rw [show libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R.length = 128
            from Std.Array.length_eq _]; exact hi)

/-- FC-style Triple for `polynomial.zeta`: returns the exact lookup
    value, with a Mont-domain absolute-value bound and the canonical-domain
    `lift_fe_mont` lift equal to `Spec.zeta_at i.val`. -/
@[spec high]
theorem polynomial.zeta_fc (i : Std.Usize) (hi : i.val < 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.zeta i
    ⦃ ⇓ r => ⌜ r = (libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!
              ∧ r.val.natAbs ≤ 1664
              ∧ lift_fe_mont r = Spec.zeta_at i.val ⌝ ⦄ := by
  apply triple_of_ok_fc (polynomial.zeta_eq_ok_fc i hi)
  refine ⟨rfl, ZETAS_bound i.val hi, ?_⟩
  unfold Spec.zeta_at
  rfl


/-! ### L3.1.A — Loop scaffolding for `ntt_at_layer_1_portable_fc`.

    Strengthened FC invariant for the 16-iter driver loop. Each iteration:
      (1) advances `zeta_i` by 4 (4 zeta lookups per chunk: positions
          `zeta_i + 4k + {1..4}`),
      (2) records the FC equation `lift_chunk acc.2[j] = Spec.chunk_ntt_layer_1_step_pure
          (lift_chunk re.coefs[j]) (Spec.zeta_at (zeta_i + 4j + ⋅))`
          for `j < k.val` (chunks already processed),
      (3) preserves `acc.2.coefficients[j] = re.coefficients[j]` for `j ≥ k.val`
          (chunks not yet processed).

    The step lemma chains the body's 9 sub-ops (zeta_i+1, index_mut, 4× zeta,
    3× usize_add, ntt_layer_1_step) using `polynomial.zeta_fc` and
    `ntt_layer_1_step_fc` (both `@[spec]`-tagged). -/

namespace Layer1FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_add_ok_eq` helper (mirrors `Equivalence/`). -/
theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `ntt_at_layer_1_portable_fc`. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val + 4 * k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_ntt_layer_1_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val + 4 * j + 1))
              (Spec.zeta_at (zeta_i_0.val + 4 * j + 2))
              (Spec.zeta_at (zeta_i_0.val + 4 * j + 3))
              (Spec.zeta_at (zeta_i_0.val + 4 * j + 4)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv zeta_i_0 re iter'.start acc').holds
  | .done y => (inv zeta_i_0 re 16#usize y).holds

end Layer1FC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma. Given a valid loop state `(acc, k)` with
    `k.val < 16`, advances `zeta_i` by 4 and records the FC equation for
    chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem ntt_at_layer_1_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_zeta_bnd : zeta_i_0.val + 64 ≤ 127)
    (acc : Layer1FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer1FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer1FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `zeta_i + 1`.  Bound: acc.1.val ≤ zeta_i_0.val + 64-4 = zeta_i_0+60 ≤ 124.
    have h_acc1_lt : acc.1.val + 4 ≤ zeta_i_0.val + 64 := by
      rw [h_zeta_acc]
      have h_k_le : 4 * k.val ≤ 60 := by omega
      omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_um3 : (3#usize : Std.Usize).val = 3 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer1FC.usize_add_ok_eq acc.1 1#usize h_z_max
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by
      rw [h_zi1_val_arith, h_zeta_acc]; omega
    -- (2) `index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]; rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- (3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      Layer1FC.usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by
      rw [h_zi3_val_arith, h_zeta_acc]; omega
    -- (5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_v, h_z2_bd, h_z2_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi3 h_zi3_lt)
    -- (6) `zi1 + 2`.
    have h_zi5_max : zi1.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]; scalar_tac
    obtain ⟨zi5, h_zi5_eq, h_zi5_val⟩ :=
      Layer1FC.usize_add_ok_eq zi1 2#usize h_zi5_max
    have h_zi5_val_arith : zi5.val = acc.1.val + 3 := by
      rw [h_zi5_val, h_um2, h_zi1_val_arith]
    have h_zi5_lt : zi5.val < 128 := by
      rw [h_zi5_val_arith, h_zeta_acc]; omega
    -- (7) `polynomial.zeta zi5`.
    obtain ⟨z3, h_z3_eq, h_z3_v, h_z3_bd, h_z3_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi5 h_zi5_lt)
    -- (8) `zi1 + 3`.
    have h_zi7_max : zi1.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um3]; scalar_tac
    obtain ⟨zi7, h_zi7_eq, h_zi7_val⟩ :=
      Layer1FC.usize_add_ok_eq zi1 3#usize h_zi7_max
    have h_zi7_val_arith : zi7.val = acc.1.val + 4 := by
      rw [h_zi7_val, h_um3, h_zi1_val_arith]
    have h_zi7_lt : zi7.val < 128 := by
      rw [h_zi7_val_arith, h_zeta_acc]; omega
    -- (9) `polynomial.zeta zi7`.
    obtain ⟨z4, h_z4_eq, h_z4_v, h_z4_bd, h_z4_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi7 h_zi7_lt)
    -- (10) `ntt_layer_1_step t z1 z2 z3 z4`. Pre: t's lanes ≤ 29439 (via h_pre + undone).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.ntt_layer_1_step.
    -- ntt_layer_1_step_fc consumes (vec, z0..z3, hz, hvec).
    obtain ⟨t1, h_t1_eq, h_t1_lift⟩ :=
      triple_exists_ok_fc (ntt_layer_1_step_fc t z1 z2 z3 z4
        ⟨h_z1_bd, h_z2_bd, h_z3_bd, h_z4_bd⟩ h_t_bd)
    -- Compose entire body.
    set acc' : Layer1FC.Acc := (zi7, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
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
      simp [Aeneas.Std.bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq,
            h_z2_eq, h_zi5_eq, h_z3_eq, h_zi7_eq, h_z4_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step t z1 z2 z3 z4
            Result.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi7,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]; rfl
    apply triple_of_ok_fc h_body
    show Layer1FC.step_post zeta_i_0 re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer1FC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Invariant at (s, acc').
    show (Layer1FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val + 4 * s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 1))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 2))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 3))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 4)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · -- acc'.1 = zi7, zi7.val = acc.1.val + 4 = zeta_i_0.val + 4 * (k.val + 1).
        show zi7.val = zeta_i_0.val + 4 * s.val
        rw [h_zi7_val_arith, h_zeta_acc, hs_val]; ring
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
        -- acc'.2.coefficients = acc.2.coefficients.set k t1.
        show lift_chunk ((acc.2.coefficients.set k t1).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: unchanged by set; use h_acc_done.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
          rw [h_set_ne_val]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: it's t1; use h_t1_lift + h_t_eq + zeta_lift identities.
          subst hj_eq_k
          have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val, h_t1_lift, h_t_eq]
          -- Need: Spec.chunk_ntt_layer_1_step_pure (lift_chunk re.coefficients[k]) (lift_fe_mont z1..z4)
          --   = Spec.chunk_ntt_layer_1_step_pure (lift_chunk re.coefficients[k])
          --       (Spec.zeta_at (zeta_i_0 + 4*k + 1..4)).
          -- Use h_z1_lift..h_z4_lift to rewrite lift_fe_mont zi → Spec.zeta_at zi.val.
          have h_zi1_z : zi1.val = zeta_i_0.val + 4 * k.val + 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          have h_zi3_z : zi3.val = zeta_i_0.val + 4 * k.val + 2 := by
            rw [h_zi3_val_arith, h_zeta_acc]
          have h_zi5_z : zi5.val = zeta_i_0.val + 4 * k.val + 3 := by
            rw [h_zi5_val_arith, h_zeta_acc]
          have h_zi7_z : zi7.val = zeta_i_0.val + 4 * k.val + 4 := by
            rw [h_zi7_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val + 4 * k.val + 1)
                from by rw [← h_zi1_z]; exact h_z1_lift]
          rw [show lift_fe_mont z2 = Spec.zeta_at (zeta_i_0.val + 4 * k.val + 2)
                from by rw [← h_zi3_z]; exact h_z2_lift]
          rw [show lift_fe_mont z3 = Spec.zeta_at (zeta_i_0.val + 4 * k.val + 3)
                from by rw [← h_zi5_z]; exact h_z3_lift]
          rw [show lift_fe_mont z4 = Spec.zeta_at (zeta_i_0.val + 4 * k.val + 4)
                from by rw [← h_zi7_z]; exact h_z4_lift]
      · -- All j ≥ s.val are unchanged.
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
        rw [h_set_ne_val]
        exact h_acc_undone j h_ge' hj_lt
    -- inv .. = pure (P)  with .holds reducing to P.
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
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
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer1FC.step_post zeta_i_0 re k (.done acc)
    unfold Layer1FC.step_post
    show (Layer1FC.inv zeta_i_0 re 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        acc.1.val = zeta_i_0.val + 4 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 1))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 2))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 3))
                  (Spec.zeta_at (zeta_i_0.val + 4 * j + 4)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3.1' — `ntt_at_layer_1` PortableVector-specialised FC equation.
    The impl returns `(zeta_i_after, re_after)`; we project on `re_after`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_bnd` : per-lane input bound 29439 across all 16 chunks × 16 lanes.
    - `h_zeta : zeta_i.val + 64 ≤ 127` — strengthened from original `≤ 128`
      to ensure all zeta indices `zeta_i+1 .. zeta_i+64` are < 128 (OOB
      check). Original `≤ 128` permitted `zeta_i.val = 64`, OOB on last iter. -/
@[spec high]
theorem ntt_at_layer_1_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + 64 ≤ 127) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_1_pure (lift_poly re) zeta_i ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          iter1 acc1.1 acc1.2)
      (β := Layer1FC.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer1FC.inv zeta_i re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0.
          show zeta_i.val = zeta_i.val + 4 * (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val + 4 * 0
          omega
        · -- No chunks done yet.
          intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · -- All chunks unchanged; goal collapses to True after simp.
          intro _ _ _
          trivial)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    -- Manually extract the inv payload (avoid `simp` aggression on `[!]`).
    have h_inv_holds : (Layer1FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val + 4 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val + 4 * j + 1))
                  (Spec.zeta_at (zeta_i.val + 4 * j + 2))
                  (Spec.zeta_at (zeta_i.val + 4 * j + 3))
                  (Spec.zeta_at (zeta_i.val + 4 * j + 4)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer1FC.inv] using h_inv_holds
    obtain ⟨_h_zeta_eq, h_done, _h_undone⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    -- `Spec.ntt_layer_1_pure (lift_poly re) zeta_i` unfolds to
    -- `flatten_chunks (Array.make 16 ((List.range 16).map (fun k =>
    --   chunk_ntt_layer_1_step_pure (chunk_at (lift_poly re) k) (zeta_at ...))))`.
    -- Show that the chunks array equals the `lift_chunk r.2.coefficients[k]` family
    -- via `h_done` + `chunk_at_lift_poly_fc`, then `flatten_chunks_eq_lift_poly_fc`.
    unfold Spec.ntt_layer_1_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_1_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + 4 * k + 1))
          (Spec.zeta_at (zeta_i.val + 4 * k + 2))
          (Spec.zeta_at (zeta_i.val + 4 * k + 3))
          (Spec.zeta_at (zeta_i.val + 4 * k + 4))))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.2.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_1_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + 4 * k + 1))
          (Spec.zeta_at (zeta_i.val + 4 * k + 2))
          (Spec.zeta_at (zeta_i.val + 4 * k + 3))
          (Spec.zeta_at (zeta_i.val + 4 * k + 4))))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc re k hk]
      exact (h_done k hk).symm
    -- Apply flatten_chunks_eq_lift_poly_fc (with `r.2` as the poly).
    have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma application: dispatch ntt_at_layer_1_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_1_step_lemma_fc zeta_i re h_bnd h_zeta acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer1FC.step_post zeta_i re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1FC.step_post] using hP
    · have hP : Layer1FC.step_post zeta_i re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1FC.step_post] using hP

/-! ### L3.2.A — Loop scaffolding for `ntt_at_layer_2_portable_fc`.

    Strengthened FC invariant for the 16-iter driver loop. Each iteration:
      (1) advances `zeta_i` by 2 (2 zeta lookups per chunk: positions
          `zeta_i + 2k + {1, 2}`),
      (2) records the FC equation `lift_chunk acc.2[j] = Spec.chunk_ntt_layer_2_step_pure
          (lift_chunk re.coefs[j]) (Spec.zeta_at (zeta_i + 2j + ⋅))`
          for `j < k.val` (chunks already processed),
      (3) preserves `acc.2.coefficients[j] = re.coefficients[j]` for `j ≥ k.val`
          (chunks not yet processed).

    The step lemma chains the body's 6 sub-ops (zeta_i+1, index_mut, 2× zeta,
    1× usize_add, ntt_layer_2_step) using `polynomial.zeta_fc` and
    `ntt_layer_2_step_fc` (both `@[spec]`-tagged). -/

namespace Layer2FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_add_ok_eq` helper (mirrors `Layer1FC.usize_add_ok_eq`). -/
theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `ntt_at_layer_2_portable_fc`. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val + 2 * k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_ntt_layer_2_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val + 2 * j + 1))
              (Spec.zeta_at (zeta_i_0.val + 2 * j + 2)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv zeta_i_0 re iter'.start acc').holds
  | .done y => (inv zeta_i_0 re 16#usize y).holds

end Layer2FC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for layer 2. Given a valid loop state
    `(acc, k)` with `k.val < 16`, advances `zeta_i` by 2 and records the
    FC equation for chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem ntt_at_layer_2_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_zeta_bnd : zeta_i_0.val + 32 ≤ 127)
    (acc : Layer2FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer2FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer2FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `zeta_i + 1`.  Bound: acc.1.val ≤ zeta_i_0.val + 32-2 = zeta_i_0+30 ≤ 125.
    have h_acc1_lt : acc.1.val + 2 ≤ zeta_i_0.val + 32 := by
      rw [h_zeta_acc]
      have h_k_le : 2 * k.val ≤ 30 := by omega
      omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer2FC.usize_add_ok_eq acc.1 1#usize h_z_max
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by
      rw [h_zi1_val_arith, h_zeta_acc]; omega
    -- (2) `index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]; rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- (3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      Layer2FC.usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by
      rw [h_zi3_val_arith, h_zeta_acc]; omega
    -- (5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_v, h_z2_bd, h_z2_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi3 h_zi3_lt)
    -- (6) `ntt_layer_2_step t z1 z2`. Pre: t's lanes ≤ 29439 (via h_pre + undone).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.ntt_layer_2_step.
    -- ntt_layer_2_step_fc consumes (vec, z0, z1, hz, hvec).
    obtain ⟨t1, h_t1_eq, h_t1_lift⟩ :=
      triple_exists_ok_fc (ntt_layer_2_step_fc t z1 z2
        ⟨h_z1_bd, h_z2_bd⟩ h_t_bd)
    -- Compose entire body.
    set acc' : Layer2FC.Acc := (zi3, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
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
      simp [Aeneas.Std.bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq, h_z2_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step t z1 z2
            Result.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi3,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]; rfl
    apply triple_of_ok_fc h_body
    show Layer2FC.step_post zeta_i_0 re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer2FC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Invariant at (s, acc').
    show (Layer2FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val + 2 * s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + 2 * j + 1))
                  (Spec.zeta_at (zeta_i_0.val + 2 * j + 2)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · -- acc'.1 = zi3, zi3.val = acc.1.val + 2 = zeta_i_0.val + 2 * (k.val + 1).
        show zi3.val = zeta_i_0.val + 2 * s.val
        rw [h_zi3_val_arith, h_zeta_acc, hs_val]; ring
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
        -- acc'.2.coefficients = acc.2.coefficients.set k t1.
        show lift_chunk ((acc.2.coefficients.set k t1).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: unchanged by set; use h_acc_done.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
          rw [h_set_ne_val]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: it's t1; use h_t1_lift + h_t_eq + zeta_lift identities.
          subst hj_eq_k
          have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val, h_t1_lift, h_t_eq]
          have h_zi1_z : zi1.val = zeta_i_0.val + 2 * k.val + 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          have h_zi3_z : zi3.val = zeta_i_0.val + 2 * k.val + 2 := by
            rw [h_zi3_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val + 2 * k.val + 1)
                from by rw [← h_zi1_z]; exact h_z1_lift]
          rw [show lift_fe_mont z2 = Spec.zeta_at (zeta_i_0.val + 2 * k.val + 2)
                from by rw [← h_zi3_z]; exact h_z2_lift]
      · -- All j ≥ s.val are unchanged.
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
        rw [h_set_ne_val]
        exact h_acc_undone j h_ge' hj_lt
    -- inv .. = pure (P)  with .holds reducing to P.
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
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
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer2FC.step_post zeta_i_0 re k (.done acc)
    unfold Layer2FC.step_post
    show (Layer2FC.inv zeta_i_0 re 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        acc.1.val = zeta_i_0.val + 2 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + 2 * j + 1))
                  (Spec.zeta_at (zeta_i_0.val + 2 * j + 2)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3.2 — `ntt_at_layer_2` PortableVector-specialised FC equation.
    The impl returns `(zeta_i_after, re_after)`; we project on `re_after`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_bnd` : per-lane input bound 29439 across all 16 chunks × 16 lanes.
    - `h_zeta : zeta_i.val + 32 ≤ 127` — strengthened from original `≤ 128`
      to ensure all zeta indices `zeta_i+1 .. zeta_i+32` are < 128 (OOB
      check). Original `≤ 128` permitted `zeta_i.val = 96`, OOB on last
      iter (index 128 = ZETAS table length). -/
@[spec high]
theorem ntt_at_layer_2_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + 32 ≤ 127) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_2_pure (lift_poly re) zeta_i ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          iter1 acc1.1 acc1.2)
      (β := Layer2FC.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer2FC.inv zeta_i re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0.
          show zeta_i.val = zeta_i.val + 2 * (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val + 2 * 0
          omega
        · -- No chunks done yet.
          intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · -- All chunks unchanged; goal collapses to True after simp.
          intro _ _ _
          trivial)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer2FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val + 2 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val + 2 * j + 1))
                  (Spec.zeta_at (zeta_i.val + 2 * j + 2)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer2FC.inv] using h_inv_holds
    obtain ⟨_h_zeta_eq, h_done, _h_undone⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    unfold Spec.ntt_layer_2_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_2_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + 2 * k + 1))
          (Spec.zeta_at (zeta_i.val + 2 * k + 2))))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.2.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_2_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + 2 * k + 1))
          (Spec.zeta_at (zeta_i.val + 2 * k + 2))))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc re k hk]
      exact (h_done k hk).symm
    -- Apply flatten_chunks_eq_lift_poly_fc (with `r.2` as the poly).
    have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma application: dispatch ntt_at_layer_2_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_2_step_lemma_fc zeta_i re h_bnd h_zeta acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer2FC.step_post zeta_i re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2FC.step_post] using hP
    · have hP : Layer2FC.step_post zeta_i re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2FC.step_post] using hP

/-! ### L3.3'.A — Loop scaffolding for `ntt_at_layer_3_portable_fc`.

    Strengthened FC invariant for the 16-iter driver loop. Each iteration:
      (1) advances `zeta_i` by 1 (1 zeta lookup per chunk: position
          `zeta_i + k + 1`),
      (2) records the FC equation `lift_chunk acc.2[j] =
          Spec.chunk_ntt_layer_3_step_pure (lift_chunk re.coefs[j])
          (Spec.zeta_at (zeta_i + j + 1))` for `j < k.val`,
      (3) preserves `acc.2.coefficients[j] = re.coefficients[j]` for `j ≥ k.val`.

    The step lemma chains the body's 4 sub-ops (zeta_i+1, index_mut, 1× zeta,
    ntt_layer_3_step) using `polynomial.zeta_fc` and `ntt_layer_3_step_fc`. -/

namespace Layer3FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_add_ok_eq` helper (mirrors `Layer2FC.usize_add_ok_eq`). -/
theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `ntt_at_layer_3_portable_fc`. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val + k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_ntt_layer_3_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val + j + 1)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv zeta_i_0 re iter'.start acc').holds
  | .done y => (inv zeta_i_0 re 16#usize y).holds

end Layer3FC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for layer 3. Given a valid loop state
    `(acc, k)` with `k.val < 16`, advances `zeta_i` by 1 and records the
    FC equation for chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem ntt_at_layer_3_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_zeta_bnd : zeta_i_0.val + 16 ≤ 127)
    (acc : Layer3FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer3FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer3FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    -- (1) `zeta_i + 1`.  Bound: acc.1.val ≤ zeta_i_0.val + 16-1 = zeta_i_0+15 ≤ 126.
    have h_acc1_lt : acc.1.val + 1 ≤ zeta_i_0.val + 16 := by
      rw [h_zeta_acc]
      have h_k_le : k.val ≤ 15 := by omega
      omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer3FC.usize_add_ok_eq acc.1 1#usize h_z_max
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by
      rw [h_zi1_val_arith, h_zeta_acc]; omega
    -- (2) `index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]; rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- (3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `ntt_layer_3_step t z1`. Pre: t's lanes ≤ 29439 (via h_pre + undone).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.ntt_layer_3_step.
    -- ntt_layer_3_step_fc consumes (vec, z, hz, hvec).
    obtain ⟨t1, h_t1_eq, h_t1_lift⟩ :=
      triple_exists_ok_fc (ntt_layer_3_step_fc t z1 h_z1_bd h_t_bd)
    -- Compose entire body.
    set acc' : Layer3FC.Acc := (zi1, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
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
      simp [Aeneas.Std.bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step t z1
            Result.ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi1,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]; rfl
    apply triple_of_ok_fc h_body
    show Layer3FC.step_post zeta_i_0 re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer3FC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Invariant at (s, acc').
    show (Layer3FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val + s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + j + 1)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · -- acc'.1 = zi1, zi1.val = acc.1.val + 1 = zeta_i_0.val + (k.val + 1).
        show zi1.val = zeta_i_0.val + s.val
        rw [h_zi1_val_arith, h_zeta_acc, hs_val]; ring
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
        -- acc'.2.coefficients = acc.2.coefficients.set k t1.
        show lift_chunk ((acc.2.coefficients.set k t1).val[j]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: unchanged by set; use h_acc_done.
          have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
          rw [h_set_ne_val]
          exact h_acc_done j hj_lt_k
        · -- j = k.val: it's t1; use h_t1_lift + h_t_eq + zeta_lift identities.
          subst hj_eq_k
          have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val, h_t1_lift, h_t_eq]
          have h_zi1_z : zi1.val = zeta_i_0.val + k.val + 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val + k.val + 1)
                from by rw [← h_zi1_z]; exact h_z1_lift]
      · -- All j ≥ s.val are unchanged.
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        have h_ne : k.val ≠ j := by omega
        have h_ge' : k.val ≤ j := by omega
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
        rw [h_set_ne_val]
        exact h_acc_undone j h_ge' hj_lt
    -- inv .. = pure (P)  with .holds reducing to P.
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
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
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer3FC.step_post zeta_i_0 re k (.done acc)
    unfold Layer3FC.step_post
    show (Layer3FC.inv zeta_i_0 re 16#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        acc.1.val = zeta_i_0.val + (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val + j + 1)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3.3' — `ntt_at_layer_3` PortableVector-specialised FC equation.
    The impl returns `(zeta_i_after, re_after)`; we project on `re_after`.

    **Preconditions** (load-bearing, beyond the locked True-pre form):
    - `h_bnd` : per-lane input bound 29439 across all 16 chunks × 16 lanes.
    - `h_zeta : zeta_i.val + 16 ≤ 127` — ensures all zeta indices
      `zeta_i+1 .. zeta_i+16` are < 128 (OOB check on ZETAS table). -/
@[spec high]
theorem ntt_at_layer_3_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + 16 ≤ 127) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_3_pure (lift_poly re) zeta_i ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          iter1 acc1.1 acc1.2)
      (β := Layer3FC.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer3FC.inv zeta_i re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0.
          show zeta_i.val = zeta_i.val + (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val + 0
          omega
        · -- No chunks done yet.
          intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · -- All chunks unchanged; goal collapses to True after simp.
          intro _ _ _
          trivial)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer3FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val + (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val + j + 1)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer3FC.inv] using h_inv_holds
    obtain ⟨_h_zeta_eq, h_done, _h_undone⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    unfold Spec.ntt_layer_3_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_3_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + k + 1))))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16
      simp
    have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
        chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
          = lift_chunk (r.2.coefficients.val[k]!) := by
      intro k hk
      show ((List.range 16).map (fun k =>
        Spec.chunk_ntt_layer_3_step_pure (Spec.chunk_at (lift_poly re) k)
          (Spec.zeta_at (zeta_i.val + k + 1))))[k]'_ = _
      rw [List.getElem_map, List.getElem_range]
      rw [chunk_at_lift_poly_fc re k hk]
      exact (h_done k hk).symm
    -- Apply flatten_chunks_eq_lift_poly_fc (with `r.2` as the poly).
    have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma application: dispatch ntt_at_layer_3_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_3_step_lemma_fc zeta_i re h_bnd h_zeta acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer3FC.step_post zeta_i re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3FC.step_post] using hP
    · have hP : Layer3FC.step_post zeta_i re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3FC.step_post] using hP

/-! ### L3.7.A — Loop scaffolding for `ntt_at_layer_7_portable_fc`.

    Strengthened FC invariant for the 8-iter chunk-pair butterfly loop.
    Each iteration j ∈ 0..8 butterflies chunks at positions `(j, j+8)`
    with the constant Mont-form zeta `-1600`. Body sub-ops (10 total):
      load `re[j+8]`, multiply by `-1600`, load `re[j]`, write t to slot
      `j+8`, index_mut at j, add, index_mut at j+8, sub.

    The invariant tracks four clauses on the accumulator
    `(re_acc, scratch_acc)`:
      (a) chunks `j < k`: a-side butterflied (chunk_pair_butterfly_a_pure
          of (re[j], re[j+8]) at zeta `Spec.zeta_layer_7`).
      (b) chunks `j+8` for `j < k`: b-side butterflied
          (chunk_pair_butterfly_b_pure of (re[j], re[j+8])).
      (c) chunks `j` for `k ≤ j < 8`: unchanged.
      (d) chunks `j+8` for `k ≤ j < 8`: unchanged. -/

namespace Layer7FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_add_ok_eq` helper (mirrors `Layer2FC.usize_add_ok_eq`). -/
theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- `IteratorRange.next` with end-bound 8 — `Some` branch. -/
theorem iter_next8_some_eq (i : Std.Usize)
    (h_lt : i.val < (8#usize : Std.Usize).val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize i 8#usize
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := 8#usize }
                  : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  have hex : ∃ v, core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize) = .ok v
      ∧ (∃ s : Std.Usize, s.val = i.val + 1
        ∧ v = (some i,
                ({ start := s, «end» := 8#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))) := by
    generalize hx : core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize) = X at hT
    match X, hT with
    | .ok v, hT => exact ⟨v, rfl, by simpa [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply] using hT⟩
    | .fail _, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
    | .div, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  obtain ⟨v, hveq, s, hs_val, hpair⟩ := hex
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- `IteratorRange.next` with end-bound 8 — `None` branch. -/
theorem iter_next8_none_eq (i : Std.Usize)
    (h_ge : i.val ≥ (8#usize : Std.Usize).val) :
    core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := 8#usize }
              : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize i 8#usize
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := 8#usize }
              : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
  generalize hx : core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize) = X at hT
  match X, hT with
  | .ok v, hT =>
      have hP : v = ((none : Option Std.Usize),
                    ({ start := i, «end» := 8#usize }
                      : CoreModels.core.ops.range.Range Std.Usize)) := by
        simpa [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply] using hT
      rw [hP]
  | .fail _, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Step-local accumulator: `(re_acc, scratch_acc)`. -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `ntt_at_layer_7_portable_fc`. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    -- (a) chunks j < k: a-side butterfly result.
    (∀ j : Nat, j < k.val →
      lift_chunk (acc.1.coefficients.val[j]!)
        = Spec.chunk_pair_butterfly_a_pure
            (lift_chunk (re.coefficients.val[j]!))
            (lift_chunk (re.coefficients.val[j + 8]!))
            Spec.zeta_layer_7)
    -- (b) chunks j+8 for j < k: b-side butterfly result.
    ∧ (∀ j : Nat, j < k.val →
      lift_chunk (acc.1.coefficients.val[j + 8]!)
        = Spec.chunk_pair_butterfly_b_pure
            (lift_chunk (re.coefficients.val[j]!))
            (lift_chunk (re.coefficients.val[j + 8]!))
            Spec.zeta_layer_7)
    -- (c) chunks j for k ≤ j < 8: unchanged.
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
    -- (d) chunks j+8 for k ≤ j < 8: unchanged.
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j + 8]! = re.coefficients.val[j + 8]!))

/-- Step-post for `loop_range_spec_usize`. -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (8#usize : Std.Usize).val ∧ iter'.«end» = 8#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 8#usize y).holds

end Layer7FC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for layer 7. Given a valid loop state
    `(acc, k)` with `k.val < 8`, butterflies chunks `(k, k+8)` with the
    constant Mont-form zeta `-1600`, leaving other chunks unchanged. -/
theorem ntt_at_layer_7_step_lemma_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 20)
    (acc : Layer7FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_inv : (Layer7FC.inv re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) 8#usize
      { start := k, «end» := 8#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer7FC.step_post re k r ⌝ ⦄ := by
  have h8 : (8#usize : Std.Usize).val = 8 := rfl
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_done_a, h_acc_done_b, h_acc_undone_a, h_acc_undone_b⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- `Some j = k` branch.
    have hk_8 : k.val < 8 := by rw [h8] at h_lt; exact h_lt
    have hk_lt_16 : k.val < 16 := by omega
    have hk8_lt_16 : k.val + 8 < 16 := by omega
    obtain ⟨s, hs_val, h_iter_some⟩ := Layer7FC.iter_next8_some_eq k h_lt
    -- (1) `j + 8 = i`. Bound: k.val + 8 ≤ 15.
    have h_um8 : (8#usize : Std.Usize).val = 8 := rfl
    have h_i_max : k.val + (8#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um8]; scalar_tac
    obtain ⟨i_idx, h_i_eq, h_i_val⟩ :=
      Layer7FC.usize_add_ok_eq k 8#usize h_i_max
    have h_i_val_arith : i_idx.val = k.val + 8 := by rw [h_i_val, h_um8]
    -- (2) `index_usize re.coefficients i` → `scratch1 = acc.1.coefs[k+8]`.
    set scratch1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.1.coefficients.val[i_idx.val]! with hscratch1_def
    have h_idx_i : Aeneas.Std.Array.index_usize acc.1.coefficients i_idx
        = .ok scratch1 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.1.coefficients i_idx
        (by rw [h_coef_len, h_i_val_arith]; exact hk8_lt_16)
    -- The actual scratch1 equals re[k+8] (via h_acc_undone_b at j=k).
    have h_scratch1_eq : scratch1 = re.coefficients.val[k.val + 8]! := by
      show acc.1.coefficients.val[i_idx.val]! = re.coefficients.val[k.val + 8]!
      rw [h_i_val_arith]
      exact h_acc_undone_b k.val (Nat.le_refl _) hk_8
    -- (3) `multiply_by_constant scratch1 (-1600)#i16`.
    -- Use BOTH the FC lift and the legacy bound.
    have h_s1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (scratch1.elements.val[ℓ]!).val.natAbs ≤ 20 := by
      intro ℓ hℓ
      rw [h_scratch1_eq]
      exact h_pre (k.val + 8) hk8_lt_16 ℓ hℓ
    have h_s1_bnd_32767 : ∀ ℓ : Nat, ℓ < 16 →
        (scratch1.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro ℓ hℓ
      have := h_s1_bnd ℓ hℓ; omega
    have h_cm1600_bnd : ((-1600)#i16 : Std.I16).val.natAbs ≤ 1664 := by decide
    have h_prod_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((scratch1.elements.val[ℓ]!).val * ((-1600)#i16 : Std.I16).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb := h_s1_bnd ℓ hℓ
      have h_cm : ((-1600)#i16 : Std.I16).val = -1600 := by decide
      have h_abs : ((scratch1.elements.val[ℓ]!).val
            * ((-1600)#i16 : Std.I16).val : Int).natAbs
          ≤ ((scratch1.elements.val[ℓ]!).val : Int).natAbs * 1600 := by
        rw [h_cm]
        rw [Int.natAbs_mul]
        simp [Int.natAbs_neg]
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_step : ((scratch1.elements.val[ℓ]!).val : Int).natAbs * 1600 ≤ 20 * 1600 :=
        Nat.mul_le_mul_right _ hb
      omega
    obtain ⟨scratch2, h_s2_eq, h_s2_lift⟩ :=
      triple_exists_ok_fc (multiply_by_constant_fc scratch1 (-1600)#i16
        h_s1_bnd_32767 h_cm1600_bnd h_prod_bnd)
    -- Also extract the per-elem value-and-bound via legacy `_spec`.
    have h_s2_spec :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.multiply_by_constant_spec scratch1 (-1600)#i16 h_prod_bnd
    obtain ⟨scratch2', h_s2_eq', h_s2_per⟩ := triple_exists_ok_fc h_s2_spec
    have h_s2_same : scratch2 = scratch2' := by
      have := h_s2_eq.symm.trans h_s2_eq'
      cases this; rfl
    subst h_s2_same
    -- (4) `index_usize re.coefficients j` → `t = acc.1.coefs[k]`.
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.1.coefficients.val[k.val]! with ht_def
    have h_idx_j : Aeneas.Std.Array.index_usize acc.1.coefficients k
        = .ok t :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq acc.1.coefficients k
        (by rw [h_coef_len]; exact hk_lt_16)
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.1.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone_a k.val (Nat.le_refl _) hk_8
    have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 20 := by
      intro ℓ hℓ
      rw [h_t_eq]
      exact h_pre k.val hk_lt_16 ℓ hℓ
    -- (5) `Array.update acc.1.coefficients i t` → `a = acc.1.coefs.set i t`.
    set a : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.1.coefficients.set i_idx t with ha_def
    have h_upd_a : Aeneas.Std.Array.update acc.1.coefficients i_idx t
        = .ok a :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq acc.1.coefficients i_idx t
        (by rw [h_coef_len, h_i_val_arith]; exact hk8_lt_16)
    -- (6) `index_mut_usize a j` → `(t1, set_back) = (a.val[k]!, a.set k)`.
    have h_a_len : a.length = 16 := by
      simp [ha_def, h_coef_len]
    -- Need to know a.val[k.val]! = acc.1.coefficients.val[k.val]! = t (k ≠ i.val).
    have hki_ne : k.val ≠ i_idx.val := by rw [h_i_val_arith]; omega
    have h_a_k : a.val[k.val]! = acc.1.coefficients.val[k.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i_idx k.val t
          (fun h => hki_ne h.symm)
    have h_imt_j : Aeneas.Std.Array.index_mut_usize a k
        = .ok (t, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      have h_idx : Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a k (by rw [h_a_len]; exact hk_lt_16)
      rw [h_idx]
      have h_aval_eq : a.val[k.val]! = t := by rw [h_a_k]
      rw [h_aval_eq]; rfl
    -- (7) `vec.add t scratch2`. Pre: |t[ℓ] + scratch2[ℓ]| ≤ 32767.
    have h_s2_bnd : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val.natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ; exact (h_s2_per ℓ hℓ).2
    have h_s2_val : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val
          = (scratch1.elements.val[ℓ]!).val * ((-1600)#i16 : Std.I16).val := by
      intro ℓ hℓ; exact (h_s2_per ℓ hℓ).1
    have h_t_s2_add_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((t.elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t := h_t_bnd ℓ hℓ
      rw [h_s2_val ℓ hℓ]
      have h_s1_b := h_s1_bnd ℓ hℓ
      have h_cm : ((-1600)#i16 : Std.I16).val = -1600 := by decide
      rw [h_cm]
      have h_prod_le : ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs
            ≤ ((scratch1.elements.val[ℓ]!).val : Int).natAbs * 1600 := by
        rw [Int.natAbs_mul]; simp [Int.natAbs_neg]
      have h_prod_b : ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs ≤ 32000 := by
        have := Nat.mul_le_mul_right 1600 h_s1_b
        omega
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      -- |a + b| ≤ |a| + |b| ≤ 20 + 32000 = 32020.
      have h_abs_add : ((t.elements.val[ℓ]!).val
            + (scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs
          ≤ ((t.elements.val[ℓ]!).val : Int).natAbs
            + ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs :=
        Int.natAbs_add_le _ _
      omega
    obtain ⟨t2, h_t2_eq, h_t2_lift⟩ :=
      triple_exists_ok_fc (add_fc t scratch2 h_t_s2_add_bnd)
    -- (8) `set_back t2` = `a.set k t2`.
    set a1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t2 with ha1_def
    -- (9) `index_mut_usize a1 i`. Need a1.val[i.val]!. a1 = (acc.1.coefs.set i t).set k t2.
    -- Since k ≠ i, a1.val[i.val]! = (acc.1.coefs.set i t).val[i.val]! = t.
    have h_a1_len : a1.length = 16 := by
      simp [ha1_def, h_a_len]
    have h_a1_i : a1.val[i_idx.val]! = t := by
      have h_ne : k.val ≠ i_idx.val := hki_ne
      have h_step1 : a1.val[i_idx.val]! = a.val[i_idx.val]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne a k i_idx.val t2 h_ne
      have h_step2 : a.val[i_idx.val]! = t := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.1.coefficients i_idx i_idx.val t
            ⟨rfl, by rw [h_coef_len, h_i_val_arith]; exact hk8_lt_16⟩
      rw [h_step1, h_step2]
    have h_imt_i : Aeneas.Std.Array.index_mut_usize a1 i_idx
        = .ok (t, a1.set i_idx) := by
      unfold Aeneas.Std.Array.index_mut_usize
      have h_idx : Aeneas.Std.Array.index_usize a1 i_idx = .ok (a1.val[i_idx.val]!) :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a1 i_idx
          (by rw [h_a1_len, h_i_val_arith]; exact hk8_lt_16)
      rw [h_idx, h_a1_i]; rfl
    -- (10) `vec.sub t scratch2`. Pre: |t[ℓ] - scratch2[ℓ]| ≤ 32767.
    have h_t_s2_sub_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((t.elements.val[ℓ]!).val - (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
      intro ℓ hℓ
      have hb_t := h_t_bnd ℓ hℓ
      rw [h_s2_val ℓ hℓ]
      have h_s1_b := h_s1_bnd ℓ hℓ
      have h_cm : ((-1600)#i16 : Std.I16).val = -1600 := by decide
      rw [h_cm]
      have h_prod_b : ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs ≤ 32000 := by
        have h_prod_le : ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs
              = ((scratch1.elements.val[ℓ]!).val : Int).natAbs * 1600 := by
          rw [Int.natAbs_mul]; simp [Int.natAbs_neg]
        have := Nat.mul_le_mul_right 1600 h_s1_b
        omega
      have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
      rw [h_p2]
      have h_abs_sub : ((t.elements.val[ℓ]!).val
            - (scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs
          ≤ ((t.elements.val[ℓ]!).val : Int).natAbs
            + ((scratch1.elements.val[ℓ]!).val * (-1600) : Int).natAbs := by
        have := Int.natAbs_sub_le (t.elements.val[ℓ]!).val
          ((scratch1.elements.val[ℓ]!).val * (-1600))
        exact this
      omega
    obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
      triple_exists_ok_fc (sub_fc t scratch2 h_t_s2_sub_bnd)
    -- Compose acc'.
    set a2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set i_idx t4 with ha2_def
    set acc' : Layer7FC.Acc := (({ coefficients := a2 }
              : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
            scratch2) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) 8#usize
          { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 8#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      -- Unfold the `@[reducible]` inst-forwards for multiply_by_constant, add, sub
      -- to the arithmetic-form names used in `h_s2_eq`, `h_t2_eq`, `h_t4_eq`.
      show (do
              let i ← k + 8#usize
              let scratch1' ← Aeneas.Std.Array.index_usize acc.1.coefficients i
              let scratch2' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.multiply_by_constant
                    scratch1' (-1600)#i16
              let t' ← Aeneas.Std.Array.index_usize acc.1.coefficients k
              let a' ← Aeneas.Std.Array.update acc.1.coefficients i t'
              let (t1, index_mut_back) ← Aeneas.Std.Array.index_mut_usize a' k
              let t2' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.add
                  t1 scratch2'
              let (t3, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize
                (index_mut_back t2') i
              let t4' ←
                libcrux_iot_ml_kem.vector.portable.arithmetic.sub
                  t3 scratch2'
              .ok (ControlFlow.cont (({ start := s, «end» := 8#usize }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := index_mut_back1 t4' }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
                        scratch2'))) = _
      rw [h_i_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_i]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_s2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_j]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_upd_a]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_j]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t2_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_i]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rfl
    apply triple_of_ok_fc h_body
    show Layer7FC.step_post re k
      (.cont (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer7FC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (Layer7FC.inv re s acc').holds
    -- Now the invariant at (s, acc'). Note acc'.1.coefficients = a2 = (a.set k t2).set i_idx t4.
    --   a.set k t2: at i=k.val it is t2, elsewhere it is a = acc.1.coefs.set i_idx t.
    --   .set i_idx t4: at i=i_idx.val it is t4, elsewhere unchanged.
    have h_inv_pure :
        (∀ j : Nat, j < s.val →
          lift_chunk (acc'.1.coefficients.val[j]!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, j < s.val →
          lift_chunk (acc'.1.coefficients.val[j + 8]!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, s.val ≤ j → j < 8 →
            acc'.1.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ j : Nat, s.val ≤ j → j < 8 →
            acc'.1.coefficients.val[j + 8]! = re.coefficients.val[j + 8]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- (a) j < s.val → a-side butterfly.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((a1.set i_idx t4).val[j]!) = _
        -- j < k.val + 1 → j < k.val OR j = k.val.
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: unchanged in a2 (since j ≠ k.val ∧ j ≠ k.val+8).
          have h_ne_i : i_idx.val ≠ j := by rw [h_i_val_arith]; omega
          have h_ne_k : k.val ≠ j := Nat.ne_of_gt hj_lt_k
          have h_step1 : (a1.set i_idx t4).val[j]! = a1.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne a1 i_idx j t4 h_ne_i
          have h_step2 : a1.val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_ne_k
          have h_step3 : a.val[j]! = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i_idx j t
                (by rw [h_i_val_arith]; omega)
          rw [h_step1, h_step2, h_step3]
          exact h_acc_done_a j hj_lt_k
        · -- j = k.val: a2[k.val] = t2 (because k.val ≠ i_idx.val).
          subst hj_eq_k
          have h_ne_i : i_idx.val ≠ k.val := fun h => hki_ne h.symm
          have h_step1 : (a1.set i_idx t4).val[k.val]! = a1.val[k.val]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne a1 i_idx k.val t4 h_ne_i
          have h_step2 : a1.val[k.val]! = t2 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t2
                ⟨rfl, by rw [h_a_len]; exact hk_lt_16⟩
          rw [h_step1, h_step2]
          -- Goal: lift_chunk t2 = chunk_pair_butterfly_a_pure (lift_chunk re[k]) (lift_chunk re[k+8]) z_layer_7.
          rw [h_t2_lift]
          show Spec.chunk_add_pure (lift_chunk t) (lift_chunk scratch2)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re.coefficients.val[k.val]!))
                (lift_chunk (re.coefficients.val[k.val + 8]!))
                Spec.zeta_layer_7
          rw [h_s2_lift, ← h_scratch1_eq, ← h_t_eq]
          -- Goal: chunk_add_pure (lift_chunk t) (chunk_mul (lift_chunk scratch1) (lift_fe -1600))
          --     = chunk_pair_butterfly_a_pure (lift_chunk t) (lift_chunk scratch1) Spec.zeta_layer_7.
          unfold Spec.chunk_add_pure Spec.chunk_multiply_by_constant_pure
            Spec.chunk_pair_butterfly_a_pure Spec.zeta_layer_7
          apply Subtype.ext
          -- Goal now: .val of LHS = .val of RHS. The .val of Std.Array.make is the list.
          change (List.range 16).map (fun i =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                ((lift_chunk t).val[i]!)
                ((Std.Array.make 16#usize ((List.range 16).map (fun i =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))) (by simp)).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                ((lift_chunk t).val[ℓ]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[ℓ]!) (lift_fe ((-1600)#i16))))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            congr 1
            -- Goal: ((Std.Array.make 16 (range.map ...)).val[ℓ]!) = mul_pure ((lift_chunk scratch1).val[ℓ]!) (lift_fe ...).
            show ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16))))[ℓ]! = _
            have h_len : ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))).length = 16 := by simp
            have h_pos : ℓ < ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))).length := by
              rw [h_len]; exact hℓ
            rw [getElem!_pos _ ℓ h_pos]
            rw [List.getElem_map, List.getElem_range]
      · -- (b) j < s.val → b-side butterfly at j+8.
        intro j hj
        rw [hs_val] at hj
        show lift_chunk ((a1.set i_idx t4).val[j + 8]!) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
        · -- j < k.val: chunk j+8 unchanged in a2.
          have h_jp8_ne_i : j + 8 ≠ i_idx.val := by rw [h_i_val_arith]; omega
          have h_jp8_ne_k : j + 8 ≠ k.val := by omega
          have h_step1 : (a1.set i_idx t4).val[j + 8]! = a1.val[j + 8]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne a1 i_idx (j + 8) t4
                (fun h => h_jp8_ne_i h.symm)
          have h_step2 : a1.val[j + 8]! = a.val[j + 8]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne a k (j + 8) t2
                (fun h => h_jp8_ne_k h.symm)
          have h_step3 : a.val[j + 8]! = acc.1.coefficients.val[j + 8]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i_idx (j + 8) t
                (by rw [h_i_val_arith]; omega)
          rw [h_step1, h_step2, h_step3]
          exact h_acc_done_b j hj_lt_k
        · -- j = k.val: a2[k.val + 8] = t4 (because i_idx.val = k.val+8).
          subst hj_eq_k
          have h_i_eq_kp8 : i_idx.val = k.val + 8 := h_i_val_arith
          have h_step1 : (a1.set i_idx t4).val[k.val + 8]! = t4 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq a1 i_idx (k.val + 8) t4
                ⟨h_i_eq_kp8, by rw [h_a1_len]; exact hk8_lt_16⟩
          rw [h_step1]
          rw [h_t4_lift]
          show Spec.chunk_sub_pure (lift_chunk t) (lift_chunk scratch2)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re.coefficients.val[k.val]!))
                (lift_chunk (re.coefficients.val[k.val + 8]!))
                Spec.zeta_layer_7
          rw [h_s2_lift, ← h_scratch1_eq, ← h_t_eq]
          unfold Spec.chunk_sub_pure Spec.chunk_multiply_by_constant_pure
            Spec.chunk_pair_butterfly_b_pure Spec.zeta_layer_7
          apply Subtype.ext
          change (List.range 16).map (fun i =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                ((lift_chunk t).val[i]!)
                ((Std.Array.make 16#usize ((List.range 16).map (fun i =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))) (by simp)).val[i]!))
            = (List.range 16).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                ((lift_chunk t).val[ℓ]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[ℓ]!) (lift_fe ((-1600)#i16))))
          apply List.ext_getElem
          · simp
          · intro ℓ hℓ1 _hℓ2
            have hℓ : ℓ < 16 := by
              have : ℓ < (List.range 16).length := by simpa using hℓ1
              simpa using this
            rw [List.getElem_map, List.getElem_range,
                List.getElem_map, List.getElem_range]
            congr 1
            -- Goal: ((Std.Array.make 16 (range.map ...)).val[ℓ]!) = mul_pure ((lift_chunk scratch1).val[ℓ]!) (lift_fe ...).
            show ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16))))[ℓ]! = _
            have h_len : ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))).length = 16 := by simp
            have h_pos : ℓ < ((List.range 16).map (fun i =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_chunk scratch1).val[i]!) (lift_fe ((-1600)#i16)))).length := by
              rw [h_len]; exact hℓ
            rw [getElem!_pos _ ℓ h_pos]
            rw [List.getElem_map, List.getElem_range]
      · -- (c) s.val ≤ j < 8 → acc'[j] = re[j].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        show (a1.set i_idx t4).val[j]! = re.coefficients.val[j]!
        have h_j_ne_i : i_idx.val ≠ j := by rw [h_i_val_arith]; omega
        have h_j_ne_k : k.val ≠ j := by omega
        have h_step1 : (a1.set i_idx t4).val[j]! = a1.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i_idx j t4 h_j_ne_i
        have h_step2 : a1.val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_j_ne_k
        have h_step3 : a.val[j]! = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i_idx j t
              (by rw [h_i_val_arith]; omega)
        rw [h_step1, h_step2, h_step3]
        have hk_le_j : k.val ≤ j := by omega
        exact h_acc_undone_a j hk_le_j hj_lt
      · -- (d) s.val ≤ j < 8 → acc'[j+8] = re[j+8].
        intro j hj_ge hj_lt
        rw [hs_val] at hj_ge
        show (a1.set i_idx t4).val[j + 8]! = re.coefficients.val[j + 8]!
        have h_jp8_ne_i : j + 8 ≠ i_idx.val := by rw [h_i_val_arith]; omega
        have h_jp8_ne_k : j + 8 ≠ k.val := by omega
        have h_step1 : (a1.set i_idx t4).val[j + 8]! = a1.val[j + 8]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i_idx (j + 8) t4
              (fun h => h_jp8_ne_i h.symm)
        have h_step2 : a1.val[j + 8]! = a.val[j + 8]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne a k (j + 8) t2
              (fun h => h_jp8_ne_k h.symm)
        have h_step3 : a.val[j + 8]! = acc.1.coefficients.val[j + 8]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i_idx (j + 8) t
              (by rw [h_i_val_arith]; omega)
        rw [h_step1, h_step2, h_step3]
        have hk_le_j : k.val ≤ j := by omega
        exact h_acc_undone_b j hk_le_j hj_lt
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 8, done.
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h8] at hk_ge; omega
    have h_iter_none := Layer7FC.iter_next8_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) 8#usize
          { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := 8#usize } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := 8#usize }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer7FC.step_post re k (.done acc)
    unfold Layer7FC.step_post
    show (Layer7FC.inv re 8#usize acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < (8#usize : Std.Usize).val →
          lift_chunk (acc.1.coefficients.val[j]!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, j < (8#usize : Std.Usize).val →
          lift_chunk (acc.1.coefficients.val[j + 8]!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, (8#usize : Std.Usize).val ≤ j → j < 8 →
            acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ j : Nat, (8#usize : Std.Usize).val ≤ j → j < 8 →
            acc.1.coefficients.val[j + 8]! = re.coefficients.val[j + 8]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj; rw [h8] at hj
        apply h_acc_done_a j; rw [hk_eq]; exact hj
      · intro j hj; rw [h8] at hj
        apply h_acc_done_b j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h8] at hj_ge
        apply h_acc_undone_a j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro j hj_ge hj_lt
        rw [h8] at hj_ge
        apply h_acc_undone_b j _ hj_lt; rw [hk_eq]; exact hj_ge
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3.7' — `ntt_at_layer_7` PortableVector-specialised FC equation.
    Single chunk-stride-8 butterfly layer with constant zeta -1600.

    The impl iterates `j ∈ 0..8` and butterflies chunks `(j, j+8)` with
    constant Mont-form zeta `-1600`; the lifted constant is
    `Spec.zeta_layer_7 = lift_fe (-1600)#i16`.

    **Preconditions** (load-bearing):
    - `h_bnd` : per-lane input bound 20 across all 16 chunks × 16 lanes
      — strengthened from the original 29439 to admit
      `multiply_by_constant_fc`'s `hpre_prod` obligation with the
      constant `c = -1600`: `|20 * 1600| = 32000 ≤ 2^15 - 1 = 32767`.
      Callers are `ntt_binomially_sampled_ring_element` (binomial-sampled
      input range `{-3..3}`) and equivalents — comfortably below 20. -/
@[spec high]
theorem ntt_at_layer_7_portable_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 20) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_at_layer_7_pure (lift_poly re) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7
  -- The driver: `i ← VECTORS_IN_RING_ELEMENT (=16), step ← i/2 (=8); loop on (0..8)`.
  have h_vre : libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
                = .ok (16#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
    rfl
  have h_div : ((16#usize : Std.Usize) / (2#usize : Std.Usize) : Result Std.Usize)
                = .ok (8#usize : Std.Usize) := by
    have h_max : ((2#usize : Std.Usize).val : Nat) ≠ 0 := by decide
    obtain ⟨z, hz_eq, hz_v⟩ := Aeneas.Std.UScalar.div_spec (16#usize : Std.Usize) h_max
    have hz_val : (↑z : Nat) = 8 := by
      rw [hz_v]; decide
    have hz_eq8 : z = (8#usize : Std.Usize) := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      show z.val = (8#usize : Std.Usize).val
      rw [hz_val]; decide
    rw [hz_eq, hz_eq8]
  rw [h_vre]
  simp only [Aeneas.Std.bind_tc_ok]
  rw [h_div]
  simp only [Aeneas.Std.bind_tc_ok]
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) 8#usize
          iter1 acc1.1 acc1.2)
      (β := Layer7FC.Acc)
      (re, scratch)
      0#usize 8#usize
      (Layer7FC.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro j hj; exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _; trivial
        · intro _ _ _; trivial)
      ?_)
  · -- Post entailment: at k=8, the invariant gives all FC equations.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer7FC.inv re 8#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j : Nat, j < (8#usize : Std.Usize).val →
          lift_chunk (r.1.coefficients.val[j]!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, j < (8#usize : Std.Usize).val →
          lift_chunk (r.1.coefficients.val[j + 8]!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re.coefficients.val[j]!))
                (lift_chunk (re.coefficients.val[j + 8]!))
                Spec.zeta_layer_7)
        ∧ (∀ j : Nat, (8#usize : Std.Usize).val ≤ j → j < 8 →
            r.1.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ j : Nat, (8#usize : Std.Usize).val ≤ j → j < 8 →
            r.1.coefficients.val[j + 8]! = re.coefficients.val[j + 8]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer7FC.inv] using h_inv_holds
    obtain ⟨h_done_a, h_done_b, _h_undone_a, _h_undone_b⟩ := h_inv
    have h8 : (8#usize : Std.Usize).val = 8 := rfl
    unfold Spec.ntt_at_layer_7_pure
    -- Build chunks_arr matching the Spec layout: per chunk c ∈ 0..16:
    --   chunk_at_layer_4_plus_pure chunks0 7#usize (fun _ => zeta_layer_7) c.
    -- For layer 7: step_vec = 128/16 = 8; group = c/16 = 0; offset = c%16 = c.
    --   c < 8: a-side with partner c+8.
    --   c ≥ 8: b-side, partner c-8 (i.e. chunk = chunks0[c-8] - chunks0[c] * z).
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun c =>
        Spec.chunk_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          7#usize
          (fun _ => Spec.zeta_layer_7)
          c))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16; simp
    have h_chunks_get : ∀ c : Nat, (hc : c < 16) →
        chunks_arr.val[c]'(by rw [h_chunks_len]; exact hc)
          = lift_chunk (r.1.coefficients.val[c]!) := by
      intro c hc
      show ((List.range 16).map (fun c =>
        Spec.chunk_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          7#usize
          (fun _ => Spec.zeta_layer_7)
          c))[c]'_ = _
      rw [List.getElem_map, List.getElem_range]
      -- Unfold Spec.chunk_at_layer_4_plus_pure.
      unfold Spec.chunk_at_layer_4_plus_pure
      have h7 : (7#usize : Std.Usize).val = 7 := rfl
      have h_sv : (1 <<< (7#usize : Std.Usize).val) / 16 = 8 := by rw [h7]; decide
      have h_off : c % (2 * 8) = c := Nat.mod_eq_of_lt (by omega)
      simp only [h_sv, h_off]
      -- Now: if c < 8 then a-side else b-side.
      -- Inner chunks0 lookup at index c, c+8, c-8 reduces via chunk_at_lift_poly_fc.
      have h_chunks0_at : ∀ k : Nat, k < 16 →
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
              (by simp)).val[k]!
            = lift_chunk (re.coefficients.val[k]!) := by
        intro k hk
        have h_len_map : ((List.range 16).map (Spec.chunk_at (lift_poly re))).length = 16 := by simp
        show ((List.range 16).map (Spec.chunk_at (lift_poly re)))[k]! = _
        rw [getElem!_pos _ k (by rw [h_len_map]; exact hk)]
        rw [List.getElem_map, List.getElem_range]
        exact chunk_at_lift_poly_fc re k hk
      by_cases h_c_lt8 : c < 8
      · -- a-side: c < 8, partner c+8.
        simp only [if_pos h_c_lt8]
        rw [h_chunks0_at c (by omega), h_chunks0_at (c + 8) (by omega)]
        exact (h_done_a c h_c_lt8).symm
      · -- b-side: c ≥ 8, partner c-8.
        simp only [if_neg h_c_lt8]
        have h_c_lt_16 : c < 16 := hc
        have h_cm8 : c - 8 < 16 := by omega
        rw [h_chunks0_at (c - 8) h_cm8, h_chunks0_at c h_c_lt_16]
        -- Goal: chunk_pair_butterfly_b_pure (lift_chunk re[c-8]) (lift_chunk re[c]) Spec.zeta_layer_7
        --     = lift_chunk r.1.coefs[c]
        -- We have h_done_b (c-8) : lift_chunk r.1.coefs[(c-8) + 8]
        --   = chunk_pair_butterfly_b_pure (lift_chunk re[c-8]) (lift_chunk re[c-8+8]) z_layer_7.
        have h_cm8_lt8 : c - 8 < 8 := by omega
        have h_simp : c - 8 + 8 = c := by omega
        have := h_done_b (c - 8) h_cm8_lt8
        rw [h_simp] at this
        exact this.symm
    -- Apply flatten_chunks_eq_lift_poly_fc.
    have h_final := flatten_chunks_eq_lift_poly_fc r.1 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma dispatch.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_7_step_lemma_fc re h_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer7FC.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer7FC.step_post] using hP
    · have hP : Layer7FC.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer7FC.step_post] using hP

/-! ### L3.4_plus' — Helper namespace and lemmas.

    Layer 4-6 NTT driver: nested loop applying a single chunk-pair
    butterfly per inner iter at chunks `(a_offset+j, b_offset+j)` with
    one zeta per outer round. The keystone `ntt_layer_int_vec_step_fc`
    encapsulates the impl's `ntt.ntt_layer_int_vec_step` body, which
    performs `(coefs[a], coefs[b]) := (coefs[a] + scratch2, coefs[a] - scratch2)`
    where `scratch2 := mont_mult(coefs[b], zeta_r)`. -/

namespace Layer4PlusFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_add_ok_eq` helper. -/
theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- Local `usize_mul_ok_eq` helper. -/
theorem usize_mul_ok_eq (x y : Std.Usize)
    (h_max : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  have hT := Std.Usize.mul_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v⟩

/-- Generic `IteratorRange.next` Some branch for arbitrary end. -/
theorem iter_next_some_eq_gen (i e : Std.Usize)
    (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  have hex : ∃ v, core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = .ok v
      ∧ (∃ s : Std.Usize, s.val = i.val + 1
        ∧ v = (some i,
                ({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize))) := by
    generalize hx : core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = X at hT
    match X, hT with
    | .ok v, hT => exact ⟨v, rfl, by simpa [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply] using hT⟩
    | .fail _, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
    | .div, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  obtain ⟨v, hveq, s, hs_val, hpair⟩ := hex
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- Generic `IteratorRange.next` None branch for arbitrary end. -/
theorem iter_next_none_eq_gen (i e : Std.Usize)
    (h_ge : i.val ≥ e.val) :
    core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
  generalize hx : core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize) = X at hT
  match X, hT with
  | .ok v, hT =>
      have hP : v = ((none : Option Std.Usize),
                    ({ start := i, «end» := e }
                      : CoreModels.core.ops.range.Range Std.Usize)) := by
        simpa [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply] using hT
      rw [hP]
  | .fail _, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, hT => exact absurd hT (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])

end Layer4PlusFC

set_option maxHeartbeats 16000000 in
/-- L3.4_plus' keystone: full FC equation for `ntt.ntt_layer_int_vec_step`
    at the chunk-pair level. Performs the impl's compound body:
    `scratch2 = mont_mult(coefs[b], zeta_r)`,
    `coefs[a] := coefs[a] + scratch2`,
    `coefs[b] := coefs[a]_orig - scratch2`. -/
theorem ntt_layer_int_vec_step_fc
    (coefficients : Std.Array
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize)
    (a b : Std.Usize) (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_r : Std.I16)
    (ha : a.val < 16) (hb : b.val < 16) (hab : a.val ≠ b.val)
    (hzeta : zeta_r.val.natAbs ≤ 1664)
    (h_bnd_a : ∀ ℓ : Nat, ℓ < 16 →
      ((coefficients.val[a.val]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_bnd_b : ∀ ℓ : Nat, ℓ < 16 →
      ((coefficients.val[b.val]!).elements.val[ℓ]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
      (vectortraitsOperationsInst := portable_ops_inst)
      coefficients a b scratch zeta_r
    ⦃ ⇓ r => ⌜
      lift_chunk (r.1.val[a.val]!)
        = Spec.chunk_pair_butterfly_a_pure
            (lift_chunk (coefficients.val[a.val]!))
            (lift_chunk (coefficients.val[b.val]!))
            (lift_fe_mont zeta_r)
      ∧ lift_chunk (r.1.val[b.val]!)
        = Spec.chunk_pair_butterfly_b_pure
            (lift_chunk (coefficients.val[a.val]!))
            (lift_chunk (coefficients.val[b.val]!))
            (lift_fe_mont zeta_r)
      ∧ (∀ k : Nat, k < 16 → k ≠ a.val → k ≠ b.val →
          r.1.val[k]! = coefficients.val[k]!)
      ⌝ ⦄ := by
  have h_coef_len : coefficients.length = 16 := Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
  -- (1) index_usize coefficients b → scratch1 = coefs[b]
  set scratch1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[b.val]! with hscratch1_def
  have h_idx_b : Aeneas.Std.Array.index_usize coefficients b = .ok scratch1 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq coefficients b
      (by rw [h_coef_len]; exact hb)
  -- (2) montgomery_multiply_fe scratch1 zeta_r → scratch2 via inst forwarder.
  -- The inst forwarder does: classify zeta_r ; arithmetic.montgomery_multiply_by_constant.
  have h_classify_zeta : libcrux_secrets.traits.Classify.Blanket.classify zeta_r = .ok zeta_r :=
    ntt_step_fc.classify_ok_eq zeta_r
  have h_scratch1_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (scratch1.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro ℓ hℓ
    have h_v : (scratch1.elements.val[ℓ]!).val.natAbs
        = ((coefficients.val[b.val]!).elements.val[ℓ]!).val.natAbs := by
      rw [hscratch1_def]
    rw [h_v]
    have := h_bnd_b ℓ hℓ
    omega
  -- Per-element legacy spec to get the modq form.
  have h_s2_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec scratch1 zeta_r hzeta
  obtain ⟨scratch2, h_s2_eq, h_s2_per⟩ := triple_exists_ok_fc h_s2_legacy
  -- Bound the output: |scratch2| ≤ 3328.
  have h_s2_bnd_3328 : ∀ ℓ : Nat, ℓ < 16 →
      (scratch2.elements.val[ℓ]!).val.natAbs ≤ 3328 := fun ℓ hℓ => (h_s2_per ℓ hℓ).1
  -- (3) index_usize coefficients a → t = coefs[a]
  set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[a.val]! with ht_def
  have h_idx_a : Aeneas.Std.Array.index_usize coefficients a = .ok t :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq coefficients a
      (by rw [h_coef_len]; exact ha)
  have h_t_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (t.elements.val[ℓ]!).val.natAbs ≤ 29439 := fun ℓ hℓ => h_bnd_a ℓ hℓ
  -- (4) update coefficients b t → c1 = coefficients.set b t
  set c1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    coefficients.set b t with hc1_def
  have h_upd_b : Aeneas.Std.Array.update coefficients b t = .ok c1 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq coefficients b t
      (by rw [h_coef_len]; exact hb)
  have h_c1_len : c1.length = 16 := by simp [hc1_def, h_coef_len]
  -- (5) index_mut_usize c1 a → (t1, set_back) = (c1[a], c1.set a).
  have h_c1_a : c1.val[a.val]! = t := by
    show (coefficients.set b t).val[a.val]! = t
    -- a ≠ b, so c1[a] = coefficients[a] = t.
    have h_ne : b.val ≠ a.val := fun h => hab h.symm
    have h_step : (coefficients.set b t).val[a.val]! = coefficients.val[a.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne coefficients b a.val t h_ne
    rw [h_step]
  have h_imt_a : Aeneas.Std.Array.index_mut_usize c1 a = .ok (t, c1.set a) := by
    unfold Aeneas.Std.Array.index_mut_usize
    have h_idx : Aeneas.Std.Array.index_usize c1 a = .ok (c1.val[a.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq c1 a (by rw [h_c1_len]; exact ha)
    rw [h_idx, h_c1_a]; rfl
  -- (6) add t scratch2 → t2 = t + scratch2 (chunk-level). Pre: |t[ℓ] + scratch2[ℓ]| ≤ 32767.
  have h_t_s2_add_bnd : ∀ ℓ : Nat, ℓ < 16 →
      ((t.elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hbt := h_t_bnd ℓ hℓ
    have hbs2 := h_s2_bnd_3328 ℓ hℓ
    have h_abs_add : ((t.elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((t.elements.val[ℓ]!).val : Int).natAbs
          + ((scratch2.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨t2, h_t2_eq, h_t2_lift⟩ :=
    triple_exists_ok_fc (add_fc t scratch2 h_t_s2_add_bnd)
  -- For per-element value-form (needed downstream): use legacy add_spec.
  have h_t2_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec t scratch2 h_t_s2_add_bnd
  obtain ⟨t2', h_t2_eq', h_t2_per⟩ := triple_exists_ok_fc h_t2_legacy
  have h_t2_same : t2 = t2' := by
    have := h_t2_eq.symm.trans h_t2_eq'; cases this; rfl
  subst h_t2_same
  -- (7) set_back t2 = c1.set a t2 → c2.
  set c2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    c1.set a t2 with hc2_def
  have h_c2_len : c2.length = 16 := by simp [hc2_def, h_c1_len]
  -- (8) index_mut_usize c2 b → (t3, set_back') = (c2[b], c2.set b).
  -- c2 = (coefficients.set b t).set a t2. At index b, since a ≠ b, c2[b] = c1[b] = t.
  have h_c2_b : c2.val[b.val]! = t := by
    show (c1.set a t2).val[b.val]! = t
    have h_ne : a.val ≠ b.val := hab
    have h_step1 : (c1.set a t2).val[b.val]! = c1.val[b.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne c1 a b.val t2 h_ne
    have h_step2 : c1.val[b.val]! = t := by
      show (coefficients.set b t).val[b.val]! = t
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq coefficients b b.val t
          ⟨rfl, by rw [h_coef_len]; exact hb⟩
    rw [h_step1, h_step2]
  have h_imt_b : Aeneas.Std.Array.index_mut_usize c2 b = .ok (t, c2.set b) := by
    unfold Aeneas.Std.Array.index_mut_usize
    have h_idx : Aeneas.Std.Array.index_usize c2 b = .ok (c2.val[b.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq c2 b (by rw [h_c2_len]; exact hb)
    rw [h_idx, h_c2_b]; rfl
  -- (9) sub t scratch2 → t4 = t - scratch2 (chunk-level). Pre similar.
  have h_t_s2_sub_bnd : ∀ ℓ : Nat, ℓ < 16 →
      ((t.elements.val[ℓ]!).val - (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hbt := h_t_bnd ℓ hℓ
    have hbs2 := h_s2_bnd_3328 ℓ hℓ
    have h_abs_sub :
        ((t.elements.val[ℓ]!).val - (scratch2.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((t.elements.val[ℓ]!).val : Int).natAbs
          + ((scratch2.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_sub_le _ _
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨t4, h_t4_eq, h_t4_lift⟩ :=
    triple_exists_ok_fc (sub_fc t scratch2 h_t_s2_sub_bnd)
  have h_t4_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.sub_spec t scratch2 h_t_s2_sub_bnd
  obtain ⟨t4', h_t4_eq', h_t4_per⟩ := triple_exists_ok_fc h_t4_legacy
  have h_t4_same : t4 = t4' := by
    have := h_t4_eq.symm.trans h_t4_eq'; cases this; rfl
  subst h_t4_same
  -- (10) set_back' t4 = c2.set b t4 → c3 (final).
  set c3 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    c2.set b t4 with hc3_def
  -- Compose body equality.
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
        (vectortraitsOperationsInst := portable_ops_inst)
        coefficients a b scratch zeta_r
      = .ok (c3, scratch2) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
    show (do
            let scratch1' ← Aeneas.Std.Array.index_usize coefficients b
            let scratch2' ←
              libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe
                portable_ops_inst scratch1' zeta_r
            let t' ← Aeneas.Std.Array.index_usize coefficients a
            let c1' ← Aeneas.Std.Array.update coefficients b t'
            let (t1, index_mut_back) ← Aeneas.Std.Array.index_mut_usize c1' a
            let t2' ← portable_ops_inst.add t1 scratch2'
            let (t3, index_mut_back1) ←
              Aeneas.Std.Array.index_mut_usize (index_mut_back t2') b
            let t4' ← portable_ops_inst.sub t3 scratch2'
            .ok (index_mut_back1 t4', scratch2')) = _
    -- The instance methods reduce to vector.portable.arithmetic.{add,sub,montgomery_multiply_by_constant}.
    show (do
            let scratch1' ← Aeneas.Std.Array.index_usize coefficients b
            let scratch2' ← do
              let i ← libcrux_secrets.traits.Classify.Blanket.classify zeta_r
              libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant scratch1' i
            let t' ← Aeneas.Std.Array.index_usize coefficients a
            let c1' ← Aeneas.Std.Array.update coefficients b t'
            let (t1, index_mut_back) ← Aeneas.Std.Array.index_mut_usize c1' a
            let t2' ← libcrux_iot_ml_kem.vector.portable.arithmetic.add t1 scratch2'
            let (t3, index_mut_back1) ←
              Aeneas.Std.Array.index_mut_usize (index_mut_back t2') b
            let t4' ← libcrux_iot_ml_kem.vector.portable.arithmetic.sub t3 scratch2'
            .ok (index_mut_back1 t4', scratch2')) = _
    rw [h_idx_b]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify_zeta]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_a]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_b]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_imt_a]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_t2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_imt_b]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_t4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rfl
  apply triple_of_ok_fc h_body
  -- Now prove the post FC equations.
  refine ⟨?_, ?_, ?_⟩
  · -- (a) c3[a] = c2[a] (since c3 = c2.set b t4, and a ≠ b).
    -- c2[a] = t2 (by set_eq with set a t2).
    -- lift_chunk t2 = chunk_add_pure (lift_chunk t) (lift_chunk scratch2)  by h_t2_lift.
    -- Need: = chunk_pair_butterfly_a_pure (lift_chunk t) (lift_chunk scratch1) (lift_fe_mont zeta_r).
    show lift_chunk (c3.val[a.val]!) = _
    have h_ne : b.val ≠ a.val := fun h => hab h.symm
    have h_c3_a : c3.val[a.val]! = c2.val[a.val]! := by
      show (c2.set b t4).val[a.val]! = c2.val[a.val]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne c2 b a.val t4 h_ne
    have h_c2_a : c2.val[a.val]! = t2 := by
      show (c1.set a t2).val[a.val]! = t2
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq c1 a a.val t2
          ⟨rfl, by rw [h_c1_len]; exact ha⟩
    rw [h_c3_a, h_c2_a]
    -- Goal: lift_chunk t2 = chunk_pair_butterfly_a_pure (lift_chunk t) (lift_chunk scratch1) (lift_fe_mont zeta_r).
    -- We have h_t2_lift : lift_chunk t2 = chunk_add_pure (lift_chunk t) (lift_chunk scratch2).
    -- Need to show: chunk_add_pure (lift_chunk t) (lift_chunk scratch2)
    --             = chunk_pair_butterfly_a_pure (lift_chunk t) (lift_chunk scratch1) (lift_fe_mont zeta_r).
    rw [h_t2_lift]
    -- t = coefficients[a], scratch1 = coefficients[b].
    show Spec.chunk_add_pure (lift_chunk t) (lift_chunk scratch2)
      = Spec.chunk_pair_butterfly_a_pure (lift_chunk t) (lift_chunk scratch1) (lift_fe_mont zeta_r)
    -- Per-lane: lift_fe scratch2[ℓ] = mul_pure (lift_fe scratch1[ℓ]) (lift_fe_mont zeta_r).
    unfold Spec.chunk_add_pure Spec.chunk_pair_butterfly_a_pure lift_chunk
    apply Subtype.ext
    show (List.range 16).map (fun i =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Std.Array.make 16#usize (t.elements.val.map lift_fe) (by simp)).val[i]!)
              ((Std.Array.make 16#usize (scratch2.elements.val.map lift_fe) (by simp)).val[i]!))
        = (List.range 16).map (fun ℓ =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Std.Array.make 16#usize (t.elements.val.map lift_fe) (by simp)).val[ℓ]!)
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                ((Std.Array.make 16#usize (scratch1.elements.val.map lift_fe) (by simp)).val[ℓ]!)
                (lift_fe_mont zeta_r)))
    apply List.ext_getElem
    · simp
    · intro ℓ hℓ1 _
      have hℓ : ℓ < 16 := by
        have : ℓ < (List.range 16).length := hℓ1
        simpa using this
      rw [List.getElem_map, List.getElem_range,
          List.getElem_map, List.getElem_range]
      congr 1
      -- Goal: (Std.Array.make 16 (s2.map lift_fe)).val[ℓ]!
      --   = mul_pure ((Std.Array.make 16 (s1.map lift_fe)).val[ℓ]!) (lift_fe_mont zeta_r).
      have h_s1_len : scratch1.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch1
      have h_s2_len : scratch2.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch2
      have h_s1_idx : (Std.Array.make 16#usize (scratch1.elements.val.map lift_fe)
                          (by simp)).val[ℓ]! = lift_fe (scratch1.elements.val[ℓ]!) := by
        show (scratch1.elements.val.map lift_fe)[ℓ]! = _
        have h_lhs_len : (scratch1.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_s1_len]
        rw [getElem!_pos _ ℓ (by rw [h_lhs_len]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos scratch1.elements.val ℓ (by rw [h_s1_len]; exact hℓ)]
      have h_s2_idx : (Std.Array.make 16#usize (scratch2.elements.val.map lift_fe)
                          (by simp)).val[ℓ]! = lift_fe (scratch2.elements.val[ℓ]!) := by
        show (scratch2.elements.val.map lift_fe)[ℓ]! = _
        have h_lhs_len : (scratch2.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_s2_len]
        rw [getElem!_pos _ ℓ (by rw [h_lhs_len]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos scratch2.elements.val ℓ (by rw [h_s2_len]; exact hℓ)]
      rw [h_s1_idx, h_s2_idx]
      -- Now goal: lift_fe (scratch2.elements.val[ℓ]!) = mul_pure (lift_fe (scratch1.elements.val[ℓ]!)) (lift_fe_mont zeta_r).
      -- Use lift_fe_mul_pure_mont_eq with the per-elem modq from h_s2_per.
      have h_modq : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
          (scratch2.elements.val[ℓ]!).val
          ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) 3329 := by
        have h_per := (h_s2_per ℓ hℓ).2
        -- h_per : (scratch2.elements.val[ℓ]!).val * 2^16 % 3329 = (scratch1.elements.val[ℓ]!).val * zeta_r.val % 3329
        -- Need to convert to modq_eq form: r ≡ scratch1*zeta_r*169 mod q.
        -- This follows from 2^16 * 169 ≡ 1 (mod 3329).
        unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
        -- (a - b) % q = 0 ↔ a ≡ b mod q.
        have h_169 : ((2^16 : Int) * 169) % 3329 = 1 := by decide
        -- r * 2^16 ≡ s1 * z (mod q)
        --   r * 2^16 * 169 ≡ s1 * z * 169 (mod q)
        --   r * 1 ≡ s1 * z * 169 (mod q)   (using 2^16 * 169 ≡ 1)
        --   r ≡ s1 * z * 169.
        have h_rmul : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
            = ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 := by
          have h1 : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
              = ((scratch2.elements.val[ℓ]!).val * (2^16 : Int)) % 3329 * 169 % 3329 := by
            rw [Int.mul_emod]
            simp
          have h2 : ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
              = ((scratch1.elements.val[ℓ]!).val * zeta_r.val) % 3329 * 169 % 3329 := by
            rw [Int.mul_emod]
            simp
          rw [h1, h2, h_per]
        have h_lhs : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
            = (scratch2.elements.val[ℓ]!).val % 3329 := by
          have h_mul_assoc : (scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169
              = (scratch2.elements.val[ℓ]!).val * ((2^16 : Int) * 169) := by ring
          rw [h_mul_assoc]
          rw [Int.mul_emod]
          rw [h_169]
          simp
        have h_zsub :
            ((scratch2.elements.val[ℓ]!).val
              - (scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 = 0 := by
          have h_sub_emod : ((scratch2.elements.val[ℓ]!).val
              - (scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
              = ((scratch2.elements.val[ℓ]!).val % 3329
                  - ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329) % 3329 := by
            rw [Int.sub_emod]
          rw [h_sub_emod]
          rw [← h_lhs]
          rw [h_rmul]
          simp
        exact h_zsub
      exact lift_fe_mul_pure_mont_eq (scratch1.elements.val[ℓ]!) zeta_r
              (scratch2.elements.val[ℓ]!) h_modq
  · -- (b) c3[b] = c2.set b t4 [b] = t4. Lifts to chunk_pair_butterfly_b_pure.
    show lift_chunk (c3.val[b.val]!) = _
    have h_c3_b : c3.val[b.val]! = t4 := by
      show (c2.set b t4).val[b.val]! = t4
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq c2 b b.val t4
          ⟨rfl, by rw [h_c2_len]; exact hb⟩
    rw [h_c3_b, h_t4_lift]
    show Spec.chunk_sub_pure (lift_chunk t) (lift_chunk scratch2)
      = Spec.chunk_pair_butterfly_b_pure (lift_chunk t) (lift_chunk scratch1) (lift_fe_mont zeta_r)
    unfold Spec.chunk_sub_pure Spec.chunk_pair_butterfly_b_pure lift_chunk
    apply Subtype.ext
    show (List.range 16).map (fun i =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              ((Std.Array.make 16#usize (t.elements.val.map lift_fe) (by simp)).val[i]!)
              ((Std.Array.make 16#usize (scratch2.elements.val.map lift_fe) (by simp)).val[i]!))
        = (List.range 16).map (fun ℓ =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              ((Std.Array.make 16#usize (t.elements.val.map lift_fe) (by simp)).val[ℓ]!)
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                ((Std.Array.make 16#usize (scratch1.elements.val.map lift_fe) (by simp)).val[ℓ]!)
                (lift_fe_mont zeta_r)))
    apply List.ext_getElem
    · simp
    · intro ℓ hℓ1 _
      have hℓ : ℓ < 16 := by
        have : ℓ < (List.range 16).length := hℓ1
        simpa using this
      rw [List.getElem_map, List.getElem_range,
          List.getElem_map, List.getElem_range]
      congr 1
      have h_s1_len : scratch1.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch1
      have h_s2_len : scratch2.elements.val.length = 16 :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch2
      have h_s1_idx : (Std.Array.make 16#usize (scratch1.elements.val.map lift_fe)
                          (by simp)).val[ℓ]! = lift_fe (scratch1.elements.val[ℓ]!) := by
        show (scratch1.elements.val.map lift_fe)[ℓ]! = _
        have h_lhs_len : (scratch1.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_s1_len]
        rw [getElem!_pos _ ℓ (by rw [h_lhs_len]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos scratch1.elements.val ℓ (by rw [h_s1_len]; exact hℓ)]
      have h_s2_idx : (Std.Array.make 16#usize (scratch2.elements.val.map lift_fe)
                          (by simp)).val[ℓ]! = lift_fe (scratch2.elements.val[ℓ]!) := by
        show (scratch2.elements.val.map lift_fe)[ℓ]! = _
        have h_lhs_len : (scratch2.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_s2_len]
        rw [getElem!_pos _ ℓ (by rw [h_lhs_len]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos scratch2.elements.val ℓ (by rw [h_s2_len]; exact hℓ)]
      rw [h_s1_idx, h_s2_idx]
      have h_modq : libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
          (scratch2.elements.val[ℓ]!).val
          ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) 3329 := by
        have h_per := (h_s2_per ℓ hℓ).2
        unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
        have h_169 : ((2^16 : Int) * 169) % 3329 = 1 := by decide
        have h_rmul : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
            = ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 := by
          have h1 : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
              = ((scratch2.elements.val[ℓ]!).val * (2^16 : Int)) % 3329 * 169 % 3329 := by
            rw [Int.mul_emod]; simp
          have h2 : ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
              = ((scratch1.elements.val[ℓ]!).val * zeta_r.val) % 3329 * 169 % 3329 := by
            rw [Int.mul_emod]; simp
          rw [h1, h2, h_per]
        have h_lhs : ((scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
            = (scratch2.elements.val[ℓ]!).val % 3329 := by
          have h_mul_assoc : (scratch2.elements.val[ℓ]!).val * (2^16 : Int) * 169
              = (scratch2.elements.val[ℓ]!).val * ((2^16 : Int) * 169) := by ring
          rw [h_mul_assoc, Int.mul_emod, h_169]; simp
        have h_zsub :
            ((scratch2.elements.val[ℓ]!).val
              - (scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 = 0 := by
          have h_sub_emod : ((scratch2.elements.val[ℓ]!).val
              - (scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
              = ((scratch2.elements.val[ℓ]!).val % 3329
                  - ((scratch1.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329) % 3329 := by
            rw [Int.sub_emod]
          rw [h_sub_emod, ← h_lhs, h_rmul]; simp
        exact h_zsub
      exact lift_fe_mul_pure_mont_eq (scratch1.elements.val[ℓ]!) zeta_r
              (scratch2.elements.val[ℓ]!) h_modq
  · -- (c) For k ≠ a, k ≠ b: c3[k] = coefficients[k].
    intro k hk hka hkb
    show c3.val[k]! = coefficients.val[k]!
    have h_step1 : c3.val[k]! = c2.val[k]! := by
      show (c2.set b t4).val[k]! = c2.val[k]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne c2 b k t4 (fun h => hkb h.symm)
    have h_step2 : c2.val[k]! = c1.val[k]! := by
      show (c1.set a t2).val[k]! = c1.val[k]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne c1 a k t2 (fun h => hka h.symm)
    have h_step3 : c1.val[k]! = coefficients.val[k]! := by
      show (coefficients.set b t).val[k]! = coefficients.val[k]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne coefficients b k t (fun h => hkb h.symm)
    rw [h_step1, h_step2, h_step3]

/-! ### L3.4_plus' — Inner loop scaffolding. -/

namespace Layer4PlusInnerFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Inner loop accumulator: (re, scratch). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC invariant for the inner loop. Parameters:
    - `re0` : poly at start of inner loop (input chunks).
    - `a_offset b_offset : Std.Usize` : the chunk-base offsets for this outer round.
    - `step_vec : Std.Usize` : inner loop end (the # of butterflies in this round).
    - `zeta : hacspec FE` : the zeta (canonical) for this round's butterflies.

    The invariant at inner iter `k`:
    - For `j' < k`: chunks at `a_offset + j'` and `b_offset + j'` are butterflied.
    - For `j' ≥ k`: chunks unchanged.
    - All other chunks unchanged. -/
def inv
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset : Std.Usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    -- (a) a-side butterflies for j' < k.
    (∀ j' : Nat, j' < k.val →
      lift_chunk (acc.1.coefficients.val[a_offset.val + j']!)
        = Spec.chunk_pair_butterfly_a_pure
            (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
            (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
            zeta)
    -- (b) b-side butterflies for j' < k.
    ∧ (∀ j' : Nat, j' < k.val →
      lift_chunk (acc.1.coefficients.val[b_offset.val + j']!)
        = Spec.chunk_pair_butterfly_b_pure
            (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
            (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
            zeta)
    -- (c) chunks at positions not yet touched, OR completely outside the a/b range.
    ∧ (∀ k' : Nat, k' < 16 →
        (∀ j' : Nat, j' < k.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
        acc.1.coefficients.val[k']! = re0.coefficients.val[k']!))

/-- Step-post for the inner loop. -/
def step_post
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < step_vec.val ∧ iter'.«end» = step_vec
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re0 a_offset b_offset zeta iter'.start acc').holds
  | .done y => (inv re0 a_offset b_offset zeta step_vec y).holds

end Layer4PlusInnerFC

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the inner loop. -/
theorem ntt_at_layer_4_plus_inner_step_lemma_fc
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize) (zeta_i1 : Std.Usize)
    (h_zi1_lt : zeta_i1.val < 128)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (h_a_offset_b : a_offset.val + step_vec.val ≤ 16)
    (h_b_offset_b : b_offset.val + step_vec.val ≤ 16)
    (h_disjoint : a_offset.val + step_vec.val ≤ b_offset.val)
    (h_pre_a : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[a_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[b_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (acc : Layer4PlusInnerFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ step_vec.val)
    (h_inv : (Layer4PlusInnerFC.inv re0 a_offset b_offset
              (Spec.zeta_at zeta_i1.val) k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i1 a_offset b_offset
      { start := k, «end» := step_vec } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
              (Spec.zeta_at zeta_i1.val) k r ⌝ ⦄ := by
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_a, h_acc_b, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
  by_cases h_lt : k.val < step_vec.val
  · -- Some j = k branch.
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      Layer4PlusFC.iter_next_some_eq_gen k step_vec h_lt
    -- (1) i ← a_offset + k.
    have h_a_max : a_offset.val + k.val ≤ Std.Usize.max := by
      have h_ab_b : a_offset.val + k.val ≤ 16 := by omega
      scalar_tac
    obtain ⟨i, h_i_eq, h_i_val⟩ :=
      Layer4PlusFC.usize_add_ok_eq a_offset k h_a_max
    -- (2) i1 ← b_offset + k.
    have h_b_max : b_offset.val + k.val ≤ Std.Usize.max := by
      have h_bb_b : b_offset.val + k.val ≤ 16 := by omega
      scalar_tac
    obtain ⟨i1, h_i1_eq, h_i1_val⟩ :=
      Layer4PlusFC.usize_add_ok_eq b_offset k h_b_max
    -- (3) zeta lookup.
    obtain ⟨z, h_z_eq, h_z_v, h_z_bd, h_z_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zeta_i1 h_zi1_lt)
    -- Now we need to derive bounds on acc.1.coefficients[i] and [i1] from h_pre + h_acc_undone.
    have h_i_lt_16 : i.val < 16 := by rw [h_i_val]; omega
    have h_i1_lt_16 : i1.val < 16 := by rw [h_i1_val]; omega
    have h_i_ne_i1 : i.val ≠ i1.val := by
      rw [h_i_val, h_i1_val]
      have : a_offset.val + k.val < b_offset.val + k.val := by omega
      omega
    -- Bounds at i and i1 via h_acc_undone.
    have h_acc_i_undone : acc.1.coefficients.val[i.val]! = re0.coefficients.val[i.val]! := by
      apply h_acc_undone i.val h_i_lt_16
      intro j' hj'
      constructor
      · -- i.val = a_offset + k ≠ a_offset + j' since j' < k.
        rw [h_i_val]; omega
      · -- i.val = a_offset + k ≠ b_offset + j' since b_offset ≥ a_offset + step_vec > a_offset + k.
        rw [h_i_val]; omega
    have h_acc_i1_undone : acc.1.coefficients.val[i1.val]! = re0.coefficients.val[i1.val]! := by
      apply h_acc_undone i1.val h_i1_lt_16
      intro j' hj'
      constructor
      · -- i1.val = b_offset + k ≠ a_offset + j' since a_offset + j' ≤ a_offset + step_vec - 1 < b_offset.
        rw [h_i1_val]; omega
      · -- i1.val = b_offset + k ≠ b_offset + j'.
        rw [h_i1_val]; omega
    -- Acc-level bound: each chunk in acc.1.coefficients has lane bounds ≤ 29439
    -- ONLY for chunks at unchanged positions. The butterflied chunks may grow,
    -- but we don't need to access them in this iter (i, i1 are pristine).
    have h_acc_at_i_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_acc_i_undone, h_i_val]
      exact h_pre_a k.val h_lt ℓ hℓ
    have h_acc_at_i1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i1.val]!).elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro ℓ hℓ
      rw [h_acc_i1_undone, h_i1_val]
      exact h_pre_b k.val h_lt ℓ hℓ
    -- Convert h_z_bd to ≤ 1664 form for zeta_r bound.
    have h_zeta_bnd : z.val.natAbs ≤ 1664 := h_z_bd
    -- Apply the keystone with bounds at i, i1.
    obtain ⟨r_pair, h_r_eq, h_r_a, h_r_b, h_r_undone⟩ :=
      triple_exists_ok_fc (ntt_layer_int_vec_step_fc
        acc.1.coefficients i i1 acc.2 z h_i_lt_16 h_i1_lt_16 h_i_ne_i1
        h_zeta_bnd h_acc_at_i_bnd h_acc_at_i1_bnd)
    -- r_pair is (new_coefs, scratch2). Build the new accumulator.
    set acc' : Layer4PlusInnerFC.Acc :=
      (({ coefficients := r_pair.1 }
        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
       r_pair.2) with hacc'_def
    -- Compose body.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset
          { start := k, «end» := step_vec } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := step_vec }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := step_vec } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := step_vec }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
              let i ← a_offset + k
              let i1 ← b_offset + k
              let i2 ← libcrux_iot_ml_kem.polynomial.zeta zeta_i1
              let (a, scratch1) ←
                libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step portable_ops_inst
                  acc.1.coefficients i i1 acc.2 i2
              Result.ok (ControlFlow.cont (({ start := s, «end» := step_vec }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        ({ coefficients := a }
                          : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
                        scratch1))) = _
      rw [h_i_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_i1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_z_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_r_eq]; rfl
    apply triple_of_ok_fc h_body
    show Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
      (Spec.zeta_at zeta_i1.val) k
      (.cont (({ start := s, «end» := step_vec }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer4PlusInnerFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Show inv at s acc'.
    show (Layer4PlusInnerFC.inv re0 a_offset b_offset
            (Spec.zeta_at zeta_i1.val) s acc').holds
    have h_inv_pure :
        (∀ j' : Nat, j' < s.val →
          lift_chunk (acc'.1.coefficients.val[a_offset.val + j']!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ j' : Nat, j' < s.val →
          lift_chunk (acc'.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < s.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            acc'.1.coefficients.val[k']! = re0.coefficients.val[k']!) := by
      refine ⟨?_, ?_, ?_⟩
      · -- (a) a-side butterfly for j' < s.val.
        intro j' hj'
        rw [hs_val] at hj'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj'_lt | hj'_eq
        · -- j' < k.val: existing butterfly, position untouched in this step.
          -- acc'.1.coefs = r_pair.1. New chunk at a_offset+j' is unchanged in r_pair
          -- since a_offset+j' ≠ i (=a_offset+k) and ≠ i1 (=b_offset+k).
          have h_ne_i : a_offset.val + j' ≠ i.val := by rw [h_i_val]; omega
          have h_ne_i1 : a_offset.val + j' ≠ i1.val := by rw [h_i1_val]; omega
          have h_pos : a_offset.val + j' < 16 := by omega
          have h_unchanged : r_pair.1.val[a_offset.val + j']!
              = acc.1.coefficients.val[a_offset.val + j']! :=
            h_r_undone (a_offset.val + j') h_pos h_ne_i h_ne_i1
          show lift_chunk (acc'.1.coefficients.val[a_offset.val + j']!) = _
          show lift_chunk (r_pair.1.val[a_offset.val + j']!) = _
          rw [h_unchanged]
          exact h_acc_a j' hj'_lt
        · -- j' = k.val: new butterfly at i = a_offset + k.
          subst hj'_eq
          -- acc'.1.coefs[a_offset + k.val] = r_pair.1[a_offset + k.val] = r_pair.1[i.val] (since i.val = a_offset+k).
          show lift_chunk (acc'.1.coefficients.val[a_offset.val + k.val]!) = _
          show lift_chunk (r_pair.1.val[a_offset.val + k.val]!) = _
          have h_eq_i : a_offset.val + k.val = i.val := by rw [h_i_val]
          rw [h_eq_i]
          -- h_r_a : lift_chunk r_pair.1[i] = chunk_pair_butterfly_a_pure (lift_chunk acc.1[i]) (lift_chunk acc.1[i1]) (lift_fe_mont z).
          rw [h_r_a]
          rw [h_acc_i_undone, h_acc_i1_undone]
          rw [h_i_val, h_i1_val]
          -- Need lift_fe_mont z = Spec.zeta_at zeta_i1.val.
          rw [h_z_lift]
      · -- (b) b-side butterfly for j' < s.val.
        intro j' hj'
        rw [hs_val] at hj'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj'_lt | hj'_eq
        · have h_ne_i : b_offset.val + j' ≠ i.val := by rw [h_i_val]; omega
          have h_ne_i1 : b_offset.val + j' ≠ i1.val := by rw [h_i1_val]; omega
          have h_pos : b_offset.val + j' < 16 := by omega
          have h_unchanged : r_pair.1.val[b_offset.val + j']!
              = acc.1.coefficients.val[b_offset.val + j']! :=
            h_r_undone (b_offset.val + j') h_pos h_ne_i h_ne_i1
          show lift_chunk (acc'.1.coefficients.val[b_offset.val + j']!) = _
          show lift_chunk (r_pair.1.val[b_offset.val + j']!) = _
          rw [h_unchanged]
          exact h_acc_b j' hj'_lt
        · subst hj'_eq
          show lift_chunk (acc'.1.coefficients.val[b_offset.val + k.val]!) = _
          show lift_chunk (r_pair.1.val[b_offset.val + k.val]!) = _
          have h_eq_i1 : b_offset.val + k.val = i1.val := by rw [h_i1_val]
          rw [h_eq_i1]
          rw [h_r_b]
          rw [h_acc_i_undone, h_acc_i1_undone]
          rw [h_i_val, h_i1_val]
          rw [h_z_lift]
      · -- (c) Other positions unchanged from re0.
        intro k' hk' h_not_touched
        have hk'_ne_i : k' ≠ i.val := by
          have h_at_k : k.val < s.val := by rw [hs_val]; omega
          have := (h_not_touched k.val h_at_k).1
          rw [h_i_val]; exact this
        have hk'_ne_i1 : k' ≠ i1.val := by
          have h_at_k : k.val < s.val := by rw [hs_val]; omega
          have := (h_not_touched k.val h_at_k).2
          rw [h_i1_val]; exact this
        -- acc'.1.coefs[k'] = r_pair.1[k']. r_pair.1[k'] = acc.1[k'] (k' ≠ i, i1).
        show acc'.1.coefficients.val[k']! = re0.coefficients.val[k']!
        show r_pair.1.val[k']! = re0.coefficients.val[k']!
        have h_unchanged := h_r_undone k' hk' hk'_ne_i hk'_ne_i1
        rw [h_unchanged]
        -- Now acc.1[k'] = re0[k'] from h_acc_undone (k' is not touched at any j' < k.val).
        apply h_acc_undone k' hk'
        intro j' hj'
        -- j' < k.val. We have h_not_touched at j' (since j' < k.val < s.val).
        have h_at_j' : j' < s.val := by rw [hs_val]; omega
        exact h_not_touched j' h_at_j'
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- None branch: k ≥ step_vec, done.
    have hk_ge : k.val ≥ step_vec.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = step_vec.val := by omega
    have h_iter_none := Layer4PlusFC.iter_next_none_eq_gen k step_vec hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset
          { start := k, «end» := step_vec } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := step_vec } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := step_vec }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
      (Spec.zeta_at zeta_i1.val) k (.done acc)
    unfold Layer4PlusInnerFC.step_post
    show (Layer4PlusInnerFC.inv re0 a_offset b_offset
            (Spec.zeta_at zeta_i1.val) step_vec acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.1.coefficients.val[a_offset.val + j']!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            acc.1.coefficients.val[k']! = re0.coefficients.val[k']!) := by
      refine ⟨?_, ?_, ?_⟩
      · intro j' hj'; rw [← hk_eq] at hj'; exact h_acc_a j' hj'
      · intro j' hj'; rw [← hk_eq] at hj'; exact h_acc_b j' hj'
      · intro k' hk' h_not_touched
        apply h_acc_undone k' hk'
        intro j' hj'
        have h_at_j' : j' < step_vec.val := by rw [← hk_eq]; exact hj'
        exact h_not_touched j' h_at_j'
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-! ### L3.4_plus' — Outer loop scaffolding. -/

namespace Layer4PlusOuterFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Outer loop accumulator: (zeta_i, re, scratch). -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC invariant for the outer loop. Parameters:
    - `re0` : original poly.
    - `zeta_i_0` : zeta_i at start of outer loop.
    - `step_vec` : (1 << layer) / 16.

    The invariant at outer iter `k`:
    - `acc.1.val = zeta_i_0.val + k.val` (zeta thread).
    - For `round' < k.val`: both a-side and b-side chunks are butterflied.
    - Chunks not in any touched pair are unchanged from re0. -/
def inv
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_0 step_vec : Std.Usize) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val + k.val
    -- (a) For each completed round, chunks at a-side positions are butterflied.
    ∧ (∀ round' : Nat, round' < k.val →
        ∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                (Spec.zeta_at (zeta_i_0.val + round' + 1)))
    -- (b) For each completed round, chunks at b-side positions are butterflied.
    ∧ (∀ round' : Nat, round' < k.val →
        ∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                (Spec.zeta_at (zeta_i_0.val + round' + 1)))
    -- (c) Chunks not touched in any round' < k.val are unchanged.
    ∧ (∀ c : Nat, c < 16 →
        (∀ round' : Nat, round' < k.val →
          ∀ j' : Nat, j' < step_vec.val →
            c ≠ 2 * round' * step_vec.val + j'
            ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
        acc.2.1.coefficients.val[c]! = re0.coefficients.val[c]!))

/-- Step-post for the outer loop. -/
def step_post
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_0 step_vec i_end : Std.Usize)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < i_end.val ∧ iter'.«end» = i_end
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re0 zeta_i_0 step_vec iter'.start acc').holds
  | .done y => (inv re0 zeta_i_0 step_vec i_end y).holds

end Layer4PlusOuterFC

/-- Helper: chunks lifted via `re0` at index `2*round'*step_vec + j'`
    (a-side) are exactly the original re0 chunks (since these positions
    have not yet been touched by outer iter `round'`). -/
theorem outer_acc_a_chunk_eq_re0
    (re0 acc : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize) (zeta_i_0 step_vec : Std.Usize)
    (h_undone : ∀ c : Nat, c < 16 →
        (∀ round' : Nat, round' < k.val →
          ∀ j' : Nat, j' < step_vec.val →
            c ≠ 2 * round' * step_vec.val + j'
            ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
        acc.coefficients.val[c]! = re0.coefficients.val[c]!)
    (h_kbound : 2 * k.val * step_vec.val + 2 * step_vec.val ≤ 16)
    (j' : Nat) (hj' : j' < step_vec.val) :
    acc.coefficients.val[2 * k.val * step_vec.val + j']! = re0.coefficients.val[2 * k.val * step_vec.val + j']! := by
  apply h_undone (2 * k.val * step_vec.val + j') (by omega)
  intro round' hround' j'' hj''
  -- round' < k, so 2*round'*step_vec + j'' < 2*k*step_vec (since 2*round'*step_vec + step_vec ≤ 2*k*step_vec).
  -- Hence 2*k*step_vec + j' > 2*round'*step_vec + j'' if step_vec ≥ 1.
  -- For the second leg: 2*round'*step_vec + step_vec + j'' < 2*round'*step_vec + 2*step_vec ≤ 2*k*step_vec.
  -- So 2*k*step_vec + j' > all these.
  constructor
  · -- 2*k*step_vec + j' ≠ 2*round'*step_vec + j''.
    have h1 : 2 * round' * step_vec.val + j'' < 2 * k.val * step_vec.val := by
      have h_lt : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
        have : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      omega
    omega
  · -- 2*k*step_vec + j' ≠ 2*round'*step_vec + step_vec + j''.
    have h1 : 2 * round' * step_vec.val + step_vec.val + j'' < 2 * k.val * step_vec.val := by
      have : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
        have : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      omega
    omega

/-- b-side variant of the above helper. -/
theorem outer_acc_b_chunk_eq_re0
    (re0 acc : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize) (zeta_i_0 step_vec : Std.Usize)
    (h_undone : ∀ c : Nat, c < 16 →
        (∀ round' : Nat, round' < k.val →
          ∀ j' : Nat, j' < step_vec.val →
            c ≠ 2 * round' * step_vec.val + j'
            ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
        acc.coefficients.val[c]! = re0.coefficients.val[c]!)
    (h_kbound : 2 * k.val * step_vec.val + 2 * step_vec.val ≤ 16)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (j' : Nat) (hj' : j' < step_vec.val) :
    acc.coefficients.val[2 * k.val * step_vec.val + step_vec.val + j']!
      = re0.coefficients.val[2 * k.val * step_vec.val + step_vec.val + j']! := by
  apply h_undone (2 * k.val * step_vec.val + step_vec.val + j') (by omega)
  intro round' hround' j'' hj''
  constructor
  · have h1 : 2 * round' * step_vec.val + j'' < 2 * k.val * step_vec.val := by
      have : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
        have : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      omega
    omega
  · have h1 : 2 * round' * step_vec.val + step_vec.val + j'' < 2 * k.val * step_vec.val := by
      have : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
        have : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      omega
    omega

set_option maxHeartbeats 16000000 in
/-- Inner loop spec wrapper: dispatches `loop_range_spec_usize` for the
    inner loop, returning the final FC equations on the post poly. -/
theorem ntt_at_layer_4_plus_inner_loop_fc
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize) (zeta_i1 : Std.Usize)
    (h_zi1_lt : zeta_i1.val < 128)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (h_a_offset_b : a_offset.val + step_vec.val ≤ 16)
    (h_b_offset_b : b_offset.val + step_vec.val ≤ 16)
    (h_disjoint : a_offset.val + step_vec.val ≤ b_offset.val)
    (h_pre_a : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[a_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[b_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := step_vec } zeta_i1 re0 scratch a_offset b_offset
    ⦃ ⇓ r => ⌜
      (∀ j' : Nat, j' < step_vec.val →
        lift_chunk (r.1.coefficients.val[a_offset.val + j']!)
          = Spec.chunk_pair_butterfly_a_pure
              (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
              (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
              (Spec.zeta_at zeta_i1.val))
      ∧ (∀ j' : Nat, j' < step_vec.val →
        lift_chunk (r.1.coefficients.val[b_offset.val + j']!)
          = Spec.chunk_pair_butterfly_b_pure
              (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
              (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
              (Spec.zeta_at zeta_i1.val))
      ∧ (∀ k' : Nat, k' < 16 →
          (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
          r.1.coefficients.val[k']! = re0.coefficients.val[k']!)
      ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset iter1 acc1.1 acc1.2)
      (β := Layer4PlusInnerFC.Acc)
      (re0, scratch)
      0#usize step_vec
      (Layer4PlusInnerFC.inv re0 a_offset b_offset (Spec.zeta_at zeta_i1.val))
      (by
        -- 0 ≤ step_vec.
        have : (0#usize : Std.Usize).val = 0 := rfl
        omega)
      (by
        -- Initial inv at k=0.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- No a-side touched yet.
          intro j' hj'; exact absurd hj' (Nat.not_lt_zero j')
        · intro j' hj'; exact absurd hj' (Nat.not_lt_zero j')
        · -- Acc = (re0, scratch); acc.1 = re0; all chunks unchanged trivially.
          intro k' _ _; trivial)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds :
        (Layer4PlusInnerFC.inv re0 a_offset b_offset
              (Spec.zeta_at zeta_i1.val) step_vec r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (r.1.coefficients.val[a_offset.val + j']!)
            = Spec.chunk_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (r.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            r.1.coefficients.val[k']! = re0.coefficients.val[k']!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer4PlusInnerFC.inv] using h_inv_holds
    exact h_inv
  · -- Step lemma dispatch.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_4_plus_inner_step_lemma_fc re0 a_offset b_offset step_vec
      zeta_i1 h_zi1_lt h_step_vec_pos h_a_offset_b h_b_offset_b h_disjoint h_pre_a h_pre_b
      acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
                  (Spec.zeta_at zeta_i1.val) k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusInnerFC.step_post] using hP
    · have hP : Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
                  (Spec.zeta_at zeta_i1.val) k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusInnerFC.step_post] using hP

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the outer loop. Dispatches the
    inner loop wrapper. -/
theorem ntt_at_layer_4_plus_outer_step_lemma_fc
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_0 step_vec i_end : Std.Usize)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (h_step_vec_dvd : 2 * i_end.val * step_vec.val = 16)
    (h_zeta_bnd : zeta_i_0.val + i_end.val ≤ 127)
    (acc : Layer4PlusOuterFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ i_end.val)
    (h_inv : (Layer4PlusOuterFC.inv re0 zeta_i_0 step_vec k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst)
      step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
    ⦃ ⇓ r => ⌜ Layer4PlusOuterFC.step_post re0 zeta_i_0 step_vec i_end k r ⌝ ⦄ := by
  obtain ⟨h_zeta_acc, h_acc_a, h_acc_b, h_acc_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
  by_cases h_lt : k.val < i_end.val
  · -- Some round = k branch.
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      Layer4PlusFC.iter_next_some_eq_gen k i_end h_lt
    -- (1) zeta_i1 ← zeta_i + 1.
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um, h_zeta_acc]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer4PlusFC.usize_add_ok_eq acc.1 1#usize h_z_max
    have h_zi1_arith : zi1.val = zeta_i_0.val + k.val + 1 := by
      rw [h_zi1_val, h_um, h_zeta_acc]
    have h_zi1_lt_128 : zi1.val < 128 := by
      rw [h_zi1_arith]; omega
    -- (2) i ← round * 2.
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_i_max : k.val * (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]
      have h_k_b : k.val * 2 ≤ 16 := by
        have : k.val ≤ 8 := by
          -- k < i_end and i_end * step_vec * 2 = 16, so k ≤ 8.
          have : i_end.val ≤ 8 := by
            have : i_end.val * step_vec.val * 2 = 16 := by rw [Nat.mul_assoc] at h_step_vec_dvd; nlinarith
            nlinarith
          omega
        omega
      scalar_tac
    obtain ⟨ii, h_ii_eq, h_ii_val⟩ :=
      Layer4PlusFC.usize_mul_ok_eq k 2#usize h_i_max
    have h_ii_arith : ii.val = 2 * k.val := by rw [h_ii_val, h_um2, Nat.mul_comm]
    -- (3) a_offset ← ii * step_vec.
    have h_a_max : ii.val * step_vec.val ≤ Std.Usize.max := by
      rw [h_ii_arith]
      have h_b : 2 * k.val * step_vec.val ≤ 16 := by
        have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      scalar_tac
    obtain ⟨ao, h_ao_eq, h_ao_val⟩ :=
      Layer4PlusFC.usize_mul_ok_eq ii step_vec h_a_max
    have h_ao_arith : ao.val = 2 * k.val * step_vec.val := by
      rw [h_ao_val, h_ii_arith]
    -- (4) b_offset ← a_offset + step_vec.
    have h_b_max : ao.val + step_vec.val ≤ Std.Usize.max := by
      rw [h_ao_arith]
      have h_b : 2 * k.val * step_vec.val + step_vec.val ≤ 16 := by
        have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
          apply Nat.mul_le_mul_right; omega
        nlinarith
      scalar_tac
    obtain ⟨bo, h_bo_eq, h_bo_val⟩ :=
      Layer4PlusFC.usize_add_ok_eq ao step_vec h_b_max
    have h_bo_arith : bo.val = 2 * k.val * step_vec.val + step_vec.val := by
      rw [h_bo_val, h_ao_arith]
    -- Now dispatch the inner loop.
    have h_a_offset_b : ao.val + step_vec.val ≤ 16 := by
      rw [h_ao_arith]
      have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
        apply Nat.mul_le_mul_right; omega
      nlinarith
    have h_b_offset_b : bo.val + step_vec.val ≤ 16 := by
      rw [h_bo_arith]
      have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
        apply Nat.mul_le_mul_right; omega
      nlinarith
    have h_disjoint : ao.val + step_vec.val ≤ bo.val := by
      rw [h_ao_arith, h_bo_arith]
    -- Localized chunk bounds for inner loop input: acc.2.1.
    have h_2kstep_bnd : 2 * k.val * step_vec.val + 2 * step_vec.val ≤ 16 := by
      have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
        apply Nat.mul_le_mul_right; omega
      nlinarith
    have h_acc_a_eq : ∀ j : Nat, j < step_vec.val →
        acc.2.1.coefficients.val[ao.val + j]! = re0.coefficients.val[ao.val + j]! := by
      intro j hj
      rw [h_ao_arith]
      exact outer_acc_a_chunk_eq_re0 re0 acc.2.1 k zeta_i_0 step_vec h_acc_undone
              h_2kstep_bnd j hj
    have h_acc_b_eq : ∀ j : Nat, j < step_vec.val →
        acc.2.1.coefficients.val[bo.val + j]! = re0.coefficients.val[bo.val + j]! := by
      intro j hj
      rw [h_bo_arith]
      exact outer_acc_b_chunk_eq_re0 re0 acc.2.1 k zeta_i_0 step_vec h_acc_undone
              h_2kstep_bnd h_step_vec_pos j hj
    have h_pre_a : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[ao.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro j hj ℓ hℓ
      rw [h_acc_a_eq j hj]
      apply h_pre _ _ ℓ hℓ
      rw [h_ao_arith]; omega
    have h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[bo.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 29439 := by
      intro j hj ℓ hℓ
      rw [h_acc_b_eq j hj]
      apply h_pre _ _ ℓ hℓ
      rw [h_bo_arith]; omega
    -- Dispatch inner loop.
    have h_inner := ntt_at_layer_4_plus_inner_loop_fc acc.2.1 acc.2.2 ao bo step_vec zi1
      h_zi1_lt_128 h_step_vec_pos h_a_offset_b h_b_offset_b h_disjoint h_pre_a h_pre_b
    obtain ⟨r_pair, h_r_eq, h_r_a, h_r_b, h_r_undone⟩ :=
      triple_exists_ok_fc h_inner
    -- Compose body.
    set acc' : Layer4PlusOuterFC.Acc :=
      (zi1, r_pair.1, r_pair.2) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
        = .ok (ControlFlow.cont (({ start := s, «end» := i_end }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := i_end } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := i_end }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp only [Aeneas.Std.bind_tc_ok]
      show (do
              let zi1' ← acc.1 + 1#usize
              let ii' ← k * 2#usize
              let ao' ← ii' * step_vec
              let bo' ← ao' + step_vec
              let (re1, scratch1) ←
                libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
                  (vectortraitsOperationsInst := portable_ops_inst)
                  { start := 0#usize, «end» := step_vec } zi1' acc.2.1 acc.2.2 ao' bo'
              .ok (ControlFlow.cont (({ start := s, «end» := i_end }
                          : CoreModels.core.ops.range.Range Std.Usize),
                        zi1', re1, scratch1))) = _
      rw [h_zi1_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_ii_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_ao_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_bo_eq]; simp only [Aeneas.Std.bind_tc_ok]
      rw [h_r_eq]; rfl
    apply triple_of_ok_fc h_body
    show Layer4PlusOuterFC.step_post re0 zeta_i_0 step_vec i_end k
      (.cont (({ start := s, «end» := i_end }
                : CoreModels.core.ops.range.Range Std.Usize), acc'))
    unfold Layer4PlusOuterFC.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    show (Layer4PlusOuterFC.inv re0 zeta_i_0 step_vec s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val + s.val
        ∧ (∀ round' : Nat, round' < s.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_a_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val + round' + 1)))
        ∧ (∀ round' : Nat, round' < s.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_b_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val + round' + 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < s.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            acc'.2.1.coefficients.val[c]! = re0.coefficients.val[c]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- zeta thread.
        show zi1.val = zeta_i_0.val + s.val
        rw [h_zi1_arith, hs_val]; ring
      · -- a-side butterflies for round' < s.val.
        intro round' hround' j' hj'
        rw [hs_val] at hround'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hround' with hround'_lt | hround'_eq
        · -- round' < k.val: use h_acc_a after observing acc'.2.1.coefs = r_pair.1.
          -- r_pair.1[c] = acc.2.1.coefs[c] for c not touched in this inner loop.
          have h_pos : 2 * round' * step_vec.val + j' < 16 := by
            have h_rb : 2 * round' * step_vec.val + 2 * step_vec.val
                ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_ne_a : ∀ j : Nat, j < step_vec.val →
              2 * round' * step_vec.val + j' ≠ ao.val + j := by
            intro j hj
            rw [h_ao_arith]
            have h1 : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_ne_b : ∀ j : Nat, j < step_vec.val →
              2 * round' * step_vec.val + j' ≠ bo.val + j := by
            intro j hj
            rw [h_bo_arith]
            have h1 : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_step_unc : r_pair.1.coefficients.val[2 * round' * step_vec.val + j']!
              = acc.2.1.coefficients.val[2 * round' * step_vec.val + j']! :=
            h_r_undone (2 * round' * step_vec.val + j') h_pos
              (fun j hj => ⟨h_ne_a j hj, h_ne_b j hj⟩)
          show lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + j']!) = _
          show lift_chunk (r_pair.1.coefficients.val[2 * round' * step_vec.val + j']!) = _
          rw [h_step_unc]
          exact h_acc_a round' hround'_lt j' hj'
        · -- round' = k.val: new butterfly at (2*k*step_vec + j', 2*k*step_vec + step_vec + j').
          subst hround'_eq
          show lift_chunk (acc'.2.1.coefficients.val[2 * k.val * step_vec.val + j']!) = _
          show lift_chunk (r_pair.1.coefficients.val[2 * k.val * step_vec.val + j']!) = _
          rw [show (2 * k.val * step_vec.val + j' : Nat) = ao.val + j' from by rw [h_ao_arith]]
          rw [h_r_a j' hj']
          rw [h_acc_a_eq j' hj', h_acc_b_eq j' hj']
          rw [show (ao.val + j' : Nat) = 2 * k.val * step_vec.val + j' from by rw [h_ao_arith]]
          rw [show (bo.val + j' : Nat) = 2 * k.val * step_vec.val + step_vec.val + j' from by rw [h_bo_arith]]
          rw [show zi1.val = zeta_i_0.val + k.val + 1 from h_zi1_arith]
      · -- b-side butterflies for round' < s.val.
        intro round' hround' j' hj'
        rw [hs_val] at hround'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hround' with hround'_lt | hround'_eq
        · -- round' < k.val: use h_acc_b.
          have h_pos : 2 * round' * step_vec.val + step_vec.val + j' < 16 := by
            have h_rb : 2 * round' * step_vec.val + 2 * step_vec.val
                ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_ne_a : ∀ j : Nat, j < step_vec.val →
              2 * round' * step_vec.val + step_vec.val + j' ≠ ao.val + j := by
            intro j hj
            rw [h_ao_arith]
            have h1 : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_ne_b : ∀ j : Nat, j < step_vec.val →
              2 * round' * step_vec.val + step_vec.val + j' ≠ bo.val + j := by
            intro j hj
            rw [h_bo_arith]
            have h1 : 2 * round' * step_vec.val + 2 * step_vec.val ≤ 2 * k.val * step_vec.val := by
              have h_pos : (round' + 1) * (2 * step_vec.val) ≤ k.val * (2 * step_vec.val) := by
                apply Nat.mul_le_mul_right; omega
              nlinarith
            omega
          have h_step_unc :
              r_pair.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!
              = acc.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']! :=
            h_r_undone (2 * round' * step_vec.val + step_vec.val + j') h_pos
              (fun j hj => ⟨h_ne_a j hj, h_ne_b j hj⟩)
          show lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!) = _
          show lift_chunk (r_pair.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!) = _
          rw [h_step_unc]
          exact h_acc_b round' hround'_lt j' hj'
        · subst hround'_eq
          show lift_chunk (acc'.2.1.coefficients.val[2 * k.val * step_vec.val + step_vec.val + j']!) = _
          show lift_chunk (r_pair.1.coefficients.val[2 * k.val * step_vec.val + step_vec.val + j']!) = _
          rw [show (2 * k.val * step_vec.val + step_vec.val + j' : Nat) = bo.val + j' from by rw [h_bo_arith]]
          rw [h_r_b j' hj']
          rw [h_acc_a_eq j' hj', h_acc_b_eq j' hj']
          rw [show (ao.val + j' : Nat) = 2 * k.val * step_vec.val + j' from by rw [h_ao_arith]]
          rw [show (bo.val + j' : Nat) = 2 * k.val * step_vec.val + step_vec.val + j' from by rw [h_bo_arith]]
          rw [show zi1.val = zeta_i_0.val + k.val + 1 from h_zi1_arith]
      · -- Untouched chunks.
        intro c hc h_not_touched
        -- acc'.2.1.coefs[c] = r_pair.1[c] = acc.2.1[c] = re0[c].
        show acc'.2.1.coefficients.val[c]! = re0.coefficients.val[c]!
        show r_pair.1.coefficients.val[c]! = re0.coefficients.val[c]!
        -- c is not touched at round' = k (since round' < s = k+1 includes k).
        have h_at_k : k.val < s.val := by rw [hs_val]; omega
        have h_ne_a_k : ∀ j : Nat, j < step_vec.val → c ≠ ao.val + j := by
          intro j hj; rw [h_ao_arith]
          exact (h_not_touched k.val h_at_k j hj).1
        have h_ne_b_k : ∀ j : Nat, j < step_vec.val → c ≠ bo.val + j := by
          intro j hj; rw [h_bo_arith]
          exact (h_not_touched k.val h_at_k j hj).2
        have h_step_unc : r_pair.1.coefficients.val[c]! = acc.2.1.coefficients.val[c]! :=
          h_r_undone c hc (fun j hj => ⟨h_ne_a_k j hj, h_ne_b_k j hj⟩)
        rw [h_step_unc]
        apply h_acc_undone c hc
        intro round' hround' j' hj'
        -- round' < k, so this is in the prior touched set; not at this c.
        have h_at_r : round' < s.val := by rw [hs_val]; omega
        exact h_not_touched round' h_at_r j' hj'
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- None branch: k ≥ i_end, done.
    have hk_ge : k.val ≥ i_end.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = i_end.val := by omega
    have h_iter_none := Layer4PlusFC.iter_next_none_eq_gen k i_end hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
        = .ok (ControlFlow.done (acc.1, acc.2.1, acc.2.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := i_end } : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := k, «end» := i_end }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2.1, acc.2.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_fc h_body
    show Layer4PlusOuterFC.step_post re0 zeta_i_0 step_vec i_end k (.done acc)
    unfold Layer4PlusOuterFC.step_post
    show (Layer4PlusOuterFC.inv re0 zeta_i_0 step_vec i_end acc).holds
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        acc.1.val = zeta_i_0.val + i_end.val
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_a_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val + round' + 1)))
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_b_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val + round' + 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < i_end.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            acc.2.1.coefficients.val[c]! = re0.coefficients.val[c]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq]
      · intro round' hround'; rw [← hk_eq] at hround'; exact h_acc_a round' hround'
      · intro round' hround'; rw [← hk_eq] at hround'; exact h_acc_b round' hround'
      · intro c hc h_nt
        apply h_acc_undone c hc
        intro round' hround' j' hj'
        have : round' < i_end.val := by rw [← hk_eq]; exact hround'
        exact h_nt round' this j' hj'
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3.4_plus' — `ntt_at_layer_4_plus` PortableVector-specialised FC equation,
    parameterized over `layer ∈ {4, 5, 6}`.

    Nested-loop pattern: outer over `round ∈ 0..(128 >>> layer)`, inner
    over `j ∈ 0..((1 <<< layer) / 16)`. Each inner iter butterflies
    chunks at positions `(round*2*step_vec + j, round*2*step_vec + step_vec + j)`
    with `Spec.zeta_at (zeta_i + round + 1)`. zeta_i advances by `128 >>> layer`
    across the entire call.

    **Preconditions** (load-bearing):
    - `h_layer` : layer in 4..7 (validity of the nested-loop shape). For
      layer=7, `step_vec=8`, `i_end=1`, so the outer loop runs one iteration
      and applies a single chunk-pair butterfly at chunks `(0+j, 8+j)` for
      `j ∈ 0..8`, matching the dedicated `ntt_at_layer_7` impl up to the
      zeta choice (Mont vs plain). The relaxation lets `ntt_vector_u` (L3.4)
      reuse this theorem for its first call.
    - `h_bnd` : per-lane input bound 29439.
    - `h_zeta` : zeta_i.val + (128 >>> layer) ≤ 127 (zeta indices within
      ZETAS table 0..127).

    Proof sketch:
    1. Unfold `ntt_at_layer_4_plus` driver. Resolve the three impl constants
       `step ← 1#usize <<< layer`, `step_vec ← step / 16#usize`,
       `i_end ← 128#usize >>> layer` to specific Std.Usize values via
       `Aeneas.Std.UScalar.ShiftLeft_spec`, `UScalar.div_spec`,
       `UScalar.ShiftRight_spec` (all sound for layer ∈ {4,5,6}).
    2. Unfold `ntt_at_layer_4_plus_loop0` and apply
       `loop_range_spec_usize` with invariant `Layer4PlusOuterFC.inv`
       (zeta-thread + per-round a/b butterflies + untouched).
    3. Initial inv at k=0: zeta-thread trivial, no round' < 0 absurd,
       chunks unchanged trivially.
    4. Post entailment at k=i_end: build chunks_arr matching Spec layout
       (`Spec.chunk_at_layer_4_plus_pure chunks0 layer zeta_fn c` per c).
       For each c < 16, case-split on `c % (2*step_vec) < step_vec`:
         - a-side: group := c/(2*step_vec), j' := offset. Use h_acc_a.
         - b-side: group := c/(2*step_vec), j' := offset - step_vec.
           Use h_acc_b. Reduce inner Spec lookups via chunk_at_lift_poly_fc.
       Apply `flatten_chunks_eq_lift_poly_fc`.
    5. Step dispatch: apply `ntt_at_layer_4_plus_outer_step_lemma_fc` and
       unwrap step_post via .cont / .done branches. -/
@[spec high]
theorem ntt_at_layer_4_plus_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (layer : Std.Usize)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (h_layer : 4 ≤ layer.val ∧ layer.val ≤ 7)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439)
    (h_zeta : zeta_i.val + (128 >>> layer.val) ≤ 127) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re layer scratch initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2.1 = Spec.ntt_at_layer_4_plus_pure (lift_poly re) zeta_i layer ⌝ ⦄ := by
  -- Layer bounds.
  obtain ⟨h_layer_lo, h_layer_hi⟩ := h_layer
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
  -- Step 1: resolve `step ← 1#usize <<< layer`.
  -- For layer ∈ {4,5,6}, layer.val < 64 = Usize.numBits, so shift is OK and
  -- the value is (1 <<< layer.val) % 2^64 = 1 <<< layer.val.
  have h_usize_bits : (Aeneas.Std.UScalarTy.Usize.numBits : Nat) = System.Platform.numBits := rfl
  have h_layer_bits : layer.val < Aeneas.Std.UScalarTy.Usize.numBits := by
    have h_p := System.Platform.numBits_eq
    rcases h_p with h32 | h64
    · rw [h_usize_bits, h32]; omega
    · rw [h_usize_bits, h64]; omega
  have h_size_eq : Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize = 2 ^ System.Platform.numBits := by
    simp [Std.Usize.size, Usize.numBits]
  -- Extract step via spec_imp_exists; we want step.val = 1 <<< layer.val.
  have h_one_shl_pow : ((1#usize : Std.Usize).val <<< layer.val) < 2 ^ System.Platform.numBits := by
    have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
    rw [h_one_eq, Nat.shiftLeft_eq, Nat.one_mul]
    have h_p := System.Platform.numBits_eq
    rcases h_p with h32 | h64
    · rw [h32]; exact Nat.pow_lt_pow_right (by decide) (by omega)
    · rw [h64]; exact Nat.pow_lt_pow_right (by decide) (by omega)
  have h_step_ex : ∃ step : Std.Usize,
      ((1#usize : Std.Usize) <<< layer : Result Std.Usize) = .ok step
      ∧ step.val = 1 <<< layer.val := by
    have hT := Aeneas.Std.UScalar.ShiftLeft_spec (1#usize : Std.Usize) layer
      (Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize) h_layer_bits rfl
    obtain ⟨z, h_eq, h_v_mod, _h_bv⟩ := Std.WP.spec_imp_exists hT
    refine ⟨z, h_eq, ?_⟩
    have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
    rw [h_v_mod, h_one_eq, h_size_eq, Nat.mod_eq_of_lt]
    rw [h_one_eq] at h_one_shl_pow
    exact h_one_shl_pow
  obtain ⟨step, h_step_eq, h_step_val⟩ := h_step_ex
  rw [h_step_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Step 2: resolve `step_vec ← step / 16#usize`.
  have h_16_nz : ((16#usize : Std.Usize).val : Nat) ≠ 0 := by decide
  have h_step_pos : 1 ≤ step.val := by
    rw [h_step_val, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.one_le_pow _ _ (by decide : (0:Nat) < 2)
  obtain ⟨step_vec, h_step_vec_eq, h_step_vec_val⟩ :=
    Aeneas.Std.UScalar.div_spec step h_16_nz
  rw [h_step_vec_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Compute step_vec.val.
  have h_step_vec_arith : step_vec.val = (1 <<< layer.val) / 16 := by
    have h_16_eq : (16#usize : Std.Usize).val = 16 := rfl
    rw [h_step_vec_val, h_step_val, h_16_eq]
  -- Step 3: resolve `i ← 128#usize >>> layer`.
  obtain ⟨i_end, h_i_end_eq, h_i_end_val, _h_i_end_bv⟩ :=
    Std.WP.spec_imp_exists (Aeneas.Std.UScalar.ShiftRight_spec (128#usize : Std.Usize) layer
      h_layer_bits)
  rw [h_i_end_eq]
  have h_i_end_arith : i_end.val = 128 >>> layer.val := h_i_end_val
  -- Step 4: positivity & dvd facts uniformly across layer ∈ {4,5,6}.
  have h_step_vec_pos : 1 ≤ step_vec.val := by
    rw [h_step_vec_arith]
    interval_cases layer.val <;> decide
  have h_step_vec_dvd : 2 * i_end.val * step_vec.val = 16 := by
    rw [h_i_end_arith, h_step_vec_arith]
    interval_cases layer.val <;> decide
  have h_i_end_pos : 1 ≤ i_end.val := by
    rw [h_i_end_arith]
    interval_cases layer.val <;> decide
  have h_zeta_bnd : zeta_i.val + i_end.val ≤ 127 := by
    rw [h_i_end_arith]; exact h_zeta
  -- Step 5: unfold the outer loop and apply loop_range_spec_usize.
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) step_vec
          iter1 acc1.1 acc1.2.1 acc1.2.2)
      (β := Layer4PlusOuterFC.Acc)
      (zeta_i, re, scratch)
      0#usize i_end
      (Layer4PlusOuterFC.inv re zeta_i step_vec)
      (by
        have h_zero : (0#usize : Std.Usize).val = 0 := rfl
        omega)
      (by
        -- Initial inv at k=0.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- zeta-thread: zeta_i.val = zeta_i.val + 0.
          show zeta_i.val = zeta_i.val + (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val + 0
          omega
        · -- No round' < 0 absurd.
          intro round' hround' _ _
          exact absurd hround' (Nat.not_lt_zero round')
        · intro round' hround' _ _
          exact absurd hround' (Nat.not_lt_zero round')
        · -- All chunks unchanged trivially.
          intro _ _ _; trivial)
      ?_)
  · -- Post entailment: at k = i_end, build chunks_arr matching Spec and apply
    -- flatten_chunks_eq_lift_poly_fc.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer4PlusOuterFC.inv re zeta_i step_vec i_end r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val + i_end.val
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (r.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_a_pure
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i.val + round' + 1)))
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (r.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_pair_butterfly_b_pure
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i.val + round' + 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < i_end.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            r.2.1.coefficients.val[c]! = re.coefficients.val[c]!) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer4PlusOuterFC.inv] using h_inv_holds
    obtain ⟨_h_zeta_done, h_done_a, h_done_b, _h_done_undone⟩ := h_inv
    -- Build chunks_arr matching the Spec layout.
    unfold Spec.ntt_at_layer_4_plus_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun c =>
        Spec.chunk_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          layer
          (fun group => Spec.zeta_at (zeta_i.val + group + 1))
          c))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16; simp
    -- Inner chunks0 lookup at index k reduces via chunk_at_lift_poly_fc.
    have h_chunks0_at : ∀ k : Nat, k < 16 →
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp)).val[k]!
          = lift_chunk (re.coefficients.val[k]!) := by
      intro k hk
      have h_len_map : ((List.range 16).map (Spec.chunk_at (lift_poly re))).length = 16 := by simp
      show ((List.range 16).map (Spec.chunk_at (lift_poly re)))[k]! = _
      rw [getElem!_pos _ k (by rw [h_len_map]; exact hk)]
      rw [List.getElem_map, List.getElem_range]
      exact chunk_at_lift_poly_fc re k hk
    -- Now prove h_chunks_get pointwise. Two cases: a-side and b-side.
    have h_chunks_get : ∀ c : Nat, (hc : c < 16) →
        chunks_arr.val[c]'(by rw [h_chunks_len]; exact hc)
          = lift_chunk (r.2.1.coefficients.val[c]!) := by
      intro c hc
      show ((List.range 16).map (fun c =>
        Spec.chunk_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          layer
          (fun group => Spec.zeta_at (zeta_i.val + group + 1))
          c))[c]'_ = _
      rw [List.getElem_map, List.getElem_range]
      -- Unfold Spec.chunk_at_layer_4_plus_pure.
      unfold Spec.chunk_at_layer_4_plus_pure
      -- Use abbreviation for step_vec_val.
      set sv := (1 <<< layer.val) / 16 with hsv_def
      have hsv_eq : sv = step_vec.val := by rw [hsv_def, h_step_vec_arith]
      -- Reveal the if condition.
      simp only []
      set group := c / (2 * sv)
      set offset := c % (2 * sv)
      have h_2sv_pos : 0 < 2 * sv := by rw [hsv_eq]; omega
      have h_c_eq : 2 * sv * group + offset = c := by
        show 2 * sv * (c / (2 * sv)) + c % (2 * sv) = c
        exact Nat.div_add_mod c (2 * sv)
      have h_off_lt : offset < 2 * sv := Nat.mod_lt _ h_2sv_pos
      -- group < i_end.val: from c < 16 = 2 * i_end.val * sv.
      have h_16_eq : 2 * i_end.val * sv = 16 := by
        rw [hsv_eq]; exact h_step_vec_dvd
      have h_group_lt : group < i_end.val := by
        by_contra h_ge
        push Not at h_ge
        have h_ge2 : 2 * sv * i_end.val ≤ 2 * sv * group := Nat.mul_le_mul_left _ h_ge
        have : c ≥ 2 * sv * i_end.val := by
          have : 2 * sv * group ≤ c := by omega
          omega
        have h_rw : 2 * sv * i_end.val = 16 := by
          have h : 2 * i_end.val * sv = 2 * sv * i_end.val := by ring
          omega
        omega
      by_cases h_off_lt_sv : offset < sv
      · -- a-side: c = 2*sv*group + offset = 2*group*sv + offset, partner c+sv.
        simp only [if_pos h_off_lt_sv]
        -- Need: chunks0[c]! and chunks0[c+sv]! reduce via h_chunks0_at.
        have h_c_lt_16 : c < 16 := hc
        have h_c_plus_sv_lt_16 : c + sv < 16 := by
          have h_succ : 2 * sv * (group + 1) ≤ 2 * sv * i_end.val := Nat.mul_le_mul_left _ h_group_lt
          have h_split : 2 * sv * (group + 1) = 2 * sv * group + 2 * sv := by ring
          have h_eq_16 : 2 * sv * i_end.val = 16 := by
            have : 2 * i_end.val * sv = 2 * sv * i_end.val := by ring
            omega
          omega
        rw [h_chunks0_at c h_c_lt_16, h_chunks0_at (c + sv) h_c_plus_sv_lt_16]
        -- Convert to round'=group, j'=offset shape for h_done_a.
        have h_c_eq_a : c = 2 * group * step_vec.val + offset := by
          rw [← hsv_eq]
          calc c = 2 * sv * group + offset := h_c_eq.symm
            _ = 2 * group * sv + offset := by ring_nf
        have h_csv_eq_a : c + sv = 2 * group * step_vec.val + step_vec.val + offset := by
          rw [h_c_eq_a]; rw [hsv_eq]; ring
        have h_off_lt_sv' : offset < step_vec.val := by rw [← hsv_eq]; exact h_off_lt_sv
        have h_done := h_done_a group h_group_lt offset h_off_lt_sv'
        rw [h_csv_eq_a, h_c_eq_a]
        exact h_done.symm
      · -- b-side: c ≥ sv. Set j' := offset - sv.
        simp only [if_neg h_off_lt_sv]
        push Not at h_off_lt_sv
        set j' := offset - sv with hj'_def
        have hj'_lt_sv : j' < sv := by
          show offset - sv < sv; omega
        have h_off_eq : offset = sv + j' := by
          show offset = sv + (offset - sv); omega
        have h_c_lt_16 : c < 16 := hc
        have h_c_minus_sv_lt_16 : c - sv < 16 := by omega
        -- c = 2*sv*group + sv + j', c - sv = 2*sv*group + j'.
        have h_c_eq_b : c = 2 * group * step_vec.val + step_vec.val + j' := by
          rw [← hsv_eq]
          have : c = 2 * sv * group + (sv + j') := by rw [← h_off_eq]; exact h_c_eq.symm
          calc c = 2 * sv * group + (sv + j') := this
            _ = 2 * group * sv + sv + j' := by ring
        have h_cmsv_eq_b : c - sv = 2 * group * step_vec.val + j' := by
          have h_sv_le_c : sv ≤ c := by
            calc sv ≤ sv + j' := Nat.le_add_right _ _
              _ = offset := h_off_eq.symm
              _ ≤ 2 * sv * group + offset := Nat.le_add_left _ _
              _ = c := h_c_eq
          rw [← hsv_eq]
          have h_full : c - sv = (2 * sv * group + (sv + j')) - sv := by rw [← h_off_eq, h_c_eq]
          rw [h_full]
          have h_simp : 2 * sv * group + (sv + j') - sv = 2 * sv * group + j' := by omega
          rw [h_simp]; ring
        rw [h_chunks0_at (c - sv) h_c_minus_sv_lt_16, h_chunks0_at c h_c_lt_16]
        have h_j'_lt : j' < step_vec.val := by rw [← hsv_eq]; exact hj'_lt_sv
        have h_done := h_done_b group h_group_lt j' h_j'_lt
        rw [h_cmsv_eq_b, h_c_eq_b]
        exact h_done.symm
    -- Apply flatten_chunks_eq_lift_poly_fc.
    have h_final := flatten_chunks_eq_lift_poly_fc r.2.1 chunks_arr h_chunks_len h_chunks_get
    exact h_final.symm
  · -- Step lemma dispatch: apply ntt_at_layer_4_plus_outer_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := ntt_at_layer_4_plus_outer_step_lemma_fc re zeta_i step_vec i_end
      h_bnd h_step_vec_pos h_step_vec_dvd h_zeta_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer4PlusOuterFC.step_post re zeta_i step_vec i_end k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusOuterFC.step_post] using hP
    · have hP : Layer4PlusOuterFC.step_post re zeta_i step_vec i_end k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusOuterFC.step_post] using hP

/-! ### Per-layer FC+bound combinators

    Each combinator pairs the FC equation (from FCTargets) with the
    per-lane output bound (from legacy `Equivalence.ntt_at_layer_X_spec(_B)`),
    so the downstream L3.3/L3.4 composition can chain them without
    re-applying two Triples per sub-call. See SKILL §9.11. -/

set_option maxHeartbeats 800000 in
/-- L3.3-step-7 — layer-7 dedicated FC + bound combinator.
    Input ≤ 3 (binomial-sampled), output ≤ 4803.
    Pairs `ntt_at_layer_7_portable_fc` (FC eq) with
    `libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_7_spec` (per-lane ≤ 4803). -/
@[spec high]
theorem ntt_at_layer_7_portable_fc_strong
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_at_layer_7_pure (lift_poly re)
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 4803 ⌝ ⦄ := by
  have h_fc := ntt_at_layer_7_portable_fc re scratch
    (fun chunk hc k hk => by
      have := h_pre chunk hc k hk; omega)
  have h_bd := libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_7_spec re scratch h_pre
  obtain ⟨r, h_eq, h_fc'⟩ := triple_exists_ok_fc h_fc
  obtain ⟨r', h_eq', h_bd'⟩ := triple_exists_ok_fc h_bd
  have h_rr : r = r' := by
    have : (Result.ok r : Result _) = Result.ok r' := by rw [← h_eq, h_eq']
    cases this; rfl
  subst h_rr
  exact triple_of_ok_fc h_eq ⟨h_fc', h_bd'⟩

set_option maxHeartbeats 800000 in
/-- L3.3-step-{4,5,6} + L3.4-step-7 — generic `layer_4_plus` FC + bound combinator.
    Parametric in `layer ∈ {4,5,6,7}`. Pairs `ntt_at_layer_4_plus_portable_fc`
    (FC eq, h_zeta strict form) with `libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_4_plus_spec`
    (output ≤ bnd.val + 3328, zeta-out = zeta_i + 128 >>> layer). -/
@[spec high]
theorem ntt_at_layer_4_plus_portable_fc_strong
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (layer : Std.Usize)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (bnd : Std.Usize)
    (h_layer : 4 ≤ layer.val ∧ layer.val ≤ 7)
    (h_bnd : bnd.val ≤ 8 * 3328)
    (h_zeta : zeta_i.val = (1 <<< (7 - layer.val)) - 1)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re layer scratch bnd
    ⦃ ⇓ p => ⌜ lift_poly p.2.1 = Spec.ntt_at_layer_4_plus_pure (lift_poly re) zeta_i layer
              ∧ p.1.val = zeta_i.val + 128 >>> layer.val
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd.val + 3328 ⌝ ⦄ := by
  obtain ⟨h_layer_lo, h_layer_hi⟩ := h_layer
  -- FC theorem h_bnd ceiling = 29439. bnd.val ≤ 8 * 3328 = 26624 ≤ 29439.
  have h_pre_29439 : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 29439 := by
    intro chunk hc k hk
    have := h_pre chunk hc k hk
    omega
  -- FC theorem h_zeta: zeta_i.val + (128 >>> layer.val) ≤ 127. Derive from
  -- h_zeta : zeta_i.val = (1 <<< (7 - layer.val)) - 1 by interval cases on layer.
  have h_zeta_fc : zeta_i.val + (128 >>> layer.val) ≤ 127 := by
    rw [h_zeta]
    interval_cases layer.val <;> decide
  have h_fc := ntt_at_layer_4_plus_portable_fc zeta_i re layer scratch bnd
    ⟨h_layer_lo, h_layer_hi⟩ h_pre_29439 h_zeta_fc
  have h_bd := libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_4_plus_spec
    layer zeta_i re scratch bnd ⟨h_layer_lo, h_layer_hi⟩ h_bnd h_zeta h_pre
  obtain ⟨r, h_eq, h_fc'⟩ := triple_exists_ok_fc h_fc
  obtain ⟨r', h_eq', h_bd'⟩ := triple_exists_ok_fc h_bd
  have h_rr : r = r' := by
    have : (Result.ok r : Result _) = Result.ok r' := by rw [← h_eq, h_eq']
    cases this; rfl
  subst h_rr
  exact triple_of_ok_fc h_eq ⟨h_fc', h_bd'.1, h_bd'.2⟩

set_option maxHeartbeats 800000 in
/-- L3.3-step-3 / L3.4-step-3 — layer-3 FC + bound combinator.
    Pairs `ntt_at_layer_3_portable_fc` (FC eq) with
    `libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_3_spec_B` (zeta-out = 31, per-lane ≤ bnd+3328). -/
@[spec high]
theorem ntt_at_layer_3_portable_fc_strong
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 15)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_3_pure (lift_poly re) zeta_i
              ∧ p.1.val = 31
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h_fc := ntt_at_layer_3_portable_fc zeta_i re initial_bound
    (fun chunk hc k hk => by have := h_pre chunk hc k hk; omega)
    (by rw [h_zeta]; decide)
  have h_bd := libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_3_spec_B
    zeta_i re initial_bound bnd h_bnd h_zeta h_pre
  obtain ⟨r, h_eq, h_fc'⟩ := triple_exists_ok_fc h_fc
  obtain ⟨r', h_eq', h_bd'⟩ := triple_exists_ok_fc h_bd
  have h_rr : r = r' := by
    have : (Result.ok r : Result _) = Result.ok r' := by rw [← h_eq, h_eq']
    cases this; rfl
  subst h_rr
  exact triple_of_ok_fc h_eq ⟨h_fc', h_bd'.1, h_bd'.2⟩

set_option maxHeartbeats 800000 in
/-- L3.3-step-2 / L3.4-step-2 — layer-2 FC + bound combinator.
    Pairs `ntt_at_layer_2_portable_fc` (FC eq) with
    `libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_2_spec_B` (zeta-out = 63, per-lane ≤ bnd+3328). -/
@[spec high]
theorem ntt_at_layer_2_portable_fc_strong
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 31)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_2_pure (lift_poly re) zeta_i
              ∧ p.1.val = 63
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h_fc := ntt_at_layer_2_portable_fc zeta_i re initial_bound
    (fun chunk hc k hk => by have := h_pre chunk hc k hk; omega)
    (by rw [h_zeta]; decide)
  have h_bd := libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_2_spec_B
    zeta_i re initial_bound bnd h_bnd h_zeta h_pre
  obtain ⟨r, h_eq, h_fc'⟩ := triple_exists_ok_fc h_fc
  obtain ⟨r', h_eq', h_bd'⟩ := triple_exists_ok_fc h_bd
  have h_rr : r = r' := by
    have : (Result.ok r : Result _) = Result.ok r' := by rw [← h_eq, h_eq']
    cases this; rfl
  subst h_rr
  exact triple_of_ok_fc h_eq ⟨h_fc', h_bd'.1, h_bd'.2⟩

set_option maxHeartbeats 800000 in
/-- L3.3-step-1 / L3.4-step-1 — layer-1 FC + bound combinator.
    Pairs `ntt_at_layer_1_portable_fc` (FC eq) with
    `libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_1_spec_B` (zeta-out = 127, per-lane ≤ bnd+3328). -/
@[spec high]
theorem ntt_at_layer_1_portable_fc_strong
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 63)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re initial_bound
    ⦃ ⇓ p => ⌜ lift_poly p.2 = Spec.ntt_layer_1_pure (lift_poly re) zeta_i
              ∧ p.1.val = 127
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  have h_fc := ntt_at_layer_1_portable_fc zeta_i re initial_bound
    (fun chunk hc k hk => by have := h_pre chunk hc k hk; omega)
    (by omega)
  have h_bd := libcrux_iot_ml_kem.Polynomial.NttDrivers.ntt_at_layer_1_spec_B
    zeta_i re initial_bound bnd h_bnd h_zeta h_pre
  obtain ⟨r, h_eq, h_fc'⟩ := triple_exists_ok_fc h_fc
  obtain ⟨r', h_eq', h_bd'⟩ := triple_exists_ok_fc h_bd
  have h_rr : r = r' := by
    have : (Result.ok r : Result _) = Result.ok r' := by rw [← h_eq, h_eq']
    cases this; rfl
  subst h_rr
  exact triple_of_ok_fc h_eq ⟨h_fc', h_bd'.1, h_bd'.2⟩


/-- L3.3 — `ntt_binomially_sampled_ring_element` driver (7 layer
    composition + barrett reduce). Projects on the poly component.

    Input bound `≤ 3`: from the upstream binomial sampler with η₁=2,
    which produces samples in `[-2, 2]`. We use `≤ 3` (one slack)
    to match `ntt_at_layer_7_spec`'s legacy bound precondition.

    Implementation chain: dedicated `ntt_at_layer_7` → 3× `ntt_at_layer_4_plus`
    (layers 6, 5, 4) → `ntt_at_layer_3` → `ntt_at_layer_2` →
    `ntt_at_layer_1` → `poly_barrett_reduce`. Each layer's FC equation
    comes from FCTargets `ntt_at_layer_X_portable_fc`; the per-layer
    output bound comes from legacy
    `libcrux_iot_ml_kem.Equivalence.ntt_at_layer_X_spec(_B)`. -/
@[spec]
theorem ntt_binomially_sampled_ring_element_fc
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_pure (lift_poly re) ⌝ ⦄ := by
  -- Strategy: collect all step equations using *_fc_strong combinators
  -- and arithmetic helpers, then assemble the full impl-body equation via
  -- `unfold ; simp [...]`. Close the Triple with `triple_of_ok_fc h_body`
  -- and prove the lift_poly equation by chaining FC equations through
  -- `Spec.ntt_pure` plus the barrett bridge.
  -- =============================================================
  -- Step 1: layer_7. re scratch → re1 scratch1. ≤ 3 → ≤ 4803.
  -- =============================================================
  obtain ⟨⟨re1, scratch1⟩, h1_eq, h1_fc, h1_bnd⟩ :=
    triple_exists_ok_fc (ntt_at_layer_7_portable_fc_strong re scratch h_bnd)
  dsimp only at h1_fc h1_bnd
  -- =============================================================
  -- Step 2: layer_4_plus (zeta_i=1, layer=6, bnd=11207). ≤ 4803 → ≤ 14535.
  -- =============================================================
  have h_re1_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re1.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ (11207#usize : Std.Usize).val := by
    intro i hi j hj
    have hb := h1_bnd i hi j hj
    show _ ≤ 11207
    omega
  obtain ⟨⟨zeta_i1, re2, scratch2⟩, h2_eq, h2_fc, h2_zout, h2_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong 1#usize re1 6#usize scratch1 11207#usize
        (by decide) (by decide) (by decide) h_re1_loose)
  dsimp only at h2_fc h2_zout h2_bnd
  have h_zeta_i1 : zeta_i1.val = 3 := by rw [h2_zout]; decide
  -- =============================================================
  -- Step 3: usize_add 11207 + 3328 = 14535.
  -- =============================================================
  obtain ⟨i14535, hi14535_eq, hi14535_val⟩ :=
    usize_add_ok_eq_fc 11207#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 4: layer_4_plus (zeta_i1, layer=5, bnd=14535). ≤ 14535 → ≤ 17863.
  -- =============================================================
  have h_re2_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ i14535.val := by
    intro i hi j hj
    have hb := h2_bnd i hi j hj
    have h11207 : (11207#usize : Std.Usize).val = 11207 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h11207] at hb
    rw [hi14535_val, h11207, h3328]
    omega
  have h_i14535_bnd : i14535.val ≤ 8 * 3328 := by
    have h := hi14535_val
    have h11207 : (11207#usize : Std.Usize).val = 11207 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h11207, h3328] at h
    omega
  obtain ⟨⟨zeta_i2, re3, scratch3⟩, h4_eq, h4_fc, h4_zout, h4_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong zeta_i1 re2 5#usize scratch2 i14535
        (by decide) h_i14535_bnd
        (by rw [h_zeta_i1]; decide) h_re2_loose)
  dsimp only at h4_fc h4_zout h4_bnd
  have h_zeta_i2 : zeta_i2.val = 7 := by
    rw [h4_zout, h_zeta_i1]; decide
  -- =============================================================
  -- Step 5: usize_mul 2 * 3328 = 6656.
  -- =============================================================
  obtain ⟨i6656, hi6656_eq, hi6656_val⟩ :=
    usize_mul_ok_eq_fc 2#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 6: usize_add 11207 + 6656 = 17863.
  -- =============================================================
  obtain ⟨i17863, hi17863_eq, hi17863_val⟩ :=
    usize_add_ok_eq_fc 11207#usize i6656 (by have := hi6656_val; scalar_tac)
  -- =============================================================
  -- Step 7: layer_4_plus (zeta_i2, layer=4, bnd=17863). ≤ 17863 → ≤ 21191.
  -- =============================================================
  have h_re3_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ i17863.val := by
    intro i hi j hj
    have hb := h4_bnd i hi j hj
    have h11207 : (11207#usize : Std.Usize).val = 11207 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    rw [hi14535_val, h11207, h3328] at hb
    rw [hi17863_val, hi6656_val, h11207, h2, h3328]
    omega
  have h_i17863_bnd : i17863.val ≤ 8 * 3328 := by
    have h := hi17863_val
    have hm := hi6656_val
    have h11207 : (11207#usize : Std.Usize).val = 11207 := by decide
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h11207] at h
    rw [h2, h3328] at hm
    omega
  obtain ⟨⟨zeta_i3, re4, scratch4⟩, h7_eq, h7_fc, h7_zout, h7_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong zeta_i2 re3 4#usize scratch3 i17863
        (by decide) h_i17863_bnd
        (by rw [h_zeta_i2]; decide) h_re3_loose)
  dsimp only at h7_fc h7_zout h7_bnd
  have h_zeta_i3 : zeta_i3.val = 15 := by
    rw [h7_zout, h_zeta_i2]; decide
  -- =============================================================
  -- Step 8: usize_mul 3 * 3328 = 9984.
  -- =============================================================
  obtain ⟨i9984, hi9984_eq, hi9984_val⟩ :=
    usize_mul_ok_eq_fc 3#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 9: usize_add 11207 + 9984 = 21191.
  -- =============================================================
  obtain ⟨i21191, hi21191_eq, hi21191_val⟩ :=
    usize_add_ok_eq_fc 11207#usize i9984 (by have := hi9984_val; scalar_tac)
  -- =============================================================
  -- Step 10: layer_3 (zeta_i3=15, bnd=21191 Nat). → ≤ 24519. zeta_out=31.
  -- =============================================================
  have h_re4_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re4.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 21191 := by
    intro i hi j hj
    have hb := h7_bnd i hi j hj
    have h11207 : (11207#usize : Std.Usize).val = 11207 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    rw [hi17863_val, hi6656_val, h11207, h2, h3328] at hb
    omega
  obtain ⟨⟨zeta_i4, re5⟩, h10_eq, h10_fc, h10_zout, h10_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_3_portable_fc_strong zeta_i3 re4 i21191 21191
        (by decide) h_zeta_i3 h_re4_loose)
  dsimp only at h10_fc h10_zout h10_bnd
  -- =============================================================
  -- Step 11: usize_mul 4 * 3328 = 13312.
  -- =============================================================
  obtain ⟨i13312, hi13312_eq, hi13312_val⟩ :=
    usize_mul_ok_eq_fc 4#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 12: usize_add 11207 + 13312 = 24519.
  -- =============================================================
  obtain ⟨i24519, hi24519_eq, hi24519_val⟩ :=
    usize_add_ok_eq_fc 11207#usize i13312 (by have := hi13312_val; scalar_tac)
  -- =============================================================
  -- Step 13: layer_2 (zeta_i4=31, bnd=24519 Nat). → ≤ 27847. zeta_out=63.
  -- =============================================================
  have h_re5_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re5.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 24519 := by
    intro i hi j hj
    have hb := h10_bnd i hi j hj
    omega
  obtain ⟨⟨zeta_i5, re6⟩, h13_eq, h13_fc, h13_zout, h13_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_2_portable_fc_strong zeta_i4 re5 i24519 24519
        (by decide) h10_zout h_re5_loose)
  dsimp only at h13_fc h13_zout h13_bnd
  -- =============================================================
  -- Step 14: usize_mul 5 * 3328 = 16640.
  -- =============================================================
  obtain ⟨i16640, hi16640_eq, hi16640_val⟩ :=
    usize_mul_ok_eq_fc 5#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 15: usize_add 11207 + 16640 = 27847.
  -- =============================================================
  obtain ⟨i27847, hi27847_eq, hi27847_val⟩ :=
    usize_add_ok_eq_fc 11207#usize i16640 (by have := hi16640_val; scalar_tac)
  -- =============================================================
  -- Step 16: layer_1 (zeta_i5=63, bnd=27847 Nat). → ≤ 31175. zeta_out=127.
  -- =============================================================
  have h_re6_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re6.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 27847 := by
    intro i hi j hj
    have hb := h13_bnd i hi j hj
    omega
  obtain ⟨⟨_zeta_i6, re7⟩, h16_eq, h16_fc, _h16_zout, h16_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_1_portable_fc_strong zeta_i5 re6 i27847 27847
        (by decide) h13_zout h_re6_loose)
  dsimp only at h16_fc h16_bnd
  -- =============================================================
  -- Step 17: poly_barrett_reduce. ≤ 31175 ≤ 32767 → canonical residue.
  -- =============================================================
  have h_re7_loose : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re7.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hc ℓ hℓ
    have hb := h16_bnd chunk hc ℓ hℓ
    omega
  obtain ⟨re8, h17_eq, h17_fc⟩ :=
    triple_exists_ok_fc (poly_barrett_reduce_fc re7 h_re7_loose)
  -- =============================================================
  -- Compose: derive the full impl `do`-block equation by simp-folding
  -- all step equations into the unfolded body.
  -- =============================================================
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
        (vectortraitsOperationsInst := portable_ops_inst) re scratch
        = .ok (re8, scratch4) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
    simp [h1_eq, h2_eq, h4_eq, h7_eq, h10_eq, h13_eq, h16_eq, h17_eq,
          hi14535_eq, hi6656_eq, hi17863_eq,
          hi9984_eq, hi21191_eq,
          hi13312_eq, hi24519_eq,
          hi16640_eq, hi27847_eq]
  apply triple_of_ok_fc h_body
  -- =============================================================
  -- Prove lift_poly equation by chaining FC equations through Spec.ntt_pure.
  -- =============================================================
  show lift_poly re8 = Spec.ntt_pure (lift_poly re)
  unfold Spec.ntt_pure
  -- Bridge barrett: h17_fc : poly_barrett_reduce (lift_poly re7) = .ok (lift_poly re8).
  have hB_bridge :
      hacspec_ml_kem.polynomial.poly_barrett_reduce (lift_poly re7)
        = .ok (Spec.Pure.polynomial.poly_barrett_reduce_pure (lift_poly re7)) :=
    Spec.Pure.polynomial.poly_barrett_reduce_eq_ok (lift_poly re7)
  rw [hB_bridge] at h17_fc
  have h_re8_eq : lift_poly re8
      = Spec.Pure.polynomial.poly_barrett_reduce_pure (lift_poly re7) := by
    have h := h17_fc
    exact (Aeneas.Std.Result.ok.injEq _ _).mp h.symm
  -- zeta_i identifications: substitute zeta values into the spec chain via .val.
  have h_zeta_i2 : zeta_i2.val = 7 := by rw [h4_zout, h_zeta_i1]; decide
  have h_zeta_i3 : zeta_i3.val = 15 := by rw [h7_zout, h_zeta_i2]; decide
  have h_zeta_eq1 : zeta_i1 = 3#usize := by
    have := h_zeta_i1; scalar_tac
  have h_zeta_eq2 : zeta_i2 = 7#usize := by
    have := h_zeta_i2; scalar_tac
  have h_zeta_eq3 : zeta_i3 = 15#usize := by
    have := h_zeta_i3; scalar_tac
  have h_zeta_eq4 : zeta_i4 = 31#usize := by
    have := h10_zout; scalar_tac
  have h_zeta_eq5 : zeta_i5 = 63#usize := by
    have := h13_zout; scalar_tac
  rw [h_re8_eq, h16_fc, h13_fc, h10_fc, h7_fc, h4_fc, h2_fc, h1_fc,
      h_zeta_eq1, h_zeta_eq2, h_zeta_eq3, h_zeta_eq4, h_zeta_eq5]




end libcrux_iot_ml_kem.Ntt
