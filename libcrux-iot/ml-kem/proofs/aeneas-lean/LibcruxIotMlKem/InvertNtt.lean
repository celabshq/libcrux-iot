/-
  # `InvertNtt.lean` — extracted from `FCTargets.lean` §invert_ntt.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.InvertNtt
open libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L3i — Inverse-NTT driver loops.

    Mirror of §L3 for the inverse direction. Each `invert_ntt_at_layer_N`
    is a 16-iter loop over `round ∈ [0, 16)` that DECREMENTS `zeta_i` by
    `4` (layer 1), `2` (layer 2), or `1` (layer 3) per chunk. Layer 4+
    is a nested cross-chunk butterfly (deferred to Task H). Each chunk
    dispatches to the corresponding `inv_ntt_layer_N_step_fc` (FCTargets
    L2.9-11, just closed in Task E).

    Top-level composer `invert_ntt_montgomery` (Task I) calls these in
    sequence: layer 1 with `zeta_i = 64`, layer 2 with `zeta_i = 32`,
    layer 3 with `zeta_i = 16`, etc. The FC posts expose both the
    output `zeta_i.val` (so the composer can chain) and the
    `Spec.invert_ntt_layer_N_pure` equation. -/

/-! ### L3i.1 — Loop scaffolding for `invert_ntt_at_layer_1_portable_fc`.

    Mirror of §L3.1 scaffolding but with `zeta_i` DECREASING (4 per chunk)
    and reads in reverse order (`zeta_i - 4k - {1,2,3,4}`). The Acc type
    `(Std.Usize, PolynomialRingElement)` matches the impl's loop state. -/

namespace Layer1FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_sub_ok_eq` helper (mirror of `Layer1FC.usize_add_ok_eq` but for sub). -/
theorem usize_sub_ok_eq (x y : Std.Usize)
    (h_ge : y.val ≤ x.val) :
    ∃ z : Std.Usize, (x - y : Result Std.Usize) = .ok z ∧ z.val = x.val - y.val := by
  have hT := Std.Usize.sub_spec h_ge
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v.1⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `invert_ntt_at_layer_1_portable_fc`.
    Tracks DECREASING `zeta_i`: at outer iter `k`, `acc.1.val = zeta_i_0.val - 4 * k.val`.
    Chunks `< k.val` are FC-equal to the per-chunk inverse step; chunks `≥ k.val`
    are unchanged from `re`. Per-lane output bound `≤ 3328` on every chunk. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val - 4 * k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_inv_ntt_layer_1_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val - 4 * j - 1))
              (Spec.zeta_at (zeta_i_0.val - 4 * j - 2))
              (Spec.zeta_at (zeta_i_0.val - 4 * j - 3))
              (Spec.zeta_at (zeta_i_0.val - 4 * j - 4)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
    ∧ (∀ c : Nat, c < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328))

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
/-- Per-iteration FC step lemma for the inverse layer-1 driver. Given a valid
    loop state `(acc, k)` with `k.val < 16`, decreases `zeta_i` by 4 and records
    the FC equation for chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem invert_ntt_at_layer_1_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 13312)
    (h_zeta_lo : 64 ≤ zeta_i_0.val)
    (h_zeta_hi : zeta_i_0.val ≤ 128)
    (acc : Layer1FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer1FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer1FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_um3 : (3#usize : Std.Usize).val = 3 := rfl
    -- acc.1.val = zeta_i_0.val - 4*k.val, with k.val ≤ 15 ⇒ acc.1.val ≥ zeta_i_0.val - 60 ≥ 4.
    have h_acc1_ge_4 : 4 ≤ acc.1.val := by
      rw [h_zeta_acc]
      have h_k_le_15 : k.val ≤ 15 := by omega
      omega
    -- (1) `zeta_i - 1` ⇒ `zi1` with `zi1.val = acc.1.val - 1`.
    have h_z_ge : (1#usize : Std.Usize).val ≤ acc.1.val := by rw [h_um]; omega
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer1FC.usize_sub_ok_eq acc.1 1#usize h_z_ge
    have h_zi1_val_arith : zi1.val = acc.1.val - 1 := by rw [h_zi1_val, h_um]
    -- zi1.val < 128: zi1.val = acc.1.val - 1 = zeta_i_0 - 4k - 1 ≤ zeta_i_0 - 1 ≤ 127.
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
    -- (3) `polynomial.zeta zi1` ⇒ `z1` at index `zi1.val = acc.1.val - 1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `zi1 - 1` ⇒ `zi3.val = zi1.val - 1 = acc.1.val - 2`.
    have h_zi3_ge : (1#usize : Std.Usize).val ≤ zi1.val := by
      rw [h_um, h_zi1_val_arith]; omega
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      Layer1FC.usize_sub_ok_eq zi1 1#usize h_zi3_ge
    have h_zi3_val_arith : zi3.val = acc.1.val - 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]; omega
    have h_zi3_lt : zi3.val < 128 := by
      rw [h_zi3_val_arith, h_zeta_acc]; omega
    -- (5) `polynomial.zeta zi3` ⇒ `z2`.
    obtain ⟨z2, h_z2_eq, h_z2_v, h_z2_bd, h_z2_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi3 h_zi3_lt)
    -- (6) `zi1 - 2` ⇒ `zi5.val = zi1.val - 2 = acc.1.val - 3`.
    have h_zi5_ge : (2#usize : Std.Usize).val ≤ zi1.val := by
      rw [h_um2, h_zi1_val_arith]; omega
    obtain ⟨zi5, h_zi5_eq, h_zi5_val⟩ :=
      Layer1FC.usize_sub_ok_eq zi1 2#usize h_zi5_ge
    have h_zi5_val_arith : zi5.val = acc.1.val - 3 := by
      rw [h_zi5_val, h_um2, h_zi1_val_arith]; omega
    have h_zi5_lt : zi5.val < 128 := by
      rw [h_zi5_val_arith, h_zeta_acc]; omega
    -- (7) `polynomial.zeta zi5` ⇒ `z3`.
    obtain ⟨z3, h_z3_eq, h_z3_v, h_z3_bd, h_z3_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi5 h_zi5_lt)
    -- (8) `zi1 - 3` ⇒ `zi7.val = zi1.val - 3 = acc.1.val - 4`.
    have h_zi7_ge : (3#usize : Std.Usize).val ≤ zi1.val := by
      rw [h_um3, h_zi1_val_arith]; omega
    obtain ⟨zi7, h_zi7_eq, h_zi7_val⟩ :=
      Layer1FC.usize_sub_ok_eq zi1 3#usize h_zi7_ge
    have h_zi7_val_arith : zi7.val = acc.1.val - 4 := by
      rw [h_zi7_val, h_um3, h_zi1_val_arith]; omega
    have h_zi7_lt : zi7.val < 128 := by
      rw [h_zi7_val_arith, h_zeta_acc]; omega
    -- (9) `polynomial.zeta zi7` ⇒ `z4`.
    obtain ⟨z4, h_z4_eq, h_z4_v, h_z4_bd, h_z4_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi7 h_zi7_lt)
    -- (10) `inv_ntt_layer_1_step t z1 z2 z3 z4`. Pre: t's lanes ≤ 13312 via h_pre + undone.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 13312 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.inv_ntt_layer_1_step.
    obtain ⟨t1, h_t1_eq, h_t1_lift, h_t1_bnd⟩ :=
      triple_exists_ok_fc (inv_ntt_layer_1_step_fc t z1 z2 z3 z4
        ⟨h_z1_bd, h_z2_bd, h_z3_bd, h_z4_bd⟩ h_t_bd)
    -- Compose entire body. Loop output for `cont` is `(iter', zi7, re')` (3-tuple in
    -- the impl's loop-state, the Acc holds the latter two as a pair).
    set acc' : Layer1FC.Acc := (zi7, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
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
              libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_1_step t z1 z2 z3 z4
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
    show (Layer1FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val - 4 * s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 1))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 2))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 3))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 4)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < s.val → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- acc'.1 = zi7, zi7.val = acc.1.val - 4 = zeta_i_0.val - 4 * (k.val + 1).
        show zi7.val = zeta_i_0.val - 4 * s.val
        rw [h_zi7_val_arith, h_zeta_acc, hs_val]
        have h_k_le_15 : k.val ≤ 15 := by omega
        omega
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
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
          -- Need: Spec.chunk_inv_ntt_layer_1_step_pure (lift_chunk re.coefficients[k])
          --   (lift_fe_mont z1..z4) = Spec.chunk_inv_ntt_layer_1_step_pure (...)
          --     (Spec.zeta_at (zeta_i_0 - 4k - 1..4)).
          have h_k_le_15 : k.val ≤ 15 := by omega
          have h_zi1_z : zi1.val = zeta_i_0.val - 4 * k.val - 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          have h_zi3_z : zi3.val = zeta_i_0.val - 4 * k.val - 2 := by
            rw [h_zi3_val_arith, h_zeta_acc]
          have h_zi5_z : zi5.val = zeta_i_0.val - 4 * k.val - 3 := by
            rw [h_zi5_val_arith, h_zeta_acc]
          have h_zi7_z : zi7.val = zeta_i_0.val - 4 * k.val - 4 := by
            rw [h_zi7_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val - 4 * k.val - 1)
                from by rw [← h_zi1_z]; exact h_z1_lift]
          rw [show lift_fe_mont z2 = Spec.zeta_at (zeta_i_0.val - 4 * k.val - 2)
                from by rw [← h_zi3_z]; exact h_z2_lift]
          rw [show lift_fe_mont z3 = Spec.zeta_at (zeta_i_0.val - 4 * k.val - 3)
                from by rw [← h_zi5_z]; exact h_z3_lift]
          rw [show lift_fe_mont z4 = Spec.zeta_at (zeta_i_0.val - 4 * k.val - 4)
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
      · -- Per-lane output bound on every chunk.
        intro c hc ℓ hℓ
        show ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        show (((acc.2.coefficients.set k t1).val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        by_cases h_ck : c = k.val
        · -- At touched chunk: value is t1, bounded by h_t1_bnd.
          have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[c]! = t1 := by
            rw [h_ck]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val]; exact h_t1_bnd ℓ hℓ
        · -- At untouched chunk: value preserved from acc.2, bounded by h_acc_bnd.
          have h_ne : k.val ≠ c := Ne.symm h_ck
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[c]! = acc.2.coefficients.val[c]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k c t1 h_ne
          rw [h_set_ne_val]; exact h_acc_bnd c (by omega) ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
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
        acc.1.val = zeta_i_0.val - 4 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 1))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 2))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 3))
                  (Spec.zeta_at (zeta_i_0.val - 4 * j - 4)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · intro c hc ℓ hℓ; exact h_acc_bnd c (by omega) ℓ hℓ
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3i.1 — `invert_ntt_at_layer_1` driver: 16-chunk loop, per-chunk
    4-zeta-lookup decreasing `zeta_i` by 4. Post: `p.1.val = zeta_i.val - 64`
    (the output zeta_i, for composition) and `lift_poly p.2 =
    Spec.invert_ntt_layer_1_pure (lift_poly re) zeta_i`.

    Tightening preconditions (added by the proof author):
    - `h_zeta_lo : 64 ≤ zeta_i.val` — needed for the 4 subtractions per chunk
      to succeed without Nat underflow at every iter (worst case at iter k=15
      is `acc.1.val = zeta_i - 60`, and we further subtract 4).
    - `h_zeta_hi : zeta_i.val ≤ 128` — so `polynomial.zeta` index (worst case
      `zeta_i - 1` at iter k=0) is `< 128`.
    - `h_bnd` per-lane bound `≤ 13312` on `re`'s chunks — matches
      `inv_ntt_layer_1_step_fc`'s precondition. The loop invariant tracks
      only PROCESSED chunks as ≤ 3328; the initial state at `k = 0` is
      vacuously satisfied (no processed chunks yet). Each iteration's
      `inv_ntt_layer_1_step_fc` establishes the bound at the touched chunk;
      at k=16 all chunks are covered, giving the output bound ≤ 3328. -/
@[spec high]
theorem invert_ntt_at_layer_1_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312)
    (h_zeta_lo : 64 ≤ zeta_i.val)
    (h_zeta_hi : zeta_i.val ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i.val - 64
              ∧ lift_poly p.2 = Spec.invert_ntt_layer_1_pure (lift_poly re) zeta_i
              ∧ (∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_1_loop.body
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
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0: zeta_i = zeta_i - 4*0.
          show zeta_i.val = zeta_i.val - 4 * (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val - 4 * 0
          omega
        · intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _
          trivial
        · -- Initial bound: vacuous at k=0 (no processed chunks yet).
          intro c hc
          exact absurd hc (Nat.not_lt_zero c))
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations + zeta_i = zeta_i_0 - 64.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer1FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val - 4 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_1_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val - 4 * j - 1))
                  (Spec.zeta_at (zeta_i.val - 4 * j - 2))
                  (Spec.zeta_at (zeta_i.val - 4 * j - 3))
                  (Spec.zeta_at (zeta_i.val - 4 * j - 4)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((r.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer1FC.inv] using h_inv_holds
    obtain ⟨h_zeta_eq, h_done, _h_undone, h_done_bnd⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    refine ⟨?_, ?_, ?_⟩
    · -- p.1.val = zeta_i.val - 64.
      rw [h_zeta_eq, h16]
    · -- The chunks equation.
      unfold Spec.invert_ntt_layer_1_pure
      set chunks_arr : Std.Array
          (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
        Std.Array.make 16#usize ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_1_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - 4 * k - 1))
            (Spec.zeta_at (zeta_i.val - 4 * k - 2))
            (Spec.zeta_at (zeta_i.val - 4 * k - 3))
            (Spec.zeta_at (zeta_i.val - 4 * k - 4))))
          (by simp) with hchunks_def
      have h_chunks_len : chunks_arr.val.length = 16 := by
        show ((List.range 16).map _).length = 16
        simp
      have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
          chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
            = lift_chunk (r.2.coefficients.val[k]!) := by
        intro k hk
        show ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_1_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - 4 * k - 1))
            (Spec.zeta_at (zeta_i.val - 4 * k - 2))
            (Spec.zeta_at (zeta_i.val - 4 * k - 3))
            (Spec.zeta_at (zeta_i.val - 4 * k - 4))))[k]'_ = _
        rw [List.getElem_map, List.getElem_range]
        rw [chunk_at_lift_poly_fc re k hk]
        exact (h_done k hk).symm
      have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
      exact h_final.symm
    · -- Per-lane output bound from the loop invariant's strengthened conjunct.
      exact h_done_bnd
  · -- Step lemma application: dispatch invert_ntt_at_layer_1_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := invert_ntt_at_layer_1_step_lemma_fc zeta_i re h_bnd h_zeta_lo h_zeta_hi
                     acc k h_le hinv
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

/-! ### L3i.2 — Loop scaffolding for `invert_ntt_at_layer_2_portable_fc`.

    Mirror of §L3i.1 scaffolding but with `zeta_i` DECREASING (2 per chunk)
    and reads in reverse order (`zeta_i - 2k - {1,2}`). -/

namespace Layer2FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_sub_ok_eq` helper (mirror of `Layer1FC.usize_sub_ok_eq`). -/
theorem usize_sub_ok_eq (x y : Std.Usize)
    (h_ge : y.val ≤ x.val) :
    ∃ z : Std.Usize, (x - y : Result Std.Usize) = .ok z ∧ z.val = x.val - y.val := by
  have hT := Std.Usize.sub_spec h_ge
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v.1⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `invert_ntt_at_layer_2_portable_fc`.
    Tracks DECREASING `zeta_i`: at outer iter `k`, `acc.1.val = zeta_i_0.val - 2 * k.val`.
    Chunks `< k.val` are FC-equal to the per-chunk inverse step; chunks `≥ k.val`
    are unchanged from `re`. Per-lane output bound `≤ 3328` on every chunk. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val - 2 * k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_inv_ntt_layer_2_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val - 2 * j - 1))
              (Spec.zeta_at (zeta_i_0.val - 2 * j - 2)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
    ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328))

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
/-- Per-iteration FC step lemma for the inverse layer-2 driver. Given a valid
    loop state `(acc, k)` with `k.val < 16`, decreases `zeta_i` by 2 and records
    the FC equation for chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem invert_ntt_at_layer_2_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 13312)
    (h_zeta_lo : 32 ≤ zeta_i_0.val)
    (h_zeta_hi : zeta_i_0.val ≤ 128)
    (acc : Layer2FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer2FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer2FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    -- acc.1.val = zeta_i_0.val - 2*k.val, with k.val ≤ 15 ⇒ acc.1.val ≥ zeta_i_0.val - 30 ≥ 2.
    have h_acc1_ge_2 : 2 ≤ acc.1.val := by
      rw [h_zeta_acc]
      have h_k_le_15 : k.val ≤ 15 := by omega
      omega
    -- (1) `zeta_i - 1` ⇒ `zi1` with `zi1.val = acc.1.val - 1`.
    have h_z_ge : (1#usize : Std.Usize).val ≤ acc.1.val := by rw [h_um]; omega
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer2FC.usize_sub_ok_eq acc.1 1#usize h_z_ge
    have h_zi1_val_arith : zi1.val = acc.1.val - 1 := by rw [h_zi1_val, h_um]
    -- zi1.val < 128: zi1.val = acc.1.val - 1 = zeta_i_0 - 2k - 1 ≤ zeta_i_0 - 1 ≤ 127.
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
    -- (3) `polynomial.zeta zi1` ⇒ `z1` at index `zi1.val = acc.1.val - 1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `zi1 - 1` ⇒ `zi3.val = zi1.val - 1 = acc.1.val - 2`.
    have h_zi3_ge : (1#usize : Std.Usize).val ≤ zi1.val := by
      rw [h_um, h_zi1_val_arith]; omega
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      Layer2FC.usize_sub_ok_eq zi1 1#usize h_zi3_ge
    have h_zi3_val_arith : zi3.val = acc.1.val - 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]; omega
    have h_zi3_lt : zi3.val < 128 := by
      rw [h_zi3_val_arith, h_zeta_acc]; omega
    -- (5) `polynomial.zeta zi3` ⇒ `z2`.
    obtain ⟨z2, h_z2_eq, h_z2_v, h_z2_bd, h_z2_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi3 h_zi3_lt)
    -- (6) `inv_ntt_layer_2_step t z1 z2`. Pre: t's lanes ≤ 13312 via h_pre + undone.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 13312 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.inv_ntt_layer_2_step.
    obtain ⟨t1, h_t1_eq, h_t1_lift, h_t1_bnd⟩ :=
      triple_exists_ok_fc (inv_ntt_layer_2_step_fc t z1 z2
        ⟨h_z1_bd, h_z2_bd⟩ h_t_bd)
    -- Compose entire body. Loop output for `cont` is `(iter', zi3, re')`.
    set acc' : Layer2FC.Acc := (zi3, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
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
            h_z2_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_2_step t z1 z2
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
    show (Layer2FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val - 2 * s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - 2 * j - 1))
                  (Spec.zeta_at (zeta_i_0.val - 2 * j - 2)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- acc'.1 = zi3, zi3.val = acc.1.val - 2 = zeta_i_0.val - 2 * (k.val + 1).
        show zi3.val = zeta_i_0.val - 2 * s.val
        rw [h_zi3_val_arith, h_zeta_acc, hs_val]
        have h_k_le_15 : k.val ≤ 15 := by omega
        omega
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
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
          have h_k_le_15 : k.val ≤ 15 := by omega
          have h_zi1_z : zi1.val = zeta_i_0.val - 2 * k.val - 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          have h_zi3_z : zi3.val = zeta_i_0.val - 2 * k.val - 2 := by
            rw [h_zi3_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val - 2 * k.val - 1)
                from by rw [← h_zi1_z]; exact h_z1_lift]
          rw [show lift_fe_mont z2 = Spec.zeta_at (zeta_i_0.val - 2 * k.val - 2)
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
      · -- Per-lane output bound on every chunk.
        intro c hc ℓ hℓ
        show ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        show (((acc.2.coefficients.set k t1).val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        by_cases h_ck : c = k.val
        · have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[c]! = t1 := by
            rw [h_ck]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val]; exact h_t1_bnd ℓ hℓ
        · have h_ne : k.val ≠ c := Ne.symm h_ck
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[c]! = acc.2.coefficients.val[c]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k c t1 h_ne
          rw [h_set_ne_val]; exact h_acc_bnd c hc ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
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
        acc.1.val = zeta_i_0.val - 2 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - 2 * j - 1))
                  (Spec.zeta_at (zeta_i_0.val - 2 * j - 2)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · exact h_acc_bnd
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3i.2 — `invert_ntt_at_layer_2` driver: 16-chunk loop, per-chunk
    2-zeta-lookup decreasing `zeta_i` by 2. Mirror of `L3i.1` and forward
    `ntt_at_layer_2_portable_fc`. Locked POST exposes
    `p.1.val = zeta_i.val - 32` (output zeta_i for composer chaining) +
    `lift_poly p.2 = Spec.invert_ntt_layer_2_pure (lift_poly re) zeta_i`.

    Tightening preconditions (added by the proof author):
    - `h_zeta_lo : 32 ≤ zeta_i.val` — needed for the 2 subtractions per chunk
      to succeed without Nat underflow at every iter (worst case at iter k=15
      is `acc.1.val = zeta_i - 30`, and we further subtract 2).
    - `h_zeta_hi : zeta_i.val ≤ 128` — so `polynomial.zeta` index (worst case
      `zeta_i - 1` at iter k=0) is `< 128`.
    - `h_bnd` per-lane bound `≤ 13312` on `re`'s chunks — matches
      `inv_ntt_layer_2_step_fc`'s precondition.
    - `h_bnd_strict` per-lane bound `≤ 3328` on `re`'s chunks — needed for
      the strengthened POST's output-bound conjunct. -/
@[spec high]
theorem invert_ntt_at_layer_2_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312)
    (h_bnd_strict : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 3328)
    (h_zeta_lo : 32 ≤ zeta_i.val)
    (h_zeta_hi : zeta_i.val ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i.val - 32
              ∧ lift_poly p.2 = Spec.invert_ntt_layer_2_pure (lift_poly re) zeta_i
              ∧ (∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_2_loop.body
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
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0: zeta_i = zeta_i - 2*0.
          show zeta_i.val = zeta_i.val - 2 * (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val - 2 * 0
          omega
        · intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _
          trivial
        · -- Initial bound: acc.2 = re at k=0, so bound from h_bnd_strict.
          intro c hc ℓ hℓ
          exact h_bnd_strict c hc ℓ hℓ)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations + zeta_i = zeta_i_0 - 32.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer2FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val - 2 * (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_2_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val - 2 * j - 1))
                  (Spec.zeta_at (zeta_i.val - 2 * j - 2)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((r.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer2FC.inv] using h_inv_holds
    obtain ⟨h_zeta_eq, h_done, _h_undone, h_done_bnd⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    refine ⟨?_, ?_, ?_⟩
    · -- p.1.val = zeta_i.val - 32.
      rw [h_zeta_eq, h16]
    · -- The chunks equation.
      unfold Spec.invert_ntt_layer_2_pure
      set chunks_arr : Std.Array
          (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
        Std.Array.make 16#usize ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_2_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - 2 * k - 1))
            (Spec.zeta_at (zeta_i.val - 2 * k - 2))))
          (by simp) with hchunks_def
      have h_chunks_len : chunks_arr.val.length = 16 := by
        show ((List.range 16).map _).length = 16
        simp
      have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
          chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
            = lift_chunk (r.2.coefficients.val[k]!) := by
        intro k hk
        show ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_2_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - 2 * k - 1))
            (Spec.zeta_at (zeta_i.val - 2 * k - 2))))[k]'_ = _
        rw [List.getElem_map, List.getElem_range]
        rw [chunk_at_lift_poly_fc re k hk]
        exact (h_done k hk).symm
      have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
      exact h_final.symm
    · -- Per-lane output bound from the loop invariant's strengthened conjunct.
      exact h_done_bnd
  · -- Step lemma application: dispatch invert_ntt_at_layer_2_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := invert_ntt_at_layer_2_step_lemma_fc zeta_i re h_bnd h_zeta_lo h_zeta_hi
                     acc k h_le hinv
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

/-! ### L3i.3 — Loop scaffolding for `invert_ntt_at_layer_3_portable_fc`.

    Mirror of §L3i.2 scaffolding simplified to **1 zeta per chunk** (instead of 2)
    with `zeta_i` DECREASING by 1 per iter and reads in reverse order at
    `zeta_i - k - 1`. -/

namespace Layer3FC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Local `usize_sub_ok_eq` helper (mirror of `Layer2FC.usize_sub_ok_eq`). -/
theorem usize_sub_ok_eq (x y : Std.Usize)
    (h_ge : y.val ≤ x.val) :
    ∃ z : Std.Usize, (x - y : Result Std.Usize) = .ok z ∧ z.val = x.val - y.val := by
  have hT := Std.Usize.sub_spec h_ge
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  exact ⟨z, h_eq, h_v.1⟩

/-- Step-local accumulator. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- FC loop invariant for `invert_ntt_at_layer_3_portable_fc`.
    Tracks DECREASING `zeta_i`: at outer iter `k`, `acc.1.val = zeta_i_0.val - k.val`.
    Chunks `< k.val` are FC-equal to the per-chunk inverse step; chunks `≥ k.val`
    are unchanged from `re`. Per-lane output bound `≤ 3328` on every chunk. -/
def inv
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val - k.val
    ∧ (∀ j : Nat, j < k.val →
        lift_chunk (acc.2.coefficients.val[j]!)
          = Spec.chunk_inv_ntt_layer_3_step_pure
              (lift_chunk (re.coefficients.val[j]!))
              (Spec.zeta_at (zeta_i_0.val - j - 1)))
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
    ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328))

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
/-- Per-iteration FC step lemma for the inverse layer-3 driver. Given a valid
    loop state `(acc, k)` with `k.val < 16`, decreases `zeta_i` by 1 and records
    the FC equation for chunk `k.val`, leaving chunks `> k.val` unchanged. -/
theorem invert_ntt_at_layer_3_step_lemma_fc
    (zeta_i_0 : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 13312)
    (h_zeta_lo : 16 ≤ zeta_i_0.val)
    (h_zeta_hi : zeta_i_0.val ≤ 128)
    (acc : Layer3FC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_inv : (Layer3FC.inv zeta_i_0 re k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer3FC.step_post zeta_i_0 re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- `Some round = k` branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_some_eq k h_lt
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    -- acc.1.val = zeta_i_0.val - k.val, with k.val ≤ 15 ⇒ acc.1.val ≥ zeta_i_0.val - 15 ≥ 1.
    have h_acc1_ge_1 : 1 ≤ acc.1.val := by
      rw [h_zeta_acc]
      have h_k_le_15 : k.val ≤ 15 := by omega
      omega
    -- (1) `zeta_i - 1` ⇒ `zi1` with `zi1.val = acc.1.val - 1`.
    have h_z_ge : (1#usize : Std.Usize).val ≤ acc.1.val := by rw [h_um]; omega
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer3FC.usize_sub_ok_eq acc.1 1#usize h_z_ge
    have h_zi1_val_arith : zi1.val = acc.1.val - 1 := by rw [h_zi1_val, h_um]
    -- zi1.val < 128: zi1.val = acc.1.val - 1 = zeta_i_0 - k - 1 ≤ zeta_i_0 - 1 ≤ 127.
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
    -- (3) `polynomial.zeta zi1` ⇒ `z1` at index `zi1.val = acc.1.val - 1`.
    obtain ⟨z1, h_z1_eq, h_z1_v, h_z1_bd, h_z1_lift⟩ :=
      triple_exists_ok_fc (polynomial.zeta_fc zi1 h_zi1_lt)
    -- (4) `inv_ntt_layer_3_step t z1`. Pre: t's lanes ≤ 13312 via h_pre + undone.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 13312 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    -- @[reducible] portable_ops_inst forwards to vector.portable.ntt.inv_ntt_layer_3_step.
    obtain ⟨t1, h_t1_eq, h_t1_lift, h_t1_bnd⟩ :=
      triple_exists_ok_fc (inv_ntt_layer_3_step_fc t z1 h_z1_bd h_t_bd)
    -- Compose entire body. Loop output for `cont` is `(iter', zi1, re')`.
    set acc' : Layer3FC.Acc := (zi1, { coefficients := acc.2.coefficients.set k t1 })
      with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
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
              libcrux_iot_ml_kem.vector.portable.ntt.inv_ntt_layer_3_step t z1
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
    show (Layer3FC.inv zeta_i_0 re s acc').holds
    have h_inv_pure :
        acc'.1.val = zeta_i_0.val - s.val
        ∧ (∀ j : Nat, j < s.val →
            lift_chunk (acc'.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - j - 1)))
        ∧ (∀ j : Nat, s.val ≤ j → j < 16 →
            acc'.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- acc'.1 = zi1, zi1.val = acc.1.val - 1 = zeta_i_0.val - (k.val + 1).
        show zi1.val = zeta_i_0.val - s.val
        rw [h_zi1_val_arith, h_zeta_acc, hs_val]
        have h_k_le_15 : k.val ≤ 15 := by omega
        omega
      · -- All j < s.val are FC-equal.
        intro j hj
        rw [hs_val] at hj
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
        · -- j = k.val: it's t1; use h_t1_lift + h_t_eq + zeta_lift identity.
          subst hj_eq_k
          have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val, h_t1_lift, h_t_eq]
          have h_k_le_15 : k.val ≤ 15 := by omega
          have h_zi1_z : zi1.val = zeta_i_0.val - k.val - 1 := by
            rw [h_zi1_val_arith, h_zeta_acc]
          rw [show lift_fe_mont z1 = Spec.zeta_at (zeta_i_0.val - k.val - 1)
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
      · -- Per-lane output bound on every chunk.
        intro c hc ℓ hℓ
        show ((acc'.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        show (((acc.2.coefficients.set k t1).val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        by_cases h_ck : c = k.val
        · have h_set_eq_val :
              (acc.2.coefficients.set k t1).val[c]! = t1 := by
            rw [h_ck]
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
                ⟨rfl, by rw [h_coef_len]; exact hk_16⟩
          rw [h_set_eq_val]; exact h_t1_bnd ℓ hℓ
        · have h_ne : k.val ≠ c := Ne.symm h_ck
          have h_set_ne_val :
              (acc.2.coefficients.set k t1).val[c]! = acc.2.coefficients.val[c]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
              Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k c t1 h_ne
          rw [h_set_ne_val]; exact h_acc_bnd c hc ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ 16, done.
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
          (vectortraitsOperationsInst := portable_ops_inst)
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
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
        acc.1.val = zeta_i_0.val - (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (acc.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i_0.val - j - 1)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            acc.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq, h16]
      · intro j hj; rw [h16] at hj
        apply h_acc_done j; rw [hk_eq]; exact hj
      · intro j hj_ge hj_lt
        rw [h16] at hj_ge
        apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge
      · exact h_acc_bnd
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
/-- L3i.3 — `invert_ntt_at_layer_3` driver: 16-chunk loop, per-chunk
    1-zeta-lookup decreasing `zeta_i` by 1. Mirror of `L3i.2` and forward
    `ntt_at_layer_3_portable_fc`. Locked POST exposes
    `p.1.val = zeta_i.val - 16` (output zeta_i for composer chaining) +
    `lift_poly p.2 = Spec.invert_ntt_layer_3_pure (lift_poly re) zeta_i`.

    Tightening preconditions (added by the proof author):
    - `h_zeta_lo : 16 ≤ zeta_i.val` — needed for the 1 subtraction per chunk
      to succeed without Nat underflow at every iter (worst case at iter k=15
      is `acc.1.val = zeta_i - 15`, and we further subtract 1).
    - `h_zeta_hi : zeta_i.val ≤ 128` — so `polynomial.zeta` index (worst case
      `zeta_i - 1` at iter k=0) is `< 128`.
    - `h_bnd` per-lane bound `≤ 13312` on `re`'s chunks — matches
      `inv_ntt_layer_3_step_fc`'s precondition.
    - `h_bnd_strict` per-lane bound `≤ 3328` on `re`'s chunks — needed for
      the strengthened POST's output-bound conjunct. -/
@[spec high]
theorem invert_ntt_at_layer_3_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312)
    (h_bnd_strict : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 3328)
    (h_zeta_lo : 16 ≤ zeta_i.val)
    (h_zeta_hi : zeta_i.val ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3
      (vectortraitsOperationsInst := portable_ops_inst) zeta_i re
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i.val - 16
              ∧ lift_poly p.2 = Spec.invert_ntt_layer_3_pure (lift_poly re) zeta_i
              ∧ (∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_3_loop.body
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
        refine ⟨?_, ?_, ?_, ?_⟩
        · -- zeta-thread invariant at k=0: zeta_i = zeta_i - 0.
          show zeta_i.val = zeta_i.val - (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val - 0
          omega
        · intro j hj
          exact absurd hj (Nat.not_lt_zero j)
        · intro _ _ _
          trivial
        · -- Initial bound: acc.2 = re at k=0, so bound from h_bnd_strict.
          intro c hc ℓ hℓ
          exact h_bnd_strict c hc ℓ hℓ)
      ?_)
  · -- Post entailment: at k=16, the invariant gives all 16 FC equations + zeta_i = zeta_i_0 - 16.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer3FC.inv zeta_i re 16#usize r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val - (16#usize : Std.Usize).val
        ∧ (∀ j : Nat, j < (16#usize : Std.Usize).val →
            lift_chunk (r.2.coefficients.val[j]!)
              = Spec.chunk_inv_ntt_layer_3_step_pure
                  (lift_chunk (re.coefficients.val[j]!))
                  (Spec.zeta_at (zeta_i.val - j - 1)))
        ∧ (∀ j : Nat, (16#usize : Std.Usize).val ≤ j → j < 16 →
            r.2.coefficients.val[j]! = re.coefficients.val[j]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((r.2.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer3FC.inv] using h_inv_holds
    obtain ⟨h_zeta_eq, h_done, _h_undone, h_done_bnd⟩ := h_inv
    have h16 : (16#usize : Std.Usize).val = 16 := rfl
    refine ⟨?_, ?_, ?_⟩
    · -- p.1.val = zeta_i.val - 16.
      rw [h_zeta_eq, h16]
    · -- The chunks equation.
      unfold Spec.invert_ntt_layer_3_pure
      set chunks_arr : Std.Array
          (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
        Std.Array.make 16#usize ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_3_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - k - 1))))
          (by simp) with hchunks_def
      have h_chunks_len : chunks_arr.val.length = 16 := by
        show ((List.range 16).map _).length = 16
        simp
      have h_chunks_get : ∀ k : Nat, (hk : k < 16) →
          chunks_arr.val[k]'(by rw [h_chunks_len]; exact hk)
            = lift_chunk (r.2.coefficients.val[k]!) := by
        intro k hk
        show ((List.range 16).map (fun k =>
          Spec.chunk_inv_ntt_layer_3_step_pure (Spec.chunk_at (lift_poly re) k)
            (Spec.zeta_at (zeta_i.val - k - 1))))[k]'_ = _
        rw [List.getElem_map, List.getElem_range]
        rw [chunk_at_lift_poly_fc re k hk]
        exact (h_done k hk).symm
      have h_final := flatten_chunks_eq_lift_poly_fc r.2 chunks_arr h_chunks_len h_chunks_get
      exact h_final.symm
    · -- Per-lane output bound from the loop invariant's strengthened conjunct.
      exact h_done_bnd
  · -- Step lemma application: dispatch invert_ntt_at_layer_3_step_lemma_fc.
    intro acc k _h_ge h_le hinv
    have h_step := invert_ntt_at_layer_3_step_lemma_fc zeta_i re h_bnd h_zeta_lo h_zeta_hi
                     acc k h_le hinv
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

/-! ### L3i.4 — `inv_ntt_layer_int_vec_step_reduce` helper FC.

    Cross-chunk INVERSE NTT (Gentleman-Sande) butterfly between coefficient
    chunks at positions `a` and `b` (where `b = a + step_vec`). Mirrors the
    impl `invert_ntt.inv_ntt_layer_int_vec_step_reduce`:

    ```
    scratch1 := coefs[a]; t := coefs[b]
    scratch3 := barrett(scratch1 + t)                    -- new coefs[a] = canonical(a + b)
    coefs1[a] := scratch3
    scratch4 := −scratch3
    scratch7 := mont(scratch4 + 2*t) zeta_r              -- new coefs[b] = (b − a) * z
    coefs2[b] := scratch7
    ```

    Used by the layer-4+ driver. The FC theorem exposes:
    1. lift_chunk equation on coefs[a] via `chunk_inv_pair_butterfly_a_pure`.
    2. lift_chunk equation on coefs[b] via `chunk_inv_pair_butterfly_b_pure`.
    3. Unchanged-chunk preservation for c ≠ a, c ≠ b.
    4. Output bound on both touched chunks (≤ 3328 since both go through
       barrett/mont reduction). -/
set_option maxHeartbeats 16000000 in
@[spec]
theorem inv_ntt_layer_int_vec_step_reduce_fc
    (coefficients : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector
                              16#usize)
    (a b : Std.Usize) (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_r : Std.I16)
    (h_a : a.val < 16) (h_b : b.val < 16) (h_ne : a.val ≠ b.val)
    (hzeta : zeta_r.val.natAbs ≤ 1664)
    (h_chunk_a : ∀ k : Nat, k < 16 →
       ((coefficients.val[a.val]!).elements.val[k]!).val.natAbs ≤ 3328)
    (h_chunk_b : ∀ k : Nat, k < 16 →
       ((coefficients.val[b.val]!).elements.val[k]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce
      portable_ops_inst coefficients a b scratch zeta_r
    ⦃ ⇓ p => ⌜ lift_chunk (p.1.val[a.val]!)
                = Spec.chunk_inv_pair_butterfly_a_pure
                    (lift_chunk (coefficients.val[a.val]!))
                    (lift_chunk (coefficients.val[b.val]!))
              ∧ lift_chunk (p.1.val[b.val]!)
                = Spec.chunk_inv_pair_butterfly_b_pure
                    (lift_chunk (coefficients.val[a.val]!))
                    (lift_chunk (coefficients.val[b.val]!))
                    (lift_fe_mont zeta_r)
              ∧ (∀ c : Nat, c < 16 → c ≠ a.val → c ≠ b.val →
                  p.1.val[c]! = coefficients.val[c]!)
              ∧ (∀ k : Nat, k < 16 →
                  ((p.1.val[a.val]!).elements.val[k]!).val.natAbs ≤ 3328)
              ∧ (∀ k : Nat, k < 16 →
                  ((p.1.val[b.val]!).elements.val[k]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  -- Setup: lengths.
  have h_coef_len : coefficients.length = 16 := Std.Array.length_eq _
  -- Bind shorthand for the two source chunks.
  set chunk_a : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[a.val]! with hca_def
  set chunk_b : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[b.val]! with hcb_def
  have h_chunk_a_len : chunk_a.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length chunk_a
  have h_chunk_b_len : chunk_b.elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length chunk_b
  unfold libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce
  -- (1) Read scratch1 = coefs[a].
  have h_idx_a : Aeneas.Std.Array.index_usize coefficients a = .ok chunk_a :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq coefficients a
      (by rw [h_coef_len]; exact h_a)
  -- (2) Read t = coefs[b].
  have h_idx_b : Aeneas.Std.Array.index_usize coefficients b = .ok chunk_b :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq coefficients b
      (by rw [h_coef_len]; exact h_b)
  -- (3) scratch2 = add(chunk_a, chunk_b). Pre: |a[ℓ] + b[ℓ]| ≤ 6656 < 32767 ✓.
  have h_add_pre1 : ∀ ℓ : Nat, ℓ < 16 →
      ((chunk_a.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hba := h_chunk_a ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((chunk_a.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((chunk_a.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨scratch2, h_s2_eq, _h_s2_lift⟩ :=
    triple_exists_ok_fc (add_fc chunk_a chunk_b h_add_pre1)
  have h_s2_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec chunk_a chunk_b h_add_pre1
  obtain ⟨scratch2', h_s2_eq', h_s2_per⟩ := triple_exists_ok_fc h_s2_legacy
  have h_s2_same : scratch2 = scratch2' := by
    have := h_s2_eq.symm.trans h_s2_eq'; cases this; rfl
  subst h_s2_same
  have h_s2_val : ∀ ℓ : Nat, ℓ < 16 →
      (scratch2.elements.val[ℓ]!).val
        = (chunk_a.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val := by
    intro ℓ hℓ; exact (h_s2_per ℓ hℓ).1
  have h_s2_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (scratch2.elements.val[ℓ]!).val.natAbs ≤ 6656 := by
    intro ℓ hℓ
    rw [h_s2_val ℓ hℓ]
    have hba := h_chunk_a ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((chunk_a.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((chunk_a.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- (4) scratch3 = barrett(scratch2). Pre: |scratch2[ℓ]| ≤ 32767 ✓.
  have h_barrett_pre : ∀ ℓ : Nat, ℓ < 16 →
      (scratch2.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro ℓ hℓ
    have := h_s2_bnd ℓ hℓ; omega
  obtain ⟨scratch3, h_s3_eq, h_s3_bnd_t, _h_s3_lift⟩ :=
    triple_exists_ok_fc (barrett_reduce_fc scratch2 h_barrett_pre)
  -- `barrett_reduce_fc` now gives the centered `≤ 1664`; this inverse-NTT step
  -- only needs the looser `≤ 3328`, so weaken.
  have h_s3_bnd : ∀ i : Nat, i < 16 → (scratch3.elements.val[i]!).val.natAbs ≤ 3328 :=
    fun i hi => Nat.le_trans (h_s3_bnd_t i hi) (by decide)
  have h_s3_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.barrett_reduce_spec scratch2 h_barrett_pre
  obtain ⟨scratch3', h_s3_eq', h_s3_per⟩ := triple_exists_ok_fc h_s3_legacy
  have h_s3_same : scratch3 = scratch3' := by
    have := h_s3_eq.symm.trans h_s3_eq'; cases this; rfl
  subst h_s3_same
  have h_s3_modq : ∀ ℓ : Nat, ℓ < 16 →
      libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch3.elements.val[ℓ]!).val
                                       (scratch2.elements.val[ℓ]!).val 3329 :=
    fun ℓ hℓ => (h_s3_per ℓ hℓ).1
  -- (5) coefficients1 = coefficients.set a scratch3.
  set c1 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    coefficients.set a scratch3 with hc1_def
  have h_upd_a : Aeneas.Std.Array.update coefficients a scratch3 = .ok c1 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq coefficients a scratch3
      (by rw [h_coef_len]; exact h_a)
  have h_c1_len : c1.length = 16 := by simp [hc1_def, h_coef_len]
  -- (6) scratch4 = negate(scratch3). Pre: |scratch3[ℓ]| ≤ 3328 ≤ 2^15-1 ✓.
  have h_neg_pre : ∀ ℓ : Nat, ℓ < 16 →
      (scratch3.elements.val[ℓ]!).val.natAbs ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hb := h_s3_bnd ℓ hℓ
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨scratch4, h_s4_eq, _h_s4_lift⟩ :=
    triple_exists_ok_fc (negate_fc scratch3 h_neg_pre)
  have h_s4_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.negate_spec scratch3
  obtain ⟨scratch4', h_s4_eq', h_s4_per⟩ := triple_exists_ok_fc h_s4_legacy
  have h_s4_same : scratch4 = scratch4' := by
    have := h_s4_eq.symm.trans h_s4_eq'; cases this; rfl
  subst h_s4_same
  -- Convert per-lane BV equality to value equality via the same dance as `negate_fc`.
  have h_s4_val : ∀ ℓ : Nat, ℓ < 16 →
      (scratch4.elements.val[ℓ]!).val = -(scratch3.elements.val[ℓ]!).val := by
    intro ℓ hℓ
    set xi : Std.I16 := scratch3.elements.val[ℓ]! with hxi
    set ri : Std.I16 := scratch4.elements.val[ℓ]! with hri
    have h_bv : ri.bv = -xi.bv := h_s4_per ℓ hℓ
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
    · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := h_neg_pre ℓ hℓ
      have h_pow : -((2 : Int) ^ (16 - 1)) = -(2^15 : Int) := by decide
      rw [h_pow]; omega
    · have h_abs : xi.val.natAbs ≤ 2^15 - 1 := h_neg_pre ℓ hℓ
      have h_pow : ((2 : Int) ^ (16 - 1)) = (2^15 : Int) := by decide
      rw [h_pow]; omega
  have h_s4_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (scratch4.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
    intro ℓ hℓ
    rw [h_s4_val ℓ hℓ, Int.natAbs_neg]; exact h_s3_bnd ℓ hℓ
  -- (7) t1 = c1[b] (= chunk_b since a ≠ b).
  have h_c1_b : c1.val[b.val]! = chunk_b := by
    show (coefficients.set a scratch3).val[b.val]! = chunk_b
    have h_ne_ab : a.val ≠ b.val := h_ne
    have h_step : (coefficients.set a scratch3).val[b.val]! = coefficients.val[b.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne coefficients a b.val scratch3 h_ne_ab
    rw [h_step]
  have h_idx_b1 : Aeneas.Std.Array.index_usize c1 b = .ok chunk_b := by
    have h_idx : Aeneas.Std.Array.index_usize c1 b = .ok (c1.val[b.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq c1 b (by rw [h_c1_len]; exact h_b)
    rw [h_idx, h_c1_b]
  -- (8) scratch5 = add(scratch4, chunk_b). |scratch4| ≤ 3328, |chunk_b| ≤ 3328, sum ≤ 6656 ✓.
  have h_add_pre2 : ∀ ℓ : Nat, ℓ < 16 →
      ((scratch4.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hb4 := h_s4_bnd ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((scratch4.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((scratch4.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨scratch5, h_s5_eq, _h_s5_lift⟩ :=
    triple_exists_ok_fc (add_fc scratch4 chunk_b h_add_pre2)
  have h_s5_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec scratch4 chunk_b h_add_pre2
  obtain ⟨scratch5', h_s5_eq', h_s5_per⟩ := triple_exists_ok_fc h_s5_legacy
  have h_s5_same : scratch5 = scratch5' := by
    have := h_s5_eq.symm.trans h_s5_eq'; cases this; rfl
  subst h_s5_same
  have h_s5_val : ∀ ℓ : Nat, ℓ < 16 →
      (scratch5.elements.val[ℓ]!).val
        = (scratch4.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val := by
    intro ℓ hℓ; exact (h_s5_per ℓ hℓ).1
  have h_s5_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (scratch5.elements.val[ℓ]!).val.natAbs ≤ 6656 := by
    intro ℓ hℓ
    rw [h_s5_val ℓ hℓ]
    have hb4 := h_s4_bnd ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((scratch4.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((scratch4.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- (9) scratch6 = add(scratch5, chunk_b). |scratch5| ≤ 6656, |chunk_b| ≤ 3328, sum ≤ 9984 ✓.
  have h_add_pre3 : ∀ ℓ : Nat, ℓ < 16 →
      ((scratch5.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ 2^15 - 1 := by
    intro ℓ hℓ
    have hb5 := h_s5_bnd ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((scratch5.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((scratch5.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    have h_p2 : (2 : Nat)^15 - 1 = 32767 := by decide
    rw [h_p2]; omega
  obtain ⟨scratch6, h_s6_eq, _h_s6_lift⟩ :=
    triple_exists_ok_fc (add_fc scratch5 chunk_b h_add_pre3)
  have h_s6_legacy := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.add_spec scratch5 chunk_b h_add_pre3
  obtain ⟨scratch6', h_s6_eq', h_s6_per⟩ := triple_exists_ok_fc h_s6_legacy
  have h_s6_same : scratch6 = scratch6' := by
    have := h_s6_eq.symm.trans h_s6_eq'; cases this; rfl
  subst h_s6_same
  have h_s6_val : ∀ ℓ : Nat, ℓ < 16 →
      (scratch6.elements.val[ℓ]!).val
        = (scratch5.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val := by
    intro ℓ hℓ; exact (h_s6_per ℓ hℓ).1
  have h_s6_bnd : ∀ ℓ : Nat, ℓ < 16 →
      (scratch6.elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro ℓ hℓ
    rw [h_s6_val ℓ hℓ]
    have hb5 := h_s5_bnd ℓ hℓ
    have hbb := h_chunk_b ℓ hℓ
    have h_tri : ((scratch5.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val : Int).natAbs
        ≤ ((scratch5.elements.val[ℓ]!).val : Int).natAbs
          + ((chunk_b.elements.val[ℓ]!).val : Int).natAbs :=
      Int.natAbs_add_le _ _
    omega
  -- (10) classify zeta_r = zeta_r (Public->Secret blanket identity on I16).
  have h_classify_zeta :
      libcrux_secrets.traits.Classify.Blanket.classify zeta_r = .ok zeta_r :=
    ntt_step_fc.classify_ok_eq zeta_r
  -- (11) scratch7 = mont_mult_by_const(scratch6, zeta_r). Pre: |scratch6| ≤ 32767, |zeta_r| ≤ 1664.
  obtain ⟨scratch7, h_s7_eq, _h_s7_lift⟩ :=
    triple_exists_ok_fc (montgomery_multiply_by_constant_fc scratch6 zeta_r h_s6_bnd hzeta)
  have h_s7_legacy :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element.montgomery_multiply_by_constant_spec scratch6 zeta_r hzeta
  obtain ⟨scratch7', h_s7_eq', h_s7_per⟩ := triple_exists_ok_fc h_s7_legacy
  have h_s7_same : scratch7 = scratch7' := by
    have := h_s7_eq.symm.trans h_s7_eq'; cases this; rfl
  subst h_s7_same
  have h_s7_modq : ∀ ℓ : Nat, ℓ < 16 →
      ((scratch7.elements.val[ℓ]!).val * (2 ^ 16 : Int)) % 3329
        = ((scratch6.elements.val[ℓ]!).val * zeta_r.val) % 3329 :=
    fun ℓ hℓ => (h_s7_per ℓ hℓ).2
  -- (12) coefficients2 = c1.set b scratch7.
  set c2 : Std.Array libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    c1.set b scratch7 with hc2_def
  have h_upd_b : Aeneas.Std.Array.update c1 b scratch7 = .ok c2 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_update_ok_eq c1 b scratch7
      (by rw [h_c1_len]; exact h_b)
  -- Compose the body equation.
  have h_body :
      libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce
        portable_ops_inst coefficients a b scratch zeta_r
        = .ok (c2, scratch7) := by
    show (do
            let scratch1' ← Aeneas.Std.Array.index_usize coefficients a
            let t' ← Aeneas.Std.Array.index_usize coefficients b
            let scratch2' ← portable_ops_inst.add scratch1' t'
            let scratch3' ← portable_ops_inst.barrett_reduce scratch2'
            let coefficients1' ← Aeneas.Std.Array.update coefficients a scratch3'
            let scratch4' ← portable_ops_inst.negate scratch3'
            let t1' ← Aeneas.Std.Array.index_usize coefficients1' b
            let scratch5' ← portable_ops_inst.add scratch4' t1'
            let scratch6' ← portable_ops_inst.add scratch5' t1'
            let scratch7' ←
              libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe
                portable_ops_inst scratch6' zeta_r
            let coefficients2' ← Aeneas.Std.Array.update coefficients1' b scratch7'
            .ok (coefficients2', scratch7')) = _
    -- Trait method calls reduce to vector.portable.arithmetic.* via reducibility.
    show (do
            let scratch1' ← Aeneas.Std.Array.index_usize coefficients a
            let t' ← Aeneas.Std.Array.index_usize coefficients b
            let scratch2' ← libcrux_iot_ml_kem.vector.portable.arithmetic.add scratch1' t'
            let scratch3' ←
              libcrux_iot_ml_kem.vector.portable.arithmetic.barrett_reduce scratch2'
            let coefficients1' ← Aeneas.Std.Array.update coefficients a scratch3'
            let scratch4' ← libcrux_iot_ml_kem.vector.portable.arithmetic.negate scratch3'
            let t1' ← Aeneas.Std.Array.index_usize coefficients1' b
            let scratch5' ← libcrux_iot_ml_kem.vector.portable.arithmetic.add scratch4' t1'
            let scratch6' ← libcrux_iot_ml_kem.vector.portable.arithmetic.add scratch5' t1'
            let scratch7' ← do
              let i ← libcrux_secrets.traits.Classify.Blanket.classify zeta_r
              libcrux_iot_ml_kem.vector.portable.arithmetic.montgomery_multiply_by_constant
                scratch6' i
            let coefficients2' ← Aeneas.Std.Array.update coefficients1' b scratch7'
            .ok (coefficients2', scratch7')) = _
    rw [h_idx_a]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_b]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s2_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s3_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_a]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s4_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_b1]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s5_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s6_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_classify_zeta]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_s7_eq]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_upd_b]
    simp only [Aeneas.Std.bind_tc_ok]
  apply triple_of_ok_fc h_body
  -- Now prove the 5-conjunct post.
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (a) lift_chunk c2[a] = chunk_inv_pair_butterfly_a_pure (lift_chunk chunk_a) (lift_chunk chunk_b).
    -- c2 = c1.set b scratch7; at index a, since a ≠ b, c2[a] = c1[a] = scratch3.
    show lift_chunk (c2.val[a.val]!) = _
    have h_ne_ba : b.val ≠ a.val := fun h => h_ne h.symm
    have h_c2_a : c2.val[a.val]! = scratch3 := by
      show (c1.set b scratch7).val[a.val]! = scratch3
      have h_step1 : (c1.set b scratch7).val[a.val]! = c1.val[a.val]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne c1 b a.val scratch7 h_ne_ba
      have h_step2 : c1.val[a.val]! = scratch3 := by
        show (coefficients.set a scratch3).val[a.val]! = scratch3
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_eq coefficients a a.val scratch3
            ⟨rfl, by rw [h_coef_len]; exact h_a⟩
      rw [h_step1, h_step2]
    rw [h_c2_a]
    -- Goal: lift_chunk scratch3 = chunk_inv_pair_butterfly_a_pure (lift_chunk chunk_a) (lift_chunk chunk_b).
    -- Per-lane: lift_fe scratch3[ℓ] = add_pure (lift_fe chunk_a[ℓ]) (lift_fe chunk_b[ℓ]).
    -- We have h_s3_modq : modq_eq scratch3[ℓ].val scratch2[ℓ].val 3329, and
    -- h_s2_val : scratch2[ℓ].val = chunk_a[ℓ].val + chunk_b[ℓ].val.
    have h_s3_lane_modq : ∀ ℓ : Nat, ℓ < 16 →
        libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch3.elements.val[ℓ]!).val
          ((chunk_a.elements.val[ℓ]!).val + (chunk_b.elements.val[ℓ]!).val) 3329 := by
      intro ℓ hℓ
      have h_m := h_s3_modq ℓ hℓ
      have h_v := h_s2_val ℓ hℓ
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_m ⊢
      rw [← h_v]; exact h_m
    -- Now unfold and prove lane-by-lane.
    unfold lift_chunk Spec.chunk_inv_pair_butterfly_a_pure
    apply Subtype.ext
    have h_s3_len : scratch3.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch3
    show scratch3.elements.val.map lift_fe
        = (List.range 16).map (fun ℓ =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Std.Array.make 16#usize (chunk_a.elements.val.map lift_fe)
                (by simp)).val[ℓ]!)
              ((Std.Array.make 16#usize (chunk_b.elements.val.map lift_fe)
                (by simp)).val[ℓ]!))
    apply List.ext_getElem
    · simp [List.length_map, List.length_range, h_s3_len]
    · intro ℓ hℓ1 _
      have hℓ : ℓ < 16 := by
        have : ℓ < (scratch3.elements.val.map lift_fe).length := hℓ1
        simp [List.length_map, h_s3_len] at this; exact this
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      -- LHS: lift_fe scratch3.elements.val[ℓ]
      -- RHS: add_pure (chunk_a.lift)[ℓ]! (chunk_b.lift)[ℓ]!
      have h_s3_get : scratch3.elements.val[ℓ] = scratch3.elements.val[ℓ]! := by
        have hi : ℓ < scratch3.elements.val.length := by rw [h_s3_len]; exact hℓ
        rw [getElem!_pos scratch3.elements.val ℓ hi]
      rw [h_s3_get]
      have h_lift_a_idx :
          (Std.Array.make 16#usize (chunk_a.elements.val.map lift_fe)
              (by simp)).val[ℓ]! = lift_fe (chunk_a.elements.val[ℓ]!) := by
        show (chunk_a.elements.val.map lift_fe)[ℓ]! = _
        have hL : (chunk_a.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_chunk_a_len]
        rw [getElem!_pos _ ℓ (by rw [hL]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos chunk_a.elements.val ℓ (by rw [h_chunk_a_len]; exact hℓ)]
      have h_lift_b_idx :
          (Std.Array.make 16#usize (chunk_b.elements.val.map lift_fe)
              (by simp)).val[ℓ]! = lift_fe (chunk_b.elements.val[ℓ]!) := by
        show (chunk_b.elements.val.map lift_fe)[ℓ]! = _
        have hL : (chunk_b.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_chunk_b_len]
        rw [getElem!_pos _ ℓ (by rw [hL]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos chunk_b.elements.val ℓ (by rw [h_chunk_b_len]; exact hℓ)]
      rw [h_lift_a_idx, h_lift_b_idx]
      -- Goal: lift_fe scratch3.elements.val[ℓ]!
      --     = add_pure (lift_fe chunk_a.elements.val[ℓ]!) (lift_fe chunk_b.elements.val[ℓ]!).
      -- We have h_s3_lane_modq ℓ hℓ : modq_eq scratch3[ℓ].val (a[ℓ].val + b[ℓ].val) 3329.
      -- Manufacture a synthetic i16 r_a := wrapping_add chunk_a[ℓ] chunk_b[ℓ];
      -- since |a| + |b| ≤ 6656 ≤ 29439 + 3328, r_a.val = a.val + b.val (no overflow).
      -- Then lift_fe scratch3[ℓ] = lift_fe r_a (via modq), and
      -- lift_fe r_a = add_pure (lift_fe a[ℓ]) (lift_fe b[ℓ]) via lift_fe_add_pure_eq.
      set xa : Std.I16 := chunk_a.elements.val[ℓ]! with hxa_def
      set xb : Std.I16 := chunk_b.elements.val[ℓ]! with hxb_def
      set ra : Std.I16 := Std.I16.wrapping_add xa xb with hra_def
      have h_xa_bnd : xa.val.natAbs ≤ 3328 := h_chunk_a ℓ hℓ
      have h_xb_bnd : xb.val.natAbs ≤ 3328 := h_chunk_b ℓ hℓ
      have h_ra_val : ra.val = xa.val + xb.val :=
        ntt_step_fc.add_no_overflow_value xa xb 3328 h_xa_bnd h_xb_bnd (by decide)
      have h_lift_ra : lift_fe ra
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (lift_fe xa) (lift_fe xb) :=
        lift_fe_add_pure_eq xa xb ra h_ra_val
      -- From h_s3_lane_modq combined with h_ra_val: modq_eq scratch3.val ra.val 3329.
      have h_s3_ra_modq :
          libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch3.elements.val[ℓ]!).val ra.val 3329 := by
        have h_m := h_s3_lane_modq ℓ hℓ
        unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_m ⊢
        rw [h_ra_val]; exact h_m
      have h_lift_eq : lift_fe (scratch3.elements.val[ℓ]!) = lift_fe ra :=
        lift_fe_eq_of_modq _ _ h_s3_ra_modq
      rw [h_lift_eq, h_lift_ra]
  · -- (b) lift_chunk c2[b] = chunk_inv_pair_butterfly_b_pure (lift_chunk chunk_a) (lift_chunk chunk_b) (lift_fe_mont zeta_r).
    -- c2[b] = (c1.set b scratch7)[b] = scratch7.
    show lift_chunk (c2.val[b.val]!) = _
    have h_c2_b : c2.val[b.val]! = scratch7 := by
      show (c1.set b scratch7).val[b.val]! = scratch7
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq c1 b b.val scratch7
          ⟨rfl, by rw [h_c1_len]; exact h_b⟩
    rw [h_c2_b]
    -- Goal: lift_chunk scratch7 = chunk_inv_pair_butterfly_b_pure ...
    -- Per-lane: lift_fe_mont scratch7[ℓ]?  NO -- chunk_inv_pair_butterfly_b_pure produces
    -- `mul_pure (sub_pure b[ℓ] a[ℓ]) z` which is a PLAIN-domain FE, not a Mont FE.
    -- So we need `lift_fe scratch7[ℓ] = mul_pure (sub_pure (lift_fe b) (lift_fe a)) (lift_fe_mont z)`.
    -- The modq fact: scratch7[ℓ].val * 2^16 ≡ scratch6[ℓ].val * zeta_r.val (mod q).
    -- We need to chain: scratch6[ℓ].val = (b[ℓ].val - a[ℓ].val) (mod q) [from the s3,s4,s5,s6 chain].
    -- Step (i): derive scratch6[ℓ].val ≡ b[ℓ].val - a[ℓ].val (mod q).
    have h_s6_lane_modq : ∀ ℓ : Nat, ℓ < 16 →
        libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch6.elements.val[ℓ]!).val
          ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val) 3329 := by
      intro ℓ hℓ
      -- scratch6[ℓ].val = scratch5[ℓ].val + chunk_b[ℓ].val
      --                = (scratch4[ℓ].val + chunk_b[ℓ].val) + chunk_b[ℓ].val
      --                = (-scratch3[ℓ].val + chunk_b[ℓ].val) + chunk_b[ℓ].val
      --                = -scratch3[ℓ].val + 2*chunk_b[ℓ].val
      -- scratch3[ℓ].val ≡ chunk_a[ℓ].val + chunk_b[ℓ].val (mod q)
      -- so scratch6[ℓ].val ≡ -(a + b) + 2b = b - a (mod q).
      have h_v6 := h_s6_val ℓ hℓ
      have h_v5 := h_s5_val ℓ hℓ
      have h_v4 := h_s4_val ℓ hℓ
      have h_v3 := h_s3_modq ℓ hℓ
      have h_v2 := h_s2_val ℓ hℓ
      -- Combine:
      have h_chain : (scratch6.elements.val[ℓ]!).val
          = -(scratch3.elements.val[ℓ]!).val + 2 * (chunk_b.elements.val[ℓ]!).val := by
        rw [h_v6, h_v5, h_v4]; ring
      -- Now modq: -scratch3 ≡ -(a+b), 2b - (a+b) = b - a (mod q).
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_v3 ⊢
      -- h_v3 : (scratch3.val - scratch2.val) % 3329 = 0.
      -- Goal: (scratch6.val - (b.val - a.val)) % 3329 = 0.
      -- scratch6.val - (b.val - a.val) = -scratch3.val + 2b - b + a
      --                                = -scratch3.val + a + b
      --                                = -(scratch3.val - (a + b))
      --                                = -(scratch3.val - scratch2.val)  [using h_v2]
      have h_eq : (scratch6.elements.val[ℓ]!).val
            - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
          = -((scratch3.elements.val[ℓ]!).val - (scratch2.elements.val[ℓ]!).val) := by
        rw [h_chain, h_v2]; ring
      rw [h_eq, Int.neg_emod]
      omega
    -- Step (ii): derive scratch7[ℓ].val ≡ scratch6[ℓ].val * zeta_r.val * 169 (mod q),
    -- using 2^16 * 169 ≡ 1 (mod q).
    have h_s7_lane_modq_pre : ∀ ℓ : Nat, ℓ < 16 →
        libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch7.elements.val[ℓ]!).val
          ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) 3329 := by
      intro ℓ hℓ
      have h_per := h_s7_modq ℓ hℓ
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq
      have h_169 : ((2^16 : Int) * 169) % 3329 = 1 := by decide
      have h_rmul : ((scratch7.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
          = ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 := by
        have h1 : ((scratch7.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
            = ((scratch7.elements.val[ℓ]!).val * (2^16 : Int)) % 3329 * 169 % 3329 := by
          rw [Int.mul_emod]; simp
        have h2 : ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
            = ((scratch6.elements.val[ℓ]!).val * zeta_r.val) % 3329 * 169 % 3329 := by
          rw [Int.mul_emod]; simp
        rw [h1, h2, h_per]
      have h_lhs : ((scratch7.elements.val[ℓ]!).val * (2^16 : Int) * 169) % 3329
          = (scratch7.elements.val[ℓ]!).val % 3329 := by
        have h_mul_assoc : (scratch7.elements.val[ℓ]!).val * (2^16 : Int) * 169
            = (scratch7.elements.val[ℓ]!).val * ((2^16 : Int) * 169) := by ring
        rw [h_mul_assoc, Int.mul_emod, h_169]; simp
      have h_zsub :
          ((scratch7.elements.val[ℓ]!).val
            - (scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 = 0 := by
        have h_sub_emod : ((scratch7.elements.val[ℓ]!).val
              - (scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
            = ((scratch7.elements.val[ℓ]!).val % 3329
                - ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329) % 3329 := by
          rw [Int.sub_emod]
        rw [h_sub_emod, ← h_lhs, h_rmul]; simp
      exact h_zsub
    -- Step (iii): combine: scratch7[ℓ].val ≡ (b - a) * zeta_r * 169 (mod q),
    -- which is what `lift_fe_mul_pure_mont_eq` needs (the first arg is `chunk_b - chunk_a`,
    -- in the role of the "a" of mul_pure_mont).
    -- But the existing `lift_fe_mul_pure_mont_eq` takes a single `a : Std.I16` whose .val
    -- is multiplied with `c`. We don't have a single i16 carrying `b - a`. We need an
    -- intermediate bridge.  Construct the desired equation manually.
    -- The b-side bridge: from modq_eq scratch7.val ((b - a) * zeta_r * 169) 3329,
    -- show lift_fe scratch7[ℓ] = mul_pure (sub_pure (lift_fe b[ℓ]) (lift_fe a[ℓ])) (lift_fe_mont zeta_r).
    have h_s7_lane_modq : ∀ ℓ : Nat, ℓ < 16 →
        libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch7.elements.val[ℓ]!).val
          (((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
            * zeta_r.val * 169) 3329 := by
      intro ℓ hℓ
      have hpre := h_s7_lane_modq_pre ℓ hℓ
      have h6 := h_s6_lane_modq ℓ hℓ
      -- Compose: scratch7 ≡ scratch6 * z * 169 ≡ (b-a) * z * 169 (mod q).
      unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at hpre h6 ⊢
      -- h6 : (scratch6 - (b - a)) % 3329 = 0.
      -- We want: (scratch7 - (b - a) * z * 169) % 3329 = 0.
      -- We have hpre : (scratch7 - scratch6 * z * 169) % 3329 = 0.
      -- And scratch6 % 3329 = (b - a) % 3329 (from h6).
      -- So scratch6 * z * 169 ≡ (b - a) * z * 169 (mod q).
      have h_scratch6_zmod :
          (scratch6.elements.val[ℓ]!).val % 3329
            = ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val) % 3329 := by
        have h_dvd : (3329 : Int) ∣ ((scratch6.elements.val[ℓ]!).val
            - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)) :=
          Int.dvd_of_emod_eq_zero h6
        have h_sub : (scratch6.elements.val[ℓ]!).val
            - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
            = (scratch6.elements.val[ℓ]!).val
                - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val) := rfl
        omega
      have h_mul_zmod :
          ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
            = (((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                  * zeta_r.val * 169) % 3329 := by
        have h1 : ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
            = ((scratch6.elements.val[ℓ]!).val % 3329) * (zeta_r.val * 169 % 3329) % 3329 := by
          conv_lhs => rw [show (scratch6.elements.val[ℓ]!).val * zeta_r.val * 169
                               = (scratch6.elements.val[ℓ]!).val * (zeta_r.val * 169) from by ring]
          rw [Int.mul_emod]
        have h2 : (((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                    * zeta_r.val * 169) % 3329
            = (((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val) % 3329)
                * (zeta_r.val * 169 % 3329) % 3329 := by
          conv_lhs => rw [show ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                                  * zeta_r.val * 169
                              = ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                                  * (zeta_r.val * 169) from by ring]
          rw [Int.mul_emod]
        rw [h1, h2, h_scratch6_zmod]
      -- Now combine: scratch7 - (b - a)*z*169 ≡ scratch7 - scratch6*z*169 (mod q).
      have h_link :
          ((scratch7.elements.val[ℓ]!).val
            - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                * zeta_r.val * 169) % 3329
            = ((scratch7.elements.val[ℓ]!).val
                - (scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329 := by
        have h_sub1 : ((scratch7.elements.val[ℓ]!).val
              - ((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                  * zeta_r.val * 169) % 3329
            = ((scratch7.elements.val[ℓ]!).val % 3329
                - (((chunk_b.elements.val[ℓ]!).val - (chunk_a.elements.val[ℓ]!).val)
                    * zeta_r.val * 169) % 3329) % 3329 := by rw [Int.sub_emod]
        have h_sub2 : ((scratch7.elements.val[ℓ]!).val
              - (scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329
            = ((scratch7.elements.val[ℓ]!).val % 3329
                - ((scratch6.elements.val[ℓ]!).val * zeta_r.val * 169) % 3329) % 3329 := by
          rw [Int.sub_emod]
        rw [h_sub1, h_sub2, h_mul_zmod]
      rw [h_link]; exact hpre
    -- Now reduce the chunk goal to per-lane.
    unfold lift_chunk Spec.chunk_inv_pair_butterfly_b_pure
    apply Subtype.ext
    have h_s7_len : scratch7.elements.val.length = 16 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length scratch7
    show scratch7.elements.val.map lift_fe
        = (List.range 16).map (fun ℓ =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                ((Std.Array.make 16#usize (chunk_b.elements.val.map lift_fe)
                  (by simp)).val[ℓ]!)
                ((Std.Array.make 16#usize (chunk_a.elements.val.map lift_fe)
                  (by simp)).val[ℓ]!))
              (lift_fe_mont zeta_r))
    apply List.ext_getElem
    · simp [List.length_map, List.length_range, h_s7_len]
    · intro ℓ hℓ1 _
      have hℓ : ℓ < 16 := by
        have : ℓ < (scratch7.elements.val.map lift_fe).length := hℓ1
        simp [List.length_map, h_s7_len] at this; exact this
      rw [List.getElem_map, List.getElem_map, List.getElem_range]
      have h_s7_get : scratch7.elements.val[ℓ] = scratch7.elements.val[ℓ]! := by
        have hi : ℓ < scratch7.elements.val.length := by rw [h_s7_len]; exact hℓ
        rw [getElem!_pos scratch7.elements.val ℓ hi]
      rw [h_s7_get]
      have h_lift_a_idx :
          (Std.Array.make 16#usize (chunk_a.elements.val.map lift_fe)
              (by simp)).val[ℓ]! = lift_fe (chunk_a.elements.val[ℓ]!) := by
        show (chunk_a.elements.val.map lift_fe)[ℓ]! = _
        have hL : (chunk_a.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_chunk_a_len]
        rw [getElem!_pos _ ℓ (by rw [hL]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos chunk_a.elements.val ℓ (by rw [h_chunk_a_len]; exact hℓ)]
      have h_lift_b_idx :
          (Std.Array.make 16#usize (chunk_b.elements.val.map lift_fe)
              (by simp)).val[ℓ]! = lift_fe (chunk_b.elements.val[ℓ]!) := by
        show (chunk_b.elements.val.map lift_fe)[ℓ]! = _
        have hL : (chunk_b.elements.val.map lift_fe).length = 16 := by
          simp [List.length_map, h_chunk_b_len]
        rw [getElem!_pos _ ℓ (by rw [hL]; exact hℓ)]
        rw [List.getElem_map]
        rw [getElem!_pos chunk_b.elements.val ℓ (by rw [h_chunk_b_len]; exact hℓ)]
      rw [h_lift_a_idx, h_lift_b_idx]
      -- Goal: lift_fe scratch7[ℓ]!
      --     = mul_pure (sub_pure (lift_fe b[ℓ]) (lift_fe a[ℓ])) (lift_fe_mont zeta_r).
      -- Manufacture rb := wrapping_sub chunk_b[ℓ] chunk_a[ℓ]; since |b| + |a| ≤ 6656,
      -- rb.val = b.val - a.val (no overflow). Then:
      --   lift_fe rb = sub_pure (lift_fe b) (lift_fe a)  via lift_fe_sub_pure_eq.
      -- The shape of `lift_fe_mul_pure_mont_eq` matches once we substitute rb for the LHS
      -- of the multiplication.
      set xa : Std.I16 := chunk_a.elements.val[ℓ]! with hxa_def
      set xb : Std.I16 := chunk_b.elements.val[ℓ]! with hxb_def
      set rb : Std.I16 := Std.I16.wrapping_sub xb xa with hrb_def
      have h_xa_bnd : xa.val.natAbs ≤ 3328 := h_chunk_a ℓ hℓ
      have h_xb_bnd : xb.val.natAbs ≤ 3328 := h_chunk_b ℓ hℓ
      have h_rb_val : rb.val = xb.val - xa.val :=
        ntt_step_fc.sub_no_overflow_value xb xa 3328 h_xb_bnd h_xa_bnd (by decide)
      -- lift_fe rb = sub_pure (lift_fe xb) (lift_fe xa).
      have h_lift_rb : lift_fe rb
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (lift_fe xb) (lift_fe xa) :=
        lift_fe_sub_pure_eq xb xa rb h_rb_val
      -- Build the modq fact in terms of rb: scratch7.val ≡ rb.val * zeta_r.val * 169 (mod q).
      have h_s7_rb_modq :
          libcrux_iot_ml_kem.Spec.ModularArith.modq_eq (scratch7.elements.val[ℓ]!).val
                                           (rb.val * zeta_r.val * 169) 3329 := by
        have h_m := h_s7_lane_modq ℓ hℓ
        unfold libcrux_iot_ml_kem.Spec.ModularArith.modq_eq at h_m ⊢
        rw [h_rb_val]; exact h_m
      -- Apply the existing bridge `lift_fe_mul_pure_mont_eq` with first arg rb.
      have h_lift_s7 : lift_fe (scratch7.elements.val[ℓ]!)
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (lift_fe rb) (lift_fe_mont zeta_r) :=
        lift_fe_mul_pure_mont_eq rb zeta_r (scratch7.elements.val[ℓ]!) h_s7_rb_modq
      rw [h_lift_s7, h_lift_rb]
  · -- (c) Preservation: for c ≠ a, c ≠ b: c2.val[c]! = coefficients.val[c]!.
    intro c hc hca hcb
    show c2.val[c]! = coefficients.val[c]!
    have h_step1 : c2.val[c]! = c1.val[c]! := by
      show (c1.set b scratch7).val[c]! = c1.val[c]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne c1 b c scratch7 (fun h => hcb h.symm)
    have h_step2 : c1.val[c]! = coefficients.val[c]! := by
      show (coefficients.set a scratch3).val[c]! = coefficients.val[c]!
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne coefficients a c scratch3 (fun h => hca h.symm)
    rw [h_step1, h_step2]
  · -- (d) Chunk a bound: c2[a] = scratch3 (Barrett-reduced) → ≤ 3328.
    intro k hk
    show ((c2.val[a.val]!).elements.val[k]!).val.natAbs ≤ 3328
    have h_ne_ba : b.val ≠ a.val := fun h => h_ne h.symm
    have h_c2_a : c2.val[a.val]! = scratch3 := by
      show (c1.set b scratch7).val[a.val]! = scratch3
      have h_step1 : (c1.set b scratch7).val[a.val]! = c1.val[a.val]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne c1 b a.val scratch7 h_ne_ba
      have h_step2 : c1.val[a.val]! = scratch3 := by
        show (coefficients.set a scratch3).val[a.val]! = scratch3
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_eq coefficients a a.val scratch3
            ⟨rfl, by rw [h_coef_len]; exact h_a⟩
      rw [h_step1, h_step2]
    rw [h_c2_a]; exact h_s3_bnd k hk
  · -- (e) Chunk b bound: c2[b] = scratch7 (Mont-multiplied by zeta ≤ 1664) → ≤ 3328.
    intro k hk
    show ((c2.val[b.val]!).elements.val[k]!).val.natAbs ≤ 3328
    have h_c2_b : c2.val[b.val]! = scratch7 := by
      show (c1.set b scratch7).val[b.val]! = scratch7
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq c1 b b.val scratch7
          ⟨rfl, by rw [h_c1_len]; exact h_b⟩
    rw [h_c2_b]; exact (h_s7_per k hk).1

/-! ### L3i.5 — `invert_ntt_at_layer_4_plus` driver (Task H.1).

    Nested-loop driver for the inverse-NTT cross-chunk butterflies at
    layers 4-7. Mirror of forward `ntt_at_layer_4_plus_portable_fc` with:
    - INVERSE butterfly direction (uses `chunk_inv_pair_butterfly_{a,b}_pure`
      instead of forward's `chunk_pair_butterfly_{a,b}_pure`).
    - zeta_i DECREMENTS (zeta_fn group := `Spec.zeta_at (zeta_i - 1 - group)`).
    - Dispatches to closed `inv_ntt_layer_int_vec_step_reduce_fc`
      (Task H.0) for each inner butterfly. -/

namespace Layer4PlusInnerFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Inner loop accumulator: (re, scratch). -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Inverse inner loop invariant (mirror of forward `Layer4PlusInnerFC.inv`
    but with inverse butterflies and no `z` on a-side). -/
def inv
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset : Std.Usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j' : Nat, j' < k.val →
      lift_chunk (acc.1.coefficients.val[a_offset.val + j']!)
        = Spec.chunk_inv_pair_butterfly_a_pure
            (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
            (lift_chunk (re0.coefficients.val[b_offset.val + j']!)))
    ∧ (∀ j' : Nat, j' < k.val →
      lift_chunk (acc.1.coefficients.val[b_offset.val + j']!)
        = Spec.chunk_inv_pair_butterfly_b_pure
            (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
            (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
            zeta)
    ∧ (∀ k' : Nat, k' < 16 →
        (∀ j' : Nat, j' < k.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
        acc.1.coefficients.val[k']! = re0.coefficients.val[k']!)
    ∧ (∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328))

/-- Step-post for the inverse inner loop. -/
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
/-- Per-iteration FC step lemma for the inverse inner loop. -/
theorem invert_ntt_at_layer_4_plus_inner_step_lemma_fc
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize) (zeta_i1 : Std.Usize)
    (h_zi1_lt : zeta_i1.val < 128)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (h_a_offset_b : a_offset.val + step_vec.val ≤ 16)
    (h_b_offset_b : b_offset.val + step_vec.val ≤ 16)
    (h_disjoint : a_offset.val + step_vec.val ≤ b_offset.val)
    (h_pre_a : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[a_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[b_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (acc : Layer4PlusInnerFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ step_vec.val)
    (h_inv : (Layer4PlusInnerFC.inv re0 a_offset b_offset
              (Spec.zeta_at zeta_i1.val) k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i1 a_offset b_offset
      { start := k, «end» := step_vec } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer4PlusInnerFC.step_post re0 a_offset b_offset step_vec
              (Spec.zeta_at zeta_i1.val) k r ⌝ ⦄ := by
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  obtain ⟨h_acc_a, h_acc_b, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
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
      refine ⟨?_, ?_⟩
      · rw [h_i_val]; omega
      · rw [h_i_val]; omega
    have h_acc_i1_undone : acc.1.coefficients.val[i1.val]! = re0.coefficients.val[i1.val]! := by
      apply h_acc_undone i1.val h_i1_lt_16
      intro j' hj'
      refine ⟨?_, ?_⟩
      · rw [h_i1_val]; omega
      · rw [h_i1_val]; omega
    -- Per-lane bounds at acc.1.coefs[i] and [i1] via the bound conjunct in h_inv.
    have h_acc_at_i_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3328 :=
      fun ℓ hℓ => h_acc_bnd i.val h_i_lt_16 ℓ hℓ
    have h_acc_at_i1_bnd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i1.val]!).elements.val[ℓ]!).val.natAbs ≤ 3328 :=
      fun ℓ hℓ => h_acc_bnd i1.val h_i1_lt_16 ℓ hℓ
    have h_zeta_bnd : z.val.natAbs ≤ 1664 := h_z_bd
    -- Apply the H.0 keystone.
    obtain ⟨r_pair, h_r_eq, h_r_a, h_r_b, h_r_undone, h_r_bnd_a, h_r_bnd_b⟩ :=
      triple_exists_ok_fc (inv_ntt_layer_int_vec_step_reduce_fc
        acc.1.coefficients i i1 acc.2 z h_i_lt_16 h_i1_lt_16 h_i_ne_i1
        h_zeta_bnd h_acc_at_i_bnd h_acc_at_i1_bnd)
    -- Build the new accumulator.
    set acc' : Layer4PlusInnerFC.Acc :=
      (({ coefficients := r_pair.1 }
        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector),
       r_pair.2) with hacc'_def
    -- Compose body.
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset
          { start := k, «end» := step_vec } acc.1 acc.2
        = .ok (ControlFlow.cont (({ start := s, «end» := step_vec }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
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
                libcrux_iot_ml_kem.invert_ntt.inv_ntt_layer_int_vec_step_reduce portable_ops_inst
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
    show (Layer4PlusInnerFC.inv re0 a_offset b_offset
            (Spec.zeta_at zeta_i1.val) s acc').holds
    have h_inv_pure :
        (∀ j' : Nat, j' < s.val →
          lift_chunk (acc'.1.coefficients.val[a_offset.val + j']!)
            = Spec.chunk_inv_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!)))
        ∧ (∀ j' : Nat, j' < s.val →
          lift_chunk (acc'.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_inv_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < s.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            acc'.1.coefficients.val[k']! = re0.coefficients.val[k']!)
        ∧ (∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- (a) a-side butterfly for j' < s.val.
        intro j' hj'
        rw [hs_val] at hj'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj'_lt | hj'_eq
        · have h_ne_i : a_offset.val + j' ≠ i.val := by rw [h_i_val]; omega
          have h_ne_i1 : a_offset.val + j' ≠ i1.val := by rw [h_i1_val]; omega
          have h_pos : a_offset.val + j' < 16 := by omega
          have h_unchanged : r_pair.1.val[a_offset.val + j']!
              = acc.1.coefficients.val[a_offset.val + j']! :=
            h_r_undone (a_offset.val + j') h_pos h_ne_i h_ne_i1
          show lift_chunk (acc'.1.coefficients.val[a_offset.val + j']!) = _
          show lift_chunk (r_pair.1.val[a_offset.val + j']!) = _
          rw [h_unchanged]
          exact h_acc_a j' hj'_lt
        · subst hj'_eq
          show lift_chunk (acc'.1.coefficients.val[a_offset.val + k.val]!) = _
          show lift_chunk (r_pair.1.val[a_offset.val + k.val]!) = _
          have h_eq_i : a_offset.val + k.val = i.val := by rw [h_i_val]
          rw [h_eq_i]
          rw [h_r_a]
          rw [h_acc_i_undone, h_acc_i1_undone]
          rw [h_i_val, h_i1_val]
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
        show acc'.1.coefficients.val[k']! = re0.coefficients.val[k']!
        show r_pair.1.val[k']! = re0.coefficients.val[k']!
        have h_unchanged := h_r_undone k' hk' hk'_ne_i hk'_ne_i1
        rw [h_unchanged]
        apply h_acc_undone k' hk'
        intro j' hj'
        have h_at_j' : j' < s.val := by rw [hs_val]; omega
        exact h_not_touched j' h_at_j'
      · -- (d) Per-lane output bound at every chunk.
        intro k' hk' ℓ hℓ
        show ((acc'.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328
        show ((r_pair.1.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328
        by_cases h_ki : k' = i.val
        · rw [h_ki]; exact h_r_bnd_a ℓ hℓ
        · by_cases h_ki1 : k' = i1.val
          · rw [h_ki1]; exact h_r_bnd_b ℓ hℓ
          · have h_unchanged : r_pair.1.val[k']! = acc.1.coefficients.val[k']! :=
              h_r_undone k' hk' h_ki h_ki1
            rw [h_unchanged]
            exact h_acc_bnd k' hk' ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- None branch: k ≥ step_vec, done.
    have hk_ge : k.val ≥ step_vec.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = step_vec.val := by omega
    have h_iter_none := Layer4PlusFC.iter_next_none_eq_gen k step_vec hk_ge
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset
          { start := k, «end» := step_vec } acc.1 acc.2
        = .ok (ControlFlow.done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
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
            = Spec.chunk_inv_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!)))
        ∧ (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_inv_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            acc.1.coefficients.val[k']! = re0.coefficients.val[k']!)
        ∧ (∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j' hj'; rw [← hk_eq] at hj'; exact h_acc_a j' hj'
      · intro j' hj'; rw [← hk_eq] at hj'; exact h_acc_b j' hj'
      · intro k' hk' h_not_touched
        apply h_acc_undone k' hk'
        intro j' hj'
        have h_at_j' : j' < step_vec.val := by rw [← hk_eq]; exact hj'
        exact h_not_touched j' h_at_j'
      · exact h_acc_bnd
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-! ### L3i.5 — Outer loop scaffolding. -/

namespace Layer4PlusOuterFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Outer loop accumulator: (zeta_i, re, scratch). -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Inverse outer loop invariant. zeta_i DECREMENTS by 1 per outer round.
    Per-round zeta = `Spec.zeta_at (zeta_i_0.val - round' - 1)`. -/
def inv
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_0 step_vec : Std.Usize) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = zeta_i_0.val - k.val
    ∧ (∀ round' : Nat, round' < k.val →
        ∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
            = Spec.chunk_inv_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)))
    ∧ (∀ round' : Nat, round' < k.val →
        ∀ j' : Nat, j' < step_vec.val →
          lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
            = Spec.chunk_inv_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                (Spec.zeta_at (zeta_i_0.val - round' - 1)))
    ∧ (∀ c : Nat, c < 16 →
        (∀ round' : Nat, round' < k.val →
          ∀ j' : Nat, j' < step_vec.val →
            c ≠ 2 * round' * step_vec.val + j'
            ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
        acc.2.1.coefficients.val[c]! = re0.coefficients.val[c]!)
    ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328))

/-- Step-post for the inverse outer loop. -/
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

/-- Inverse a-side outer helper: chunks lifted via `re0` at index
    `2*k*step_vec + j'` are exactly the original re0 chunks (since these
    positions have not yet been touched by outer iter `round' < k`). -/
theorem outer_acc_inv_a_chunk_eq_re0
    (re0 acc : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize) (step_vec : Std.Usize)
    (h_undone : ∀ c : Nat, c < 16 →
        (∀ round' : Nat, round' < k.val →
          ∀ j' : Nat, j' < step_vec.val →
            c ≠ 2 * round' * step_vec.val + j'
            ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
        acc.coefficients.val[c]! = re0.coefficients.val[c]!)
    (h_kbound : 2 * k.val * step_vec.val + 2 * step_vec.val ≤ 16)
    (j' : Nat) (hj' : j' < step_vec.val) :
    acc.coefficients.val[2 * k.val * step_vec.val + j']!
      = re0.coefficients.val[2 * k.val * step_vec.val + j']! := by
  apply h_undone (2 * k.val * step_vec.val + j') (by omega)
  intro round' hround' j'' hj''
  refine ⟨?_, ?_⟩
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

/-- Inverse b-side outer helper. -/
theorem outer_acc_inv_b_chunk_eq_re0
    (re0 acc : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize) (step_vec : Std.Usize)
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
  refine ⟨?_, ?_⟩
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
/-- Inverse inner loop spec wrapper: dispatches `loop_range_spec_usize` for the
    inner loop, returning the final FC equations on the post poly. -/
theorem invert_ntt_at_layer_4_plus_inner_loop_fc
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
      ((re0.coefficients.val[a_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[b_offset.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_pre_all : ∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := step_vec } zeta_i1 re0 scratch a_offset b_offset
    ⦃ ⇓ r => ⌜
      (∀ j' : Nat, j' < step_vec.val →
        lift_chunk (r.1.coefficients.val[a_offset.val + j']!)
          = Spec.chunk_inv_pair_butterfly_a_pure
              (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
              (lift_chunk (re0.coefficients.val[b_offset.val + j']!)))
      ∧ (∀ j' : Nat, j' < step_vec.val →
        lift_chunk (r.1.coefficients.val[b_offset.val + j']!)
          = Spec.chunk_inv_pair_butterfly_b_pure
              (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
              (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
              (Spec.zeta_at zeta_i1.val))
      ∧ (∀ k' : Nat, k' < 16 →
          (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
          r.1.coefficients.val[k']! = re0.coefficients.val[k']!)
      ∧ (∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
          ((r.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328)
      ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          zeta_i1 a_offset b_offset iter1 acc1.1 acc1.2)
      (β := Layer4PlusInnerFC.Acc)
      (re0, scratch)
      0#usize step_vec
      (Layer4PlusInnerFC.inv re0 a_offset b_offset (Spec.zeta_at zeta_i1.val))
      (by
        have : (0#usize : Std.Usize).val = 0 := rfl
        omega)
      (by
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j' hj'; exact absurd hj' (Nat.not_lt_zero j')
        · intro j' hj'; exact absurd hj' (Nat.not_lt_zero j')
        · intro k' _ _; trivial
        · -- Initial bound holds via h_pre_a/h_pre_b for touched indices,
          -- and trivially for untouched indices via the input precondition
          -- on re0 chunks. Need a global bound on re0.
          -- At k=0, acc.1 = re0. We need ((re0.coef.val[k']!).elem.val[ℓ]!).natAbs ≤ 3328.
          -- This is NOT covered by h_pre_a/h_pre_b alone (those are only for
          -- a_offset+j and b_offset+j).
          -- We use a global precondition added below: h_pre_all.
          intro k' hk' ℓ hℓ
          exact h_pre_all k' hk' ℓ hℓ)
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
            = Spec.chunk_inv_pair_butterfly_a_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!)))
        ∧ (∀ j' : Nat, j' < step_vec.val →
          lift_chunk (r.1.coefficients.val[b_offset.val + j']!)
            = Spec.chunk_inv_pair_butterfly_b_pure
                (lift_chunk (re0.coefficients.val[a_offset.val + j']!))
                (lift_chunk (re0.coefficients.val[b_offset.val + j']!))
                (Spec.zeta_at zeta_i1.val))
        ∧ (∀ k' : Nat, k' < 16 →
            (∀ j' : Nat, j' < step_vec.val → k' ≠ a_offset.val + j' ∧ k' ≠ b_offset.val + j') →
            r.1.coefficients.val[k']! = re0.coefficients.val[k']!)
        ∧ (∀ k' : Nat, k' < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((r.1.coefficients.val[k']!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer4PlusInnerFC.inv] using h_inv_holds
    exact h_inv
  · -- Step lemma dispatch.
    intro acc k _h_ge h_le hinv
    have h_step := invert_ntt_at_layer_4_plus_inner_step_lemma_fc re0 a_offset b_offset step_vec
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
/-- Per-iteration FC step lemma for the inverse outer loop. -/
theorem invert_ntt_at_layer_4_plus_outer_step_lemma_fc
    (re0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_0 step_vec i_end : Std.Usize)
    (h_pre : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re0.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 3328)
    (h_step_vec_pos : 1 ≤ step_vec.val)
    (h_step_vec_dvd : 2 * i_end.val * step_vec.val = 16)
    (h_zeta_lo : i_end.val ≤ zeta_i_0.val)
    (h_zeta_hi : zeta_i_0.val ≤ 128)
    (acc : Layer4PlusOuterFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ i_end.val)
    (h_inv : (Layer4PlusOuterFC.inv re0 zeta_i_0 step_vec k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst)
      step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
    ⦃ ⇓ r => ⌜ Layer4PlusOuterFC.step_post re0 zeta_i_0 step_vec i_end k r ⌝ ⦄ := by
  obtain ⟨h_zeta_acc, h_acc_a, h_acc_b, h_acc_undone, h_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
  by_cases h_lt : k.val < i_end.val
  · -- Some round = k branch.
    obtain ⟨s, hs_val, h_iter_some⟩ :=
      Layer4PlusFC.iter_next_some_eq_gen k i_end h_lt
    -- (1) zeta_i1 ← acc.1 - 1.
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_acc1_ge_1 : 1 ≤ acc.1.val := by
      rw [h_zeta_acc]
      have : k.val < i_end.val := h_lt
      have : k.val + 1 ≤ i_end.val := by omega
      omega
    have h_z_ge : (1#usize : Std.Usize).val ≤ acc.1.val := by rw [h_um]; omega
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      Layer2FC.usize_sub_ok_eq acc.1 1#usize h_z_ge
    have h_zi1_arith : zi1.val = zeta_i_0.val - k.val - 1 := by
      rw [h_zi1_val, h_um, h_zeta_acc]
    have h_zi1_lt_128 : zi1.val < 128 := by
      rw [h_zi1_arith]; omega
    -- (2) i ← round * 2.
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_i_end_le_16 : i_end.val ≤ 16 := by
      have : i_end.val * step_vec.val * 2 = 16 := by rw [Nat.mul_assoc] at h_step_vec_dvd; nlinarith
      nlinarith
    have h_i_max : k.val * (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]
      have h_k_b : k.val * 2 ≤ 16 := by
        have : k.val ≤ 8 := by
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
    have h_2kstep_bnd : 2 * k.val * step_vec.val + 2 * step_vec.val ≤ 16 := by
      have : (k.val + 1) * (2 * step_vec.val) ≤ i_end.val * (2 * step_vec.val) := by
        apply Nat.mul_le_mul_right; omega
      nlinarith
    have h_acc_a_eq : ∀ j : Nat, j < step_vec.val →
        acc.2.1.coefficients.val[ao.val + j]! = re0.coefficients.val[ao.val + j]! := by
      intro j hj
      rw [h_ao_arith]
      exact outer_acc_inv_a_chunk_eq_re0 re0 acc.2.1 k step_vec h_acc_undone
              h_2kstep_bnd j hj
    have h_acc_b_eq : ∀ j : Nat, j < step_vec.val →
        acc.2.1.coefficients.val[bo.val + j]! = re0.coefficients.val[bo.val + j]! := by
      intro j hj
      rw [h_bo_arith]
      exact outer_acc_inv_b_chunk_eq_re0 re0 acc.2.1 k step_vec h_acc_undone
              h_2kstep_bnd h_step_vec_pos j hj
    have h_pre_a : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[ao.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro j hj ℓ hℓ
      rw [h_acc_a_eq j hj]
      apply h_pre _ _ ℓ hℓ
      rw [h_ao_arith]; omega
    have h_pre_b : ∀ j : Nat, j < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[bo.val + j]!).elements.val[ℓ]!).val.natAbs ≤ 3328 := by
      intro j hj ℓ hℓ
      rw [h_acc_b_eq j hj]
      apply h_pre _ _ ℓ hℓ
      rw [h_bo_arith]; omega
    -- Dispatch inner loop.
    have h_inner := invert_ntt_at_layer_4_plus_inner_loop_fc acc.2.1 acc.2.2 ao bo step_vec zi1
      h_zi1_lt_128 h_step_vec_pos h_a_offset_b h_b_offset_b h_disjoint h_pre_a h_pre_b h_acc_bnd
    obtain ⟨r_pair, h_r_eq, h_r_a, h_r_b, h_r_undone, h_r_bnd⟩ :=
      triple_exists_ok_fc h_inner
    set acc' : Layer4PlusOuterFC.Acc :=
      (zi1, r_pair.1, r_pair.2) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
        = .ok (ControlFlow.cont (({ start := s, «end» := i_end }
                        : CoreModels.core.ops.range.Range Std.Usize), acc')) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
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
              let zi1' ← acc.1 - 1#usize
              let ii' ← k * 2#usize
              let ao' ← ii' * step_vec
              let bo' ← ao' + step_vec
              let (re1, scratch1) ←
                libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0_loop0
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
        acc'.1.val = zeta_i_0.val - s.val
        ∧ (∀ round' : Nat, round' < s.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_a_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)))
        ∧ (∀ round' : Nat, round' < s.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc'.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_b_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val - round' - 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < s.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            acc'.2.1.coefficients.val[c]! = re0.coefficients.val[c]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc'.2.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- zeta thread: zi1.val = zeta_i_0.val - (k.val + 1) = zeta_i_0.val - s.val.
        show zi1.val = zeta_i_0.val - s.val
        rw [h_zi1_arith, hs_val]; omega
      · -- a-side butterflies for round' < s.val.
        intro round' hround' j' hj'
        rw [hs_val] at hround'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hround' with hround'_lt | hround'_eq
        · have h_pos : 2 * round' * step_vec.val + j' < 16 := by
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
        · subst hround'_eq
          show lift_chunk (acc'.2.1.coefficients.val[2 * k.val * step_vec.val + j']!) = _
          show lift_chunk (r_pair.1.coefficients.val[2 * k.val * step_vec.val + j']!) = _
          rw [show (2 * k.val * step_vec.val + j' : Nat) = ao.val + j' from by rw [h_ao_arith]]
          rw [h_r_a j' hj']
          rw [h_acc_a_eq j' hj', h_acc_b_eq j' hj']
          rw [show (ao.val + j' : Nat) = 2 * k.val * step_vec.val + j' from by rw [h_ao_arith]]
          rw [show (bo.val + j' : Nat) = 2 * k.val * step_vec.val + step_vec.val + j' from by rw [h_bo_arith]]
      · -- b-side butterflies for round' < s.val.
        intro round' hround' j' hj'
        rw [hs_val] at hround'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hround' with hround'_lt | hround'_eq
        · have h_pos : 2 * round' * step_vec.val + step_vec.val + j' < 16 := by
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
          rw [show zi1.val = zeta_i_0.val - k.val - 1 from h_zi1_arith]
      · -- Untouched chunks.
        intro c hc h_not_touched
        show acc'.2.1.coefficients.val[c]! = re0.coefficients.val[c]!
        show r_pair.1.coefficients.val[c]! = re0.coefficients.val[c]!
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
        have h_at_r : round' < s.val := by rw [hs_val]; omega
        exact h_not_touched round' h_at_r j' hj'
      · -- Per-lane output bound at every chunk: inner loop result already
        -- has the bound on r_pair.1 = acc'.2.1.
        intro c hc ℓ hℓ
        show ((acc'.2.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        show ((r_pair.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328
        exact h_r_bnd c hc ℓ hℓ
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- None branch: k ≥ i_end, done.
    have hk_ge : k.val ≥ i_end.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = i_end.val := by omega
    have h_iter_none := Layer4PlusFC.iter_next_none_eq_gen k i_end hk_ge
    have h_body :
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst)
          step_vec { start := k, «end» := i_end } acc.1 acc.2.1 acc.2.2
        = .ok (ControlFlow.done (acc.1, acc.2.1, acc.2.2)) := by
      unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
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
        acc.1.val = zeta_i_0.val - i_end.val
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_a_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)))
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (acc.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_b_pure
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re0.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i_0.val - round' - 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < i_end.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            acc.2.1.coefficients.val[c]! = re0.coefficients.val[c]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((acc.2.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h_zeta_acc, hk_eq]
      · intro round' hround'; rw [← hk_eq] at hround'; exact h_acc_a round' hround'
      · intro round' hround'; rw [← hk_eq] at hround'; exact h_acc_b round' hround'
      · intro c hc h_nt
        apply h_acc_undone c hc
        intro round' hround' j' hj'
        have : round' < i_end.val := by rw [← hk_eq]; exact hround'
        exact h_nt round' this j' hj'
      · exact h_acc_bnd
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 16000000 in
@[spec high]
theorem invert_ntt_at_layer_4_plus_portable_fc
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (layer : Std.Usize)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_layer : 4 ≤ layer.val ∧ layer.val ≤ 7)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 3328)
    (h_zeta : (128 >>> layer.val) ≤ zeta_i.val ∧ zeta_i.val ≤ 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
      (vectortraitsOperationsInst := portable_ops_inst)
      zeta_i re layer scratch
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i.val - 128 >>> layer.val
              ∧ lift_poly p.2.1 = Spec.invert_ntt_layer_4_plus_pure (lift_poly re) zeta_i layer
              ∧ (∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  obtain ⟨h_layer_lo, h_layer_hi⟩ := h_layer
  obtain ⟨h_zeta_lo, h_zeta_hi⟩ := h_zeta
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus
  -- Resolve step ← 1 <<< layer.
  have h_usize_bits : (Aeneas.Std.UScalarTy.Usize.numBits : Nat) = System.Platform.numBits := rfl
  have h_layer_bits : layer.val < Aeneas.Std.UScalarTy.Usize.numBits := by
    have h_p := System.Platform.numBits_eq
    rcases h_p with h32 | h64
    · rw [h_usize_bits, h32]; omega
    · rw [h_usize_bits, h64]; omega
  have h_size_eq : Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize = 2 ^ System.Platform.numBits := by
    simp [Std.Usize.size, Usize.numBits]
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
  -- Unfold FIELD_ELEMENTS_IN_VECTOR (= 16#usize) so we can use UScalar.div_spec.
  unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
  -- Resolve step_vec ← step / 16.
  have h_16_nz : ((16#usize : Std.Usize).val : Nat) ≠ 0 := by decide
  have h_step_pos : 1 ≤ step.val := by
    rw [h_step_val, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.one_le_pow _ _ (by decide : (0:Nat) < 2)
  obtain ⟨step_vec, h_step_vec_eq, h_step_vec_val⟩ :=
    Aeneas.Std.UScalar.div_spec step h_16_nz
  rw [h_step_vec_eq]
  simp only [Aeneas.Std.bind_tc_ok]
  have h_step_vec_arith : step_vec.val = (1 <<< layer.val) / 16 := by
    have h_16_eq : (16#usize : Std.Usize).val = 16 := rfl
    rw [h_step_vec_val, h_step_val, h_16_eq]
  -- Resolve i_end ← 128 >>> layer.
  obtain ⟨i_end, h_i_end_eq, h_i_end_val, _h_i_end_bv⟩ :=
    Std.WP.spec_imp_exists (Aeneas.Std.UScalar.ShiftRight_spec (128#usize : Std.Usize) layer
      h_layer_bits)
  rw [h_i_end_eq]
  have h_i_end_arith : i_end.val = 128 >>> layer.val := h_i_end_val
  have h_step_vec_pos : 1 ≤ step_vec.val := by
    rw [h_step_vec_arith]
    interval_cases layer.val <;> decide
  have h_step_vec_dvd : 2 * i_end.val * step_vec.val = 16 := by
    rw [h_i_end_arith, h_step_vec_arith]
    interval_cases layer.val <;> decide
  have h_i_end_pos : 1 ≤ i_end.val := by
    rw [h_i_end_arith]
    interval_cases layer.val <;> decide
  have h_zeta_lo' : i_end.val ≤ zeta_i.val := by
    rw [h_i_end_arith]; exact h_zeta_lo
  -- Unfold outer loop and apply loop_range_spec_usize.
  unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.invert_ntt.invert_ntt_at_layer_4_plus_loop0.body
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
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show zeta_i.val = zeta_i.val - (0#usize : Std.Usize).val
          show zeta_i.val = zeta_i.val - 0
          omega
        · intro round' hround' _ _
          exact absurd hround' (Nat.not_lt_zero round')
        · intro round' hround' _ _
          exact absurd hround' (Nat.not_lt_zero round')
        · intro _ _ _; trivial
        · -- Initial bound: acc.2.1 = re at k=0, so bound from h_bnd.
          intro c hc ℓ hℓ
          exact h_bnd c hc ℓ hℓ)
      ?_)
  · -- Post entailment: at k = i_end, build chunks_arr matching Spec.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Layer4PlusOuterFC.inv re zeta_i step_vec i_end r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    have h_inv :
        r.1.val = zeta_i.val - i_end.val
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (r.2.1.coefficients.val[2 * round' * step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_a_pure
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)))
        ∧ (∀ round' : Nat, round' < i_end.val →
            ∀ j' : Nat, j' < step_vec.val →
              lift_chunk (r.2.1.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!)
                = Spec.chunk_inv_pair_butterfly_b_pure
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + j']!))
                    (lift_chunk (re.coefficients.val[2 * round' * step_vec.val + step_vec.val + j']!))
                    (Spec.zeta_at (zeta_i.val - round' - 1)))
        ∧ (∀ c : Nat, c < 16 →
            (∀ round' : Nat, round' < i_end.val →
              ∀ j' : Nat, j' < step_vec.val →
                c ≠ 2 * round' * step_vec.val + j'
                ∧ c ≠ 2 * round' * step_vec.val + step_vec.val + j') →
            r.2.1.coefficients.val[c]! = re.coefficients.val[c]!)
        ∧ (∀ c : Nat, c < 16 → ∀ ℓ : Nat, ℓ < 16 →
            ((r.2.1.coefficients.val[c]!).elements.val[ℓ]!).val.natAbs ≤ 3328) := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
             Layer4PlusOuterFC.inv] using h_inv_holds
    obtain ⟨h_zeta_done, h_done_a, h_done_b, _h_done_undone, h_done_bnd⟩ := h_inv
    -- Build chunks_arr matching the Spec layout.
    unfold Spec.invert_ntt_layer_4_plus_pure
    set chunks_arr : Std.Array
        (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize :=
      Std.Array.make 16#usize ((List.range 16).map (fun c =>
        Spec.chunk_inv_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          layer
          (fun group => Spec.zeta_at (zeta_i.val - 1 - group))
          c))
        (by simp) with hchunks_def
    have h_chunks_len : chunks_arr.val.length = 16 := by
      show ((List.range 16).map _).length = 16; simp
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
    have h_chunks_get : ∀ c : Nat, (hc : c < 16) →
        chunks_arr.val[c]'(by rw [h_chunks_len]; exact hc)
          = lift_chunk (r.2.1.coefficients.val[c]!) := by
      intro c hc
      show ((List.range 16).map (fun c =>
        Spec.chunk_inv_at_layer_4_plus_pure
          (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at (lift_poly re)))
            (by simp))
          layer
          (fun group => Spec.zeta_at (zeta_i.val - 1 - group))
          c))[c]'_ = _
      rw [List.getElem_map, List.getElem_range]
      unfold Spec.chunk_inv_at_layer_4_plus_pure
      set sv := (1 <<< layer.val) / 16 with hsv_def
      have hsv_eq : sv = step_vec.val := by rw [hsv_def, h_step_vec_arith]
      simp only []
      set group := c / (2 * sv)
      set offset := c % (2 * sv)
      have h_2sv_pos : 0 < 2 * sv := by rw [hsv_eq]; omega
      have h_c_eq : 2 * sv * group + offset = c := by
        show 2 * sv * (c / (2 * sv)) + c % (2 * sv) = c
        exact Nat.div_add_mod c (2 * sv)
      have h_off_lt : offset < 2 * sv := Nat.mod_lt _ h_2sv_pos
      have h_16_eq : 2 * i_end.val * sv = 16 := by
        rw [hsv_eq]; exact h_step_vec_dvd
      have h_group_lt : group < i_end.val := by
        by_contra h_ge
        push Not at h_ge
        have h_ge2 : 2 * sv * i_end.val ≤ 2 * sv * group := Nat.mul_le_mul_left _ h_ge
        have h_c_ge : c ≥ 2 * sv * i_end.val := by
          have : 2 * sv * group ≤ c := by omega
          omega
        have h_rw : 2 * sv * i_end.val = 16 := by
          have h : 2 * i_end.val * sv = 2 * sv * i_end.val := by ring
          omega
        omega
      by_cases h_off_lt_sv : offset < sv
      · -- a-side.
        simp only [if_pos h_off_lt_sv]
        have h_c_lt_16 : c < 16 := hc
        have h_c_plus_sv_lt_16 : c + sv < 16 := by
          have h_succ : 2 * sv * (group + 1) ≤ 2 * sv * i_end.val := Nat.mul_le_mul_left _ h_group_lt
          have h_split : 2 * sv * (group + 1) = 2 * sv * group + 2 * sv := by ring
          have h_eq_16 : 2 * sv * i_end.val = 16 := by
            have : 2 * i_end.val * sv = 2 * sv * i_end.val := by ring
            omega
          omega
        rw [h_chunks0_at c h_c_lt_16, h_chunks0_at (c + sv) h_c_plus_sv_lt_16]
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
      · -- b-side.
        simp only [if_neg h_off_lt_sv]
        push Not at h_off_lt_sv
        set j' := offset - sv with hj'_def
        have hj'_lt_sv : j' < sv := by
          show offset - sv < sv; omega
        have h_off_eq : offset = sv + j' := by
          show offset = sv + (offset - sv); omega
        have h_c_lt_16 : c < 16 := hc
        have h_c_minus_sv_lt_16 : c - sv < 16 := by omega
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
        -- The zeta expression: spec uses `zeta_i.val - 1 - group`,
        -- invariant uses `zeta_i.val - group - 1`. These are equal.
        rw [show zeta_i.val - 1 - group = zeta_i.val - group - 1 by omega]
        exact h_done.symm
    have h_final := flatten_chunks_eq_lift_poly_fc r.2.1 chunks_arr h_chunks_len h_chunks_get
    exact ⟨by rw [h_zeta_done, h_i_end_arith], h_final.symm, h_done_bnd⟩
  · -- Step lemma dispatch.
    intro acc k _h_ge h_le hinv
    have h_step := invert_ntt_at_layer_4_plus_outer_step_lemma_fc re zeta_i step_vec i_end
      h_bnd h_step_vec_pos h_step_vec_dvd h_zeta_lo' h_zeta_hi acc k h_le hinv
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

/-! ### L3i.6 — `invert_ntt_montgomery` composer (Task I).

    Top-level inverse-NTT composer. 7-step bind chain through the closed
    layer FC equations (F + G.2 + G.3 + H.1 instantiated at 4 different
    layer values). Closest yardstick: forward `ntt_binomially_sampled_ring_element_fc` (~247 LOC).

    Impl:
    ```
    let zeta_i := 256 / 2 = 128
    let (zeta_i1, re1)         := invert_ntt_at_layer_1 portable zeta_i re
    let (zeta_i2, re2)         := invert_ntt_at_layer_2 portable zeta_i1 re1
    let (zeta_i3, re3)         := invert_ntt_at_layer_3 portable zeta_i2 re2
    let (zeta_i4, re4, sc1)    := invert_ntt_at_layer_4_plus portable zeta_i3 re3 4 sc
    let (zeta_i5, re5, sc2)    := invert_ntt_at_layer_4_plus portable zeta_i4 re4 5 sc1
    let (zeta_i6, re6, sc3)    := invert_ntt_at_layer_4_plus portable zeta_i5 re5 6 sc2
    let (_,       re7, sc4)    := invert_ntt_at_layer_4_plus portable zeta_i6 re6 7 sc3
    ok (re7, sc4)
    ```

    zeta_i thread: 128 → 64 → 32 → 16 → 8 → 4 → 2 → 1. -/
set_option maxHeartbeats 16000000 in
@[spec]
theorem invert_ntt_montgomery_fc
    {K : Std.Usize}
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
      K (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.invert_ntt_montgomery_pure (lift_poly re)
              ∧ (∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) ⌝ ⦄ := by
  -- `h_bnd` is already ≤ 13312; keep alias for readability at layer-1 call site.
  have h_bnd_loose : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312 := h_bnd
  -- =============================================================
  -- Step 0: resolve `let zeta_i ← constants.COEFFICIENTS_IN_RING_ELEMENT / 2`
  --         = `256#usize / 2#usize = .ok 128#usize`.
  -- =============================================================
  have h_div : (libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
                  / (2#usize : Std.Usize) : Result Std.Usize)
                = .ok (128#usize : Std.Usize) := by
    unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
    have h_2_nz : ((2#usize : Std.Usize).val : Nat) ≠ 0 := by decide
    obtain ⟨z, hz_eq, hz_v⟩ :=
      Aeneas.Std.UScalar.div_spec (256#usize : Std.Usize) h_2_nz
    have hz_val : (↑z : Nat) = 128 := by rw [hz_v]; decide
    have hz_eq128 : z = (128#usize : Std.Usize) := by
      apply Aeneas.Std.UScalar.eq_of_val_eq
      show z.val = (128#usize : Std.Usize).val
      rw [hz_val]; decide
    rw [hz_eq, hz_eq128]
  -- =============================================================
  -- Step 1: invert_ntt_at_layer_1. zeta_i = 128 → 64. bound stays ≤ 3328.
  -- =============================================================
  obtain ⟨⟨zeta_i1, re1⟩, h1_eq, h1_zout, h1_fc, h1_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_1_portable_fc (128#usize : Std.Usize) re
        h_bnd_loose (by decide) (by decide))
  dsimp only at h1_zout h1_fc h1_bnd
  have h_zeta_i1 : zeta_i1.val = 64 := by rw [h1_zout]; decide
  -- =============================================================
  -- Step 2: invert_ntt_at_layer_2. zeta_i = 64 → 32. bound stays ≤ 3328.
  -- =============================================================
  have h_re1_loose : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re1.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312 := by
    intro chunk hc k hk
    have := h1_bnd chunk hc k hk
    omega
  obtain ⟨⟨zeta_i2, re2⟩, h2_eq, h2_zout, h2_fc, h2_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_2_portable_fc zeta_i1 re1
        h_re1_loose h1_bnd (by rw [h_zeta_i1]; decide)
        (by rw [h_zeta_i1]; decide))
  dsimp only at h2_zout h2_fc h2_bnd
  have h_zeta_i2 : zeta_i2.val = 32 := by rw [h2_zout, h_zeta_i1]
  -- =============================================================
  -- Step 3: invert_ntt_at_layer_3. zeta_i = 32 → 16. bound stays ≤ 3328.
  -- =============================================================
  have h_re2_loose : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re2.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312 := by
    intro chunk hc k hk
    have := h2_bnd chunk hc k hk
    omega
  obtain ⟨⟨zeta_i3, re3⟩, h3_eq, h3_zout, h3_fc, h3_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_3_portable_fc zeta_i2 re2
        h_re2_loose h2_bnd (by rw [h_zeta_i2]; decide)
        (by rw [h_zeta_i2]; decide))
  dsimp only at h3_zout h3_fc h3_bnd
  have h_zeta_i3 : zeta_i3.val = 16 := by rw [h3_zout, h_zeta_i2]
  -- =============================================================
  -- Step 4: invert_ntt_at_layer_4_plus (layer = 4). zeta_i = 16 → 8.
  -- 128 >>> 4 = 8.
  -- =============================================================
  obtain ⟨⟨zeta_i4, re4, scratch1⟩, h4_eq, h4_zout, h4_fc, h4_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_4_plus_portable_fc zeta_i3 re3 (4#usize : Std.Usize) scratch
        (by decide) h3_bnd
        (by refine ⟨?_, ?_⟩ <;> · rw [h_zeta_i3]; decide))
  dsimp only at h4_zout h4_fc h4_bnd
  have h_zeta_i4 : zeta_i4.val = 8 := by
    rw [h4_zout, h_zeta_i3]; decide
  -- =============================================================
  -- Step 5: invert_ntt_at_layer_4_plus (layer = 5). zeta_i = 8 → 4.
  -- 128 >>> 5 = 4.
  -- =============================================================
  obtain ⟨⟨zeta_i5, re5, scratch2⟩, h5_eq, h5_zout, h5_fc, h5_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_4_plus_portable_fc zeta_i4 re4 (5#usize : Std.Usize) scratch1
        (by decide) h4_bnd
        (by refine ⟨?_, ?_⟩ <;> · rw [h_zeta_i4]; decide))
  dsimp only at h5_zout h5_fc h5_bnd
  have h_zeta_i5 : zeta_i5.val = 4 := by
    rw [h5_zout, h_zeta_i4]; decide
  -- =============================================================
  -- Step 6: invert_ntt_at_layer_4_plus (layer = 6). zeta_i = 4 → 2.
  -- 128 >>> 6 = 2.
  -- =============================================================
  obtain ⟨⟨zeta_i6, re6, scratch3⟩, h6_eq, h6_zout, h6_fc, h6_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_4_plus_portable_fc zeta_i5 re5 (6#usize : Std.Usize) scratch2
        (by decide) h5_bnd
        (by refine ⟨?_, ?_⟩ <;> · rw [h_zeta_i5]; decide))
  dsimp only at h6_zout h6_fc h6_bnd
  have h_zeta_i6 : zeta_i6.val = 2 := by
    rw [h6_zout, h_zeta_i5]; decide
  -- =============================================================
  -- Step 7: invert_ntt_at_layer_4_plus (layer = 7). zeta_i = 2 → 1.
  -- 128 >>> 7 = 1.
  -- =============================================================
  obtain ⟨⟨_zeta_i7, re7, scratch4⟩, h7_eq, _h7_zout, h7_fc, h7_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_at_layer_4_plus_portable_fc zeta_i6 re6 (7#usize : Std.Usize) scratch3
        (by decide) h6_bnd
        (by refine ⟨?_, ?_⟩ <;> · rw [h_zeta_i6]; decide))
  dsimp only at h7_fc h7_bnd
  -- =============================================================
  -- Compose: derive the full impl `do`-block equation by simp-folding
  -- all step equations into the unfolded body.
  -- =============================================================
  have h_body :
      libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery K
        (vectortraitsOperationsInst := portable_ops_inst) re scratch
        = .ok (re7, scratch4) := by
    unfold libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
    simp [h_div, h1_eq, h2_eq, h3_eq, h4_eq, h5_eq, h6_eq, h7_eq]
  apply triple_of_ok_fc h_body
  -- POST is now a conjunction: equality (proved below) ∧ per-lane bound
  -- (≤ 3328, exactly the layer-7 output bound `h7_bnd`, since `p.1 = re7`).
  refine ⟨?_, h7_bnd⟩
  -- =============================================================
  -- Prove lift_poly equation by chaining FC equations through
  -- `Spec.invert_ntt_montgomery_pure`.
  -- =============================================================
  show lift_poly re7 = Spec.invert_ntt_montgomery_pure (lift_poly re)
  unfold Spec.invert_ntt_montgomery_pure
  -- Identify each zeta_i with the spec's literal value.
  have h_zeta_eq1 : zeta_i1 = (64#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i1]; decide
  have h_zeta_eq2 : zeta_i2 = (32#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i2]; decide
  have h_zeta_eq3 : zeta_i3 = (16#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i3]; decide
  have h_zeta_eq4 : zeta_i4 = (8#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i4]; decide
  have h_zeta_eq5 : zeta_i5 = (4#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i5]; decide
  have h_zeta_eq6 : zeta_i6 = (2#usize : Std.Usize) := by
    apply Aeneas.Std.UScalar.eq_of_val_eq
    rw [h_zeta_i6]; decide
  rw [h7_fc, h6_fc, h5_fc, h4_fc, h3_fc, h2_fc, h1_fc,
      h_zeta_eq1, h_zeta_eq2, h_zeta_eq3, h_zeta_eq4, h_zeta_eq5, h_zeta_eq6]


/-- L3.4 — `ntt_vector_u` driver (4 layer_4_plus calls + 3 dedicated layers
    + barrett reduce, used for the encryption "u" vector NTT). Note that the
    impl's first call is `ntt_at_layer_4_plus(0, layer=7)` (Mont multiply
    through `ZETAS_TIMES_MONTGOMERY_R[1]`), not the dedicated
    `ntt_at_layer_7` (plain multiply with `-1600`). The two paths produce
    the same field element in `ZMod 3329` (see `Spec.zeta_at_one_eq_layer_7`)
    but differ structurally; we target the spec actually computed by the
    impl, `Spec.ntt_pure_vec_u`. -/
@[spec]
theorem ntt_vector_u_fc
    (VECTOR_U_COMPRESSION_FACTOR : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((re.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_vector_u
      VECTOR_U_COMPRESSION_FACTOR
      (vectortraitsOperationsInst := portable_ops_inst) re scratch
    ⦃ ⇓ p => ⌜ lift_poly p.1 = Spec.ntt_pure_vec_u (lift_poly re) ⌝ ⦄ := by
  -- Strategy: mirror L3.3, but use `ntt_at_layer_4_plus_portable_fc_strong`
  -- with `zeta_i = 0, layer = 7` for the FIRST step (impl uses layer_4_plus
  -- at layer 7, not the dedicated layer_7), and target `Spec.ntt_pure_vec_u`.
  -- =============================================================
  -- Step 1: layer_4_plus (zeta_i=0, layer=7, bnd=3328). ≤ 3328 → ≤ 6656.
  -- =============================================================
  obtain ⟨⟨zeta_i1, re1, scratch1⟩, h1_eq, h1_fc, h1_zout, h1_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong 0#usize re 7#usize scratch 3328#usize
        (by decide) (by decide) (by decide) h_bnd)
  dsimp only at h1_fc h1_zout h1_bnd
  have h_zeta_i1 : zeta_i1.val = 1 := by rw [h1_zout]; decide
  -- =============================================================
  -- Step 2: usize_mul 2 * 3328 = 6656.
  -- =============================================================
  obtain ⟨i6656, hi6656_eq, hi6656_val⟩ :=
    usize_mul_ok_eq_fc 2#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 3: layer_4_plus (zeta_i1=1, layer=6, bnd=6656). ≤ 6656 → ≤ 9984.
  -- =============================================================
  have h_re1_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re1.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ i6656.val := by
    intro i hi j hj
    have hb := h1_bnd i hi j hj
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    rw [h3328] at hb
    rw [hi6656_val, h2, h3328]
    omega
  have h_i6656_bnd : i6656.val ≤ 8 * 3328 := by
    have h := hi6656_val
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h2, h3328] at h
    omega
  obtain ⟨⟨zeta_i2, re2, scratch2⟩, h3_eq, h3_fc, h3_zout, h3_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong zeta_i1 re1 6#usize scratch1 i6656
        (by decide) h_i6656_bnd
        (by rw [h_zeta_i1]; decide) h_re1_loose)
  dsimp only at h3_fc h3_zout h3_bnd
  have h_zeta_i2 : zeta_i2.val = 3 := by
    rw [h3_zout, h_zeta_i1]; decide
  -- =============================================================
  -- Step 4: usize_mul 3 * 3328 = 9984.
  -- =============================================================
  obtain ⟨i9984, hi9984_eq, hi9984_val⟩ :=
    usize_mul_ok_eq_fc 3#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 5: layer_4_plus (zeta_i2=3, layer=5, bnd=9984). ≤ 9984 → ≤ 13312.
  -- =============================================================
  have h_re2_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ i9984.val := by
    intro i hi j hj
    have hb := h3_bnd i hi j hj
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h2 : (2#usize : Std.Usize).val = 2 := by decide
    have h3 : (3#usize : Std.Usize).val = 3 := by decide
    rw [hi6656_val, h2, h3328] at hb
    rw [hi9984_val, h3, h3328]
    omega
  have h_i9984_bnd : i9984.val ≤ 8 * 3328 := by
    have h := hi9984_val
    have h3 : (3#usize : Std.Usize).val = 3 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h3, h3328] at h
    omega
  obtain ⟨⟨zeta_i3, re3, scratch3⟩, h5_eq, h5_fc, h5_zout, h5_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong zeta_i2 re2 5#usize scratch2 i9984
        (by decide) h_i9984_bnd
        (by rw [h_zeta_i2]; decide) h_re2_loose)
  dsimp only at h5_fc h5_zout h5_bnd
  have h_zeta_i3 : zeta_i3.val = 7 := by
    rw [h5_zout, h_zeta_i2]; decide
  -- =============================================================
  -- Step 6: usize_mul 4 * 3328 = 13312.
  -- =============================================================
  obtain ⟨i13312, hi13312_eq, hi13312_val⟩ :=
    usize_mul_ok_eq_fc 4#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 7: layer_4_plus (zeta_i3=7, layer=4, bnd=13312). ≤ 13312 → ≤ 16640.
  -- =============================================================
  have h_re3_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ i13312.val := by
    intro i hi j hj
    have hb := h5_bnd i hi j hj
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h3 : (3#usize : Std.Usize).val = 3 := by decide
    have h4 : (4#usize : Std.Usize).val = 4 := by decide
    rw [hi9984_val, h3, h3328] at hb
    rw [hi13312_val, h4, h3328]
    omega
  have h_i13312_bnd : i13312.val ≤ 8 * 3328 := by
    have h := hi13312_val
    have h4 : (4#usize : Std.Usize).val = 4 := by decide
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    rw [h4, h3328] at h
    omega
  obtain ⟨⟨zeta_i4, re4, scratch4⟩, h7_eq, h7_fc, h7_zout, h7_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_4_plus_portable_fc_strong zeta_i3 re3 4#usize scratch3 i13312
        (by decide) h_i13312_bnd
        (by rw [h_zeta_i3]; decide) h_re3_loose)
  dsimp only at h7_fc h7_zout h7_bnd
  have h_zeta_i4 : zeta_i4.val = 15 := by
    rw [h7_zout, h_zeta_i3]; decide
  -- =============================================================
  -- Step 8: usize_mul 5 * 3328 = 16640.
  -- =============================================================
  obtain ⟨i16640, hi16640_eq, hi16640_val⟩ :=
    usize_mul_ok_eq_fc 5#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 9: layer_3 (zeta_i4=15, bnd=16640 Nat). → ≤ 19968. zeta_out=31.
  -- =============================================================
  have h_re4_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re4.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 16640 := by
    intro i hi j hj
    have hb := h7_bnd i hi j hj
    have h3328 : (3328#usize : Std.Usize).val = 3328 := by decide
    have h4 : (4#usize : Std.Usize).val = 4 := by decide
    rw [hi13312_val, h4, h3328] at hb
    omega
  obtain ⟨⟨zeta_i5, re5⟩, h9_eq, h9_fc, h9_zout, h9_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_3_portable_fc_strong zeta_i4 re4 i16640 16640
        (by decide) h_zeta_i4 h_re4_loose)
  dsimp only at h9_fc h9_zout h9_bnd
  -- =============================================================
  -- Step 10: usize_mul 6 * 3328 = 19968.
  -- =============================================================
  obtain ⟨i19968, hi19968_eq, hi19968_val⟩ :=
    usize_mul_ok_eq_fc 6#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 11: layer_2 (zeta_i5=31, bnd=19968 Nat). → ≤ 23296. zeta_out=63.
  -- =============================================================
  have h_re5_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re5.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 19968 := by
    intro i hi j hj
    have hb := h9_bnd i hi j hj
    omega
  obtain ⟨⟨zeta_i6, re6⟩, h11_eq, h11_fc, h11_zout, h11_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_2_portable_fc_strong zeta_i5 re5 i19968 19968
        (by decide) h9_zout h_re5_loose)
  dsimp only at h11_fc h11_zout h11_bnd
  -- =============================================================
  -- Step 12: usize_mul 7 * 3328 = 23296.
  -- =============================================================
  obtain ⟨i23296, hi23296_eq, hi23296_val⟩ :=
    usize_mul_ok_eq_fc 7#usize 3328#usize (by scalar_tac)
  -- =============================================================
  -- Step 13: layer_1 (zeta_i6=63, bnd=23296 Nat). → ≤ 26624. zeta_out=127.
  -- =============================================================
  have h_re6_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re6.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 23296 := by
    intro i hi j hj
    have hb := h11_bnd i hi j hj
    omega
  obtain ⟨⟨_zeta_i7, re7⟩, h13_eq, h13_fc, _h13_zout, h13_bnd⟩ :=
    triple_exists_ok_fc
      (ntt_at_layer_1_portable_fc_strong zeta_i6 re6 i23296 23296
        (by decide) h11_zout h_re6_loose)
  dsimp only at h13_fc h13_bnd
  -- =============================================================
  -- Step 14: poly_barrett_reduce. ≤ 26624 ≤ 32767 → canonical residue.
  -- =============================================================
  have h_re7_loose : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re7.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hc ℓ hℓ
    have hb := h13_bnd chunk hc ℓ hℓ
    omega
  obtain ⟨re8, h14_eq, h14_fc⟩ :=
    triple_exists_ok_fc (poly_barrett_reduce_fc re7 h_re7_loose)
  -- =============================================================
  -- Compose: derive the full impl `do`-block equation by simp-folding
  -- all step equations into the unfolded body.
  -- =============================================================
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_vector_u
        VECTOR_U_COMPRESSION_FACTOR
        (vectortraitsOperationsInst := portable_ops_inst) re scratch
        = .ok (re8, scratch4) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_vector_u
    simp [h1_eq, h3_eq, h5_eq, h7_eq, h9_eq, h11_eq, h13_eq, h14_eq,
          hi6656_eq, hi9984_eq, hi13312_eq,
          hi16640_eq, hi19968_eq, hi23296_eq]
  apply triple_of_ok_fc h_body
  -- =============================================================
  -- Prove lift_poly equation by chaining FC equations through Spec.ntt_pure_vec_u.
  -- =============================================================
  show lift_poly re8 = Spec.ntt_pure_vec_u (lift_poly re)
  unfold Spec.ntt_pure_vec_u
  -- Bridge barrett: h14_fc : poly_barrett_reduce (lift_poly re7) = .ok (lift_poly re8).
  have hB_bridge :
      hacspec_ml_kem.polynomial.poly_barrett_reduce (lift_poly re7)
        = .ok (Spec.Pure.polynomial.poly_barrett_reduce_pure (lift_poly re7)) :=
    Spec.Pure.polynomial.poly_barrett_reduce_eq_ok (lift_poly re7)
  rw [hB_bridge] at h14_fc
  have h_re8_eq : lift_poly re8
      = Spec.Pure.polynomial.poly_barrett_reduce_pure (lift_poly re7) := by
    have h := h14_fc
    exact (Aeneas.Std.Result.ok.injEq _ _).mp h.symm
  -- zeta_i identifications: substitute zeta values into the spec chain via .val.
  have h_zeta_eq1 : zeta_i1 = 1#usize := by
    have := h_zeta_i1; scalar_tac
  have h_zeta_eq2 : zeta_i2 = 3#usize := by
    have := h_zeta_i2; scalar_tac
  have h_zeta_eq3 : zeta_i3 = 7#usize := by
    have := h_zeta_i3; scalar_tac
  have h_zeta_eq4 : zeta_i4 = 15#usize := by
    have := h_zeta_i4; scalar_tac
  have h_zeta_eq5 : zeta_i5 = 31#usize := by
    have := h9_zout; scalar_tac
  have h_zeta_eq6 : zeta_i6 = 63#usize := by
    have := h11_zout; scalar_tac
  rw [h_re8_eq, h13_fc, h11_fc, h9_fc, h7_fc, h5_fc, h3_fc, h1_fc,
      h_zeta_eq1, h_zeta_eq2, h_zeta_eq3, h_zeta_eq4, h_zeta_eq5, h_zeta_eq6]

/-! ### L6.2.A — Loop scaffolding for `subtract_reduce_fc`.

    Strengthened FC invariant for the 16-iter chunk-loop. Each iteration
    `i ∈ 0..16` applies the fused chain
      `b[i] := barrett (negate ((mont_mul b[i] 1441) - self[i]))`
    leaving `b[j]` for `j ≠ i` untouched (and `self` immutable throughout).

    The chunk-level closure for chunk `i` is
      `lift_chunk b'[i] = Spec.chunk_subtract_reduce_pure
                            (lift_chunk self[i]) (lift_chunk b[i])`
    where `Spec.chunk_subtract_reduce_pure` (defined in §0.5) is the
    16-lane version of `self - b * lift_fe_mont(1441)`. -/


end libcrux_iot_ml_kem.InvertNtt
