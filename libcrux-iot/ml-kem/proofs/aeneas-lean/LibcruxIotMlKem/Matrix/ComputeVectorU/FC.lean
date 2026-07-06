/-
  # `Matrix/ComputeVectorU/FC.lean` — L7.2 FC theorem glue.

  Houses the L7.2 FC theorem `compute_vector_u_fc` — the top-level
  assembly gluing the impl walk (`compute_vector_u_loop0` row-0 column
  loop + `compute_vector_u_loop1` outer rows loop, both proven in
  `Impl/ComputeVectorU.lean`) to the hacspec `matrix.compute_vector_u`
  (transpose → multiply_matrix_by_column → createi(ntt_inverse) →
  add_vectors).

  Two added subtleties vs L7.4:
  * a vector output (K rows, two accumulation loops: row 0 fills the cache;
    rows 1..K consume it);
  * a hacspec part-A reduction `compute_vector_u_hacspec_eq` relating the
    hacspec do-block to the per-row `AllRowsFillFC.row_spec`. Because the
    Hacspec `extractCol`/`mcol_*` helpers are `private`, the
    matrix-column reduction is re-derived locally here.

  PRE strengthening: `hK ≤ 4`, lengths, per-lane bounds.
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.InvertNtt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Polynomial.PolyOpsFc
import LibcruxIotMlKem.Polynomial.NttMultiply
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeAsPlusE
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeMessage.Impl
import LibcruxIotMlKem.Matrix.ComputeVectorU.Impl
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec
import LibcruxIotMlKem.Matrix.ComputeVectorU.Hacspec

namespace libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec libcrux_iot_ml_kem.Matrix.ComputeVectorU.Impl
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-- Local copy of the `private triple_exists_ok_fc` helper. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Local copy of the `private triple_of_ok_fc` helper. -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## PART A — hacspec reduction.

    The Hacspec `extractCol`/`mcol_*` helpers + the public
    `multiply_matrix_by_column_at_eq_multiply_vectors` are usable only modulo
    the `private` `extractCol` they refer to. Since we cannot name/unfold the
    private `extractCol`, we RE-DERIVE the matrix-column reduction locally with
    a public-in-this-module copy `extractColL`, mirroring Hacspec
    `multiply_matrix_by_column_at_eq_mcol` / `multiply_vectors_eq_mcol`. -/

section PartA

open hacspec_ml_kem.parameters (FieldElement)
open Result ControlFlow

/-- Polynomial as a 256-lane field-element array. -/
private abbrev Poly256L := Std.Array FieldElement 256#usize

/-- Local copy of Hacspec `extractCol` (private there). -/
private noncomputable def extractColL {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K)
    (i : Std.Usize) : Std.Array Poly256L K :=
  Std.Array.make K ((List.range K.val).map (fun j => (m.val[j]!).val[i.val]!))
    (by simp [List.length_map, List.length_range])

private theorem extractColL_lane {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K)
    (i : Std.Usize) (j : Nat) (hj : j < K.val) :
    (extractColL m i).val[j]! = (m.val[j]!).val[i.val]! := by
  unfold extractColL
  show ((List.range K.val).map (fun j => (m.val[j]!).val[i.val]!))[j]! = _
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  simp [List.getElem_map, List.getElem_range]

/-- Local copy of Hacspec `mcol_lane_at_step`. -/
private noncomputable def mcolLane {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (k : Nat) (ℓ : Nat) : FieldElement :=
  (List.range k).foldl
    (fun s c =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
        ((Spec.multiply_ntts_pure (col.val[c]!) (vec.val[c]!)).val[ℓ]!))
    ({ val := 0#u16 } : FieldElement)

private noncomputable def mcolResult {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (k : Nat) : Poly256L :=
  ⟨(List.range 256).map (fun ℓ => mcolLane col vec k ℓ),
   by simp [List.length_map, List.length_range]⟩

private theorem mcolResult_val_lane {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (k : Nat) (ℓ : Nat) (hℓ : ℓ < 256) :
    (mcolResult col vec k).val[ℓ]! = mcolLane col vec k ℓ := by
  unfold mcolResult
  show ((List.range 256).map (fun ℓ' => mcolLane col vec k ℓ'))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]

private theorem mcolLane_zero {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (ℓ : Nat) :
    mcolLane col vec 0 ℓ = ({ val := 0#u16 } : FieldElement) := by
  unfold mcolLane; rw [List.range_zero, List.foldl_nil]

private theorem mcolLane_succ {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (k : Nat) (ℓ : Nat) :
    mcolLane col vec (k + 1) ℓ
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (mcolLane col vec k ℓ)
          ((Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[ℓ]!) := by
  unfold mcolLane
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem mcol_mult_eq (a1 a2 : Poly256L) :
    hacspec_ml_kem.ntt.multiply_ntts a1 a2 = .ok (Spec.multiply_ntts_pure a1 a2) := by
  unfold Spec.multiply_ntts_pure
  rw [HelpersFC.multiply_ntts_eq_pure_array]

private theorem mcol_step_add_eq {K : Std.Usize}
    (col vec : Std.Array Poly256L K) (k : Nat) :
    hacspec_ml_kem.matrix.add_polynomials (mcolResult col vec k)
        (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!))
      = .ok (mcolResult col vec (k + 1)) := by
  rw [Stage4MatrixAddFC.matrix_add_polynomials_eq_ok]
  apply congrArg Result.ok
  apply Subtype.ext
  show (List.range 256).map (fun n =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (mcolResult col vec k).val[n]!
        (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[n]!)
    = (mcolResult col vec (k + 1)).val
  unfold mcolResult
  apply List.map_congr_left
  intro n hn_mem
  have hn_lt : n < 256 := List.mem_range.mp hn_mem
  show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
      (mcolResult col vec k).val[n]!
      (Spec.multiply_ntts_pure (col.val[k]!) (vec.val[k]!)).val[n]!
    = mcolLane col vec (k + 1) n
  rw [mcolResult_val_lane _ _ _ _ hn_lt, mcolLane_succ]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- Local copy of Hacspec `multiply_vectors_eq_mcol`. -/
private theorem multiply_vectors_eq_mcolL {K : Std.Usize}
    (col vec : Std.Array Poly256L K) :
    hacspec_ml_kem.matrix.multiply_vectors col vec
      = .ok (mcolResult col vec K.val) := by
  unfold hacspec_ml_kem.matrix.multiply_vectors
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_vectors_loop
        ({ start := 0#usize, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        col vec
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
      ⦃ ⇓ r => ⌜ r = mcolResult col vec K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_vectors_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
          hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
        (β := Poly256L)
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
        0#usize K
        (fun k result => pure (result = mcolResult col vec k.val))
        (Nat.zero_le _)
        (by
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold mcolResult
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = mcolLane col vec 0 n
          rw [mcolLane_zero])
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = mcolResult col vec K.val) : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · intro acc k _h_ge h_le hinv
      have h_acc_eq : acc = mcolResult col vec k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
      by_cases h_lt : k.val < K.val
      · have h_iter_step :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                        r = (some k, ({ start := s, «end» := K }
                              : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun _ s hs => by
              dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
              exact ⟨s, hs, rfl⟩)
            (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
        obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
        have hlen_col : col.length = K.val := Std.Array.length_eq col
        have hlen_vec : vec.length = K.val := Std.Array.length_eq vec
        have h_idx_a1 : Aeneas.Std.Array.index_usize col k = .ok (col.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq col k
            (by rw [hlen_col]; exact h_lt)
        have h_idx_a2 : Aeneas.Std.Array.index_usize vec k = .ok (vec.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec k
            (by rw [hlen_vec]; exact h_lt)
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
              ({ start := k, «end» := K }, mcolResult col vec k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  mcolResult col vec (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec
                { start := k, «end» := K } (mcolResult col vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
          conv_lhs =>
            rw [show
              (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_pair] at hv_iter_eq
          rw [hv_iter_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          show ((do
                  let a ← Aeneas.Std.Array.index_usize col k
                  let a1' ← Aeneas.Std.Array.index_usize vec k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a a1'
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (mcolResult col vec k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
          rw [h_idx_a1]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a2]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_mult_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_step_add_eq]
          simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_fc h_body
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (mcolResult col vec (k.val + 1)
                      = mcolResult col vec s_iter.val) : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
      · have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
        have hk_eq : k.val = K.val := by omega
        have h_iter_none :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ r = ((none : Option Std.Usize),
                              ({ start := k, «end» := K }
                                : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun hlt => absurd hlt (Nat.not_lt.mpr hk_ge))
            (fun _ => by dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_none
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec p.1 p.2)
              ({ start := k, «end» := K }, mcolResult col vec k.val)
            = .ok (ControlFlow.done (mcolResult col vec k.val)) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body col vec
                { start := k, «end» := K } (mcolResult col vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
          conv_lhs =>
            rw [show
              (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_post] at hv_iter_eq
          rw [hv_iter_eq]
          rfl
        apply triple_of_ok_fc h_body
        show (pure (mcolResult col vec k.val
                      = mcolResult col vec K.val) : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  obtain ⟨v, hv_eq, hv_post⟩ := triple_exists_ok_fc h_triple
  rw [hv_eq, hv_post]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- Local copy of Hacspec `multiply_matrix_by_column_at_eq_mcol`. -/
private theorem mmbc_at_eq_mcolL {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K)
    (vec : Std.Array Poly256L K) (i : Std.Usize)
    (hi : i.val < K.val) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column_at m vec i
      = .ok (mcolResult (extractColL m i) vec K.val) := by
  unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
        ({ start := 0#usize, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        m vec i
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
      ⦃ ⇓ r => ⌜ r = mcolResult (extractColL m i) vec K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
          hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
        (β := Poly256L)
        (Std.Array.repeat (256#usize : Std.Usize) ({ val := 0#u16 } : FieldElement))
        0#usize K
        (fun k result => pure (result = mcolResult (extractColL m i) vec k.val))
        (Nat.zero_le _)
        (by
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold mcolResult
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = mcolLane (extractColL m i) vec 0 n
          rw [mcolLane_zero])
        ?_)
    · rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = mcolResult (extractColL m i) vec K.val)
                  : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · intro acc k _h_ge h_le hinv
      have h_acc_eq : acc = mcolResult (extractColL m i) vec k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
      by_cases h_lt : k.val < K.val
      · have h_iter_step :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                        r = (some k, ({ start := s, «end» := K }
                              : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun _ s hs => by
              dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
              exact ⟨s, hs, rfl⟩)
            (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
        obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
        have hlen_m : m.length = K.val := Std.Array.length_eq m
        have hlen_vec : vec.length = K.val := Std.Array.length_eq vec
        have hlen_mk : (m.val[k.val]!).length = K.val := Std.Array.length_eq (m.val[k.val]!)
        have h_idx_mk : Aeneas.Std.Array.index_usize m k = .ok (m.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq m k
            (by rw [hlen_m]; exact h_lt)
        have h_col_eq : (extractColL m i).val[k.val]! = (m.val[k.val]!).val[i.val]! :=
          extractColL_lane m i k.val h_lt
        have h_idx_a1 :
            Aeneas.Std.Array.index_usize (m.val[k.val]!) i = .ok ((extractColL m i).val[k.val]!) := by
          rw [h_col_eq]
          exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (m.val[k.val]!) i
            (by rw [hlen_mk]; exact hi)
        have h_idx_a2 : Aeneas.Std.Array.index_usize vec k = .ok (vec.val[k.val]!) :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq vec k
            (by rw [hlen_vec]; exact h_lt)
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
              ({ start := k, «end» := K }, mcolResult (extractColL m i) vec k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  mcolResult (extractColL m i) vec (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i
                { start := k, «end» := K }
                (mcolResult (extractColL m i) vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_pair] at hv_iter_eq
          rw [hv_iter_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          show ((do
                  let a ← Aeneas.Std.Array.index_usize m k
                  let a1 ← Aeneas.Std.Array.index_usize a i
                  let a2 ← Aeneas.Std.Array.index_usize vec k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a1 a2
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (mcolResult (extractColL m i) vec k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
          rw [h_idx_mk]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a1]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a2]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_mult_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [mcol_step_add_eq]
          simp only [Aeneas.Std.bind_tc_ok]
        apply triple_of_ok_fc h_body
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (mcolResult (extractColL m i) vec (k.val + 1)
                      = mcolResult (extractColL m i) vec s_iter.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
      · have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
        have hk_eq : k.val = K.val := by omega
        have h_iter_none :
            ⦃ ⌜ True ⌝ ⦄
            CoreModels.core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ r = ((none : Option Std.Usize),
                              ({ start := k, «end» := K }
                                : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun hlt => absurd hlt (Nat.not_lt.mpr hk_ge))
            (fun _ => by dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_none
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize × Poly256L =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i p.1 p.2)
              ({ start := k, «end» := K }, mcolResult (extractColL m i) vec k.val)
            = .ok (ControlFlow.done (mcolResult (extractColL m i) vec k.val)) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body m vec i
                { start := k, «end» := K }
                (mcolResult (extractColL m i) vec k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (CoreModels.core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
                  core.Usize.Insts.CoreIterRangeStep
                  ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize))
                = (CoreModels.core.iter.range.IteratorRange.next
                    core.Usize.Insts.CoreIterRangeStep
                    ({ start := k, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize))
              from rfl]
          rw [hv_iter_post] at hv_iter_eq
          rw [hv_iter_eq]
          rfl
        apply triple_of_ok_fc h_body
        show (pure (mcolResult (extractColL m i) vec k.val
                      = mcolResult (extractColL m i) vec K.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  obtain ⟨v, hv_eq, hv_post⟩ := triple_exists_ok_fc h_triple
  rw [hv_eq, hv_post]

/-- `multiply_matrix_by_column_at m vec i = multiply_vectors (extractColL m i) vec`. -/
private theorem mmbc_at_eq_multiply_vectorsL {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K)
    (vec : Std.Array Poly256L K)
    (i : Std.Usize) (hi : i.val < K.val) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column_at m vec i
      = hacspec_ml_kem.matrix.multiply_vectors (extractColL m i) vec := by
  rw [mmbc_at_eq_mcolL m vec i hi, multiply_vectors_eq_mcolL]

/-! ### transpose reduction. -/

/-- `BitVec.ofNat.toNat = k` for `k < K.val`. -/
private theorem ofNat_toNat_eq {K : Std.Usize} (k : Nat) (hk : k < K.val) :
    (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
  show (BitVec.ofNat _ k).toNat = k
  apply Nat.mod_eq_of_lt
  have hK_lt : K.val < 2^System.Platform.numBits := by
    have h := K.hBounds
    simp at h
    omega
  exact Nat.lt_of_lt_of_le hk (Nat.le_of_lt hK_lt)

/-- The inner transpose closure (`createi RANK closure (m,j)`) builds the
    column-`j` vector: lane `i'` is `m[i'][j]`. -/
private theorem transpose_inner_eq {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K) (j : Std.Usize) (hj : j.val < K.val) :
    hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayArrayFieldElement256RANK.call
        (RANK := K) (m) j
      = .ok ⟨(List.range K.val).map (fun i' => (m.val[i']!).val[j.val]!),
             by simp [List.length_map, List.length_range]⟩ := by
  unfold hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayArrayFieldElement256RANK.call
  show hacspec_ml_kem.parameters.createi K
      (hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K)
      (m, j) = _
  unfold hacspec_ml_kem.parameters.createi
  have hpure : ∀ i' : Nat, i' < K.val →
      (hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K).FnMutInst.call_mut
        (m, j) ⟨BitVec.ofNat _ i'⟩
        = .ok ((m.val[i']!).val[j.val]!, (m, j)) := by
    intro i' hi'
    show hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
        (m, j) ⟨BitVec.ofNat _ i'⟩
      = .ok ((m.val[i']!).val[j.val]!, (m, j))
    unfold hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    have hi'_val : (⟨BitVec.ofNat _ i'⟩ : Std.Usize).val = i' := ofNat_toNat_eq i' hi'
    have hlen_m : m.length = K.val := Std.Array.length_eq m
    have hlen_mi : (m.val[i']!).length = K.val := Std.Array.length_eq (m.val[i']!)
    have h_idx_m : Std.Array.index_usize m (⟨BitVec.ofNat _ i'⟩ : Std.Usize)
                    = .ok (m.val[i']!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq m (⟨BitVec.ofNat _ i'⟩ : Std.Usize)
                (by rw [hi'_val, hlen_m]; exact hi')
      rw [hi'_val] at this; exact this
    have h_idx_mi : Std.Array.index_usize (m.val[i']!) j
                    = .ok ((m.val[i']!).val[j.val]!) :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (m.val[i']!) j
        (by rw [hlen_mi]; exact hj)
    change (do
            let a ← (do
              let a1 ← Std.Array.index_usize m (⟨BitVec.ofNat _ i'⟩ : Std.Usize)
              Std.Array.index_usize a1 j)
            .ok (a, m, j)) = .ok ((m.val[i']!).val[j.val]!, (m, j))
    rw [h_idx_m]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_mi]; simp only [Aeneas.Std.bind_tc_ok]
  have h := libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq
    (T := Poly256L)
    (F := hacspec_ml_kem.matrix.transpose.closure.closure K)
    (N := K)
    (inst := hacspec_ml_kem.matrix.transpose.closure.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K)
    (c := (m, j))
    (f := fun i' => (m.val[i']!).val[j.val]!)
    hpure
  exact h

/-- `(transpose m).val[j]! = column j of m` (for `j < K`). -/
private theorem transpose_row_eq {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K) :
    hacspec_ml_kem.matrix.transpose m
      = .ok ⟨(List.range K.val).map (fun j =>
              (⟨(List.range K.val).map (fun i' => (m.val[i']!).val[j]!),
                by simp [List.length_map, List.length_range]⟩ : Std.Array Poly256L K)),
             by simp [List.length_map, List.length_range]⟩ := by
  unfold hacspec_ml_kem.matrix.transpose
  unfold hacspec_ml_kem.parameters.createi
  set f : Nat → Std.Array Poly256L K :=
    fun j => ⟨(List.range K.val).map (fun i' => (m.val[i']!).val[j]!),
              by simp [List.length_map, List.length_range]⟩ with hf_def
  have hpure : ∀ j : Nat, j < K.val →
      (hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayArrayFieldElement256RANK K).FnMutInst.call_mut
        (m) ⟨BitVec.ofNat _ j⟩
        = .ok (f j, m) := by
    intro j hj
    show hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayArrayFieldElement256RANK.call_mut
        (m) ⟨BitVec.ofNat _ j⟩ = .ok (f j, m)
    unfold hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayArrayFieldElement256RANK.call_mut
    have hj_val : (⟨BitVec.ofNat _ j⟩ : Std.Usize).val = j := ofNat_toNat_eq j hj
    have h_inner := transpose_inner_eq m (⟨BitVec.ofNat _ j⟩ : Std.Usize) (by rw [hj_val]; exact hj)
    show (do let a ← hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayArrayFieldElement256RANK.call
                (RANK := K) m (⟨BitVec.ofNat _ j⟩ : Std.Usize)
             .ok (a, m)) = .ok (f j, m)
    rw [h_inner]; simp only [Aeneas.Std.bind_tc_ok]
    rw [hf_def, hj_val]
  have h := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
    (T := Std.Array Poly256L K)
    (F := hacspec_ml_kem.matrix.transpose.closure K)
    (N := K)
    (inst := (hacspec_ml_kem.matrix.transpose.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayArrayFieldElement256RANK K).FnMutInst)
    (c := m)
    (f := f)
    hpure
  show core.array.from_fn K _ _ = _
  rw [h]

/-- `extractColL (transpose m) i = m.val[i]!` for `i < K`. -/
private theorem extractColL_transpose_eq {K : Std.Usize}
    (m : Std.Array (Std.Array Poly256L K) K) (i : Std.Usize) (hi : i.val < K.val) :
    ∃ T, hacspec_ml_kem.matrix.transpose m = .ok T ∧ extractColL T i = m.val[i.val]! := by
  refine ⟨_, transpose_row_eq m, ?_⟩
  set T : Std.Array (Std.Array Poly256L K) K :=
    ⟨(List.range K.val).map (fun j =>
        (⟨(List.range K.val).map (fun i' => (m.val[i']!).val[j]!),
          by simp [List.length_map, List.length_range]⟩ : Std.Array Poly256L K)),
       by simp [List.length_map, List.length_range]⟩ with hT_def
  -- T.val[j]!.val[i]! = m.val[i]!.val[j]!
  have hT_at : ∀ j : Nat, j < K.val →
      (T.val[j]!).val[i.val]! = (m.val[i.val]!).val[j]! := by
    intro j hj
    have h1 : T.val[j]! = (⟨(List.range K.val).map (fun i' => (m.val[i']!).val[j]!),
                by simp [List.length_map, List.length_range]⟩ : Std.Array Poly256L K) := by
      rw [hT_def]
      show ((List.range K.val).map _)[j]! = _
      rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
      rw [List.getElem_map, List.getElem_range]
    rw [h1]
    show ((List.range K.val).map (fun i' => (m.val[i']!).val[j]!))[i.val]! = _
    rw [getElem!_pos _ i.val (by simp [List.length_map, List.length_range, hi])]
    rw [List.getElem_map, List.getElem_range]
  -- extractColL T i = m[i] by Subtype.ext + List.ext_getElem.
  apply Subtype.ext
  show ((List.range K.val).map (fun j => (T.val[j]!).val[i.val]!)) = (m.val[i.val]!).val
  have hmi_len : (m.val[i.val]!).val.length = K.val := by
    have := Std.Array.length_eq (m.val[i.val]!)
    exact this
  apply List.ext_getElem
  · rw [List.length_map, List.length_range, hmi_len]
  · intro j hj1 _
    have hj : j < K.val := by
      have : j < ((List.range K.val).map _).length := hj1
      simpa [List.length_map, List.length_range] using this
    rw [List.getElem_map, List.getElem_range]
    rw [hT_at j hj]
    rw [getElem!_pos (m.val[i.val]!).val j (by rw [hmi_len]; exact hj)]

/-! ### createi-stage reduction for the hacspec `compute_vector_u`. -/

/-- `Result.ok`-extraction (default on non-ok); used to give `createi` a total
    index function from per-index `.ok`-ness. -/
private def resGet {α : Type} [Inhabited α] : Result α → α
  | .ok v => v
  | _ => default

private theorem resGet_ok {α : Type} [Inhabited α] {x : Result α} {v : α}
    (h : x = .ok v) : x = .ok (resGet x) := by
  rw [h]; rfl

/-- A `createi` whose per-index closure op is `g i` (when `g i = .ok …`) yields
    `.ok ⟨map (resGet ∘ g)⟩`. Specialized to closures of the shape used by the
    hacspec `compute_vector_u` stages (mmbc / ntt_inverse / add_vectors), where
    `call_mut c ⟨k⟩ = (do let a ← g k; ok (a, c))`. -/
private theorem createi_stage_eq {K : Std.Usize} {T F : Type} [Inhabited T]
    (inst : CoreModels.core.ops.function.Fn F Std.Usize T) (c : F)
    (g : Nat → Result T)
    (hcall : ∀ k : Nat, k < K.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = (do let a ← g k; .ok (a, c)))
    (hok : ∀ k : Nat, k < K.val → ∃ v, g k = .ok v) :
    hacspec_ml_kem.parameters.createi K inst c
      = .ok ⟨(List.range K.val).map (fun k => resGet (g k)),
             by simp [List.length_map, List.length_range]⟩ := by
  unfold hacspec_ml_kem.parameters.createi
  have hpure : ∀ k : Nat, k < K.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (resGet (g k), c) := by
    intro k hk
    rw [hcall k hk]
    obtain ⟨v, hv⟩ := hok k hk
    rw [hv]; rfl
  exact libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq K inst.FnMutInst c
    (fun k => resGet (g k)) hpure

private theorem array_make_lane {K : Std.Usize} {α : Type} [Inhabited α]
    (l : List α) (h : l.length = K.val) (i : Nat) (hi : i < K.val) :
    (Std.Array.make K l h).val[i]! = l[i]! := rfl

/-- Lane of a `(List.range K).map f` array at `i < K`. -/
private theorem range_map_lane {α : Type} [Inhabited α]
    (K : Nat) (f : Nat → α) (i : Nat) (hi : i < K) :
    ((List.range K).map f)[i]! = f i := by
  rw [getElem!_pos _ i (by simp [List.length_map, List.length_range, hi])]
  rw [List.getElem_map, List.getElem_range]

set_option maxHeartbeats 1600000 in
/-- **PART A.** The hacspec `compute_vector_u lm rvec evec` reduces to a vector
    `W` whose row `i` is the per-row `multiply_vectors lm[i] rvec → ntt_inverse →
    add_polynomials (·) evec[i]` chain. Stages reduced via `createi_stage_eq`. -/
private theorem compute_vector_u_hacspec_eq {K : Std.Usize}
    (lm : Std.Array (Std.Array Poly256L K) K)
    (rvec evec : Std.Array Poly256L K)
    (W : Std.Array Poly256L K)
    (hWlen : W.length = K.val)
    (hrow : ∀ i : Nat, i < K.val →
      (do
        let prod ← hacspec_ml_kem.matrix.multiply_vectors (lm.val[i]!) rvec
        let inv ← hacspec_ml_kem.invert_ntt.ntt_inverse prod
        hacspec_ml_kem.matrix.add_polynomials inv (evec.val[i]!))
        = .ok (W.val[i]!)) :
    hacspec_ml_kem.matrix.compute_vector_u lm rvec evec = .ok W := by
  unfold hacspec_ml_kem.matrix.compute_vector_u
  -- per-row witnesses: prodᵢ, invᵢ from `hrow`.
  have hprod_ok : ∀ i : Nat, i < K.val →
      ∃ p, hacspec_ml_kem.matrix.multiply_vectors (lm.val[i]!) rvec = .ok p := by
    intro i hi
    have h := hrow i hi
    match hmv : hacspec_ml_kem.matrix.multiply_vectors (lm.val[i]!) rvec with
    | .ok p => exact ⟨p, rfl⟩
    | .fail e => rw [hmv] at h; simp only [Aeneas.Std.bind_tc_fail] at h; exact absurd h (by simp)
    | .div => rw [hmv] at h; simp only [Aeneas.Std.bind_tc_div] at h; exact absurd h (by simp)
  -- Stage 0: transpose lm = .ok T, extractColL T i = lm[i].
  -- (transpose_row_eq gives a concrete T; we use a generic T below.)
  -- Stage 1: multiply_matrix_by_column T rvec.
  set T : Std.Array (Std.Array Poly256L K) K :=
    ⟨(List.range K.val).map (fun j =>
        (⟨(List.range K.val).map (fun i' => (lm.val[i']!).val[j]!),
          by simp [List.length_map, List.length_range]⟩ : Std.Array Poly256L K)),
       by simp [List.length_map, List.length_range]⟩ with hT_def
  have hT_eq : hacspec_ml_kem.matrix.transpose lm = .ok T := transpose_row_eq lm
  have hcolT : ∀ i : Nat, i < K.val →
      extractColL T (⟨BitVec.ofNat _ i⟩ : Std.Usize) = lm.val[i]! := by
    intro i hi
    obtain ⟨T', hT'_eq, hcol⟩ := extractColL_transpose_eq lm (⟨BitVec.ofNat _ i⟩ : Std.Usize)
      (by rw [ofNat_toNat_eq i hi]; exact hi)
    rw [hT_eq] at hT'_eq
    have : T' = T := (Result.ok.inj hT'_eq).symm
    rw [this] at hcol
    rw [hcol, ofNat_toNat_eq i hi]
  rw [hT_eq]; simp only [Aeneas.Std.bind_tc_ok]
  -- product := multiply_matrix_by_column T rvec, reduced via createi_stage_eq.
  set g_prod : Nat → Result Poly256L :=
    fun k => hacspec_ml_kem.matrix.multiply_matrix_by_column_at T rvec ⟨BitVec.ofNat _ k⟩
    with hg_prod_def
  have hg_prod_ok : ∀ k : Nat, k < K.val → ∃ v, g_prod k = .ok v := by
    intro k hk
    show ∃ v, hacspec_ml_kem.matrix.multiply_matrix_by_column_at T rvec
                (⟨BitVec.ofNat _ k⟩ : Std.Usize) = .ok v
    have hkv : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := ofNat_toNat_eq k hk
    rw [mmbc_at_eq_multiply_vectorsL T rvec ⟨BitVec.ofNat _ k⟩ (by rw [hkv]; exact hk)]
    rw [hcolT k hk]
    exact hprod_ok k hk
  have h_prod_stage :
      hacspec_ml_kem.matrix.multiply_matrix_by_column T rvec
        = .ok ⟨(List.range K.val).map (fun k => resGet (g_prod k)),
               by simp [List.length_map, List.length_range]⟩ := by
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column
    apply createi_stage_eq _ _ g_prod _ hg_prod_ok
    intro k hk
    show hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
        (T, rvec) ⟨BitVec.ofNat _ k⟩ = (do let a ← g_prod k; .ok (a, (T, rvec)))
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    rfl
  rw [h_prod_stage]; simp only [Aeneas.Std.bind_tc_ok]
  set P : Std.Array Poly256L K :=
    ⟨(List.range K.val).map (fun k => resGet (g_prod k)),
     by simp [List.length_map, List.length_range]⟩ with hP_def
  have hP_at : ∀ i : Nat, i < K.val → P.val[i]! = resGet (g_prod i) := by
    intro i hi; rw [hP_def]; exact range_map_lane K.val _ i hi
  -- Stage 2: createi(ntt_inverse) P.
  set g_inv : Nat → Result Poly256L :=
    fun k => hacspec_ml_kem.invert_ntt.ntt_inverse (P.val[k]!) with hg_inv_def
  have hg_inv_ok : ∀ k : Nat, k < K.val → ∃ v, g_inv k = .ok v := by
    intro k hk
    show ∃ v, hacspec_ml_kem.invert_ntt.ntt_inverse (P.val[k]!) = .ok v
    rw [hP_at k hk]
    -- resGet (g_prod k) = prodₖ, and ntt_inverse prodₖ succeeds by hrow.
    obtain ⟨p, hp⟩ := hprod_ok k hk
    have hgp : g_prod k = .ok p := by
      show hacspec_ml_kem.matrix.multiply_matrix_by_column_at T rvec (⟨BitVec.ofNat _ k⟩ : Std.Usize) = .ok p
      rw [mmbc_at_eq_multiply_vectorsL T rvec ⟨BitVec.ofNat _ k⟩
            (by rw [ofNat_toNat_eq k hk]; exact hk), hcolT k hk]; exact hp
    rw [hgp]
    show ∃ v, hacspec_ml_kem.invert_ntt.ntt_inverse p = .ok v
    have h := hrow k hk
    rw [hp] at h; simp only [Aeneas.Std.bind_tc_ok] at h
    match hni : hacspec_ml_kem.invert_ntt.ntt_inverse p with
    | .ok q => exact ⟨q, rfl⟩
    | .fail e => rw [hni] at h; simp only [Aeneas.Std.bind_tc_fail] at h; exact absurd h (by simp)
    | .div => rw [hni] at h; simp only [Aeneas.Std.bind_tc_div] at h; exact absurd h (by simp)
  have h_inv_stage :
      hacspec_ml_kem.parameters.createi K
          (hacspec_ml_kem.matrix.compute_vector_u.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K) P
        = .ok ⟨(List.range K.val).map (fun k => resGet (g_inv k)),
               by simp [List.length_map, List.length_range]⟩ := by
    apply createi_stage_eq _ _ g_inv _ hg_inv_ok
    intro k hk
    show hacspec_ml_kem.matrix.compute_vector_u.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
        P ⟨BitVec.ofNat _ k⟩ = (do let a ← g_inv k; .ok (a, P))
    unfold hacspec_ml_kem.matrix.compute_vector_u.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.compute_vector_u.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    have hkv : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := ofNat_toNat_eq k hk
    have h_idx_P : Std.Array.index_usize P (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                    = .ok (P.val[k]!) := by
      have hPlen : P.length = K.val := by
        rw [hP_def]; show ((List.range K.val).map _).length = K.val
        simp [List.length_map, List.length_range]
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq P (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                (by rw [hkv, hPlen]; exact hk)
      rw [hkv] at this; exact this
    rw [hg_inv_def]
    show (do let a ← Std.Array.index_usize P (⟨BitVec.ofNat _ k⟩ : Std.Usize)
             hacspec_ml_kem.invert_ntt.ntt_inverse a) >>= (fun a => .ok (a, P))
       = (do let a ← hacspec_ml_kem.invert_ntt.ntt_inverse (P.val[k]!); .ok (a, P))
    rw [h_idx_P]; simp only [Aeneas.Std.bind_tc_ok]
  rw [h_inv_stage]; simp only [Aeneas.Std.bind_tc_ok]
  set PI : Std.Array Poly256L K :=
    ⟨(List.range K.val).map (fun k => resGet (g_inv k)),
     by simp [List.length_map, List.length_range]⟩ with hPI_def
  have hPI_at : ∀ i : Nat, i < K.val → PI.val[i]! = resGet (g_inv i) := by
    intro i hi; rw [hPI_def]; exact range_map_lane K.val _ i hi
  -- Stage 3: add_vectors PI evec = .ok W.
  set g_add : Nat → Result Poly256L :=
    fun k => hacspec_ml_kem.matrix.add_polynomials (PI.val[k]!) (evec.val[k]!) with hg_add_def
  have hg_add_ok : ∀ k : Nat, k < K.val → g_add k = .ok (W.val[k]!) := by
    intro k hk
    show hacspec_ml_kem.matrix.add_polynomials (PI.val[k]!) (evec.val[k]!) = .ok (W.val[k]!)
    -- PI[k] = invₖ; combine the chain.
    obtain ⟨p, hp⟩ := hprod_ok k hk
    have hgp : g_prod k = .ok p := by
      show hacspec_ml_kem.matrix.multiply_matrix_by_column_at T rvec (⟨BitVec.ofNat _ k⟩ : Std.Usize) = .ok p
      rw [mmbc_at_eq_multiply_vectorsL T rvec ⟨BitVec.ofNat _ k⟩
            (by rw [ofNat_toNat_eq k hk]; exact hk), hcolT k hk]; exact hp
    have h := hrow k hk
    rw [hp] at h; simp only [Aeneas.Std.bind_tc_ok] at h
    -- ntt_inverse p = .ok q for some q.
    obtain ⟨q, hq⟩ : ∃ q, hacspec_ml_kem.invert_ntt.ntt_inverse p = .ok q := by
      match hni : hacspec_ml_kem.invert_ntt.ntt_inverse p with
      | .ok q => exact ⟨q, rfl⟩
      | .fail e => rw [hni] at h; simp only [Aeneas.Std.bind_tc_fail] at h; exact absurd h (by simp)
      | .div => rw [hni] at h; simp only [Aeneas.Std.bind_tc_div] at h; exact absurd h (by simp)
    have hPIk : PI.val[k]! = q := by
      rw [hPI_at k hk]
      show resGet (g_inv k) = q
      show resGet (hacspec_ml_kem.invert_ntt.ntt_inverse (P.val[k]!)) = q
      rw [hP_at k hk]
      show resGet (hacspec_ml_kem.invert_ntt.ntt_inverse (resGet (g_prod k))) = q
      rw [hgp]
      show resGet (hacspec_ml_kem.invert_ntt.ntt_inverse p) = q
      rw [hq]; rfl
    rw [hPIk]
    rw [hq] at h; simp only [Aeneas.Std.bind_tc_ok] at h
    exact h
  have hcall_add : ∀ k : Nat, k < K.val →
      (hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K).FnMutInst.call_mut
        (PI, evec) ⟨BitVec.ofNat _ k⟩ = (do let a ← g_add k; .ok (a, (PI, evec))) := by
    intro k hk
    show hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
        (PI, evec) ⟨BitVec.ofNat _ k⟩ = (do let a ← g_add k; .ok (a, (PI, evec)))
    unfold hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    have hkv : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := ofNat_toNat_eq k hk
    have hPIlen : PI.length = K.val := by
      rw [hPI_def]; show ((List.range K.val).map _).length = K.val
      simp [List.length_map, List.length_range]
    have hElen : evec.length = K.val := Std.Array.length_eq evec
    have h_idx_PI : Std.Array.index_usize PI (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                    = .ok (PI.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq PI (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                (by rw [hkv, hPIlen]; exact hk)
      rw [hkv] at this; exact this
    have h_idx_E : Std.Array.index_usize evec (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                    = .ok (evec.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq evec (⟨BitVec.ofNat _ k⟩ : Std.Usize)
                (by rw [hkv, hElen]; exact hk)
      rw [hkv] at this; exact this
    show (do let a2 ← Std.Array.index_usize PI (⟨BitVec.ofNat _ k⟩ : Std.Usize)
             let a3 ← Std.Array.index_usize evec (⟨BitVec.ofNat _ k⟩ : Std.Usize)
             hacspec_ml_kem.matrix.add_polynomials a2 a3) >>= (fun a => .ok (a, (PI, evec)))
       = (do let a ← hacspec_ml_kem.matrix.add_polynomials (PI.val[k]!) (evec.val[k]!)
             .ok (a, (PI, evec)))
    rw [h_idx_PI]; simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_E]; simp only [Aeneas.Std.bind_tc_ok]
  have h_add_stage :
      hacspec_ml_kem.matrix.add_vectors PI evec = .ok W := by
    unfold hacspec_ml_kem.matrix.add_vectors
    rw [createi_stage_eq _ _ g_add hcall_add (fun k hk => ⟨W.val[k]!, hg_add_ok k hk⟩)]
    apply congrArg Result.ok
    apply Subtype.ext
    show (List.range K.val).map (fun k => resGet (g_add k)) = W.val
    have hWval_len : W.val.length = K.val := by
      have := Std.Array.length_eq W; exact this
    apply List.ext_getElem
    · rw [List.length_map, List.length_range, hWval_len]
    · intro k hk1 _
      have hk : k < K.val := by
        have : k < ((List.range K.val).map _).length := hk1
        simpa [List.length_map, List.length_range] using this
      rw [List.getElem_map, List.getElem_range]
      rw [show resGet (g_add k) = resGet (.ok (W.val[k]!)) from by rw [hg_add_ok k hk]]
      show W.val[k]! = W.val[k]
      rw [getElem!_pos W.val k (by rw [hWval_len]; exact hk)]
  exact h_add_stage

/-- Lane of `lift_vec_slice v K` at `i < K`. -/
private theorem lift_vec_slice_lane
    (v : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (K : Std.Usize) (i : Nat) (hi : i < K.val) :
    (lift_vec_slice v K).val[i]! = lift_poly v.val[i]! := by
  show (Std.Array.make K ((List.range K.val).map (fun i => lift_poly v.val[i]!)) (by simp)).val[i]!
      = lift_poly v.val[i]!
  show ((List.range K.val).map (fun i => lift_poly v.val[i]!))[i]! = lift_poly v.val[i]!
  exact range_map_lane K.val _ i hi

end PartA

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do

set_option maxHeartbeats 3200000 in
/-- **L7.2 MAIN theorem.** The top-level `matrix.compute_vector_u` glue.
    PRE: `hK : K.val ≤ 4`, `h_K_pos : 1 ≤ K.val`, slice lengths, and per-lane
    bounds on `r_as_ntt` (≤ 3328) / `error_1` (≤ 29439). Mirrors L7.4's
    `compute_message_fc` glue + the impl `matrix.compute_vector_u` body. -/
@[spec]
theorem compute_vector_u_fc
    {Hasher : Type} (K : Std.Usize)
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (seed : Slice Std.U8)
    (r_as_ntt error_1 result : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (cache : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (accumulator : Std.Array Std.I32 256#usize)
    (hK : K.val ≤ 4)
    (h_K_pos : 1 ≤ K.val)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_err_len : error_1.length = K.val)
    (h_result_len : result.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_err_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((error_1.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u
      K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      matrix_entry seed r_as_ntt error_1 result scratch cache accumulator
    ⦃ ⇓ p => ⌜ ∃ spec_out,
                  hacspec_ml_kem.matrix.compute_vector_u
                    (lift_matrix_from_seed seed K)
                    (lift_vec_slice r_as_ntt K)
                    (lift_vec_slice error_1 K)
                  = .ok spec_out
                ∧ VecMatches p.2.1.val spec_out ⌝ ⦄ := by
  set lm : Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
    lift_matrix_from_seed seed K with hlm_def
  -- massert lengths.
  have h_len_r : core.slice.Slice.len r_as_ntt = .ok K := by
    unfold core.slice.Slice.len
    apply congrArg Result.ok
    apply Std.UScalar.eq_of_val_eq
    show r_as_ntt.val.length = K.val
    exact h_r_len
  have h_len_e : core.slice.Slice.len error_1 = .ok K := by
    unfold core.slice.Slice.len
    apply congrArg Result.ok
    apply Std.UScalar.eq_of_val_eq
    show error_1.val.length = K.val
    exact h_err_len
  -- Step 0: i2 := classify 0 = 0#i32; acc1 := repeat 256 0.
  set i2 : Std.I32 := 0#i32 with hi2_def
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify (0#i32 : Std.I32) = .ok i2 := by
    rw [hi2_def]; rfl
  set acc1 : Std.Array Std.I32 256#usize :=
    Std.Array.repeat (256#usize : Std.Usize) i2 with h_acc1_def
  have h_acc1_zero : ∀ n : Nat, n < 256 → (acc1.val[n]!).val = 0 := by
    intro n hn
    rw [h_acc1_def, Std.Array.repeat_val]
    rw [getElem!_pos _ n (by rw [List.length_replicate]; exact hn)]
    rw [List.getElem_replicate]; rfl
  have h_acc1_natAbs : ∀ n : Nat, n < 256 → (acc1.val[n]!).val.natAbs = 0 := by
    intro n hn; rw [h_acc1_zero n hn]; rfl
  -- r_arr : Array Poly K from r_as_ntt.
  set r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
    ⟨r_as_ntt.val, by rw [← h_r_len]⟩ with h_r_arr_def
  have h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]! := by
    intro c hc; rfl
  -- Acc budget for loop0: acc1[n]=0, K≤4 ⟹ K·2^25 ≤ 2^30.
  have h_acc1_budget : ∀ n : Fin 256,
      (acc1.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
    intro n
    rw [h_acc1_natAbs n.val n.isLt]
    have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    have : (4 : Nat) * 2^25 ≤ 2^30 := by decide
    omega
  -- S1: row-0 column loop.
  obtain ⟨⟨me1, cache1, acc2⟩, h_loop0_eq, h_row0⟩ := triple_exists_ok_fc
    (compute_vector_u_loop0_fc hash_functionsHashInst matrix_entry seed r_as_ntt cache
      r_arr acc1 h_seed_len h_r_len h_cache_len h_r_arr h_r_bnd h_acc1_budget)
  dsimp only at h_loop0_eq h_row0
  -- cache1 length preservation (same impl call, deterministic).
  have h_cache1_len : cache1.length = K.val := by
    obtain ⟨v, hv_eq, hv_len⟩ := triple_exists_ok_fc
      (compute_vector_u_loop0_cache_len_fc hash_functionsHashInst matrix_entry seed r_as_ntt cache
        r_arr acc1 h_seed_len h_r_len h_cache_len h_r_arr h_r_bnd h_acc1_budget)
    rw [h_loop0_eq] at hv_eq
    have : v = (me1, cache1, acc2) := (Result.ok.inj hv_eq).symm
    rw [this] at hv_len; exact hv_len
  -- row-0 acc-bridge: multiply_vectors lm[0] (lift r) = .ok (scaleZ 2285 (mont_strip (poly_reducing acc2))).
  have h_bridge0 := compute_vector_u_row0_acc_bridge seed r_as_ntt r_arr cache cache1 acc1 acc2
    h_acc1_zero h_r_arr h_r_bnd h_row0
  -- Destructure row0_inv once.
  obtain ⟨_h_ex, h_acc2_bnd_raw, h_cache_done, _h_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
      Row0FillFC.row0_inv, ← List.getElem!_eq_getElem?_getD] using h_row0
  -- cache-post bridge for loop1: from row0_inv conjunct (3) + h_r_arr.
  have h_cache_post : ∀ c : Nat, c < K.val →
      accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache1.val[c]!) := by
    intro c hc
    have := h_cache_done c hc
    rw [h_r_arr c hc] at this; exact this
  -- acc2 bound for the row-0 reducing step: ≤ 2^16*3328.
  have h_acc2_bnd : ∀ n : Nat, n < 256 → (acc2.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
    intro n hn
    have hb := h_acc2_bnd_raw n hn
    rw [h_acc1_natAbs n hn] at hb
    have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    have h2 : (4 : Nat) * 2^25 ≤ 2^16 * 3328 := by decide
    omega
  set acc_slice : Slice Std.I32 := Aeneas.Std.Array.to_slice acc2 with h_acc_slice_def
  have h_acc_slice_len : acc_slice.length = 256 := by
    rw [h_acc_slice_def, Aeneas.Std.Array.length_to_slice]; rfl
  have h_acc_slice_val : acc_slice.val = acc2.val := Aeneas.Std.Array.val_to_slice acc2
  have h_acc_slice_bnd : ∀ n : Nat, n < 256 →
      (acc_slice.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
    intro n hn; rw [h_acc_slice_val]; exact h_acc2_bnd n hn
  -- (a) index_mut result 0 → (result[0]!, result.set 0).
  set pre0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    result.val[0]! with h_pre0_def
  have h0lt : (0 : Nat) < K.val := h_K_pos
  have h_idx_result0 : Aeneas.Std.Slice.index_usize result (0#usize : Std.Usize) = .ok pre0 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq result 0#usize
      (by show (0#usize : Std.Usize).val < result.length; rw [h_result_len]; exact h0lt)
  have h_imt_result0 : Aeneas.Std.Slice.index_mut_usize result (0#usize : Std.Usize)
      = .ok (pre0, result.set 0#usize) := by
    unfold Aeneas.Std.Slice.index_mut_usize
    rw [h_idx_result0]; rfl
  -- (b) reducing step.
  obtain ⟨result1, h_result1_eq, h_result1_mont, h_result1_lane_bnd⟩ :=
    triple_exists_ok_fc
      (poly_reducing_from_i32_array_fc acc_slice pre0 h_acc_slice_len h_acc_slice_bnd)
  have h_result1_lift : lift_poly result1
      = Impl.mont_strip_pure (Spec.poly_reducing_from_i32_array_pure acc_slice) := by
    rw [← h_result1_mont, Impl.mont_strip_lift_poly_mont_eq_lift_poly]
  set rslice1 : Slice _ := result.set 0#usize result1 with h_rslice1_def
  have h_rslice1_at0 : rslice1.val[0]! = result1 := by
    rw [h_rslice1_def]
    simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
      Aeneas.Std.Slice.getElem!_Nat_set_eq result 0#usize 0 result1
        ⟨rfl, by show (0:Nat) < result.length; rw [h_result_len]; exact h0lt⟩
  have h_rslice1_len : rslice1.length = K.val := by
    rw [h_rslice1_def, Aeneas.Std.Slice.set_length]; exact h_result_len
  have h_pre2_eq : rslice1.val[0]! = result1 := h_rslice1_at0
  have h_idx_rslice1 : Aeneas.Std.Slice.index_usize rslice1 (0#usize : Std.Usize) = .ok result1 := by
    rw [← h_rslice1_at0]
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq rslice1 0#usize
      (by show (0#usize : Std.Usize).val < rslice1.length; rw [h_rslice1_len]; exact h0lt)
  have h_imt_rslice1 : Aeneas.Std.Slice.index_mut_usize rslice1 (0#usize : Std.Usize)
      = .ok (result1, rslice1.set 0#usize) := by
    unfold Aeneas.Std.Slice.index_mut_usize
    rw [h_idx_rslice1]; rfl
  -- (c) invert step.
  have h_result1_bnd : ∀ chunk : Nat, chunk < 16 → ∀ k : Nat, k < 16 →
      ((result1.coefficients.val[chunk]!).elements.val[k]!).val.natAbs ≤ 13312 := by
    intro chunk hchunk k hk
    have := h_result1_lane_bnd chunk hchunk k hk; omega
  obtain ⟨⟨result2, scratch1⟩, h_inv_eq, h_result2_lift, h_result2_bnd⟩ :=
    triple_exists_ok_fc
      (invert_ntt_montgomery_fc (K := K) result1 scratch h_result1_bnd)
  dsimp only at h_inv_eq h_result2_lift h_result2_bnd
  set rslice2 : Slice _ := rslice1.set 0#usize result2 with h_rslice2_def
  have h_rslice2_at0 : rslice2.val[0]! = result2 := by
    rw [h_rslice2_def]
    simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
      Aeneas.Std.Slice.getElem!_Nat_set_eq rslice1 0#usize 0 result2
        ⟨rfl, by show (0:Nat) < rslice1.length; rw [h_rslice1_len]; exact h0lt⟩
  have h_rslice2_len : rslice2.length = K.val := by
    rw [h_rslice2_def, Aeneas.Std.Slice.set_length]; exact h_rslice1_len
  have h_idx_rslice2 : Aeneas.Std.Slice.index_usize rslice2 (0#usize : Std.Usize) = .ok result2 := by
    rw [← h_rslice2_at0]
    exact libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq rslice2 0#usize
      (by show (0#usize : Std.Usize).val < rslice2.length; rw [h_rslice2_len]; exact h0lt)
  have h_imt_rslice2 : Aeneas.Std.Slice.index_mut_usize rslice2 (0#usize : Std.Usize)
      = .ok (result2, rslice2.set 0#usize) := by
    unfold Aeneas.Std.Slice.index_mut_usize
    rw [h_idx_rslice2]; rfl
  -- (d) index error_1 0 → error_1[0]!.
  set err0 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    error_1.val[0]! with h_err0_def
  have h_idx_err0 : Aeneas.Std.Slice.index_usize error_1 (0#usize : Std.Usize) = .ok err0 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq error_1 0#usize
      (by show (0#usize : Std.Usize).val < error_1.length; rw [h_err_len]; exact h0lt)
  -- (e) add_error_reduce step.
  have h_result2_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((result2.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hchunk ℓ hℓ
    have := h_result2_bnd chunk hchunk ℓ hℓ; omega
  have h_err0_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((err0.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439 :=
    fun chunk hchunk ℓ hℓ => h_err_bnd 0 h0lt ⟨chunk, hchunk⟩ ⟨ℓ, hℓ⟩
  obtain ⟨row0poly, h_add0_eq, h_row0poly_lift, h_row0poly_bnd⟩ :=
    triple_exists_ok_fc
      (add_error_reduce_fc result2 err0 h_result2_self_bnd h_err0_bnd)
  set s1 : Slice _ := rslice2.set 0#usize row0poly with h_s1_def
  have h_s1_at0 : s1.val[0]! = row0poly := by
    rw [h_s1_def]
    simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
      Aeneas.Std.Slice.getElem!_Nat_set_eq rslice2 0#usize 0 row0poly
        ⟨rfl, by show (0:Nat) < rslice2.length; rw [h_rslice2_len]; exact h0lt⟩
  have h_s1_len : s1.length = K.val := by
    rw [h_s1_def, Aeneas.Std.Slice.set_length]; exact h_rslice2_len
  -- row-0 row_spec: row_spec lm r_as_ntt error_1 0 = .ok (lift_poly row0poly).
  have h_row_spec0 : AllRowsFillFC.row_spec lm r_as_ntt error_1 0 = .ok (lift_poly row0poly) := by
    unfold AllRowsFillFC.row_spec
    have hA : hacspec_ml_kem.matrix.multiply_vectors (lm.val[0]!) (lift_vec_slice r_as_ntt K)
        = .ok (scaleZ 2285 (lift_poly result1)) := by
      rw [hlm_def, h_result1_lift, h_acc_slice_def]
      exact h_bridge0
    rw [hA]; simp only [Aeneas.Std.bind_tc_ok]
    rw [compute_vector_u_ntt_inverse_eq result1 result2 h_result2_lift.symm]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [← h_err0_def]
    exact compute_vector_u_add_eq result2 err0 row0poly h_row0poly_lift.symm
  -- S2: outer rows loop [1, K). Budget: acc2 re-zeroed per row (loop1 ignores acc2 content).
  obtain ⟨⟨me2, result3, scratch2, acc3⟩, h_loop1_eq, h_rows⟩ := triple_exists_ok_fc
    (compute_vector_u_loop1_fc hash_functionsHashInst i2 me1 seed r_as_ntt error_1 s1
      scratch1 cache1 acc2 r_arr 1#usize hK
      (by show 1 ≤ (1#usize : Std.Usize).val; rfl)
      (by show (1#usize : Std.Usize).val ≤ K.val; exact h_K_pos) h_seed_len h_r_len
      h_cache1_len h_s1_len h_err_len (by rw [hi2_def]; rfl)
      h_r_arr h_r_bnd h_err_bnd h_cache_post)
  dsimp only at h_loop1_eq h_rows
  -- Destructure rows_inv: done rows [1,K) + unchanged rows + length.
  obtain ⟨h_rows_done, h_rows_undone, h_result3_len, h_rows_bnd⟩ := by
    simpa [AllRowsFillFC.rows_inv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
      ← List.getElem!_eq_getElem?_getD] using h_rows
  -- result3[0] = s1[0] = row0poly (loop1 leaves row 0 since start = 1).
  have h_result3_at0 : result3.val[0]! = row0poly := by
    have := h_rows_undone 0 h0lt (Or.inl (by decide))
    rw [this, h_s1_at0]
  -- W := lift_vec_slice result3 K; per-row row_spec = .ok W[r].
  set W : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    lift_vec_slice result3 K with hW_def
  have hW_at : ∀ r : Nat, r < K.val → W.val[r]! = lift_poly result3.val[r]! := by
    intro r hr; rw [hW_def]; exact lift_vec_slice_lane result3 K r hr
  have h_row_spec_all : ∀ r : Nat, r < K.val →
      AllRowsFillFC.row_spec lm r_as_ntt error_1 r = .ok (W.val[r]!) := by
    intro r hr
    rw [hW_at r hr]
    by_cases h0 : r = 0
    · subst h0; rw [h_result3_at0]; exact h_row_spec0
    · have hr1 : (1#usize : Std.Usize).val ≤ r := by
        have h1v : (1#usize : Std.Usize).val = 1 := rfl
        rw [h1v]; omega
      have := h_rows_done r hr1 hr
      rw [hlm_def]; exact this
  -- Bridge row_spec → PART A `hrow` (evec = lift_vec_slice error_1 K).
  have hrow : ∀ i : Nat, i < K.val →
      (do
        let prod ← hacspec_ml_kem.matrix.multiply_vectors (lm.val[i]!) (lift_vec_slice r_as_ntt K)
        let inv ← hacspec_ml_kem.invert_ntt.ntt_inverse prod
        hacspec_ml_kem.matrix.add_polynomials inv ((lift_vec_slice error_1 K).val[i]!))
        = .ok (W.val[i]!) := by
    intro i hi
    have h := h_row_spec_all i hi
    unfold AllRowsFillFC.row_spec at h
    rw [lift_vec_slice_lane error_1 K i hi]
    exact h
  -- PART A: hacspec compute_vector_u lm (lift r) (lift e) = .ok W.
  have h_hacspec : hacspec_ml_kem.matrix.compute_vector_u lm
        (lift_vec_slice r_as_ntt K) (lift_vec_slice error_1 K) = .ok W :=
    compute_vector_u_hacspec_eq lm (lift_vec_slice r_as_ntt K) (lift_vec_slice error_1 K) W
      (Std.Array.length_eq W) hrow
  -- Reduce the impl do-block to `.ok (me2, result3, scratch2, cache1, acc3)`.
  apply triple_of_ok_fc (v := (me2, result3, scratch2, cache1, acc3))
  · unfold libcrux_iot_ml_kem.matrix.compute_vector_u
    rw [h_len_r]; simp only [Aeneas.Std.bind_tc_ok, Aeneas.Std.massert]
    rw [h_len_e]; simp only [Aeneas.Std.bind_tc_ok]
    rw [show libcrux_secrets.traits.Classify.Blanket.classify (0#i32 : Std.I32)
          = Aeneas.Std.Result.ok i2 from h_classify]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (Std.Array.repeat (256#usize : Std.Usize) i2) = acc1 from rfl]
    rw [h_loop0_eq]; simp only [Aeneas.Std.bind_tc_ok]
    show (do
            let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice acc2)
            let (pre, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize result 0#usize
            let pre1 ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                portable_ops_inst s pre
            let result1 := index_mut_back pre1
            let (pre2, index_mut_back1) ← Aeneas.Std.Slice.index_mut_usize result1 0#usize
            let (pre3, scratch1) ← libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
                K portable_ops_inst pre2 scratch
            let result2 := index_mut_back1 pre3
            let (pre4, index_mut_back2) ← Aeneas.Std.Slice.index_mut_usize result2 0#usize
            let pre5 ← Aeneas.Std.Slice.index_usize error_1 0#usize
            let pre6 ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                portable_ops_inst pre4 pre5
            let s1 := index_mut_back2 pre6
            let (matrix_entry2, result3, scratch2, accumulator3) ←
              libcrux_iot_ml_kem.matrix.compute_vector_u_loop1
                K portable_ops_inst hash_functionsHashInst i2 { start := 1#usize, «end» := K }
                me1 seed r_as_ntt error_1 s1 scratch1 cache1 acc2
            .ok (matrix_entry2, result3, scratch2, cache1, accumulator3))
        = .ok (me2, result3, scratch2, cache1, acc3)
    rw [show Aeneas.Std.lift (Aeneas.Std.Array.to_slice acc2) = Aeneas.Std.Result.ok acc_slice
          from by rw [h_acc_slice_def]; rfl]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_imt_result0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [show libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
          (vectortraitsOperationsInst := portable_ops_inst) acc_slice pre0
          = Aeneas.Std.Result.ok result1 from h_result1_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (result.set 0#usize) result1 = rslice1 from rfl, h_imt_rslice1]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
          K (vectortraitsOperationsInst := portable_ops_inst) result1 scratch
          = Aeneas.Std.Result.ok (result2, scratch1) from h_inv_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (rslice1.set 0#usize) result2 = rslice2 from rfl, h_imt_rslice2]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_err0]; simp only [Aeneas.Std.bind_tc_ok]
    rw [show libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
          (vectortraitsOperationsInst := portable_ops_inst) result2 err0
          = Aeneas.Std.Result.ok row0poly from h_add0_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [show (rslice2.set 0#usize) row0poly = s1 from rfl]
    rw [h_loop1_eq]; simp only [Aeneas.Std.bind_tc_ok]
  · -- POST: witness `spec_out := lift_vec_slice result3 K` (hacspec equation
    -- `h_hacspec`), then the per-lane `LaneMatches` bridge. Each impl output lane
    -- is the unique centered Barrett representative `|x| ≤ 1664` whose residue
    -- `(x : ZMod q)` equals `zmodOfFE (spec lane)`.
    refine ⟨lift_vec_slice result3 K, ?_, ?_⟩
    · show hacspec_ml_kem.matrix.compute_vector_u (lift_matrix_from_seed seed K)
            (lift_vec_slice r_as_ntt K) (lift_vec_slice error_1 K)
          = .ok (lift_vec_slice result3 K)
      rw [← hlm_def, ← hW_def]
      exact h_hacspec
    · unfold VecMatches PolyMatches
      intro r hr ℓ hℓ
      have hj : ℓ / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hℓ
      have hm : ℓ % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
      -- Tight centered Barrett output bound on this lane: row 0 from `row0poly`,
      -- rows [1,K) from the loop invariant's per-row bound.
      have hbnd :
          (((result3.val[r]!).coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!.val).natAbs ≤ 1664 := by
        by_cases h0 : r = 0
        · subst h0
          rw [h_result3_at0]
          exact h_row0poly_bnd (ℓ / 16) hj (ℓ % 16) hm
        · have hr1 : (1#usize : Std.Usize).val ≤ r := by
            have h1v : (1#usize : Std.Usize).val = 1 := rfl
            omega
          exact h_rows_bnd r hr1 hr (ℓ / 16) hj (ℓ % 16) hm
      -- `LaneMatches` via `laneMatches_lift_fe`: tight bound + residue equality.
      rw [lift_vec_slice_lane result3 K r hr, lift_poly_getElem _ ℓ hℓ]
      exact laneMatches_lift_fe _ hbnd

/--
info: 'libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC.compute_vector_u_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 sample_matrix_entry_fc]
-/
#guard_msgs in
#print axioms compute_vector_u_fc

end libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC
