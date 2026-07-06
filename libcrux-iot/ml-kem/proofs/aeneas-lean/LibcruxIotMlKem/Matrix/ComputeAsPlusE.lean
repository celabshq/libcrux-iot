/-
  # `Matrix/ComputeAsPlusE.lean` — extracted from `FCTargets.lean` §compute_as_plus_e.
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

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Matrix.ComputeAsPlusE
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec

/-! ## §L7-prep — Mont→canonical bridge.

    Single lemma `lift_poly_mont_to_lift_poly` used by L7.1's outer-loop
    composition. The L6 forward-deps for matrix-row accumulation
    (`accumulating_ntt_multiply_*_poly_fc` + `add_standard_error_reduce_fc`)
    produce per-lane outputs in Mont form (`lift_poly_mont`), but L7.1's
    POST consumes them through hacspec's `add_polynomials` after the row
    finalizer, which expects canonical-domain values. The L6.3a finalizer
    calls `montgomery_multiply_by_constant 1353` (= `R²` mod q) to strip
    one R per lane, so the bridge takes the form of a `mul_pure` against
    `lift_fe_mont 1353` collapsing to `lift_fe`. -/

/-- FE-level Mont→canonical bridge: `mul_pure (lift_fe_mont x) (lift_fe_mont 1353)
    = lift_fe x`. In `ZMod 3329`, `lift_fe_mont x = x · 169` (where
    `169 = R⁻¹ mod q`), so the LHS reduces via `zmodOfFE_mul_pure +
    zmodOfFE_lift_fe_mont` to `(x · 169) · (1353 · 169) = x · (169² · 1353)`.
    The keystone gives `1353 ≡ R² (mod q)` and `R⁻¹ = 169`, so
    `169² · 1353 ≡ R⁻² · R² = 1`. Canonical round-trip closes. -/
lemma lift_fe_mont_mul_1353_eq_lift_fe (x : Std.I16) :
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16))
      = lift_fe x := by
  set s : hacspec_ml_kem.parameters.FieldElement :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16)) with hs_def
  -- (1) `s` is canonical (Canonical_mul_pure unconditional).
  have h_canon : s.val.val < 3329 := by
    have h_cs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
      (lift_fe_mont x) (lift_fe_mont (1353#i16 : Std.I16))
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at h_cs
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at h_cs
    exact h_cs
  -- (2) Canonical round-trip.
  have h_round_trip : feOfZMod (zmodOfFE s) = s :=
    feOfZMod_zmodOfFE_of_canonical s h_canon
  -- (3) `zmodOfFE s = (x.val : ZMod 3329)`.
  have h_zmod_s : zmodOfFE s = ((x.val : Int) : ZMod 3329) := by
    rw [hs_def, L2_8c.zmodOfFE_mul_pure,
        L2_8c.zmodOfFE_lift_fe_mont, L2_8c.zmodOfFE_lift_fe_mont]
    -- Goal: (x.val : ZMod 3329) * 169 * (((1353#i16).val : ZMod 3329) * 169) = (x.val : ZMod 3329)
    have h_1353 : (((1353#i16 : Std.I16).val : Int) : ZMod 3329) = 1353 := by
      decide
    rw [h_1353]
    -- Goal: (x.val : ZMod 3329) * 169 * (1353 * 169) = (x.val : ZMod 3329)
    have h_inv : (169 : ZMod 3329) * (1353 * 169) = 1 := by decide
    calc ((x.val : Int) : ZMod 3329) * 169 * (1353 * 169)
        = ((x.val : Int) : ZMod 3329) * (169 * (1353 * 169)) := by ring
      _ = ((x.val : Int) : ZMod 3329) * 1 := by rw [h_inv]
      _ = ((x.val : Int) : ZMod 3329) := by ring
  -- (4) Glue: `s = feOfZMod (zmodOfFE s) = feOfZMod ((x.val : ZMod 3329)) = lift_fe x`.
  show s = lift_fe x
  rw [← h_round_trip, h_zmod_s]
  unfold lift_fe i16_to_spec_fe_plain
  rfl

/-- Poly-level Mont→canonical bridge: at every lane in [0, 256),
    `mul_pure (lift_poly_mont re).val[lane]! (lift_fe_mont 1353)
      = (lift_poly re).val[lane]!`.

    Reduces to the FE-level helper `lift_fe_mont_mul_1353_eq_lift_fe`
    after unfolding the two `lift_poly*` getters to their underlying
    `lift_fe_mont`/`lift_fe` of the same I16 lane
    `(re.coefficients.val[lane/16]!).elements.val[lane%16]!`. -/
lemma lift_poly_mont_to_lift_poly
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (lane : Nat) (h_lane : lane < 256) :
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      ((lift_poly_mont re).val[lane]!) (lift_fe_mont (1353#i16 : Std.I16))
      = (lift_poly re).val[lane]! := by
  -- Pin the underlying I16 lane.
  set x : Std.I16 :=
    (re.coefficients.val[lane / 16]!).elements.val[lane % 16]! with hx_def
  -- (A) `(lift_poly_mont re).val[lane]! = lift_fe_mont x`.
  have h_mont : (lift_poly_mont re).val[lane]! = lift_fe_mont x := by
    unfold lift_poly_mont
    show ((List.range 256).map (fun j =>
            lift_fe_mont (re.coefficients.val[j / 16]!).elements.val[j % 16]!))[lane]!
          = lift_fe_mont x
    have h_len : ((List.range 256).map (fun j =>
            lift_fe_mont (re.coefficients.val[j / 16]!).elements.val[j % 16]!)).length = 256 := by
      simp
    rw [getElem!_pos _ lane (by rw [h_len]; exact h_lane)]
    rw [List.getElem_map, List.getElem_range]
  -- (B) `(lift_poly re).val[lane]! = lift_fe x`.
  have h_plain : (lift_poly re).val[lane]! = lift_fe x := by
    unfold lift_poly
    show ((List.range 256).map (fun j =>
            lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!))[lane]!
          = lift_fe x
    have h_len : ((List.range 256).map (fun j =>
            lift_fe (re.coefficients.val[j / 16]!).elements.val[j % 16]!)).length = 256 := by
      simp
    rw [getElem!_pos _ lane (by rw [h_len]; exact h_lane)]
    rw [List.getElem_map, List.getElem_range]
  rw [h_mont, h_plain]
  exact lift_fe_mont_mul_1353_eq_lift_fe x

/-! ## §L7.1-loop0 — row-0 column loop scaffolding.

    Namespace `Stage1FillCacheFC` provides the invariant + step-post predicates
    used to characterize `matrix.compute_As_plus_e_loop0` (the K-iteration
    column loop for row 0) via `loop_range_spec_usize`. Each iteration
    calls `accumulating_ntt_multiply_fill_cache` on column `j ∈ [0, K)`,
    adding column j's contribution to the I32 accumulator AND populating
    `s_cache.val[j]!`. The invariant tracks both effects across `k`
    iterations.

    Mirrors `FillCacheFC` but at the row-axis K-scale
    rather than the chunk-axis 16-scale. -/

namespace Stage1FillCacheFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 4-conjunct invariant for the row-0 column loop. Tracks:
    (1) accumulator characterization: for each chunk j and lane ℓ in
        `[0, 16)²`, `Spec.mont_reduce_pure (lift_fe_int acc[16j+ℓ].val)`
        equals init plus the canonical-form sum of column contributions
        from columns `[0, k)`.
    (2) accumulator bound: `|acc.val[n]| ≤ |acc_init.val[n]| + k · 2^25`.
    (3) cache characterization: for each c ∈ `[0, k)`,
        `cache.val[c]!.coefficients[j]!` (across all chunks j) stores the
        per-chunk `ntt_multiply_cache_post` for `s_as_ntt.val[c]!.coefficients[j]!`.
    (4) cache unchanged: for each c ∈ `[k, K)`, `cache.val[c]! = cache_init.val[c]!`. -/
def row0_inv {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc)
    (cache_init : Std.Array
                    (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) :
    Std.Usize → Acc →
    Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K →
    Result Prop :=
  fun k acc cache => pure (
    -- (1) Per-(chunk j, lane ℓ) accumulator: canonical-form K-column sum.
    (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
      Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
        = (List.range k.val).foldl
            (fun s c =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (matrix_A.val[c]!.coefficients.val[j]!))
                    (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
            (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
    -- (2) Accumulator bound grows by 2^25 per column iteration.
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k.val * 2^25)
    -- (3) Cache populated for columns [0, k).
    ∧ (∀ c : Nat, c < k.val →
        accumulating_ntt_multiply_poly_cache_post
          (s_as_ntt.val[c]!) (cache.val[c]!))
    -- (4) Cache unchanged for columns [k, K).
    ∧ (∀ c : Nat, k.val ≤ c → c < K.val →
        cache.val[c]! = cache_init.val[c]!))

/-- Step-post for `loop_range_spec_usize` over (acc, cache). -/
def row0_step_post {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc)
    (cache_init : Std.Array
                    (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) ×
        (Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) ×
        Acc)
      (Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K × Acc)) :
    Prop :=
  match r with
  | .cont (iter', cache', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (row0_inv matrix_A s_as_ntt acc_init cache_init iter'.start acc' cache').holds
  | .done y => (row0_inv matrix_A s_as_ntt acc_init cache_init K y.2 y.1).holds

end Stage1FillCacheFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Mirrors `L6_3c_fill_irreducible`
-- — heavy POST predicates and the per-column forward dep are
-- made locally irreducible across the step lemma + outer Triple so that
-- elaboration does not whnf-explode through the 4-conjunct `row0_inv` body or
-- the nested `∀ j : Fin 16, ∀ ℓ : Fin 16` accumulator characterization.
-- we do NOT mark
-- `Stage1FillCacheFC.row0_inv` / `row0_step_post` irreducible — keeping them reducible
-- preserves the `simpa`-based destructure of `h_inv`.
section L7_1a_irreducible
attribute [local irreducible] Spec.ntt_multiply_cache_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- Per-iteration FC step lemma for the row-0 column loop. Given the
    `row0_inv` invariant at step k and the strengthened PRE bounds, executing
    one body iteration of `matrix.compute_As_plus_e_loop0.body` produces the
    `row0_step_post` (either `.cont` advancing the invariant to k+1 or
    `.done` capping at K).

    Mirrors `accumulating_ntt_multiply_fill_cache_poly_step_lemma_fc` but at the row-axis K-scale rather than the chunk-axis
    16-scale. Per-iteration step composes:
    1. `matrix.entry` reduction (via `entry_eq_ok_fc_aux`) at `(i, j) = (0, k)`
       gives `matrix_A.val[0*K+k]! = matrix_A.val[k]!`.
    2. `array_index_usize_ok_eq` for `s_as_ntt[k]`.
    3. `Array.index_mut_usize` reduction for `s_cache[k]` (extract pre +
       `cache.set k` setter).
    4. `accumulating_ntt_multiply_fill_cache_poly_fc` on
       column k. The current accumulator's bound `≤ 2^30` follows from the
       PRE budget `(acc_init[n]).val.natAbs + K·2^25 ≤ 2^30` combined with
       invariant conjunct (2) `acc[n] ≤ acc_init[n] + k·2^25`.
    5. Splice the new cache chunk into `s_cache.set k _`.
    6. Re-establish `row0_inv` at k+1 (advancing the per-(j, ℓ) foldl by one
       step via List.range_succ + List.foldl_append), or unchanged at k=K for
       the `.done` branch. -/
theorem compute_As_plus_e_loop0_step_lemma_fc
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Stage1FillCacheFC.Acc)
    (cache_init : Std.Array
                    (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ i j : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (acc : Stage1FillCacheFC.Acc)
    (cache : Std.Array
                (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Std.Usize) (h_le : k.val ≤ K.val)
    (h_inv : (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt acc_init cache_init k acc cache).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt
      { start := k, «end» := K } cache acc
    ⦃ ⇓ r => ⌜ Stage1FillCacheFC.row0_step_post matrix_A s_as_ntt acc_init cache_init k r ⌝ ⦄ := by
  have h_cache_len : cache.length = K.val := Std.Array.length_eq cache
  have h_cache_init_len : cache_init.length = K.val := Std.Array.length_eq cache_init
  have h_s_as_ntt_len : s_as_ntt.length = K.val := Std.Array.length_eq s_as_ntt
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 4-conjunct invariant.
  obtain ⟨h_inv_acc, h_inv_acc_bnd, h_inv_cache_done, h_inv_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch.
    -- (1) IteratorRange.next reduces to .ok (some k, { start := s_iter, end := K }).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
          core.Usize.Insts.CoreIterRangeStep
          ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                    r = (some k,
                        ({ start := s, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
      libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
        (fun _ s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨s, hs, rfl⟩)
        (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
    obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
    obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
    -- (2) matrix.entry reduces to .ok matrix_A.val[k.val]! (since i = 0, j = k).
    have h_0K : (0#usize : Std.Usize).val < K.val := by
      have h0 : (0#usize : Std.Usize).val = 0 := rfl
      rw [h0]; omega
    have h_matrix_entry :
        libcrux_iot_ml_kem.matrix.entry K portable_ops_inst matrix_A 0#usize k
          = .ok (matrix_A.val[(0#usize : Std.Usize).val * K.val + k.val]!) :=
      entry_eq_ok_fc_aux K matrix_A 0#usize k hAlen h_0K h_lt
    have h_idx0 : (0#usize : Std.Usize).val * K.val + k.val = k.val := by
      have h0 : (0#usize : Std.Usize).val = 0 := rfl
      rw [h0]; omega
    set t_matrix : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      matrix_A.val[k.val]! with ht_matrix_def
    have h_matrix_entry' :
        libcrux_iot_ml_kem.matrix.entry K portable_ops_inst matrix_A 0#usize k
          = .ok t_matrix := by
      rw [h_matrix_entry]
      congr 1
      show matrix_A.val[(0#usize : Std.Usize).val * K.val + k.val]! = matrix_A.val[k.val]!
      congr 1
    -- (3) Array.index_usize s_as_ntt k reduces to .ok s_as_ntt[k.val]!.
    set t_s : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      s_as_ntt.val[k.val]! with ht_s_def
    have h_idx_s : Aeneas.Std.Array.index_usize s_as_ntt k = .ok t_s :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq s_as_ntt k
        (by rw [h_s_as_ntt_len]; exact h_lt)
    -- (4) Array.index_mut_usize s_cache k splits into (s_cache[k]!, set).
    set t_cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.val[k.val]! with ht_cache_def
    have h_idx_cache : Aeneas.Std.Array.index_usize cache k = .ok t_cache :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq cache k
        (by rw [h_cache_len]; exact h_lt)
    have h_imt_cache : Aeneas.Std.Array.index_mut_usize cache k
        = .ok (t_cache, cache.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx_cache]; rfl
    -- (5) Apply L6.3c per-column forward dep at column k.
    -- Per-lane bounds on t_matrix and t_s (16×16 lanes).
    have hK_pos : 0 < K.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt
    have h_k_lt_KK : k.val < K.val * K.val := by
      calc k.val < K.val := h_lt
        _ ≤ K.val * K.val := Nat.le_mul_of_pos_left K.val hK_pos
    have h_k_lt_len : k.val < matrix_A.length := by rw [hAlen]; exact h_k_lt_KK
    have h_t_matrix_bnd : ∀ i : Fin 16, ∀ j : Fin 16,
        ((t_matrix.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 :=
      fun i j => h_matrix_bnd ⟨k.val, h_k_lt_len⟩ i j
    have h_t_s_bnd : ∀ i : Fin 16, ∀ j : Fin 16,
        ((t_s.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 :=
      fun i j => h_s_bnd ⟨k.val, h_lt⟩ i j
    -- Current acc bound ≤ 2^30: combine inv conjunct (2) with budget PRE.
    have h_acc_cur_bnd : ∀ n : Fin 256, (acc.val[n.val]!).val.natAbs ≤ 2^30 := by
      intro n
      have hb := h_inv_acc_bnd n.val n.isLt
      have hp := h_acc_bnd n
      -- hb : (acc[n]).val.natAbs ≤ (acc_init[n]).val.natAbs + k.val * 2^25
      -- hp : (acc_init[n]).val.natAbs + K.val * 2^25 ≤ 2^30
      have hk_le : k.val * 2^25 ≤ K.val * 2^25 := Nat.mul_le_mul_right _ h_le
      omega
    obtain ⟨p_pair, h_p_eq, h_p_bnd_rel, h_p_acc_post, h_p_cache_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_fill_cache_poly_fc t_matrix t_s t_cache acc
          h_t_matrix_bnd h_t_s_bnd h_acc_cur_bnd)
    set acc1 : Stage1FillCacheFC.Acc := p_pair.1 with hacc1_def
    set cache_chunk1 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      p_pair.2 with hcc1_def
    -- (5') p_pair.2 expressed as cache_chunk1 (for splicing back into s_cache).
    -- (6) cache1 := s_cache.set k cache_chunk1.
    set cache1 : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
      cache.set k cache_chunk1 with hcache1_def
    have h_cache1_at : cache1.val[k.val]! = cache_chunk1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq cache k k.val cache_chunk1
          ⟨rfl, by rw [h_cache_len]; exact h_lt⟩
    have h_cache1_ne : ∀ j : Nat, j ≠ k.val →
        cache1.val[j]! = cache.val[j]! := by
      intro j hj
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne cache k j cache_chunk1
          (fun h => hj h.symm)
    -- (7) Body equation.
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt
          { start := k, «end» := K } cache acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), cache1, acc1)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
              let pre ← libcrux_iot_ml_kem.matrix.entry K portable_ops_inst
                          matrix_A 0#usize k
              let pre1 ← Aeneas.Std.Array.index_usize s_as_ntt k
              let (pre2, index_mut_back) ← Aeneas.Std.Array.index_mut_usize cache k
              let (accumulator1, pre3) ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
                  portable_ops_inst pre pre1 acc pre2
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          index_mut_back pre3, accumulator1)))
            : Result _) = _
      rw [h_matrix_entry']
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_s]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_cache]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let (accumulator1, pre3) ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
                  portable_ops_inst t_matrix t_s acc t_cache
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          (cache.set k) pre3, accumulator1)))
            : Result _) = _
      rw [h_p_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rfl
    apply triple_of_ok_fc h_body
    -- (8) Discharge the step_post.
    show Stage1FillCacheFC.row0_step_post matrix_A s_as_ntt acc_init cache_init k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), cache1, acc1))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    -- (9) Re-establish `row0_inv` at s_iter (= k+1).
    show (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt acc_init cache_init s_iter acc1 cache1).holds
    unfold Stage1FillCacheFC.row0_inv
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = (List.range s_iter.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (matrix_A.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + s_iter.val * 2^25)
        ∧ (∀ c : Nat, c < s_iter.val →
            accumulating_ntt_multiply_poly_cache_post
              (s_as_ntt.val[c]!) (cache1.val[c]!))
        ∧ (∀ c : Nat, s_iter.val ≤ c → c < K.val →
            cache1.val[c]! = cache_init.val[c]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- (a) Accumulator characterization at s_iter = k+1.
        intro j hj ℓ hℓ
        -- Use p_acc_post to extend the foldl from k to k+1.
        -- p_acc_post : accumulating_ntt_multiply_poly_post t_matrix t_s acc acc1.
        -- For each (j, ℓ):
        --   mont_reduce_pure (lift_fe_int acc1[16j+ℓ].val)
        --   = add_pure (mont_reduce_pure (lift_fe_int acc[16j+ℓ].val))
        --             (ntt_multiply_pure_no_acc (lift_chunk_mont t_matrix.coef[j])
        --                                       (lift_chunk_mont t_s.coef[j])
        --                                       zetas...).val[ℓ]!
        -- IH at k: mont_reduce_pure (lift_fe_int acc[16j+ℓ].val) = foldl over [0, k).
        -- Goal: mont_reduce_pure (lift_fe_int acc1[16j+ℓ].val) = foldl over [0, k+1).
        have h_step_acc :
            Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val))
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (t_matrix.coefficients.val[j]!))
                      (lift_chunk_mont (t_s.coefficients.val[j]!))
                      (Spec.zeta_at (64 + 4 * j))
                      (Spec.zeta_at (64 + 4 * j + 1))
                      (Spec.zeta_at (64 + 4 * j + 2))
                      (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!) := by
          have := h_p_acc_post
          unfold accumulating_ntt_multiply_poly_post at this
          exact this j hj ℓ hℓ
        have h_ih := h_inv_acc j hj ℓ hℓ
        rw [h_step_acc, h_ih]
        -- LHS now: add_pure (foldl [0, k) init) (ntt_multiply ...[ℓ]!).
        -- RHS:     foldl [0, k+1) init = foldl ([0, k) ++ [k]) init
        --        = foldl [k] (foldl [0, k) init)
        --        = add_pure (foldl [0, k) init) (ntt_multiply at c=k ...[ℓ]!).
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        rw [List.range_succ, List.foldl_append]
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((List.range k.val).foldl _ _)
              ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont (t_matrix.coefficients.val[j]!))
                  (lift_chunk_mont (t_s.coefficients.val[j]!))
                  (Spec.zeta_at (64 + 4 * j))
                  (Spec.zeta_at (64 + 4 * j + 1))
                  (Spec.zeta_at (64 + 4 * j + 2))
                  (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)
            = (List.foldl _ ((List.range k.val).foldl _ _) [k.val])
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  ((List.range k.val).foldl _ _)
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (matrix_A.val[k.val]!.coefficients.val[j]!))
                      (lift_chunk_mont (s_as_ntt.val[k.val]!.coefficients.val[j]!))
                      (Spec.zeta_at (64 + 4 * j))
                      (Spec.zeta_at (64 + 4 * j + 1))
                      (Spec.zeta_at (64 + 4 * j + 2))
                      (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)
        -- t_matrix = matrix_A.val[k.val]! and t_s = s_as_ntt.val[k.val]!.
        rfl
      · -- (b) Bound: ≤ acc_init[n] + s_iter.val * 2^25.
        intro n hn
        have h_p_bnd_n := h_p_bnd_rel ⟨n, hn⟩
        -- h_p_bnd_n : (acc1.val[⟨n, hn⟩.val]!).val.natAbs ≤ (acc.val[⟨n, hn⟩.val]!).val.natAbs + 2^25.
        -- Convert Fin .val to plain n by definitional unfold.
        have h_p_bnd_n' : (acc1.val[n]!).val.natAbs ≤ (acc.val[n]!).val.natAbs + 2^25 :=
          h_p_bnd_n
        have h_inv_n := h_inv_acc_bnd n hn
        -- h_inv_n : (acc[n]).val.natAbs ≤ (acc_init[n]).val.natAbs + k.val * 2^25.
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        -- Goal: (acc1[n]).val.natAbs ≤ (acc_init[n]).val.natAbs + (k.val + 1) * 2^25.
        have h_arith : (k.val + 1) * 2^25 = k.val * 2^25 + 2^25 := by ring
        rw [h_arith]
        linarith [h_p_bnd_n', h_inv_n]
      · -- (c) Cache populated for [0, s_iter).
        intro c hc
        rw [hs_iter_val] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
        · -- c < k: cache1[c] = cache[c], use h_inv_cache_done.
          have hc_ne : c ≠ k.val := by omega
          rw [h_cache1_ne c hc_ne]
          exact h_inv_cache_done c hc_lt
        · -- c = k: cache1[k] = cache_chunk1, use h_p_cache_post.
          subst hc_eq
          rw [h_cache1_at]
          -- h_p_cache_post : accumulating_ntt_multiply_poly_cache_post t_s p_pair.2.
          -- cache_chunk1 = p_pair.2; t_s = s_as_ntt.val[k.val]!.
          exact h_p_cache_post
      · -- (d) Cache unchanged for [s_iter, K).
        intro c hc_ge hc_lt
        rw [hs_iter_val] at hc_ge
        have hc_ne : c ≠ k.val := by omega
        rw [h_cache1_ne c hc_ne]
        have hc_ge_k : k.val ≤ c := by omega
        exact h_inv_cache_undone c hc_ge_k hc_lt
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ K, done.
    have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = K.val := by omega
    have h_iter_none :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
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
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt
          { start := k, «end» := K } cache acc
        = .ok (ControlFlow.done (cache, acc)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
    show Stage1FillCacheFC.row0_step_post matrix_A s_as_ntt acc_init cache_init k (.done (cache, acc))
    show (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt acc_init cache_init K acc cache).holds
    unfold Stage1FillCacheFC.row0_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = (List.range K.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (matrix_A.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25)
        ∧ (∀ c : Nat, c < K.val →
            accumulating_ntt_multiply_poly_cache_post
              (s_as_ntt.val[c]!) (cache.val[c]!))
        ∧ (∀ c : Nat, K.val ≤ c → c < K.val →
            cache.val[c]! = cache_init.val[c]!) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj ℓ hℓ
        have h_eq := h_inv_acc j hj ℓ hℓ
        -- h_eq has (List.range k.val); rewrite to (List.range K.val) via hk_eq.
        have h_rng : (List.range k.val) = (List.range K.val) := by rw [hk_eq]
        rw [h_rng] at h_eq
        exact h_eq
      · intro n hn
        have h_b := h_inv_acc_bnd n hn
        have h_arith : k.val * 2^25 = K.val * 2^25 := by rw [hk_eq]
        rw [h_arith] at h_b
        exact h_b
      · intro c hc
        exact h_inv_cache_done c (by rw [hk_eq]; exact hc)
      · intro c hc_ge hc_lt; omega
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- L7.1 Stage 1 — `matrix.compute_As_plus_e_loop0`: the row-0 column loop.
    Iterates over `j ∈ [0, K)`, accumulating column-j's contribution to the
    I32 accumulator and populating `s_cache.val[j]!` with the per-column
    NTT-multiply cache.

    POST: `row0_inv` holds at k = K, i.e. for all (j, ℓ) ∈ [0, 16)²:
    `mont_reduce_pure (lift_fe_int acc[16j+ℓ].val)` equals the K-column
    canonical-form sum of `ntt_multiply_pure_no_acc` outputs starting from
    the initial accumulator's `mont_reduce_pure` lift.

    PRE: the standard 16×16 bound (3328) on `matrix_A` and `s_as_ntt`'s
    entries, K·K matrix length, plus the accumulator BUDGET
    `(acc_init[n]).val.natAbs + K·2^25 ≤ 2^30`. This budget is consumed by
    the per-column inner forward dep (`accumulating_ntt_multiply_fill_cache_poly_fc`,
    PRE `≤ 2^30`) at every iteration: the running accumulator satisfies
    `acc[n] ≤ acc_init[n] + k·2^25 ≤ acc_init[n] + K·2^25 ≤ 2^30` for k ≤ K.

    Mirrors `accumulating_ntt_multiply_fill_cache_poly_fc`
    but at the row-axis K-scale rather than the chunk-axis 16-scale. -/
@[spec]
theorem compute_As_plus_e_loop0_fc
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt s_cache : Std.Array
                          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ i j : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := K } matrix_A s_as_ntt s_cache accumulator
    ⦃ ⇓ p => ⌜ (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt accumulator s_cache K p.2 p.1).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt iter1 p.1 p.2)
      (β := (Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
              × Stage1FillCacheFC.Acc)
      (s_cache, accumulator)
      0#usize K
      (fun k p => Stage1FillCacheFC.row0_inv matrix_A s_as_ntt accumulator s_cache k p.2 p.1)
      (by
        have h0 : (0#usize : Std.Usize).val = 0 := rfl
        rw [h0]; exact Nat.zero_le _)
      (by
        -- Base case at k = 0.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj ℓ hℓ
          show Spec.mont_reduce_pure _
            = (List.range (0#usize : Std.Usize).val).foldl _ _
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']
          show Spec.mont_reduce_pure _ = (List.range 0).foldl _ _
          simp [List.range_zero, List.foldl_nil]
        · intro n _; have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']; omega
        · intro c hc
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0'] at hc
          exact absurd hc (Nat.not_lt_zero c)
        · intro c _ _; trivial)
      ?_)
  · -- Post entailment: the final invariant holds at K.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt accumulator s_cache K r.2 r.1).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    show (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt accumulator s_cache K r.2 r.1).holds
    exact h_inv_holds
  · -- Step entailment.
    intro p k _h_ge h_le hinv
    have h_step := compute_As_plus_e_loop0_step_lemma_fc
      matrix_A s_as_ntt accumulator s_cache hAlen h_matrix_bnd h_s_bnd h_acc_bnd
      p.2 p.1 k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', cache_acc⟩ | y
    · have hP : Stage1FillCacheFC.row0_step_post matrix_A s_as_ntt accumulator s_cache k
                  (.cont (iter', cache_acc.1, cache_acc.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage1FillCacheFC.row0_step_post] using hP
    · have hP : Stage1FillCacheFC.row0_step_post matrix_A s_as_ntt accumulator s_cache k
                  (.done (y.1, y.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage1FillCacheFC.row0_step_post] using hP

end L7_1a_irreducible

/-! ## §L7.1-loop1-loop0 — row-i (i ≥ 1) column loop scaffolding.

    Namespace `Stage2UseCacheFC` provides the invariant + step-post predicates
    used to characterize `matrix.compute_As_plus_e_loop1_loop0` (the
    K-iteration column loop run once per row i ∈ [1, K)) via
    `loop_range_spec_usize`. Each iteration calls
    `accumulating_ntt_multiply_use_cache` on column `j ∈ [0, K)`, adding
    column j's contribution to the I32 accumulator. Unlike Stage 1
    (`compute_As_plus_e_loop0`), the cache is INPUT only — it was
    populated by Stage 1's column loop on row 0, and is consumed
    read-only here.

    Mirrors `Stage1FillCacheFC` minus the two cache-state
    conjuncts (3)/(4), and with the matrix lane index parameterized by
    the row index `i` (i.e. `i.val * K.val + c` rather than
    `0 * K.val + c`). The per-column forward dep is
    `accumulating_ntt_multiply_use_cache_poly_fc`
    instead of `_fill_cache_poly_fc`. -/

namespace Stage2UseCacheFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 2-conjunct invariant for the row-i (i ≥ 1) column loop. Tracks:
    (1) accumulator characterization: for each (chunk j, lane ℓ) in
        `[0, 16)²`, `Spec.mont_reduce_pure (lift_fe_int acc[16j+ℓ].val)`
        equals init plus the canonical-form sum of column contributions
        from columns `[0, k)` for the fixed row `i`.
    (2) accumulator bound: `|acc.val[n]| ≤ |acc_init.val[n]| + k · 2^25`. -/
def row_i_inv {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) (i : Std.Usize) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    -- (1) Per-(chunk j, lane ℓ) accumulator: canonical-form k-column sum.
    (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
      Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
        = (List.range k.val).foldl
            (fun s c =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (matrix_A.val[i.val * K.val + c]!.coefficients.val[j]!))
                    (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
            (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
    -- (2) Accumulator bound grows by 2^25 per column iteration.
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k.val * 2^25))

/-- Step-post for `loop_range_spec_usize` over the accumulator only. -/
def row_i_step_post {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) (i : Std.Usize) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) :
    Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (row_i_inv matrix_A s_as_ntt acc_init i iter'.start acc').holds
  | .done y => (row_i_inv matrix_A s_as_ntt acc_init i K y).holds

end Stage2UseCacheFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Mirrors `L7_1a_irreducible`
-- — heavy POST predicates and the per-column forward dep
-- are made locally irreducible across the step lemma + outer Triple so that
-- elaboration does not whnf-explode through the 2-conjunct `row_i_inv` body or
-- the nested `∀ j : Fin 16, ∀ ℓ : Fin 16` accumulator characterization.
-- we do NOT mark
-- `Stage2UseCacheFC.row_i_inv` / `row_i_step_post` irreducible.
section L7_1b_irreducible
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- Per-iteration FC step lemma for the row-i (i ≥ 1) column loop. Given
    the `row_i_inv` invariant at step k and the strengthened PRE bounds
    + the cache-post hypothesis, executing one body iteration of
    `matrix.compute_As_plus_e_loop1_loop0.body` produces the
    `row_i_step_post` (either `.cont` advancing the invariant to k+1 or
    `.done` capping at K).

    Mirrors `compute_As_plus_e_loop0_step_lemma_fc` but
    with three differences:
    1. No cache mutation: cache is INPUT only.
    2. Matrix lane uses `i.val * K.val + k.val` rather than
       `0 * K.val + k.val = k.val`.
    3. Per-column forward dep is `accumulating_ntt_multiply_use_cache_poly_fc` instead of `_fill_cache_poly_fc`. This requires the
       cache-post hypothesis at column k:
       `accumulating_ntt_multiply_poly_cache_post (s_as_ntt[k]!) (s_cache[k]!)`.
       We pass the OUTER ∀-quantified hypothesis through the step lemma so the
       main theorem can hand it through unchanged. -/
theorem compute_As_plus_e_loop1_loop0_step_lemma_fc
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt s_cache : Std.Array
                          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Stage2UseCacheFC.Acc)
    (i : Std.Usize) (hi : i.val < K.val)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ a b : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (s_as_ntt.val[c]!) (s_cache.val[c]!))
    (acc : Stage2UseCacheFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ K.val)
    (h_inv : (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt acc_init i k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt s_cache i
      { start := k, «end» := K } acc
    ⦃ ⇓ r => ⌜ Stage2UseCacheFC.row_i_step_post matrix_A s_as_ntt acc_init i k r ⌝ ⦄ := by
  have h_s_as_ntt_len : s_as_ntt.length = K.val := Std.Array.length_eq s_as_ntt
  have h_s_cache_len : s_cache.length = K.val := Std.Array.length_eq s_cache
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 2-conjunct invariant.
  obtain ⟨h_inv_acc, h_inv_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch.
    -- (1) IteratorRange.next reduces to .ok (some k, { start := s_iter, end := K }).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
          core.Usize.Insts.CoreIterRangeStep
          ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                    r = (some k,
                        ({ start := s, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
      libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
        (fun _ s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨s, hs, rfl⟩)
        (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
    obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
    obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
    -- (2) matrix.entry reduces to .ok matrix_A.val[i.val * K.val + k.val]!.
    have h_matrix_entry :
        libcrux_iot_ml_kem.matrix.entry K portable_ops_inst matrix_A i k
          = .ok (matrix_A.val[i.val * K.val + k.val]!) :=
      entry_eq_ok_fc_aux K matrix_A i k hAlen hi h_lt
    set t_matrix : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      matrix_A.val[i.val * K.val + k.val]! with ht_matrix_def
    -- (3) Array.index_usize s_as_ntt k reduces to .ok s_as_ntt[k.val]!.
    set t_s : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      s_as_ntt.val[k.val]! with ht_s_def
    have h_idx_s : Aeneas.Std.Array.index_usize s_as_ntt k = .ok t_s :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq s_as_ntt k
        (by rw [h_s_as_ntt_len]; exact h_lt)
    -- (4) Array.index_usize s_cache k reduces to .ok s_cache[k.val]!. (read-only)
    set t_cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      s_cache.val[k.val]! with ht_cache_def
    have h_idx_cache : Aeneas.Std.Array.index_usize s_cache k = .ok t_cache :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq s_cache k
        (by rw [h_s_cache_len]; exact h_lt)
    -- (5) Apply L6.3c per-column forward dep at column k (use_cache flavor).
    -- Per-lane bounds on t_matrix and t_s (16×16 lanes).
    have hK_pos : 0 < K.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt
    have h_iKk_lt_KK : i.val * K.val + k.val < K.val * K.val := by
      have h_iK_lt : i.val * K.val + K.val ≤ K.val * K.val := by
        have hstep : (i.val + 1) * K.val ≤ K.val * K.val :=
          Nat.mul_le_mul_right _ hi
        have h_expand : (i.val + 1) * K.val = i.val * K.val + K.val := by ring
        rw [h_expand] at hstep; exact hstep
      omega
    have h_iKk_lt_len : i.val * K.val + k.val < matrix_A.length := by
      rw [hAlen]; exact h_iKk_lt_KK
    have h_t_matrix_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_matrix.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_matrix_bnd ⟨i.val * K.val + k.val, h_iKk_lt_len⟩ a b
    have h_t_s_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_s.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_s_bnd ⟨k.val, h_lt⟩ a b
    -- Cache-post hypothesis at column k.
    have h_cache_at_k : accumulating_ntt_multiply_poly_cache_post t_s t_cache :=
      h_cache k.val h_lt
    -- Current acc bound ≤ 2^30: combine inv conjunct (2) with budget PRE.
    have h_acc_cur_bnd : ∀ n : Fin 256, (acc.val[n.val]!).val.natAbs ≤ 2^30 := by
      intro n
      have hb := h_inv_acc_bnd n.val n.isLt
      have hp := h_acc_bnd n
      have hk_le : k.val * 2^25 ≤ K.val * 2^25 := Nat.mul_le_mul_right _ h_le
      omega
    obtain ⟨acc1, h_acc1_eq, h_acc1_bnd_rel, h_acc1_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_use_cache_poly_fc t_matrix t_s t_cache acc
          h_t_matrix_bnd h_t_s_bnd h_acc_cur_bnd h_cache_at_k)
    -- (6) Body equation.
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt s_cache i
          { start := k, «end» := K } acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), acc1)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
              let pre ← libcrux_iot_ml_kem.matrix.entry K portable_ops_inst
                          matrix_A i k
              let pre1 ← Aeneas.Std.Array.index_usize s_as_ntt k
              let pre2 ← Aeneas.Std.Array.index_usize s_cache k
              let accumulator1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache
                  portable_ops_inst pre pre1 acc pre2
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), accumulator1)))
            : Result _) = _
      rw [h_matrix_entry]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_s]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_cache]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_acc1_eq]
      rfl
    apply triple_of_ok_fc h_body
    -- (7) Discharge the step_post.
    show Stage2UseCacheFC.row_i_step_post matrix_A s_as_ntt acc_init i k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), acc1))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    -- (8) Re-establish `row_i_inv` at s_iter (= k+1).
    show (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt acc_init i s_iter acc1).holds
    unfold Stage2UseCacheFC.row_i_inv
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = (List.range s_iter.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (matrix_A.val[i.val * K.val + c]!.coefficients.val[j]!))
                        (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + s_iter.val * 2^25) := by
      refine ⟨?_, ?_⟩
      · -- (a) Accumulator characterization at s_iter = k+1.
        intro j hj ℓ hℓ
        have h_step_acc :
            Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val))
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (t_matrix.coefficients.val[j]!))
                      (lift_chunk_mont (t_s.coefficients.val[j]!))
                      (Spec.zeta_at (64 + 4 * j))
                      (Spec.zeta_at (64 + 4 * j + 1))
                      (Spec.zeta_at (64 + 4 * j + 2))
                      (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!) := by
          have := h_acc1_post
          unfold accumulating_ntt_multiply_poly_post at this
          exact this j hj ℓ hℓ
        have h_ih := h_inv_acc j hj ℓ hℓ
        rw [h_step_acc, h_ih]
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        rw [List.range_succ, List.foldl_append]
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((List.range k.val).foldl _ _)
              ((Spec.ntt_multiply_pure_no_acc
                  (lift_chunk_mont (t_matrix.coefficients.val[j]!))
                  (lift_chunk_mont (t_s.coefficients.val[j]!))
                  (Spec.zeta_at (64 + 4 * j))
                  (Spec.zeta_at (64 + 4 * j + 1))
                  (Spec.zeta_at (64 + 4 * j + 2))
                  (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)
            = (List.foldl _ ((List.range k.val).foldl _ _) [k.val])
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  ((List.range k.val).foldl _ _)
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (matrix_A.val[i.val * K.val + k.val]!.coefficients.val[j]!))
                      (lift_chunk_mont (s_as_ntt.val[k.val]!.coefficients.val[j]!))
                      (Spec.zeta_at (64 + 4 * j))
                      (Spec.zeta_at (64 + 4 * j + 1))
                      (Spec.zeta_at (64 + 4 * j + 2))
                      (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)
        rfl
      · -- (b) Bound: ≤ acc_init[n] + s_iter.val * 2^25.
        intro n hn
        have h_acc1_bnd_n := h_acc1_bnd_rel ⟨n, hn⟩
        have h_acc1_bnd_n' : (acc1.val[n]!).val.natAbs ≤ (acc.val[n]!).val.natAbs + 2^25 :=
          h_acc1_bnd_n
        have h_inv_n := h_inv_acc_bnd n hn
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        have h_arith : (k.val + 1) * 2^25 = k.val * 2^25 + 2^25 := by ring
        rw [h_arith]
        linarith [h_acc1_bnd_n', h_inv_n]
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ K, done.
    have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = K.val := by omega
    have h_iter_none :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
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
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt s_cache i
          { start := k, «end» := K } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
    show Stage2UseCacheFC.row_i_step_post matrix_A s_as_ntt acc_init i k (.done acc)
    show (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt acc_init i K acc).holds
    unfold Stage2UseCacheFC.row_i_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = (List.range K.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (matrix_A.val[i.val * K.val + c]!.coefficients.val[j]!))
                        (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25) := by
      refine ⟨?_, ?_⟩
      · intro j hj ℓ hℓ
        have h_eq := h_inv_acc j hj ℓ hℓ
        have h_rng : (List.range k.val) = (List.range K.val) := by rw [hk_eq]
        rw [h_rng] at h_eq
        exact h_eq
      · intro n hn
        have h_b := h_inv_acc_bnd n hn
        have h_arith : k.val * 2^25 = K.val * 2^25 := by rw [hk_eq]
        rw [h_arith] at h_b
        exact h_b
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- L7.1 Stage 2 — `matrix.compute_As_plus_e_loop1_loop0`: the row-i
    (i ≥ 1) column loop. Iterates over `j ∈ [0, K)`, accumulating
    column-j's contribution to the I32 accumulator via
    `accumulating_ntt_multiply_use_cache`. The cache is INPUT only —
    populated by Stage 1's row-0 column loop and consumed read-only here.

    POST: `row_i_inv` holds at k = K, i.e. for all (j, ℓ) ∈ [0, 16)²:
    `mont_reduce_pure (lift_fe_int acc[16j+ℓ].val)` equals the K-column
    canonical-form sum at row `i` of `ntt_multiply_pure_no_acc` outputs
    starting from the initial accumulator's `mont_reduce_pure` lift.

    PRE: standard 16×16 bound (3328) on matrix and s_as_ntt entries, the
    K·K matrix-length axiom, `hK : K.val ≤ 4`, `hi : i.val < K.val`, the
    additive accumulator BUDGET `(acc_init[n]).val.natAbs + K·2^25 ≤ 2^30`,
    and the cache-post hypothesis `h_cache` — at every column c < K,
    `s_cache.val[c]!` satisfies `accumulating_ntt_multiply_poly_cache_post`
    against `s_as_ntt.val[c]!`. The latter is established by Stage 1's
    final invariant (row-0 column loop populates the cache).

    Mirrors `compute_As_plus_e_loop0_fc` minus cache
    threading; the cache passes through as a read-only parameter. -/
@[spec]
theorem compute_As_plus_e_loop1_loop0_fc
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt s_cache : Std.Array
                          (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (i : Std.Usize)
    (hi : i.val < K.val)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ a b : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (s_as_ntt.val[c]!) (s_cache.val[c]!)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := K } matrix_A s_as_ntt s_cache accumulator i
    ⦃ ⇓ p => ⌜ (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt accumulator i K p).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt s_cache i
          iter1 acc1)
      (β := Stage2UseCacheFC.Acc)
      accumulator
      0#usize K
      (fun k acc => Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt accumulator i k acc)
      (by
        have h0 : (0#usize : Std.Usize).val = 0 := rfl
        rw [h0]; exact Nat.zero_le _)
      (by
        -- Base case at k = 0.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_⟩
        · intro j hj ℓ hℓ
          show Spec.mont_reduce_pure _
            = (List.range (0#usize : Std.Usize).val).foldl _ _
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']
          show Spec.mont_reduce_pure _ = (List.range 0).foldl _ _
          simp [List.range_zero, List.foldl_nil]
        · intro n _; have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']; omega)
      ?_)
  · -- Post entailment: the final invariant holds at K.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt accumulator i K r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    show (Stage2UseCacheFC.row_i_inv matrix_A s_as_ntt accumulator i K r).holds
    exact h_inv_holds
  · -- Step entailment.
    intro acc k _h_ge h_le hinv
    have h_step := compute_As_plus_e_loop1_loop0_step_lemma_fc
      matrix_A s_as_ntt s_cache accumulator i hi hAlen h_matrix_bnd h_s_bnd h_acc_bnd
      h_cache acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Stage2UseCacheFC.row_i_step_post matrix_A s_as_ntt accumulator i k
                  (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage2UseCacheFC.row_i_step_post] using hP
    · have hP : Stage2UseCacheFC.row_i_step_post matrix_A s_as_ntt accumulator i k
                  (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage2UseCacheFC.row_i_step_post] using hP

end L7_1b_irreducible

/-! ## §L7.1-loop1 — outer rows loop (rows i ∈ [start, K)) scaffolding.

    Namespace `Stage3MontStripFC` provides the invariant + step-post predicates
    for `matrix.compute_As_plus_e_loop1` (the outer rows loop) via
    `loop_range_spec_usize`. Each iteration covers one full row i:
    re-zeros accumulator, calls `compute_As_plus_e_loop1_loop0_fc`
    (Stage 2) for the column sum, converts via `reducing_from_i32_array`
    to Mont FE form, then applies `add_standard_error_reduce` (×1353 +
    add error) to produce the canonical FE row.

    Composes Stage 2 + L6.7 (poly_reducing_from_i32_array_fc) + L6.5
    (add_standard_error_reduce_fc) per row. The per-lane invariant equation
    has the form `(lift_poly t_as_ntt[r]).val[lane]! =
    add_pure (mul_pure (canonical_row_sum_lane ...) (lift_fe_mont 1353))
              ((lift_poly error[r]).val[lane]!)`, where
    `canonical_row_sum_lane` absorbs ONE Mont→canonical bridge step
    (mul_pure × lift_fe_mont 1353) over the K-fold sum-in-Mont produced
    by Stage 2+L6.7; the OUTER × 1353 in the invariant comes from L6.5's
    own `mul_pure self (lift_fe_mont 1353)` step. -/

namespace Stage3MontStripFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev TVec (K : Std.Usize) := Std.Array
  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K

abbrev Acc := Std.Array Std.I32 256#usize

/-- The canonical-form per-(row i, chunk j, lane-within-chunk q) value:
    the column-K sum of `Spec.ntt_multiply_pure_no_acc` contributions
    extracted at chunk j, lane q, with the OUTER Mont→canonical bridge
    (`mul_pure _ (lift_fe_mont 1353)`) folded in. This equals
    `(lift_poly pre1).val[16*j+q]!` after the Stage 2 + L6.7 + bridge
    composition, where `pre1` is L6.7's Mont-form polynomial output.

    Per-row composition with L6.5 then gives the canonical FE row:
    `(lift_poly t_as_ntt[r]!).val[lane]!
      = add_pure (mul_pure (canonical_row_sum_lane ...) (lift_fe_mont 1353))
                 ((lift_poly error[r]!).val[lane]!)`
    where lane = 16*j + q.

    The foldl seed `Spec.mont_reduce_pure (lift_fe_int 0)` matches the
    zero-init accumulator after Stage 2 — each iteration of the outer
    loop re-zeros via `Array.repeat 256#usize (classify 0#i32)`, so the
    `acc_init` slot in Stage 2's invariant collapses to the zero
    accumulator's `mont_reduce_pure (lift_fe_int 0)` constant. -/
noncomputable def canonical_row_sum_lane
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : TVec K) (i : Nat) (j q : Nat) :
    hacspec_ml_kem.parameters.FieldElement :=
  libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
    ((List.range K.val).foldl
      (fun s c =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
          ((Spec.ntt_multiply_pure_no_acc
              (lift_chunk_mont (matrix_A.val[i * K.val + c]!.coefficients.val[j]!))
              (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[j]!))
              (Spec.zeta_at (64 + 4 * j))
              (Spec.zeta_at (64 + 4 * j + 1))
              (Spec.zeta_at (64 + 4 * j + 2))
              (Spec.zeta_at (64 + 4 * j + 3))).val[q]!))
      (Spec.mont_reduce_pure (lift_fe_int 0)))
    (lift_fe_mont (1353#i16 : Std.I16))

/-- 2-conjunct invariant for the outer rows loop. Tracks:
    (1) Per-completed-row characterization: for each row `r ∈ [start, k)`,
        and each lane `ℓ ∈ [0, 256)`,
        `(lift_poly t_as_ntt.val[r]!).val[ℓ]!`
          = `add_pure (mul_pure (canonical_row_sum_lane matrix_A s_as_ntt r (ℓ/16) (ℓ%16))
                                (lift_fe_mont 1353))
                     ((lift_poly error_as_ntt.val[r]!).val[ℓ]!)`.
    (2) Unchanged rows: for each row `r ∈ [0, K)` with
        `r < start.val ∨ k.val ≤ r`,
        `t_as_ntt.val[r]! = t_as_ntt_init.val[r]!`. -/
def rows_inv {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt : TVec K)
    (t_as_ntt_init : TVec K) (start : Std.Usize) :
    Std.Usize → TVec K → Acc → Result Prop :=
  fun k t_as_ntt _acc => pure (
    (∀ r : Nat, start.val ≤ r → r < k.val → ∀ ℓ : Nat, ℓ < 256 →
      (lift_poly t_as_ntt.val[r]!).val[ℓ]!
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (canonical_row_sum_lane matrix_A s_as_ntt r (ℓ / 16) (ℓ % 16))
              (lift_fe_mont (1353#i16 : Std.I16)))
            ((lift_poly error_as_ntt.val[r]!).val[ℓ]!))
    ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ k.val ≤ r) →
        t_as_ntt.val[r]! = t_as_ntt_init.val[r]!)
    ∧ (∀ r : Nat, start.val ≤ r → r < k.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
        ((t_as_ntt.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize` over (t_as_ntt, accumulator). -/
def rows_step_post {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt : TVec K)
    (t_as_ntt_init : TVec K) (start : Std.Usize) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × TVec K × Acc)
      (TVec K × Acc)) :
    Prop :=
  match r with
  | .cont (iter', t', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
            iter'.start t' acc').holds
  | .done y => (rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
                  K y.1 y.2).holds

end Stage3MontStripFC

/-! ## §L7.1 Stage 4 bridge lemmas — `chunk_at (lift_poly _)` ↔ `lift_chunk_mont _`.

    These two helpers connect the `Spec.multiply_ntts_pure_eq_chunked_no_acc`
    side (which operates on `chunk_at (lift_poly _)` chunks, i.e. canonical
    `lift_fe` lanes) to the `Stage3MontStripFC.canonical_row_sum_lane` side (which
    operates on `lift_chunk_mont _` chunks, i.e. Mont-stripped `lift_fe_mont`
    lanes). The relationship per lane is exactly the FE-level
    `lift_fe_mont_mul_1353_eq_lift_fe` identity at.

    Both helpers are private to FCTargets and used only by the L7.1 Stage 4
    closing argument. -/

namespace Stage3MontStripFC

set_option maxHeartbeats 1000000 in
/-- Per-lane bridge: `Spec.chunk_at (lift_poly p) j` interprets each I16
    lane via `lift_fe` (canonical, value = `x.val mod q`), while
    `lift_chunk_mont p.coefficients.val[j]!` uses `lift_fe_mont` (Mont-
    stripped, value = `x.val · R⁻¹ mod q`). The conversion factor is
    `lift_fe_mont 1353 = R` (since `1353 = R² mod q`, so
    `lift_fe_mont 1353 = 1353 · R⁻¹ = R²·R⁻¹ = R mod q`). Thus
    `lift_fe x = (lift_fe_mont x) · R = (lift_fe_mont x) · (lift_fe_mont 1353)`,
    which is exactly `lift_fe_mont_mul_1353_eq_lift_fe`. -/
theorem chunk_at_lift_poly_lane
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (h_j : j < 16) (q : Nat) (h_q : q < 16) :
    (Spec.chunk_at (lift_poly p) j).val[q]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((lift_chunk_mont p.coefficients.val[j]!).val[q]!)
          (lift_fe_mont (1353#i16 : Std.I16)) := by
  -- Pin the underlying I16 lane shared by both sides.
  set x : Std.I16 :=
    (p.coefficients.val[j]!).elements.val[q]! with hx_def
  -- The elements list has length 16 (from PortableVector's invariant).
  have h_elem_len : ((p.coefficients.val[j]!).elements.val).length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
  -- (A) RHS factor: `(lift_chunk_mont p.coefficients.val[j]!).val[q]! = lift_fe_mont x`.
  have h_mont : (lift_chunk_mont p.coefficients.val[j]!).val[q]! = lift_fe_mont x := by
    unfold lift_chunk_mont
    show (((p.coefficients.val[j]!).elements.val).map lift_fe_mont)[q]!
          = lift_fe_mont x
    have h_len : (((p.coefficients.val[j]!).elements.val).map lift_fe_mont).length = 16 := by
      rw [List.length_map]; exact h_elem_len
    rw [getElem!_pos _ q (by rw [h_len]; exact h_q)]
    rw [List.getElem_map]
    -- Goal: lift_fe_mont ((p.coefficients.val[j]!).elements.val[q]) = lift_fe_mont x.
    -- Convert `[q]` (with bounds proof) back to `[q]!` to match `x`'s definition.
    rw [show ((p.coefficients.val[j]!).elements.val)[q]
            = ((p.coefficients.val[j]!).elements.val)[q]! from
          (getElem!_pos _ q (by rw [h_elem_len]; exact h_q)).symm]
  -- (B) LHS: `(Spec.chunk_at (lift_poly p) j).val[q]! = lift_fe x`.
  have h_plain : (Spec.chunk_at (lift_poly p) j).val[q]! = lift_fe x := by
    unfold Spec.chunk_at
    show ((List.range 16).map (fun j' => (lift_poly p).val[16 * j + j']!))[q]!
          = lift_fe x
    have h_len_outer : ((List.range 16).map
        (fun j' => (lift_poly p).val[16 * j + j']!)).length = 16 := by simp
    rw [getElem!_pos _ q (by rw [h_len_outer]; exact h_q)]
    rw [List.getElem_map, List.getElem_range]
    -- Goal: (lift_poly p).val[16 * j + q]! = lift_fe x.
    have h_lane : 16 * j + q < 256 := by omega
    unfold lift_poly
    show ((List.range 256).map (fun n =>
            lift_fe (p.coefficients.val[n / 16]!).elements.val[n % 16]!))[16 * j + q]!
          = lift_fe x
    have h_len_inner : ((List.range 256).map (fun n =>
            lift_fe (p.coefficients.val[n / 16]!).elements.val[n % 16]!)).length = 256 := by simp
    rw [getElem!_pos _ (16 * j + q) (by rw [h_len_inner]; exact h_lane)]
    rw [List.getElem_map, List.getElem_range]
    -- Goal: lift_fe (p.coefficients.val[(16*j+q)/16]!).elements.val[(16*j+q)%16]! = lift_fe x.
    have h_div : (16 * j + q) / 16 = j := by omega
    have h_mod : (16 * j + q) % 16 = q := by omega
    rw [h_div, h_mod]
  rw [h_mont, h_plain]
  -- Goal: lift_fe x = mul_pure (lift_fe_mont x) (lift_fe_mont 1353).
  rw [lift_fe_mont_mul_1353_eq_lift_fe]

/-- Per-lane reduction of `Spec.ntt_multiply_pure_no_acc` projection.

    Used by `ntt_multiply_pure_no_acc_lane_scale` to give both sides a
    uniform `if q%2=0 ...` shape over the four operand projections
    (`.val[2·(q/2)]!`, `.val[2·(q/2)+1]!`). The reduction is `rfl` after
    unfolding `Spec.ntt_multiply_pure_no_acc` and projecting through
    `Std.Array.make` + `(List.range 16).map`.

    The 8-zeta list is materialized inline (no `let`) so downstream
    `simp`/`rw` substitutions see explicit `FieldElement.{add,mul,neg}_pure`
    head symbols for `zmodOfFE_{add,mul}_pure` simp-set rewrites. -/
theorem ntt_multiply_pure_no_acc_val_q
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta0 zeta1 zeta2 zeta3 : hacspec_ml_kem.parameters.FieldElement)
    (q : Nat) (h_q : q < 16) :
    (Spec.ntt_multiply_pure_no_acc a b zeta0 zeta1 zeta2 zeta3).val[q]!
      = (let neg := libcrux_iot_ml_kem.Spec.Pure.FieldElement.neg_pure
         let zeta_q : hacspec_ml_kem.parameters.FieldElement :=
           [zeta0, neg zeta0, zeta1, neg zeta1,
            zeta2, neg zeta2, zeta3, neg zeta3][q / 2]!
         if q % 2 = 0 then
           libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
             (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
               a.val[2 * (q / 2)]! b.val[2 * (q / 2)]!)
             (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
               (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                 a.val[2 * (q / 2) + 1]! b.val[2 * (q / 2) + 1]!)
               zeta_q)
         else
           libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
             (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
               a.val[2 * (q / 2)]! b.val[2 * (q / 2) + 1]!)
             (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
               a.val[2 * (q / 2) + 1]! b.val[2 * (q / 2)]!)) := by
  unfold Spec.ntt_multiply_pure_no_acc
  rw [show ∀ (l : List hacspec_ml_kem.parameters.FieldElement)
          (h : l.length = (16#usize : Std.Usize).val),
          (Std.Array.make 16#usize l h).val[q]! = l[q]! from fun _ _ => rfl,
      List.getElem!_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h_q,
      Option.map_some, Option.getD_some]

set_option maxHeartbeats 8000000 in
/-- **Bilinearity of `Spec.ntt_multiply_pure_no_acc` over a per-lane scalar.**

    If inputs `a, b` scale `am, bm` lane-wise by a common scalar `c`, then
    each output lane scales by `c²`. Proof:
    - Reduce both `.val[q]!` lookups via `ntt_multiply_pure_no_acc_val_q`
      (uniform `if q%2=0 ...` form over `2·(q/2), 2·(q/2)+1`).
    - Substitute `h_a, h_b` at those four positions, exposing
      `mul_pure am_k c` / `mul_pure bm_k c` factors.
    - Case-split `q % 2 = 0 ∨ q % 2 = 1` and project via `zmodOfFE` to
      `ZMod 3329`; canonical round-trip + `ring` closes each branch.

    Used by Helper 2 (`ntt_multiply_pure_no_acc_chunk_at_lift_poly_eq`) as
    a 1-line corollary with `c = lift_fe_mont 1353`. -/
theorem ntt_multiply_pure_no_acc_lane_scale
    (a am b bm : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (c : hacspec_ml_kem.parameters.FieldElement)
    (h_a : ∀ k : Nat, k < 16 → a.val[k]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure am.val[k]! c)
    (h_b : ∀ k : Nat, k < 16 → b.val[k]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure bm.val[k]! c)
    (zeta0 zeta1 zeta2 zeta3 : hacspec_ml_kem.parameters.FieldElement)
    (q : Nat) (h_q : q < 16) :
    (Spec.ntt_multiply_pure_no_acc a b zeta0 zeta1 zeta2 zeta3).val[q]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((Spec.ntt_multiply_pure_no_acc am bm zeta0 zeta1 zeta2 zeta3).val[q]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure c c) := by
  have h_2pi : 2 * (q / 2) < 16 := by omega
  have h_2pi1 : 2 * (q / 2) + 1 < 16 := by omega
  rw [ntt_multiply_pure_no_acc_val_q a b _ _ _ _ q h_q,
      ntt_multiply_pure_no_acc_val_q am bm _ _ _ _ q h_q]
  rw [h_a (2 * (q / 2)) h_2pi, h_a (2 * (q / 2) + 1) h_2pi1,
      h_b (2 * (q / 2)) h_2pi, h_b (2 * (q / 2) + 1) h_2pi1]
  -- Helper: canonical round-trip closer.
  have h_close : ∀ s t : hacspec_ml_kem.parameters.FieldElement,
      s.val.val < 3329 → t.val.val < 3329 →
      zmodOfFE s = zmodOfFE t → s = t := by
    intro s t hs ht heq
    rw [← feOfZMod_zmodOfFE_of_canonical s hs,
        ← feOfZMod_zmodOfFE_of_canonical t ht, heq]
  -- Helper: `Canonical x → x.val.val < 3329`.
  have h_canon_to_lt : ∀ x : hacspec_ml_kem.parameters.FieldElement,
      libcrux_iot_ml_kem.Spec.Pure.Canonical x → x.val.val < 3329 := by
    intro x hx
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at hx
    exact hx
  -- Case split on q % 2.
  rcases (show q % 2 = 0 ∨ q % 2 = 1 from by omega) with h_par | h_par
  · -- q % 2 = 0 branch.
    rw [if_pos h_par, if_pos h_par]
    apply h_close
    · apply h_canon_to_lt
      exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
    · apply h_canon_to_lt
      exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
    · simp only [L2_8c.zmodOfFE_add_pure, L2_8c.zmodOfFE_mul_pure]
      ring
  · -- q % 2 = 1 branch.
    have h_par_ne : q % 2 ≠ 0 := by omega
    rw [if_neg h_par_ne, if_neg h_par_ne]
    apply h_close
    · apply h_canon_to_lt
      exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
    · apply h_canon_to_lt
      exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
    · simp only [L2_8c.zmodOfFE_add_pure, L2_8c.zmodOfFE_mul_pure]
      ring

/-- **L7.1 Stage 4 chunked bilinearity bridge (Helper 2).**

    Connects per-chunk `Spec.chunk_at (lift_poly _)` (canonical lift, used
    by .4 `Spec.multiply_ntts_pure_eq_chunked_no_acc`) to
    `lift_chunk_mont _` (Mont-stripped, used by `canonical_row_sum_lane`)
    via the bilinearity of `Spec.ntt_multiply_pure_no_acc`. Both inputs
    differ from the Mont versions by per-lane `× lift_fe_mont 1353` (= R
    in ZMod 3329), so the per-lane output differs by `(lift_fe_mont 1353)²`.

    1-line composition: `ntt_multiply_pure_no_acc_lane_scale` with
    `c = lift_fe_mont 1353` and lane hypothesis `chunk_at_lift_poly_lane`. -/
theorem ntt_multiply_pure_no_acc_chunk_at_lift_poly_eq
    (a b : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (h_j : j < 16)
    (zeta0 zeta1 zeta2 zeta3 : hacspec_ml_kem.parameters.FieldElement)
    (q : Nat) (h_q : q < 16) :
    (Spec.ntt_multiply_pure_no_acc
        (Spec.chunk_at (lift_poly a) j) (Spec.chunk_at (lift_poly b) j)
        zeta0 zeta1 zeta2 zeta3).val[q]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((Spec.ntt_multiply_pure_no_acc
              (lift_chunk_mont a.coefficients.val[j]!)
              (lift_chunk_mont b.coefficients.val[j]!)
              zeta0 zeta1 zeta2 zeta3).val[q]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont (1353#i16 : Std.I16))
            (lift_fe_mont (1353#i16 : Std.I16))) :=
  ntt_multiply_pure_no_acc_lane_scale
    (Spec.chunk_at (lift_poly a) j) (lift_chunk_mont a.coefficients.val[j]!)
    (Spec.chunk_at (lift_poly b) j) (lift_chunk_mont b.coefficients.val[j]!)
    (lift_fe_mont (1353#i16 : Std.I16))
    (fun k h_k => chunk_at_lift_poly_lane a j h_j k h_k)
    (fun k h_k => chunk_at_lift_poly_lane b j h_j k h_k)
    zeta0 zeta1 zeta2 zeta3 q h_q

end Stage3MontStripFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Heavy `accumulating_ntt_multiply_*_post`
-- predicates + the `canonical_row_sum_lane` foldl are made locally irreducible across
-- the Stage 3 step lemma + main Triple to keep elaboration tractable through the 2-conjunct
-- `rows_inv` body. We do NOT mark `Stage3MontStripFC.rows_inv` / `rows_step_post`
-- irreducible — keeping them reducible preserves the `simpa`-based
-- destructure of `h_inv`.
section L7_1c_irreducible
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure
attribute [local irreducible] Stage3MontStripFC.canonical_row_sum_lane

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the outer rows loop. Given the
    `Stage3MontStripFC.rows_inv` invariant at step `k` and the strengthened PRE bounds,
    executing one body iteration of `matrix.compute_As_plus_e_loop1.body`
    produces the `Stage3MontStripFC.rows_step_post` (either `.cont` advancing the
    invariant to `k+1` or `.done` capping at `K`).

    Per-iteration step composes:
    1. `iter.next` → row index `i = k`.
    2. `classify 0#i32` → `i1 = 0#i32`; `Array.repeat 256#usize 0#i32` →
       `accumulator1` (zeroed accumulator).
    3. Stage 2 (`compute_As_plus_e_loop1_loop0_fc`) on row `i` with the zeroed
       accumulator. Yields `accumulator2` satisfying `Stage2UseCacheFC.row_i_inv`.
    4. `lift (Array.to_slice accumulator2)` → `s`.
    5. `Array.index_mut_usize t_as_ntt i` → `(pre, set t_as_ntt i)`.
    6. L6.7 (`poly_reducing_from_i32_array_fc`, NOW STRENGTHENED) on `s` and
       `pre`. Yields Mont-form `t1` with per-lane bound `≤ 4993`.
    7. `t_as_ntt1 := set t_as_ntt i t1`.
    8. `Array.index_mut_usize t_as_ntt1 i` → `(t1, set t_as_ntt1 i)`.
    9. `Array.index_usize error_as_ntt i` → `error_as_ntt[i]`.
    10. L6.5 (`add_standard_error_reduce_fc`) on (t1, error_as_ntt[i]). Uses
        `4993 ≤ 32767` to discharge the L6.5 self-bound PRE.
    11. `a := set t_as_ntt1 i pre4`.
    12. Re-establish `rows_inv` at `k+1`. -/
theorem compute_As_plus_e_loop1_step_lemma_fc
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
                                       (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                         libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (t_as_ntt_init : Stage3MontStripFC.TVec K)
    (start : Std.Usize)
    (hK : K.val ≤ 4)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ a b : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_error_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((error_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (s_as_ntt.val[c]!) (s_cache.val[c]!))
    (t_as_ntt : Stage3MontStripFC.TVec K) (accumulator : Stage3MontStripFC.Acc)
    (k : Std.Usize) (h_ge : start.val ≤ k.val) (h_le : k.val ≤ K.val)
    (h_inv : (Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
              k t_as_ntt accumulator).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
      (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt error_as_ntt s_cache
      { start := k, «end» := K } t_as_ntt accumulator
    ⦃ ⇓ r => ⌜ Stage3MontStripFC.rows_step_post matrix_A s_as_ntt error_as_ntt t_as_ntt_init
                start k r ⌝ ⦄ := by
  have h_t_as_ntt_len : t_as_ntt.length = K.val := Std.Array.length_eq t_as_ntt
  have h_error_len : error_as_ntt.length = K.val := Std.Array.length_eq error_as_ntt
  -- Destructure the 2-conjunct invariant.
  obtain ⟨h_inv_done, h_inv_undone, h_inv_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch (i = k).
    -- (1) IteratorRange.next reduces to (some k, {start := s_iter, end := K}).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
          core.Usize.Insts.CoreIterRangeStep
          ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                    r = (some k,
                        ({ start := s, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
      libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
        (fun _ s hs => by
          dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
          exact ⟨s, hs, rfl⟩)
        (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
    obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
    obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
    -- (2) classify 0#i32 = .ok 0#i32.
    have h_classify : libcrux_secrets.traits.Classify.Blanket.classify (0#i32 : Std.I32)
        = .ok (0#i32 : Std.I32) := rfl
    -- (3) Array.repeat 256 0#i32 — fresh zeroed accumulator.
    set acc_zero : Stage3MontStripFC.Acc :=
      Aeneas.Std.Array.repeat 256#usize (0#i32 : Std.I32) with h_acc_zero_def
    have h_acc_zero_val : acc_zero.val = List.replicate 256 (0#i32 : Std.I32) := by
      show (Aeneas.Std.Array.repeat 256#usize (0#i32 : Std.I32)).val = _
      simp [Aeneas.Std.Array.repeat_val]
    have h_acc_zero_get : ∀ n : Nat, n < 256 →
        acc_zero.val[n]! = (0#i32 : Std.I32) := by
      intro n hn
      rw [h_acc_zero_val]
      rw [getElem!_pos (List.replicate 256 (0#i32 : Std.I32)) n
            (by rw [List.length_replicate]; exact hn)]
      exact List.getElem_replicate _
    have h_acc_zero_bnd : ∀ n : Fin 256,
        (acc_zero.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
      intro n
      rw [h_acc_zero_get n.val n.isLt]
      have h0 : ((0#i32 : Std.I32).val).natAbs = 0 := rfl
      rw [h0]
      have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
      have : 4 * 2^25 ≤ 2^30 := by decide
      omega
    -- (4) Apply Stage 2 forward dep at row i = k with the zeroed accumulator.
    have h_stage2 :=
      compute_As_plus_e_loop1_loop0_fc matrix_A s_as_ntt s_cache acc_zero k h_lt
        hAlen h_matrix_bnd h_s_bnd h_acc_zero_bnd h_cache
    obtain ⟨acc_final, h_acc_final_eq, h_acc_final_inv⟩ := triple_exists_ok_fc h_stage2
    -- Destructure the Stage 2 POST into its 2 conjuncts.
    obtain ⟨h_acc_final_lane, h_acc_final_bnd⟩ := by
      simpa [Stage2UseCacheFC.row_i_inv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        using h_acc_final_inv
    -- (5) `lift (Array.to_slice acc_final) = .ok acc_final.to_slice`.
    set acc_slice : Slice Std.I32 := Aeneas.Std.Array.to_slice acc_final with h_acc_slice_def
    have h_acc_slice_val : acc_slice.val = acc_final.val :=
      Aeneas.Std.Array.val_to_slice acc_final
    have h_acc_slice_len : acc_slice.length = 256 := by
      show (Aeneas.Std.Array.to_slice acc_final).length = 256
      rw [Aeneas.Std.Array.length_to_slice]; rfl
    have h_acc_slice_len_val : acc_slice.val.length = 256 := by
      show acc_slice.val.length = 256
      rw [h_acc_slice_val]; exact Std.Array.length_eq acc_final
    -- (6) Array.index_mut_usize t_as_ntt k → (t_as_ntt[k.val]!, set t_as_ntt k).
    set pre : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      t_as_ntt.val[k.val]! with h_pre_def
    have h_idx_mut : Aeneas.Std.Array.index_mut_usize t_as_ntt k
        = .ok (pre, t_as_ntt.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      have h_idx : Aeneas.Std.Array.index_usize t_as_ntt k = .ok pre :=
        libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq t_as_ntt k
          (by rw [h_t_as_ntt_len]; exact h_lt)
      rw [h_idx]; rfl
    -- (7) Apply L6.7 (poly_reducing_from_i32_array_fc, strengthened) on acc_slice and pre.
    have h_acc_zero_natAbs : ∀ n : Nat, n < 256 →
        (acc_zero.val[n]!).val.natAbs = 0 := by
      intro n hn
      have h_eq := h_acc_zero_get n hn
      rw [h_eq]; rfl
    have h_acc_final_lane_bnd : ∀ n : Nat, n < 256 →
        (acc_slice.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
      intro n hn
      rw [h_acc_slice_val]
      have h_b := h_acc_final_bnd n hn
      -- h_b uses `[n]?.getD default`; rewrite via `List.getElem!_eq_getElem?_getD`.
      simp only [← List.getElem!_eq_getElem?_getD] at h_b
      have h_z := h_acc_zero_natAbs n hn
      have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
      have h_bnd_2 : (4 : Nat) * 2^25 ≤ 2^16 * 3328 := by decide
      omega
    have h_l67 :=
      poly_reducing_from_i32_array_fc acc_slice pre h_acc_slice_len h_acc_final_lane_bnd
    obtain ⟨t1, h_t1_eq, h_t1_post⟩ := triple_exists_ok_fc h_l67
    obtain ⟨h_t1_lift, h_t1_bnd⟩ := h_t1_post
    -- (8) t_as_ntt1 := set t_as_ntt k t1.
    set t_as_ntt1 : Stage3MontStripFC.TVec K := t_as_ntt.set k t1 with h_t_as_ntt1_def
    have h_t_as_ntt1_at : t_as_ntt1.val[k.val]! = t1 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq t_as_ntt k k.val t1
          ⟨rfl, by rw [h_t_as_ntt_len]; exact h_lt⟩
    have h_t_as_ntt1_ne : ∀ j : Nat, j ≠ k.val →
        t_as_ntt1.val[j]! = t_as_ntt.val[j]! := by
      intro j hj
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne t_as_ntt k j t1 (fun h => hj h.symm)
    have h_t_as_ntt1_len : t_as_ntt1.length = K.val := Std.Array.length_eq t_as_ntt1
    -- (9) Array.index_mut_usize t_as_ntt1 k → (t1, set t_as_ntt1 k).
    have h_idx_mut1 : Aeneas.Std.Array.index_mut_usize t_as_ntt1 k
        = .ok (t1, t_as_ntt1.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      have h_idx : Aeneas.Std.Array.index_usize t_as_ntt1 k = .ok t1 := by
        have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq t_as_ntt1 k
                  (by rw [h_t_as_ntt1_len]; exact h_lt)
        rw [h_t_as_ntt1_at] at this
        exact this
      rw [h_idx]; rfl
    -- (10) Array.index_usize error_as_ntt k → error_as_ntt[k.val]!.
    set pre3 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      error_as_ntt.val[k.val]! with h_pre3_def
    have h_idx_err : Aeneas.Std.Array.index_usize error_as_ntt k = .ok pre3 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq error_as_ntt k
        (by rw [h_error_len]; exact h_lt)
    -- (11) Apply L6.5 (add_standard_error_reduce_fc) on (t1, pre3).
    have h_t1_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((t1.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro chunk hchunk ℓ hℓ
      have h_b := h_t1_bnd chunk hchunk ℓ hℓ
      -- h_b : … ≤ 4993; want ≤ 32767.
      omega
    have h_pre3_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((pre3.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439 :=
      fun chunk hchunk ℓ hℓ =>
        h_error_bnd ⟨k.val, h_lt⟩ ⟨chunk, hchunk⟩ ⟨ℓ, hℓ⟩
    have h_l65 :=
      add_standard_error_reduce_fc t1 pre3 h_t1_self_bnd h_pre3_error_bnd
    obtain ⟨pre4, h_pre4_eq, h_pre4_lift, h_pre4_bnd⟩ := triple_exists_ok_fc h_l65
    -- h_pre4_post : lift_poly pre4 = Spec.add_standard_error_reduce_pure (lift_poly t1) (lift_poly pre3).
    -- (12) t_as_ntt_new := set t_as_ntt1 k pre4.
    set t_as_ntt_new : Stage3MontStripFC.TVec K := t_as_ntt1.set k pre4 with h_t_as_ntt_new_def
    have h_t_as_ntt_new_at : t_as_ntt_new.val[k.val]! = pre4 := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq t_as_ntt1 k k.val pre4
          ⟨rfl, by rw [h_t_as_ntt1_len]; exact h_lt⟩
    have h_t_as_ntt_new_ne : ∀ j : Nat, j ≠ k.val →
        t_as_ntt_new.val[j]! = t_as_ntt.val[j]! := by
      intro j hj
      have h1 : t_as_ntt_new.val[j]! = t_as_ntt1.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
          Aeneas.Std.Array.getElem!_Nat_set_ne t_as_ntt1 k j pre4 (fun h => hj h.symm)
      rw [h1]
      exact h_t_as_ntt1_ne j hj
    -- (13) Body equation: reduce do-block to .ok (cont (s_iter_range, t_as_ntt_new, acc_final)).
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt error_as_ntt s_cache
          { start := k, «end» := K } t_as_ntt accumulator
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), t_as_ntt_new, acc_final)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
              let i1 ← libcrux_secrets.traits.Classify.Blanket.classify (0#i32 : Std.I32)
              let accumulator1 := Aeneas.Std.Array.repeat 256#usize i1
              let accumulator2 ←
                libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1_loop0
                  (vectortraitsOperationsInst := portable_ops_inst)
                  { start := 0#usize, «end» := K } matrix_A s_as_ntt s_cache
                  accumulator1 k
              let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice accumulator2)
              let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt k
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst s pre
              let t_as_ntt1 := index_mut_back pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 k
              let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt k
              let pre4 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst pre2 pre3
              let a := index_mut_back1 pre4
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), a, accumulator2)))
            : Result _) = _
      rw [h_classify]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_acc_final_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice acc_final)
              let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt k
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst s pre
              let t_as_ntt1 := index_mut_back pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 k
              let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt k
              let pre4 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst pre2 pre3
              let a := index_mut_back1 pre4
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), a, acc_final)))
            : Result _) = _
      show ((do
              let s := Aeneas.Std.Array.to_slice acc_final
              let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt k
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst s pre
              let t_as_ntt1 := index_mut_back pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 k
              let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt k
              let pre4 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst pre2 pre3
              let a := index_mut_back1 pre4
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), a, acc_final)))
            : Result _) = _
      rw [h_idx_mut]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst (Aeneas.Std.Array.to_slice acc_final) pre
              let t_as_ntt1 := t_as_ntt.set k pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 k
              let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt k
              let pre4 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst pre2 pre3
              let a := index_mut_back1 pre4
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), a, acc_final)))
            : Result _) = _
      have h_t1_eq' :
          libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
            (vectortraitsOperationsInst := portable_ops_inst)
            (Aeneas.Std.Array.to_slice acc_final) pre = .ok t1 := h_t1_eq
      rw [h_t1_eq']
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_mut1]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt k
              let pre4 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst t1 pre3
              let a := t_as_ntt1.set k pre4
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), a, acc_final)))
            : Result _) = _
      rw [h_idx_err]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_pre4_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rfl
    apply triple_of_ok_fc h_body
    -- (14) Discharge the step_post.
    show Stage3MontStripFC.rows_step_post matrix_A s_as_ntt error_as_ntt t_as_ntt_init start k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), t_as_ntt_new, acc_final))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    -- (15) Re-establish `rows_inv` at s_iter (= k+1).
    show (Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
            s_iter t_as_ntt_new acc_final).holds
    unfold Stage3MontStripFC.rows_inv
    show (pure _ : Result Prop).holds
    have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
    have h_inv_pure :
        (∀ r : Nat, start.val ≤ r → r < s_iter.val → ∀ ℓ : Nat, ℓ < 256 →
          (lift_poly t_as_ntt_new.val[r]!).val[ℓ]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r (ℓ / 16) (ℓ % 16))
                  (lift_fe_mont (1353#i16 : Std.I16)))
                ((lift_poly error_as_ntt.val[r]!).val[ℓ]!))
        ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ s_iter.val ≤ r) →
            t_as_ntt_new.val[r]! = t_as_ntt_init.val[r]!)
        ∧ (∀ r : Nat, start.val ≤ r → r < s_iter.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
            ((t_as_ntt_new.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · -- Conjunct (1): per-completed-row lane characterization.
        intro r hr_ge hr_lt ℓ hℓ
        rw [hs_iter_eq] at hr_lt
        -- Case r < k.val (already-completed row, unchanged by this iteration)
        -- vs r = k.val (the row we just wrote).
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hr_lt_k | hr_eq_k
        · -- r < k: row unchanged; use inv (1) at k.
          have hr_ne : r ≠ k.val := by omega
          rw [h_t_as_ntt_new_ne r hr_ne]
          -- From the rows_inv (1) at k: (lift_poly t_as_ntt.val[r]!).val[ℓ]! = ....
          have h_old := h_inv_done r hr_ge hr_lt_k ℓ hℓ
          exact h_old
        · -- r = k: row was written by this iteration.
          subst hr_eq_k
          rw [h_t_as_ntt_new_at]
          -- Goal: (lift_poly pre4).val[ℓ]! = add_pure (mul_pure canonical_row_sum_lane 1353) (lift_poly error_as_ntt[r]).val[ℓ]!.
          -- pre4 = output of L6.5 on (t1, pre3 = error_as_ntt[r]).
          -- From h_pre4_post:
          --   lift_poly pre4 = Spec.add_standard_error_reduce_pure (lift_poly t1) (lift_poly pre3).
          -- Expand per-lane.
          have hℓ_div_lt : ℓ / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hℓ
          have hℓ_mod_lt : ℓ % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
          have hℓ_decomp : 16 * (ℓ / 16) + ℓ % 16 = ℓ := by
            have := Nat.div_add_mod ℓ 16
            omega
          -- Step A: (lift_poly pre4).val[ℓ]! =
          --         (chunk_add_standard_error_reduce_pure (chunk_at (lift_poly t1) (ℓ/16))
          --                                               (chunk_at (lift_poly pre3) (ℓ/16))).val[ℓ%16]!
          have h_lift_pre4_lane :
              (lift_poly pre4).val[ℓ]!
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                      ((lift_poly t1).val[ℓ]!) (lift_fe_mont (1353#i16 : Std.I16)))
                    ((lift_poly pre3).val[ℓ]!) := by
            -- Use h_pre4_lift (full equality) + flatten_chunks + chunk_at lane.
            rw [h_pre4_lift]
            unfold Spec.add_standard_error_reduce_pure
            unfold Spec.flatten_chunks
            -- Goal: (Std.Array.make 256 ((List.range 256).map (fun j => ...)) _).val[ℓ]! = ...
            show ((List.range 256).map (fun j =>
                    ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
                      Spec.chunk_add_standard_error_reduce_pure
                        (Spec.chunk_at (lift_poly t1) kk)
                        (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[j / 16]!).val[j % 16]!))[ℓ]!
                = _
            have h_len_outer : ((List.range 256).map (fun j =>
                    ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
                      Spec.chunk_add_standard_error_reduce_pure
                        (Spec.chunk_at (lift_poly t1) kk)
                        (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[j / 16]!).val[j % 16]!)).length = 256 := by
              simp
            rw [getElem!_pos _ ℓ (by rw [h_len_outer]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range]
            -- Now reduce the inner [ℓ/16]! lookup on the chunks list.
            have h_chunks_at :
                ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
                    Spec.chunk_add_standard_error_reduce_pure
                      (Spec.chunk_at (lift_poly t1) kk)
                      (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[ℓ / 16]!)
                = Spec.chunk_add_standard_error_reduce_pure
                    (Spec.chunk_at (lift_poly t1) (ℓ / 16))
                    (Spec.chunk_at (lift_poly pre3) (ℓ / 16)) := by
              show ((List.range 16).map (fun kk =>
                      Spec.chunk_add_standard_error_reduce_pure
                        (Spec.chunk_at (lift_poly t1) kk)
                        (Spec.chunk_at (lift_poly pre3) kk)))[ℓ / 16]! = _
              have h_len_inner : ((List.range 16).map (fun kk =>
                      Spec.chunk_add_standard_error_reduce_pure
                        (Spec.chunk_at (lift_poly t1) kk)
                        (Spec.chunk_at (lift_poly pre3) kk))).length = 16 := by simp
              rw [getElem!_pos _ (ℓ / 16) (by rw [h_len_inner]; exact hℓ_div_lt)]
              rw [List.getElem_map, List.getElem_range]
            rw [h_chunks_at]
            -- Now reduce chunk_add_standard_error_reduce_pure ... .val[ℓ%16]!.
            unfold Spec.chunk_add_standard_error_reduce_pure
            show ((List.range 16).map (fun ℓ' =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                        ((Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ']!)
                        (lift_fe_mont (1353#i16 : Std.I16)))
                      ((Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ']!)))[ℓ % 16]! = _
            have h_len_chunk : ((List.range 16).map (fun ℓ' =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                        ((Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ']!)
                        (lift_fe_mont (1353#i16 : Std.I16)))
                      ((Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ']!))).length = 16 := by simp
            rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk]; exact hℓ_mod_lt)]
            rw [List.getElem_map, List.getElem_range]
            -- Now we have:
            --   add_pure (mul_pure (chunk_at (lift_poly t1) (ℓ/16)).val[ℓ%16]! (lift_fe_mont 1353))
            --            ((chunk_at (lift_poly pre3) (ℓ/16)).val[ℓ%16]!)
            -- Need: chunk_at_lane = (lift_poly _).val[ℓ]!.
            have h_t1_chunk_at :
                (Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ % 16]!
                  = (lift_poly t1).val[ℓ]! := by
              unfold Spec.chunk_at
              show ((List.range 16).map
                      (fun j => (lift_poly t1).val[16 * (ℓ / 16) + j]!))[ℓ % 16]! = _
              have h_len_chunk_at : ((List.range 16).map
                      (fun j => (lift_poly t1).val[16 * (ℓ / 16) + j]!)).length = 16 := by simp
              rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk_at]; exact hℓ_mod_lt)]
              rw [List.getElem_map, List.getElem_range, hℓ_decomp]
            have h_pre3_chunk_at :
                (Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ % 16]!
                  = (lift_poly pre3).val[ℓ]! := by
              unfold Spec.chunk_at
              show ((List.range 16).map
                      (fun j => (lift_poly pre3).val[16 * (ℓ / 16) + j]!))[ℓ % 16]! = _
              have h_len_chunk_at : ((List.range 16).map
                      (fun j => (lift_poly pre3).val[16 * (ℓ / 16) + j]!)).length = 16 := by simp
              rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk_at]; exact hℓ_mod_lt)]
              rw [List.getElem_map, List.getElem_range, hℓ_decomp]
            rw [h_t1_chunk_at, h_pre3_chunk_at]
          rw [h_lift_pre4_lane]
          -- Step B: bridge `mul_pure ((lift_poly t1).val[ℓ]!) (lift_fe_mont 1353) =
          --                 mul_pure (canonical_row_sum_lane ...) (lift_fe_mont 1353)`.
          -- Need: (lift_poly t1).val[ℓ]! = canonical_row_sum_lane matrix_A s_as_ntt k.val (ℓ/16) (ℓ%16).
          -- Use h_t1_lift : lift_poly_mont t1 = Spec.poly_reducing_from_i32_array_pure acc_slice.
          -- And h_acc_final_lane : per-(j, ℓ') foldl over [0, K.val) equation.
          -- Step B.1: (lift_poly_mont t1).val[ℓ]! = mont_reduce_pure (lift_fe_int acc_final.val[ℓ]).
          have h_lift_mont_t1_lane :
              (lift_poly_mont t1).val[ℓ]!
                = Spec.mont_reduce_pure (lift_fe_int (acc_final.val[ℓ]!).val) := by
            rw [h_t1_lift]
            unfold Spec.poly_reducing_from_i32_array_pure
            show ((List.range 256).map (fun i =>
                    Spec.mont_reduce_pure (lift_fe_int (acc_slice.val[i]!).val)))[ℓ]! = _
            have h_len : ((List.range 256).map (fun i =>
                    Spec.mont_reduce_pure (lift_fe_int (acc_slice.val[i]!).val))).length = 256 := by simp
            rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
            rw [List.getElem_map, List.getElem_range, h_acc_slice_val]
          -- Step B.2: mont_reduce_pure (lift_fe_int acc_final[ℓ]) = canonical_row_sum (no outer × 1353).
          have h_acc_final_at_ℓ :
              Spec.mont_reduce_pure (lift_fe_int (acc_final.val[ℓ]!).val)
                = (List.range K.val).foldl
                    (fun s c =>
                      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                        ((Spec.ntt_multiply_pure_no_acc
                            (lift_chunk_mont (matrix_A.val[k.val * K.val + c]!.coefficients.val[ℓ / 16]!))
                            (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
                            (Spec.zeta_at (64 + 4 * (ℓ / 16)))
                            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
                            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
                            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
                    (Spec.mont_reduce_pure (lift_fe_int 0)) := by
            have h_at := h_acc_final_lane (ℓ / 16) hℓ_div_lt (ℓ % 16) hℓ_mod_lt
            simp only [← List.getElem!_eq_getElem?_getD] at h_at
            rw [hℓ_decomp] at h_at
            -- The init term in h_at is mont_reduce_pure (lift_fe_int (acc_zero[ℓ]).val).
            -- acc_zero[ℓ] = 0, so .val = 0.
            have h_zero_val : ((0#i32 : Std.I32).val) = 0 := rfl
            rw [h_acc_zero_get ℓ hℓ] at h_at
            rw [h_zero_val] at h_at
            -- Convert (16 * (ℓ / 16) + ℓ % 16) to ℓ in the init too — already done by hℓ_decomp.
            exact h_at
          -- Step B.3: combine bridge with canonical_row_sum_lane definition.
          have h_canon_unfold :
              Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt k.val (ℓ / 16) (ℓ % 16)
                = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    ((List.range K.val).foldl
                      (fun s c =>
                        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                          ((Spec.ntt_multiply_pure_no_acc
                              (lift_chunk_mont (matrix_A.val[k.val * K.val + c]!.coefficients.val[ℓ / 16]!))
                              (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
                              (Spec.zeta_at (64 + 4 * (ℓ / 16)))
                              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
                              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
                              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
                      (Spec.mont_reduce_pure (lift_fe_int 0)))
                    (lift_fe_mont (1353#i16 : Std.I16)) := by
            -- canonical_row_sum_lane is `attribute [local irreducible]` per the section,
            -- but unfolding via with_unfolding_all once is necessary here.
            with_unfolding_all rfl
          -- Now we need: (lift_poly t1).val[ℓ]! = canonical_row_sum_lane ....
          -- We use the bridge `lift_poly_mont_to_lift_poly`:
          --   mul_pure ((lift_poly_mont t1).val[ℓ]!) (lift_fe_mont 1353) = (lift_poly t1).val[ℓ]!.
          have h_bridge : libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              ((lift_poly_mont t1).val[ℓ]!) (lift_fe_mont (1353#i16 : Std.I16))
            = (lift_poly t1).val[ℓ]! := lift_poly_mont_to_lift_poly t1 ℓ hℓ
          -- Combine: (lift_poly t1).val[ℓ]! = mul_pure ((lift_poly_mont t1).val[ℓ]!) (lift_fe_mont 1353)
          --                                 = mul_pure (foldl ...) (lift_fe_mont 1353)
          --                                 = canonical_row_sum_lane.
          have h_lift_t1_lane :
              (lift_poly t1).val[ℓ]!
                = Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt k.val (ℓ / 16) (ℓ % 16) := by
            rw [← h_bridge, h_lift_mont_t1_lane, h_acc_final_at_ℓ, h_canon_unfold]
          -- Show pre3 = error_as_ntt.val[k.val]! by definitional unfolding (set above).
          show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((lift_poly t1).val[ℓ]!) (lift_fe_mont (1353#i16 : Std.I16)))
                ((lift_poly pre3).val[ℓ]!)
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt k.val (ℓ / 16) (ℓ % 16))
                    (lift_fe_mont (1353#i16 : Std.I16)))
                  ((lift_poly error_as_ntt.val[k.val]!).val[ℓ]!)
          rw [h_lift_t1_lane]
      · -- Conjunct (2): rows outside [start, s_iter) unchanged.
        intro r hr_lt_K hr_disj
        rw [hs_iter_eq] at hr_disj
        -- r < start.val ∨ k+1 ≤ r — so in particular r ≠ k (since if r = k, hr_disj says r < start
        -- which contradicts h_ge ≤ r, OR k+1 ≤ r = k which is false).
        have hr_ne : r ≠ k.val := by
          rcases hr_disj with hr_lt_start | hr_ge_succ
          · -- r < start ≤ k, so r ≠ k.
            omega
          · -- k+1 ≤ r, so r > k.
            omega
        rw [h_t_as_ntt_new_ne r hr_ne]
        -- Now need: t_as_ntt.val[r]! = t_as_ntt_init.val[r]!.
        apply h_inv_undone r hr_lt_K
        rcases hr_disj with hr_lt_start | hr_ge_succ
        · exact Or.inl hr_lt_start
        · -- k+1 ≤ r, so k ≤ r.
          exact Or.inr (by omega)
      · -- Conjunct (3): per-completed-row centered Barrett bound |lane| ≤ 1664.
        intro r hr_ge hr_lt j hj m hm
        rw [hs_iter_eq] at hr_lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hr_lt_k | hr_eq_k
        · -- r < k: row unchanged; reuse inv (3) at k.
          have hr_ne : r ≠ k.val := by omega
          rw [h_t_as_ntt_new_ne r hr_ne]
          exact h_inv_bnd r hr_ge hr_lt_k j hj m hm
        · -- r = k: the row just written = pre4; use the L6.5 output bound.
          subst hr_eq_k
          rw [h_t_as_ntt_new_at]
          exact h_pre4_bnd j hj m hm
    simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _; exact h_inv_pure
  · -- `None` branch: k ≥ K, done.
    have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = K.val := by omega
    have h_iter_none :
        ⦃ ⌜ True ⌝ ⦄
        core.iter.range.IteratorRange.next
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
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt error_as_ntt s_cache
          { start := k, «end» := K } t_as_ntt accumulator
        = .ok (ControlFlow.done (t_as_ntt, accumulator)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
    show Stage3MontStripFC.rows_step_post matrix_A s_as_ntt error_as_ntt t_as_ntt_init start k
      (.done (t_as_ntt, accumulator))
    show (Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
            K t_as_ntt accumulator).holds
    unfold Stage3MontStripFC.rows_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ r : Nat, start.val ≤ r → r < K.val → ∀ ℓ : Nat, ℓ < 256 →
          (lift_poly t_as_ntt.val[r]!).val[ℓ]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r (ℓ / 16) (ℓ % 16))
                  (lift_fe_mont (1353#i16 : Std.I16)))
                ((lift_poly error_as_ntt.val[r]!).val[ℓ]!))
        ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ K.val ≤ r) →
            t_as_ntt.val[r]! = t_as_ntt_init.val[r]!)
        ∧ (∀ r : Nat, start.val ≤ r → r < K.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
            ((t_as_ntt.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, ?_⟩
      · intro r hr_ge hr_lt ℓ hℓ
        have h_eq := h_inv_done r hr_ge (by rw [hk_eq]; exact hr_lt) ℓ hℓ
        exact h_eq
      · intro r hr_lt_K hr_disj
        exact h_inv_undone r hr_lt_K (by
          rcases hr_disj with hl | hr
          · exact Or.inl hl
          · exact Or.inr (by rw [hk_eq]; exact hr))
      · intro r hr_ge hr_lt j hj m hm
        exact h_inv_bnd r hr_ge (by rw [hk_eq]; exact hr_lt) j hj m hm
    simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
    intro _; exact h_inv_pure

/-- L7.1 Stage 3 — `matrix.compute_As_plus_e_loop1`: the outer rows loop over
    `i ∈ [start, K)`. Each iteration re-zeros the accumulator, calls Stage 2
    (`compute_As_plus_e_loop1_loop0_fc`) for the row's column sum, converts via
    L6.7 (`poly_reducing_from_i32_array_fc`) to Mont FE form, then applies
    L6.5 (`add_standard_error_reduce_fc`) (× lift_fe_mont 1353 + error) to
    produce the canonical FE row. The Mont→canonical bridge step (× 1353) is
    absorbed inside `canonical_row_sum_lane`; the OUTER × 1353 in the
    invariant comes from L6.5's own mul step.

    POST: `rows_inv` holds at k = K — i.e. for each row `r ∈ [start, K)`,
    every lane `ℓ ∈ [0, 256)` equals
    `add_pure (mul_pure (canonical_row_sum_lane matrix_A s_as_ntt r (ℓ/16) (ℓ%16))
                        (lift_fe_mont 1353))
              ((lift_poly error_as_ntt.val[r]!).val[ℓ]!)`,
    and rows outside `[start, K)` are unchanged from `t_as_ntt_init`.

    PRE: standard 16×16 bounds (3328/3328/29439) on matrix/s/error entries,
    `hAlen : matrix_A.length = K·K`, `hK : K.val ≤ 4` (drives Stage 2's
    K·2^25 ≤ 2^27 ≤ 2^16·3328 reasoning at L6.7), `h_start_le_K : start ≤ K`,
    and the cache-post hypothesis `h_cache` — at every column `c < K`,
    `s_cache.val[c]!` satisfies `accumulating_ntt_multiply_poly_cache_post`
    against `s_as_ntt.val[c]!`. The accumulator passed in is rewritten on each
    iteration (Stage 2 starts from a freshly-zeroed accumulator). -/
@[spec]
theorem compute_As_plus_e_loop1_fc
    {K : Std.Usize}
    (t_as_ntt_init : Std.Array
                      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
                                       (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                         libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (start : Std.Usize)
    (hK : K.val ≤ 4)
    (h_start_le_K : start.val ≤ K.val)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ a b : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_error_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((error_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (s_as_ntt.val[c]!) (s_cache.val[c]!)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := start, «end» := K } t_as_ntt_init matrix_A s_as_ntt error_as_ntt s_cache accumulator
    ⦃ ⇓ p => ⌜ (Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start K p.1 p.2).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1.body
          (vectortraitsOperationsInst := portable_ops_inst) matrix_A s_as_ntt error_as_ntt s_cache
          iter1 p.1 p.2)
      (β := Stage3MontStripFC.TVec K × Stage3MontStripFC.Acc)
      (t_as_ntt_init, accumulator)
      start K
      (fun k p => Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start k p.1 p.2)
      h_start_le_K
      (by
        -- Base case at k = start: rows_inv holds trivially.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, ?_⟩
        · -- (1) Vacuous: r ∈ [start, start) is empty.
          intro r hr_ge hr_lt _ _; omega
        · -- (2) For r ∉ [start, start), trivially t_as_ntt_init[r] = t_as_ntt_init[r].
          intro r _ _; trivial
        · -- (3) Vacuous: r ∈ [start, start) is empty.
          intro r hr_ge hr_lt _ _ _ _; omega)
      ?_)
  · -- Post entailment: at k = K, rows_inv holds.
    rw [PostCond.entails_noThrow]
    intro r hh
    have h_inv_holds : (Stage3MontStripFC.rows_inv matrix_A s_as_ntt error_as_ntt t_as_ntt_init start
                          K r.1 r.2).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    exact h_inv_holds
  · -- Step entailment.
    intro p k h_ge h_le hinv
    have h_step := compute_As_plus_e_loop1_step_lemma_fc
      matrix_A s_as_ntt error_as_ntt s_cache t_as_ntt_init start hK hAlen
      h_matrix_bnd h_s_bnd h_error_bnd h_cache p.1 p.2 k h_ge h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', t_acc⟩ | y
    · have hP : Stage3MontStripFC.rows_step_post matrix_A s_as_ntt error_as_ntt t_as_ntt_init start k
                  (.cont (iter', t_acc.1, t_acc.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage3MontStripFC.rows_step_post] using hP
    · have hP : Stage3MontStripFC.rows_step_post matrix_A s_as_ntt error_as_ntt t_as_ntt_init start k
                  (.done (y.1, y.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Stage3MontStripFC.rows_step_post] using hP

set_option maxHeartbeats 16000000 in
/-- L7.1 Stage 4a — row-0 finalization helper.

    Given a row-0 column-loop output `accumulator` satisfying `Stage1FillCacheFC.row0_inv`
    at k=K (with `acc_init = accumulator` itself — i.e. the lemma's caller passes
    the original L7.1 accumulator and the Stage 1 output coincides at this slot,
    consistent with the calling pattern at `compute_As_plus_e_loop0_fc`), executes the bind chain
    `Array.to_slice + index_mut_usize t_as_ntt 0 + L6.7 + index_mut t_as_ntt1 0
     + index_usize error_as_ntt 0 + L6.5` and produces `a` such that:

    (1) For row 0, every lane ℓ < 256:
        `(lift_poly a.val[0]!).val[ℓ]!
          = add_pure
              (mul_pure (canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ/16) (ℓ%16))
                        (lift_fe_mont 1353))
              ((lift_poly error_as_ntt.val[0]!).val[ℓ]!)`.
    (2) For rows r > 0: `a.val[r]! = t_as_ntt.val[r]!`.

    Mirrors `compute_As_plus_e_loop1_step_lemma_fc` structurally
    — the `.cont` branch's bind chain at lines 30880-31320, with row index `k`
    replaced by `0#usize` and matrix lane index `k.val * K.val + c` replaced by
    just `c` (since `0 * K + c = c`).

    Extra PRE beyond the template: `h_acc_zero` collapses row0_inv's foldl seed
    `mont_reduce_pure (lift_fe_int accumulator[16j+ℓ].val)` to
    `mont_reduce_pure (lift_fe_int 0)` — matching `canonical_row_sum_lane`'s
    init. `h_acc_lane_bnd` discharges the L6.7 PRE on the slice. -/
theorem compute_As_plus_e_row0_finalize_fc
    {K : Std.Usize}
    (t_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
                                       (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                         libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init accumulator : Stage3MontStripFC.Acc)
    (s_cache_fin : Std.Array
                     (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                       libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (hK_pos : 0 < K.val)
    (h_error_bnd : ∀ k : Fin K.val, ∀ a b : Fin 16,
        ((error_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439)
    (h_acc_zero : ∀ n : Nat, n < 256 → acc_init.val[n]! = (0#i32 : Std.I32))
    (h_acc_lane_bnd : ∀ n : Nat, n < 256 →
        (accumulator.val[n]!).val.natAbs ≤ 2^16 * 3328)
    (h_row0_inv : (Stage1FillCacheFC.row0_inv matrix_A s_as_ntt acc_init s_cache K accumulator
                    s_cache_fin).holds) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice accumulator)
      let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt 0#usize
      let pre1 ←
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
          portable_ops_inst s pre
      let t_as_ntt1 := index_mut_back pre1
      let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 0#usize
      let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
      let pre4 ←
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
          portable_ops_inst pre2 pre3
      .ok (index_mut_back1 pre4) :
        Result (Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K))
    ⦃ ⇓ a => ⌜
        (∀ ℓ : Nat, ℓ < 256 →
          (lift_poly a.val[0]!).val[ℓ]!
            = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ / 16) (ℓ % 16))
                  (lift_fe_mont (1353#i16 : Std.I16)))
                ((lift_poly error_as_ntt.val[0]!).val[ℓ]!))
        ∧ (∀ r : Nat, 0 < r → r < K.val →
            a.val[r]! = t_as_ntt.val[r]!)
        ∧ (∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
            ((a.val[0]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664) ⌝ ⦄ := by
  have h_t_as_ntt_len : t_as_ntt.length = K.val := Std.Array.length_eq t_as_ntt
  have h_error_len : error_as_ntt.length = K.val := Std.Array.length_eq error_as_ntt
  -- Convenience: (0#usize).val = 0.
  have h_zero_val : (0#usize : Std.Usize).val = 0 := rfl
  -- Destructure the 4-conjunct row0_inv (we only need (1)).
  obtain ⟨h_row0_lane, _h_row0_bnd, _h_row0_cache_pop, _h_row0_cache_unch⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_row0_inv
  -- (1) acc_slice := Array.to_slice accumulator.
  set acc_slice : Slice Std.I32 := Aeneas.Std.Array.to_slice accumulator with h_acc_slice_def
  have h_acc_slice_val : acc_slice.val = accumulator.val :=
    Aeneas.Std.Array.val_to_slice accumulator
  have h_acc_slice_len : acc_slice.length = 256 := by
    show (Aeneas.Std.Array.to_slice accumulator).length = 256
    rw [Aeneas.Std.Array.length_to_slice]; rfl
  -- (2) Array.index_mut_usize t_as_ntt 0 → (t_as_ntt[0]!, set t_as_ntt 0).
  set pre : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    t_as_ntt.val[(0#usize : Std.Usize).val]! with h_pre_def
  have h_idx_mut : Aeneas.Std.Array.index_mut_usize t_as_ntt (0#usize : Std.Usize)
      = .ok (pre, t_as_ntt.set (0#usize : Std.Usize)) := by
    unfold Aeneas.Std.Array.index_mut_usize
    have h_idx : Aeneas.Std.Array.index_usize t_as_ntt (0#usize : Std.Usize) = .ok pre :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq t_as_ntt (0#usize : Std.Usize)
        (by rw [h_t_as_ntt_len]; exact hK_pos)
    rw [h_idx]; rfl
  -- (3) Apply L6.7 on acc_slice + pre. Use h_acc_lane_bnd via h_acc_slice_val.
  have h_acc_slice_lane_bnd : ∀ n : Nat, n < 256 →
      (acc_slice.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
    intro n hn; rw [h_acc_slice_val]; exact h_acc_lane_bnd n hn
  have h_l67 :=
    poly_reducing_from_i32_array_fc acc_slice pre h_acc_slice_len h_acc_slice_lane_bnd
  obtain ⟨t1, h_t1_eq, h_t1_post⟩ := triple_exists_ok_fc h_l67
  obtain ⟨h_t1_lift, h_t1_bnd⟩ := h_t1_post
  -- (4) t_as_ntt1 := set t_as_ntt 0 t1.
  set t_as_ntt1 : Stage3MontStripFC.TVec K := t_as_ntt.set (0#usize : Std.Usize) t1
    with h_t_as_ntt1_def
  have h_t_as_ntt1_at : t_as_ntt1.val[(0#usize : Std.Usize).val]! = t1 := by
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
      Aeneas.Std.Array.getElem!_Nat_set_eq t_as_ntt (0#usize : Std.Usize)
        (0#usize : Std.Usize).val t1
        ⟨rfl, by rw [h_t_as_ntt_len]; exact hK_pos⟩
  have h_t_as_ntt1_ne : ∀ j : Nat, j ≠ (0#usize : Std.Usize).val →
      t_as_ntt1.val[j]! = t_as_ntt.val[j]! := by
    intro j hj
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
      Aeneas.Std.Array.getElem!_Nat_set_ne t_as_ntt (0#usize : Std.Usize) j t1
        (fun h => hj h.symm)
  have h_t_as_ntt1_len : t_as_ntt1.length = K.val := Std.Array.length_eq t_as_ntt1
  -- (5) Array.index_mut_usize t_as_ntt1 0 → (t1, set t_as_ntt1 0).
  have h_idx_mut1 : Aeneas.Std.Array.index_mut_usize t_as_ntt1 (0#usize : Std.Usize)
      = .ok (t1, t_as_ntt1.set (0#usize : Std.Usize)) := by
    unfold Aeneas.Std.Array.index_mut_usize
    have h_idx : Aeneas.Std.Array.index_usize t_as_ntt1 (0#usize : Std.Usize) = .ok t1 := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq t_as_ntt1 (0#usize : Std.Usize)
                (by rw [h_t_as_ntt1_len]; exact hK_pos)
      rw [h_t_as_ntt1_at] at this
      exact this
    rw [h_idx]; rfl
  -- (6) Array.index_usize error_as_ntt 0 → error_as_ntt[0]!.
  set pre3 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    error_as_ntt.val[(0#usize : Std.Usize).val]! with h_pre3_def
  have h_idx_err : Aeneas.Std.Array.index_usize error_as_ntt (0#usize : Std.Usize) = .ok pre3 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq error_as_ntt (0#usize : Std.Usize)
      (by rw [h_error_len]; exact hK_pos)
  -- (7) Apply L6.5 on (t1, pre3).
  have h_t1_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((t1.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
    intro chunk hchunk ℓ hℓ
    have h_b := h_t1_bnd chunk hchunk ℓ hℓ
    omega
  have h_pre3_error_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((pre3.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439 :=
    fun chunk hchunk ℓ hℓ =>
      h_error_bnd ⟨(0#usize : Std.Usize).val, hK_pos⟩ ⟨chunk, hchunk⟩ ⟨ℓ, hℓ⟩
  have h_l65 :=
    add_standard_error_reduce_fc t1 pre3 h_t1_self_bnd h_pre3_error_bnd
  obtain ⟨pre4, h_pre4_eq, h_pre4_lift, h_pre4_bnd⟩ := triple_exists_ok_fc h_l65
  -- (8) t_as_ntt_new := set t_as_ntt1 0 pre4.
  set t_as_ntt_new : Stage3MontStripFC.TVec K := t_as_ntt1.set (0#usize : Std.Usize) pre4
    with h_t_as_ntt_new_def
  have h_t_as_ntt_new_at : t_as_ntt_new.val[0]! = pre4 := by
    have h := Aeneas.Std.Array.getElem!_Nat_set_eq t_as_ntt1 (0#usize : Std.Usize)
                0 pre4 ⟨rfl, by rw [h_t_as_ntt1_len]; exact hK_pos⟩
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h
  have h_t_as_ntt_new_ne : ∀ j : Nat, j ≠ 0 →
      t_as_ntt_new.val[j]! = t_as_ntt.val[j]! := by
    intro j hj
    have h1 : t_as_ntt_new.val[j]! = t_as_ntt1.val[j]! := by
      have := Aeneas.Std.Array.getElem!_Nat_set_ne t_as_ntt1 (0#usize : Std.Usize) j pre4
        (fun h => hj (by rw [← h_zero_val]; exact h.symm))
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using this
    rw [h1]
    exact h_t_as_ntt1_ne j (by rw [h_zero_val]; exact hj)
  -- (9) Body equation: reduce do-block to .ok t_as_ntt_new.
  have h_body :
      (do
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice accumulator)
        let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt 0#usize
        let pre1 ←
          libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
            portable_ops_inst s pre
        let t_as_ntt1 := index_mut_back pre1
        let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 0#usize
        let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
        let pre4 ←
          libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
            portable_ops_inst pre2 pre3
        .ok (index_mut_back1 pre4) :
          Result (Std.Array
                    (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K))
      = .ok t_as_ntt_new := by
    show ((do
            let s := Aeneas.Std.Array.to_slice accumulator
            let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt 0#usize
            let pre1 ←
              libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                portable_ops_inst s pre
            let t_as_ntt1 := index_mut_back pre1
            let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 0#usize
            let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
            let pre4 ←
              libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                portable_ops_inst pre2 pre3
            .ok (index_mut_back1 pre4))
          : Result _) = _
    rw [h_idx_mut]
    simp only [Aeneas.Std.bind_tc_ok]
    show ((do
            let pre1 ←
              libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                portable_ops_inst (Aeneas.Std.Array.to_slice accumulator) pre
            let t_as_ntt1 := t_as_ntt.set (0#usize : Std.Usize) pre1
            let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize t_as_ntt1 0#usize
            let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
            let pre4 ←
              libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                portable_ops_inst pre2 pre3
            .ok (index_mut_back1 pre4))
          : Result _) = _
    have h_t1_eq' :
        libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
          (vectortraitsOperationsInst := portable_ops_inst)
          (Aeneas.Std.Array.to_slice accumulator) pre = .ok t1 := h_t1_eq
    rw [h_t1_eq']
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_idx_mut1]
    simp only [Aeneas.Std.bind_tc_ok]
    show ((do
            let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
            let pre4 ←
              libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                portable_ops_inst t1 pre3
            .ok (t_as_ntt1.set (0#usize : Std.Usize) pre4))
          : Result _) = _
    rw [h_idx_err]
    simp only [Aeneas.Std.bind_tc_ok]
    rw [h_pre4_eq]
    simp only [Aeneas.Std.bind_tc_ok]
    rfl
  apply triple_of_ok_fc h_body
  -- (10) Discharge the 3-conjunct post.
  refine ⟨?_, ?_, ?_⟩
  · -- Conjunct (1): per-lane characterization at row 0.
    intro ℓ hℓ
    rw [h_t_as_ntt_new_at]
    -- Now: (lift_poly pre4).val[ℓ]! = add_pure (mul_pure canonical_row_sum_lane 1353)
    --                                          ((lift_poly error_as_ntt[0]!).val[ℓ]!).
    have hℓ_div_lt : ℓ / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hℓ
    have hℓ_mod_lt : ℓ % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
    have hℓ_decomp : 16 * (ℓ / 16) + ℓ % 16 = ℓ := by
      have := Nat.div_add_mod ℓ 16
      omega
    -- Step A: (lift_poly pre4).val[ℓ]! = add_pure (mul_pure ((lift_poly t1).val[ℓ]!) 1353)
    --                                            ((lift_poly pre3).val[ℓ]!).
    have h_lift_pre4_lane :
        (lift_poly pre4).val[ℓ]!
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                ((lift_poly t1).val[ℓ]!) (lift_fe_mont (1353#i16 : Std.I16)))
              ((lift_poly pre3).val[ℓ]!) := by
      rw [h_pre4_lift]
      unfold Spec.add_standard_error_reduce_pure
      unfold Spec.flatten_chunks
      show ((List.range 256).map (fun j =>
              ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
                Spec.chunk_add_standard_error_reduce_pure
                  (Spec.chunk_at (lift_poly t1) kk)
                  (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[j / 16]!).val[j % 16]!))[ℓ]!
          = _
      have h_len_outer : ((List.range 256).map (fun j =>
              ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
                Spec.chunk_add_standard_error_reduce_pure
                  (Spec.chunk_at (lift_poly t1) kk)
                  (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[j / 16]!).val[j % 16]!)).length = 256 := by
        simp
      rw [getElem!_pos _ ℓ (by rw [h_len_outer]; exact hℓ)]
      rw [List.getElem_map, List.getElem_range]
      have h_chunks_at :
          ((Std.Array.make 16#usize ((List.range 16).map (fun kk =>
              Spec.chunk_add_standard_error_reduce_pure
                (Spec.chunk_at (lift_poly t1) kk)
                (Spec.chunk_at (lift_poly pre3) kk))) (by simp)).val[ℓ / 16]!)
          = Spec.chunk_add_standard_error_reduce_pure
              (Spec.chunk_at (lift_poly t1) (ℓ / 16))
              (Spec.chunk_at (lift_poly pre3) (ℓ / 16)) := by
        show ((List.range 16).map (fun kk =>
                Spec.chunk_add_standard_error_reduce_pure
                  (Spec.chunk_at (lift_poly t1) kk)
                  (Spec.chunk_at (lift_poly pre3) kk)))[ℓ / 16]! = _
        have h_len_inner : ((List.range 16).map (fun kk =>
                Spec.chunk_add_standard_error_reduce_pure
                  (Spec.chunk_at (lift_poly t1) kk)
                  (Spec.chunk_at (lift_poly pre3) kk))).length = 16 := by simp
        rw [getElem!_pos _ (ℓ / 16) (by rw [h_len_inner]; exact hℓ_div_lt)]
        rw [List.getElem_map, List.getElem_range]
      rw [h_chunks_at]
      unfold Spec.chunk_add_standard_error_reduce_pure
      show ((List.range 16).map (fun ℓ' =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ']!)
                  (lift_fe_mont (1353#i16 : Std.I16)))
                ((Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ']!)))[ℓ % 16]! = _
      have h_len_chunk : ((List.range 16).map (fun ℓ' =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  ((Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ']!)
                  (lift_fe_mont (1353#i16 : Std.I16)))
                ((Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ']!))).length = 16 := by simp
      rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk]; exact hℓ_mod_lt)]
      rw [List.getElem_map, List.getElem_range]
      have h_t1_chunk_at :
          (Spec.chunk_at (lift_poly t1) (ℓ / 16)).val[ℓ % 16]!
            = (lift_poly t1).val[ℓ]! := by
        unfold Spec.chunk_at
        show ((List.range 16).map
                (fun j => (lift_poly t1).val[16 * (ℓ / 16) + j]!))[ℓ % 16]! = _
        have h_len_chunk_at : ((List.range 16).map
                (fun j => (lift_poly t1).val[16 * (ℓ / 16) + j]!)).length = 16 := by simp
        rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk_at]; exact hℓ_mod_lt)]
        rw [List.getElem_map, List.getElem_range, hℓ_decomp]
      have h_pre3_chunk_at :
          (Spec.chunk_at (lift_poly pre3) (ℓ / 16)).val[ℓ % 16]!
            = (lift_poly pre3).val[ℓ]! := by
        unfold Spec.chunk_at
        show ((List.range 16).map
                (fun j => (lift_poly pre3).val[16 * (ℓ / 16) + j]!))[ℓ % 16]! = _
        have h_len_chunk_at : ((List.range 16).map
                (fun j => (lift_poly pre3).val[16 * (ℓ / 16) + j]!)).length = 16 := by simp
        rw [getElem!_pos _ (ℓ % 16) (by rw [h_len_chunk_at]; exact hℓ_mod_lt)]
        rw [List.getElem_map, List.getElem_range, hℓ_decomp]
      rw [h_t1_chunk_at, h_pre3_chunk_at]
    rw [h_lift_pre4_lane]
    -- Step B: (lift_poly t1).val[ℓ]! = canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ/16) (ℓ%16).
    have h_lift_mont_t1_lane :
        (lift_poly_mont t1).val[ℓ]!
          = Spec.mont_reduce_pure (lift_fe_int (accumulator.val[ℓ]!).val) := by
      rw [h_t1_lift]
      unfold Spec.poly_reducing_from_i32_array_pure
      show ((List.range 256).map (fun i =>
              Spec.mont_reduce_pure (lift_fe_int (acc_slice.val[i]!).val)))[ℓ]! = _
      have h_len : ((List.range 256).map (fun i =>
              Spec.mont_reduce_pure (lift_fe_int (acc_slice.val[i]!).val))).length = 256 := by simp
      rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
      rw [List.getElem_map, List.getElem_range, h_acc_slice_val]
    -- Step B.2: mont_reduce_pure (lift_fe_int accumulator[ℓ]) = foldl (no outer × 1353)
    --   with seed mont_reduce_pure (lift_fe_int 0).
    -- The row0_inv conjunct (1) at j = ℓ/16, ℓ' = ℓ%16:
    --   mont_reduce_pure (lift_fe_int (accumulator[16*(ℓ/16)+ℓ%16]).val)
    --     = (List.range K.val).foldl ... (mont_reduce_pure (lift_fe_int (accumulator[16*(ℓ/16)+ℓ%16]).val))
    -- where the foldl uses matrix_A[c] (not k*K+c) and s_as_ntt[c].
    -- h_acc_zero collapses the seed via accumulator[ℓ] = 0#i32 → .val = 0.
    have h_acc_at_ℓ :
        Spec.mont_reduce_pure (lift_fe_int (accumulator.val[ℓ]!).val)
          = (List.range K.val).foldl
              (fun s c =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (matrix_A.val[c]!.coefficients.val[ℓ / 16]!))
                      (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
                      (Spec.zeta_at (64 + 4 * (ℓ / 16)))
                      (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
                      (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
                      (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
              (Spec.mont_reduce_pure (lift_fe_int 0)) := by
      have h_at := h_row0_lane (ℓ / 16) hℓ_div_lt (ℓ % 16) hℓ_mod_lt
      rw [hℓ_decomp] at h_at
      -- h_at: mont_reduce_pure (lift_fe_int (acc_final[ℓ]).val)
      --         = foldl ... (mont_reduce_pure (lift_fe_int (acc_init[ℓ]).val))
      -- Goal seed: mont_reduce_pure (lift_fe_int 0). The acc_init seed collapses to 0
      -- via h_acc_zero (acc_init is the loop0 INPUT accumulator, which is zero).
      have h_z := h_acc_zero ℓ hℓ
      have h_zero_i32_val : ((0#i32 : Std.I32).val) = 0 := rfl
      have h_collapse : (acc_init.val[ℓ]!).val = 0 := by rw [h_z]; exact h_zero_i32_val
      rw [h_collapse] at h_at
      exact h_at
    -- Step B.3: combine via canonical_row_sum_lane.
    -- For row i = 0, canonical_row_sum_lane's internal index 0*K.val + c = c.
    have h_canon_unfold :
        Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ / 16) (ℓ % 16)
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              ((List.range K.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (matrix_A.val[0 * K.val + c]!.coefficients.val[ℓ / 16]!))
                        (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
                        (Spec.zeta_at (64 + 4 * (ℓ / 16)))
                        (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
                        (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
                        (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
                (Spec.mont_reduce_pure (lift_fe_int 0)))
              (lift_fe_mont (1353#i16 : Std.I16)) := by
      with_unfolding_all rfl
    -- 0 * K.val + c = c, so the matrix index in h_canon_unfold matches h_acc_at_ℓ.
    have h_zero_K_c : ∀ c : Nat, 0 * K.val + c = c := by intro c; omega
    -- Bridge: lift_poly_mont_to_lift_poly converts the Mont-lift to the canonical lift.
    have h_bridge : libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        ((lift_poly_mont t1).val[ℓ]!) (lift_fe_mont (1353#i16 : Std.I16))
      = (lift_poly t1).val[ℓ]! := lift_poly_mont_to_lift_poly t1 ℓ hℓ
    have h_lift_t1_lane :
        (lift_poly t1).val[ℓ]!
          = Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ / 16) (ℓ % 16) := by
      rw [← h_bridge, h_lift_mont_t1_lane, h_acc_at_ℓ, h_canon_unfold]
      -- Both sides have the same foldl, but matrix indices differ by 0*K.val+c = c.
      -- Since 0*K.val = 0, this is just c = c.
      simp only [Nat.zero_mul, Nat.zero_add]
    -- pre3 = error_as_ntt.val[0]! (definitionally, since (0#usize).val = 0).
    -- Goal: add_pure (mul_pure (lift_poly t1)[ℓ] 1353) (lift_poly pre3)[ℓ]
    --     = add_pure (mul_pure (canonical_row_sum_lane ...) 1353) (lift_poly error_as_ntt[0])[ℓ]
    rw [h_lift_t1_lane]
    -- Now match pre3 = error_as_ntt.val[0]! on the RHS.
    show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt 0 (ℓ / 16) (ℓ % 16))
            (lift_fe_mont (1353#i16 : Std.I16)))
          ((lift_poly (error_as_ntt.val[(0#usize : Std.Usize).val]!)).val[ℓ]!)
        = _
    rfl
  · -- Conjunct (2): rows r > 0 unchanged.
    intro r hr_pos _hr_lt_K
    have hr_ne : r ≠ 0 := by omega
    exact h_t_as_ntt_new_ne r hr_ne
  · -- Conjunct (3): row-0 centered Barrett output bound |lane| ≤ 1664 (from L6.5).
    intro j hj m hm
    rw [h_t_as_ntt_new_at]
    exact h_pre4_bnd j hj m hm

end L7_1c_irreducible

/-! ## §L7.1 Stage 4b — hacspec-side bridge lemma.

    Given the per-row, per-lane characterization of `t_as_ntt_final`,
    proves the hacspec `compute_As_plus_e` equation that L7.1's POST
    demands. The proof unfolds `compute_As_plus_e` to its do-block
    `multiply_matrix_by_column ; add_vectors` and uses three layered
    `from_fn_pure_eq` applications. -/

namespace Stage4MatrixAddFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

/-- Clone of `polynomial.add_to_ring_element_eq_ok` for the byte-identical
    `matrix.add_polynomials` closure (both compile from the same Rust
    source pattern; the closure bodies are identical up to namespace). -/
-- Public (exported for L7.4 `compute_message_acc_bridge`): per-step reduction of
-- the hacspec `matrix.add_polynomials` to its pure-lane `add_pure` array form.
-- Visibility-only change (proof/statement unchanged).
theorem matrix_add_polynomials_eq_ok
    (lhs rhs : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    hacspec_ml_kem.matrix.add_polynomials lhs rhs
      = .ok ⟨(List.range 256).map (fun k =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (lhs.val[k]!) (rhs.val[k]!)),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun k => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (lhs.val[k]!) (rhs.val[k]!) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.matrix.add_polynomials.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            (lhs, rhs) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (lhs, rhs)) := by
    intro k hk
    have hk' : k < 256 := hk
    show hacspec_ml_kem.matrix.add_polynomials.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        (lhs, rhs) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (lhs, rhs))
    unfold hacspec_ml_kem.matrix.add_polynomials.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold hacspec_ml_kem.matrix.add_polynomials.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have hlhs_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < lhs.length := by
      rw [hk_us]; show k < lhs.val.length
      rw [lhs.property]; exact hk
    have hrhs_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < rhs.length := by
      rw [hk_us]; show k < rhs.val.length
      rw [rhs.property]; exact hk
    have h_lhs_idx :
        Std.Array.index_usize lhs (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (lhs.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq lhs
                  (⟨BitVec.ofNat _ k⟩ : Std.Usize) hlhs_len
      rw [hk_us] at this; exact this
    have h_rhs_idx :
        Std.Array.index_usize rhs (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (rhs.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq rhs
                  (⟨BitVec.ofNat _ k⟩ : Std.Usize) hrhs_len
      rw [hk_us] at this; exact this
    have h_add :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_eq_ok (lhs.val[k]!) (rhs.val[k]!)
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize lhs ⟨BitVec.ofNat _ k⟩
        let i ← lift (Std.UScalar.cast .U32 fe.val)
        let fe1 ← Std.Array.index_usize rhs ⟨BitVec.ofNat _ k⟩
        let i1 ← lift (Std.UScalar.cast .U32 fe1.val)
        let i2 ← i + i1
        let i3 ← lift (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS)
        let i4 ← i2 % i3
        let i5 ← lift (Std.UScalar.cast .U16 i4)
        hacspec_ml_kem.parameters.FieldElement.new i5)
      Result.ok (fe, lhs, rhs)) = Result.ok (f k, lhs, rhs)
    rw [h_lhs_idx]; simp only [bind_tc_ok]
    rw [h_rhs_idx]; simp only [bind_tc_ok]
    unfold hacspec_ml_kem.parameters.FieldElement.add at h_add
    rw [h_add]
    simp only [bind_tc_ok, hf_def]
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (F := hacspec_ml_kem.matrix.add_polynomials.closure)
      (N := 256#usize)
      (inst := hacspec_ml_kem.matrix.add_polynomials.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := (lhs, rhs))
      (f := f)
      hpure
  unfold hacspec_ml_kem.matrix.add_polynomials
  unfold hacspec_ml_kem.parameters.createi
  show core.array.from_fn 256#usize _ (lhs, rhs) = _
  exact h_from_fn

/-- **Helper 1.** Single-product lane-eq characterization: for any two
    `PolynomialRingElement`s `a, b`, lane `ℓ` of `Spec.multiply_ntts_pure
    (lift_poly a) (lift_poly b)` equals the corresponding chunk-projected
    `Spec.ntt_multiply_pure_no_acc` lane on `lift_chunk_mont`-style chunks,
    scaled by `(lift_fe_mont 1353)²`.

    Composes `Spec.multiply_ntts_pure_eq_chunked_no_acc`
    with Helper 2 `Stage3MontStripFC.ntt_multiply_pure_no_acc_chunk_at_lift_poly_eq`. -/
theorem multiply_ntts_lane_eq_canonical_factor
    (a b : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (ℓ : Nat) (hℓ : ℓ < 256) :
    (Spec.multiply_ntts_pure (lift_poly a) (lift_poly b)).val[ℓ]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((Spec.ntt_multiply_pure_no_acc
              (lift_chunk_mont a.coefficients.val[ℓ / 16]!)
              (lift_chunk_mont b.coefficients.val[ℓ / 16]!)
              (Spec.zeta_at (64 + 4 * (ℓ / 16)))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont (1353#i16 : Std.I16))
            (lift_fe_mont (1353#i16 : Std.I16))) := by
  have h_div_lt : ℓ / 16 < 16 := by omega
  have h_mod_lt : ℓ % 16 < 16 := Nat.mod_lt _ (by decide)
  -- Step 1: rewrite Spec.multiply_ntts_pure via the chunked form.
  rw [Spec.multiply_ntts_pure_eq_chunked_no_acc]
  -- Step 2: project lane ℓ through flatten_chunks via the inner list.
  unfold Spec.flatten_chunks
  -- The Std.Array.make's `.val[k]!` lookup is direct list-lookup.
  show ((List.range 256).map (fun j =>
          (((List.range 16).map (fun j' =>
              Spec.ntt_multiply_pure_no_acc
                (Spec.chunk_at (lift_poly a) j') (Spec.chunk_at (lift_poly b) j')
                (Spec.zeta_at (64 + 4 * j')) (Spec.zeta_at (64 + 4 * j' + 1))
                (Spec.zeta_at (64 + 4 * j' + 2)) (Spec.zeta_at (64 + 4 * j' + 3)))
              )[j / 16]!).val[j % 16]!))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]
  -- Now we have: `(((List.range 16).map f)[ℓ / 16]!).val[ℓ % 16]! = RHS`.
  -- Reduce the inner getElem!.
  rw [getElem!_pos _ (ℓ / 16) (by simp [List.length_map, List.length_range, h_div_lt])]
  rw [List.getElem_map, List.getElem_range]
  -- Now apply Helper 2.
  exact Stage3MontStripFC.ntt_multiply_pure_no_acc_chunk_at_lift_poly_eq
    a b (ℓ / 16) h_div_lt
    (Spec.zeta_at (64 + 4 * (ℓ / 16))) (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
    (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2)) (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))
    (ℓ % 16) h_mod_lt

set_option maxHeartbeats 1000000 in
/-- **Helper 2.** Generic foldl/mul distributivity: pulling a uniform
    right-multiplicand `K` out of every accumulator step.

    `mul_pure (foldl (fun s x => add_pure s (f x)) seed L) K
       = foldl (fun s x => add_pure s (mul_pure (f x) K)) (mul_pure seed K) L`. -/
theorem foldl_add_mul_distrib
    {α : Type} (L : List α)
    (f : α → hacspec_ml_kem.parameters.FieldElement)
    (seed K : hacspec_ml_kem.parameters.FieldElement) :
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (L.foldl (fun s x => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                            s (f x)) seed) K
      = L.foldl (fun s x => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                              s
                              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure (f x) K))
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure seed K) := by
  -- Key fact: `mul_pure (add_pure a b) K = add_pure (mul_pure a K) (mul_pure b K)`.
  -- We prove this via ZMod 3329 projection + canonical round-trip.
  have h_distrib :
      ∀ a b K' : hacspec_ml_kem.parameters.FieldElement,
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) K'
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a K')
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b K') := by
    intro a b K'
    have h_canon_lhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) K') :=
      libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
    have h_canon_rhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a K')
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b K')) :=
      libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
    have h_canon_to_lt : ∀ x : hacspec_ml_kem.parameters.FieldElement,
        libcrux_iot_ml_kem.Spec.Pure.Canonical x → x.val.val < 3329 := by
      intro x hx
      unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
      have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
        unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
      rw [hq] at hx
      exact hx
    have h_lt_lhs := h_canon_to_lt _ h_canon_lhs
    have h_lt_rhs := h_canon_to_lt _ h_canon_rhs
    rw [← feOfZMod_zmodOfFE_of_canonical _ h_lt_lhs,
        ← feOfZMod_zmodOfFE_of_canonical _ h_lt_rhs]
    congr 1
    simp only [L2_8c.zmodOfFE_add_pure, L2_8c.zmodOfFE_mul_pure]
    ring
  -- Now induction on L. We need an aux that handles the changing seed.
  induction L generalizing seed with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h_step := ih
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure seed (f h))
    rw [h_step]
    -- Goal: foldl ... (mul_pure (add_pure seed (f h)) K)
    --     = foldl ... (add_pure (mul_pure seed K) (mul_pure (f h) K))
    rw [h_distrib seed (f h) K]

/-- Canonical row-sum at column step k (foldl form in `lift_chunk_mont`,
    canonical post-scale via `mul_pure 1353 1353`). This is the partial-sum
    value at lane ℓ that the column loop produces at step k. -/
noncomputable def col_loop_lane_at_step
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (k : Nat) (ℓ : Nat) :
    hacspec_ml_kem.parameters.FieldElement :=
  libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
    ((List.range k).foldl
      (fun s c =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
          ((Spec.ntt_multiply_pure_no_acc
              (lift_chunk_mont (matrix_A.val[i * K.val + c]!.coefficients.val[ℓ / 16]!))
              (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
              (Spec.zeta_at (64 + 4 * (ℓ / 16)))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
              (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
      (Spec.mont_reduce_pure (lift_fe_int 0)))
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
      (lift_fe_mont (1353#i16 : Std.I16))
      (lift_fe_mont (1353#i16 : Std.I16)))

/-- The expected result of `multiply_matrix_by_column_at` at step k:
    an `Array FE 256` whose lane ℓ equals `col_loop_lane_at_step ... k ℓ`. -/
noncomputable def col_loop_result_at_step
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (k : Nat) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  ⟨(List.range 256).map (fun ℓ => col_loop_lane_at_step matrix_A s_as_ntt i k ℓ),
   by simp [List.length_map, List.length_range]⟩

/-- The lane-ℓ equation of `col_loop_result_at_step`. -/
theorem col_loop_result_at_step_val_lane
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (k : Nat) (ℓ : Nat) (hℓ : ℓ < 256) :
    (col_loop_result_at_step matrix_A s_as_ntt i k).val[ℓ]!
      = col_loop_lane_at_step matrix_A s_as_ntt i k ℓ := by
  unfold col_loop_result_at_step
  show ((List.range 256).map (fun ℓ' => col_loop_lane_at_step matrix_A s_as_ntt i k ℓ'))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]

/-- **Helper 3a.** Base-case lane equation: at step k=0, every lane of
    `col_loop_result_at_step` equals `parameters.FieldElement.new 0`. -/
theorem col_loop_lane_at_step_zero
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (ℓ : Nat) :
    col_loop_lane_at_step matrix_A s_as_ntt i 0 ℓ
      = ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement) := by
  unfold col_loop_lane_at_step
  rw [List.range_zero, List.foldl_nil]
  -- Now: mul_pure (mont_reduce_pure (lift_fe_int 0)) (mul_pure 1353 1353) = ⟨0#u16⟩.
  -- Both sides have ZMod 3329 value 0, both are canonical.
  have h_canon_lhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (Spec.mont_reduce_pure (lift_fe_int 0))
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (lift_fe_mont (1353#i16 : Std.I16)) (lift_fe_mont (1353#i16 : Std.I16)))) :=
    libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
  have h_canon_rhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
      ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement) := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq]
    decide
  have h_canon_to_lt : ∀ x : hacspec_ml_kem.parameters.FieldElement,
      libcrux_iot_ml_kem.Spec.Pure.Canonical x → x.val.val < 3329 := by
    intro x hx
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at hx; exact hx
  have h_lt_lhs := h_canon_to_lt _ h_canon_lhs
  have h_lt_rhs := h_canon_to_lt _ h_canon_rhs
  rw [← feOfZMod_zmodOfFE_of_canonical _ h_lt_lhs,
      ← feOfZMod_zmodOfFE_of_canonical _ h_lt_rhs]
  congr 1
  rw [L2_8c.zmodOfFE_mul_pure]
  unfold Spec.mont_reduce_pure
  rw [zmodOfFE_feOfZMod]
  unfold lift_fe_int
  rw [zmodOfFE_feOfZMod]
  -- LHS: 0 * 169 * 169 * (zmodOfFE ...) = 0; RHS: zmodOfFE ⟨0#u16⟩ = 0.
  unfold zmodOfFE
  simp

set_option maxHeartbeats 4000000 in
/-- **Helper 3b.** Step lemma: at step k < K, taking one column iteration
    transforms `col_loop_result_at_step ... k` into `col_loop_result_at_step ... (k+1)`. -/
theorem col_loop_lane_at_step_succ
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (k : Nat) (ℓ : Nat) (hℓ : ℓ < 256) :
    col_loop_lane_at_step matrix_A s_as_ntt i (k + 1) ℓ
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (col_loop_lane_at_step matrix_A s_as_ntt i k ℓ)
          (Spec.multiply_ntts_pure
            (lift_poly matrix_A.val[i * K.val + k]!) (lift_poly s_as_ntt.val[k]!)).val[ℓ]! := by
  unfold col_loop_lane_at_step
  -- LHS: mul_pure (foldl_{k+1}) (mul_pure 1353 1353).
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- Now LHS = mul_pure (add_pure (foldl_k) (no_acc_lane_at_k)) (mul_pure 1353 1353).
  -- Distribute via h_distrib (essentially Helper 2's per-pair fact, inlined).
  -- Specifically: mul_pure (add_pure x y) z = add_pure (mul_pure x z) (mul_pure y z).
  have h_distrib :
      ∀ a b c : hacspec_ml_kem.parameters.FieldElement,
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) c
          = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a c)
              (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b c) := by
    intro a b c
    have h_canon_lhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) c) :=
      libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
    have h_canon_rhs : libcrux_iot_ml_kem.Spec.Pure.Canonical
        (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a c)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure b c)) :=
      libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
    have h_canon_to_lt : ∀ x : hacspec_ml_kem.parameters.FieldElement,
        libcrux_iot_ml_kem.Spec.Pure.Canonical x → x.val.val < 3329 := by
      intro x hx
      unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
      have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
        unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
      rw [hq] at hx; exact hx
    rw [← feOfZMod_zmodOfFE_of_canonical _ (h_canon_to_lt _ h_canon_lhs),
        ← feOfZMod_zmodOfFE_of_canonical _ (h_canon_to_lt _ h_canon_rhs)]
    congr 1
    simp only [L2_8c.zmodOfFE_add_pure, L2_8c.zmodOfFE_mul_pure]
    ring
  rw [h_distrib]
  -- Now LHS = add_pure (mul_pure (foldl_k) (mul_pure 1353 1353)) (mul_pure (no_acc_lane_at_k) (mul_pure 1353 1353))
  -- The first summand is `col_loop_lane_at_step ... k ℓ` (after unfold).
  -- The second summand should equal `(Spec.multiply_ntts_pure (lift_poly matrix_A.val[i*K+k]!) (lift_poly s_as_ntt.val[k]!)).val[ℓ]!`
  -- via Helper 1.
  congr 1
  -- Apply Helper 1.
  rw [multiply_ntts_lane_eq_canonical_factor _ _ ℓ hℓ]

/-- **Helper 3c.** Closing equation: `col_loop_lane_at_step ... K.val ℓ = mul_pure (canonical_row_sum_lane ...) (lift_fe_mont 1353)`. -/
theorem col_loop_lane_at_step_K_eq_canonical
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (i : Nat) (ℓ : Nat) :
    col_loop_lane_at_step matrix_A s_as_ntt i K.val ℓ
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i (ℓ / 16) (ℓ % 16))
          (lift_fe_mont (1353#i16 : Std.I16)) := by
  unfold col_loop_lane_at_step Stage3MontStripFC.canonical_row_sum_lane
  -- LHS: mul_pure (foldl ...) (mul_pure 1353 1353).
  -- RHS: mul_pure (mul_pure (foldl ...) 1353) 1353.
  -- Same foldl on both sides; associativity of mul_pure is the only step.
  -- Use canonical round-trip + ring.
  have h_canon_to_lt : ∀ x : hacspec_ml_kem.parameters.FieldElement,
      libcrux_iot_ml_kem.Spec.Pure.Canonical x → x.val.val < 3329 := by
    intro x hx
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq] at hx; exact hx
  -- Apply the canonical-rewrite via the result of mul_pure being canonical.
  set foldl_sum := (List.range K.val).foldl
    (fun s c =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
        ((Spec.ntt_multiply_pure_no_acc
            (lift_chunk_mont (matrix_A.val[i * K.val + c]!.coefficients.val[ℓ / 16]!))
            (lift_chunk_mont (s_as_ntt.val[c]!.coefficients.val[ℓ / 16]!))
            (Spec.zeta_at (64 + 4 * (ℓ / 16)))
            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2))
            (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))).val[ℓ % 16]!))
    (Spec.mont_reduce_pure (lift_fe_int 0)) with h_fs_def
  set mont1353 := lift_fe_mont (1353#i16 : Std.I16)
  -- Both LHS and RHS are products of `mul_pure`, hence canonical.
  have h_canon_lhs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
    foldl_sum
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure mont1353 mont1353)
  have h_canon_rhs := libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure foldl_sum mont1353)
    mont1353
  rw [← feOfZMod_zmodOfFE_of_canonical _ (h_canon_to_lt _ h_canon_lhs),
      ← feOfZMod_zmodOfFE_of_canonical _ (h_canon_to_lt _ h_canon_rhs)]
  apply congrArg
  simp only [L2_8c.zmodOfFE_mul_pure]
  ring

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
theorem multiply_matrix_by_column_at_eq
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (i : Std.Usize) (hi : i.val < K.val) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column_at
        (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i
      = .ok ⟨(List.range 256).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i.val
                  (ℓ / 16) (ℓ % 16))
                (lift_fe_mont (1353#i16 : Std.I16))),
             by simp [List.length_map, List.length_range]⟩ := by
  -- Reduce the target: the .ok's payload coincides with `col_loop_result_at_step ... K.val`
  -- after applying `col_loop_lane_at_step_K_eq_canonical`.
  have h_target_eq :
      (⟨(List.range 256).map (fun ℓ =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i.val
                  (ℓ / 16) (ℓ % 16))
                (lift_fe_mont (1353#i16 : Std.I16))),
             by simp [List.length_map, List.length_range]⟩ :
       Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) =
      col_loop_result_at_step matrix_A s_as_ntt i.val K.val := by
    apply Subtype.ext
    unfold col_loop_result_at_step
    show _ = (List.range 256).map _
    apply List.map_congr_left
    intro ℓ _
    rw [col_loop_lane_at_step_K_eq_canonical]
  rw [h_target_eq]
  -- Now we need: multiply_matrix_by_column_at lift_M lift_S i = .ok (col_loop_result_at_step ... K.val).
  -- Use the loop equation directly.
  unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  -- Now goal: multiply_matrix_by_column_at_loop ⟨0, K⟩ lift_M lift_S i (Array.repeat 256 ⟨0⟩) = .ok ...
  -- Use loop_range_spec_usize with `inv k r = pure (r = col_loop_result_at_step ... k.val)`.
  -- Step 1: get the Triple form, then extract the .ok form.
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
        ({ start := 0#usize, «end» := K }
          : CoreModels.core.ops.range.Range Std.Usize)
        (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i
        (Std.Array.repeat (256#usize : Std.Usize)
          ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement))
      ⦃ ⇓ r => ⌜ r = col_loop_result_at_step matrix_A s_as_ntt i.val K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                   Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
          hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
            (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i p.1 p.2)
        (β := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
        (Std.Array.repeat (256#usize : Std.Usize)
          ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement))
        0#usize K
        (fun k result => pure (result = col_loop_result_at_step matrix_A s_as_ntt i.val k.val))
        (Nat.zero_le _)
        (by
          -- Base: init = col_loop_result_at_step ... 0.
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold col_loop_result_at_step
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = col_loop_lane_at_step matrix_A s_as_ntt i.val 0 n
          rw [col_loop_lane_at_step_zero])
        ?_)
    · -- Post entailment.
      rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = col_loop_result_at_step matrix_A s_as_ntt i.val K.val)
                  : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · -- Step.
      intro acc k h_ge h_le hinv
      have h_acc_eq : acc = col_loop_result_at_step matrix_A s_as_ntt i.val k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      -- Body: Range.next; if Some j (j < K), then index_usize + multiply_ntts + add_polynomials.
      unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
      by_cases h_lt : k.val < K.val
      · -- `Some k` branch.
        have h_iter_step :
            ⦃ ⌜ True ⌝ ⦄
            core.iter.range.IteratorRange.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
            ⦃ ⇓ r => ⌜ ∃ s : Std.Usize, s.val = k.val + 1 ∧
                        r = (some k,
                            ({ start := s, «end» := K }
                              : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
          libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
            (fun _ s hs => by
              dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
              exact ⟨s, hs, rfl⟩)
            (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
        obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_step
        obtain ⟨s_iter, hs_iter_val, hv_iter_pair⟩ := hv_iter_post
        -- Compute (lift_matrix_from_slice matrix_A K).val[k.val]! — the k-th column.
        have h_lift_M_len : (lift_matrix_from_slice matrix_A K).length = K.val :=
          Std.Array.length_eq _
        set col_k : Std.Array
              (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
          (lift_matrix_from_slice matrix_A K).val[k.val]! with h_col_k_def
        have h_idx_col : Aeneas.Std.Array.index_usize (lift_matrix_from_slice matrix_A K) k
            = .ok col_k :=
          libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq _ k
            (by rw [h_lift_M_len]; exact h_lt)
        -- The k-th column at row i is lift_poly matrix_A.val[i.val * K.val + k.val]!.
        have h_col_k_val : col_k.val[i.val]!
            = lift_poly matrix_A.val[i.val * K.val + k.val]! := by
          rw [h_col_k_def]
          unfold lift_matrix_from_slice
          show ((List.range K.val).map (fun j' =>
                Std.Array.make K
                  ((List.range K.val).map (fun i' =>
                    lift_poly matrix_A.val[i' * K.val + j']!))
                  (by simp)))[k.val]!.val[i.val]! = _
          rw [getElem!_pos _ k.val (by simp [List.length_map, List.length_range]; exact h_lt)]
          rw [List.getElem_map, List.getElem_range]
          show ((List.range K.val).map (fun i' =>
                lift_poly matrix_A.val[i' * K.val + k.val]!))[i.val]! = _
          rw [getElem!_pos _ i.val (by simp [List.length_map, List.length_range]; exact hi)]
          rw [List.getElem_map, List.getElem_range]
        have h_col_k_len : col_k.length = K.val := Std.Array.length_eq _
        set a1 : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          lift_poly matrix_A.val[i.val * K.val + k.val]! with h_a1_def
        have h_idx_a1 : Aeneas.Std.Array.index_usize col_k i = .ok a1 := by
          have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq col_k i
            (by rw [h_col_k_len]; exact hi)
          rw [h_col_k_val] at this; exact this
        -- Compute (lift_vec s_as_ntt).val[k.val]! = lift_poly s_as_ntt.val[k.val]!.
        have h_lift_S_len : (lift_vec s_as_ntt).length = K.val := Std.Array.length_eq _
        set a2 : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          lift_poly s_as_ntt.val[k.val]! with h_a2_def
        have h_lift_S_val : (lift_vec s_as_ntt).val[k.val]! = a2 := by
          rw [h_a2_def]
          unfold lift_vec
          show (s_as_ntt.val.map lift_poly)[k.val]! = _
          have h_len_s : s_as_ntt.val.length = K.val := Std.Array.length_eq _
          rw [getElem!_pos _ k.val (by rw [List.length_map, h_len_s]; exact h_lt)]
          rw [List.getElem_map]
          rw [show s_as_ntt.val[k.val] = s_as_ntt.val[k.val]! from
                (getElem!_pos _ k.val (by rw [h_len_s]; exact h_lt)).symm]
        have h_idx_a2 : Aeneas.Std.Array.index_usize (lift_vec s_as_ntt) k = .ok a2 := by
          have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (lift_vec s_as_ntt) k
            (by rw [h_lift_S_len]; exact h_lt)
          rw [h_lift_S_val] at this; exact this
        -- multiply_ntts a1 a2 = .ok (Spec.multiply_ntts_pure a1 a2).
        have h_mult_eq : hacspec_ml_kem.ntt.multiply_ntts a1 a2
            = .ok (Spec.multiply_ntts_pure a1 a2) := by
          unfold Spec.multiply_ntts_pure
          rw [HelpersFC.multiply_ntts_eq_pure_array]
        -- add_polynomials previous product = .ok new_acc.
        have h_add_eq := Stage4MatrixAddFC.matrix_add_polynomials_eq_ok
          (col_loop_result_at_step matrix_A s_as_ntt i.val k.val)
          (Spec.multiply_ntts_pure a1 a2)
        -- Show the new accumulator equals col_loop_result_at_step ... (k.val + 1).
        set new_acc : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          ⟨(List.range 256).map (fun n =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (col_loop_result_at_step matrix_A s_as_ntt i.val k.val).val[n]!
                (Spec.multiply_ntts_pure a1 a2).val[n]!),
           by simp [List.length_map, List.length_range]⟩ with h_new_acc_def
        have h_new_acc_eq : new_acc
            = col_loop_result_at_step matrix_A s_as_ntt i.val (k.val + 1) := by
          unfold col_loop_result_at_step
          apply Subtype.ext
          rw [h_new_acc_def]
          apply List.map_congr_left
          intro n hn_mem
          have hn_lt : n < 256 := List.mem_range.mp hn_mem
          rw [col_loop_result_at_step_val_lane _ _ _ _ _ hn_lt]
          rw [col_loop_lane_at_step_succ _ _ _ _ _ hn_lt]
        -- Body equation: drive the do-block to .ok (cont ...).
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
                (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i p.1 p.2)
              ({ start := k, «end» := K },
                col_loop_result_at_step matrix_A s_as_ntt i.val k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  col_loop_result_at_step matrix_A s_as_ntt i.val (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
                (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i
                { start := k, «end» := K }
                (col_loop_result_at_step matrix_A s_as_ntt i.val k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
          -- Force destructure (some k, iter') into the some j=k branch.
          show ((do
                  let a ← Aeneas.Std.Array.index_usize
                            (lift_matrix_from_slice matrix_A K) k
                  let a1' ← Aeneas.Std.Array.index_usize a i
                  let a2' ← Aeneas.Std.Array.index_usize (lift_vec s_as_ntt) k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a1' a2'
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (col_loop_result_at_step matrix_A s_as_ntt i.val k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
          rw [h_idx_col]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a1]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_idx_a2]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_mult_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [h_add_eq]
          simp only [Aeneas.Std.bind_tc_ok]
          rw [← h_new_acc_eq]
        apply triple_of_ok_fc h_body
        -- Discharge step_post for .cont branch.
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (col_loop_result_at_step matrix_A s_as_ntt i.val (k.val + 1)
                      = col_loop_result_at_step matrix_A s_as_ntt i.val s_iter.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
      · -- `None` branch: k ≥ K, body returns .ok (.done result).
        have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
        have hk_eq : k.val = K.val := by omega
        have h_iter_none :
            ⦃ ⌜ True ⌝ ⦄
            core.iter.range.IteratorRange.next
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
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
              hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
                (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i p.1 p.2)
              ({ start := k, «end» := K },
                col_loop_result_at_step matrix_A s_as_ntt i.val k.val)
            = .ok (ControlFlow.done
                (col_loop_result_at_step matrix_A s_as_ntt i.val k.val)) := by
          show hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
                (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i
                { start := k, «end» := K }
                (col_loop_result_at_step matrix_A s_as_ntt i.val k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop.body
          conv_lhs =>
            rw [show
              (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
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
        show (pure (col_loop_result_at_step matrix_A s_as_ntt i.val k.val
                      = col_loop_result_at_step matrix_A s_as_ntt i.val K.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  -- Now extract the .ok form from h_triple.
  match h_loop : hacspec_ml_kem.matrix.multiply_matrix_by_column_at_loop
        ({ start := 0#usize, «end» := K }
          : CoreModels.core.ops.range.Range Std.Usize)
        (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt) i
        (Std.Array.repeat (256#usize : Std.Usize)
          ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement)),
        h_triple with
  | .ok r, h =>
    have hr : r = col_loop_result_at_step matrix_A s_as_ntt i.val K.val := by
      simpa [Std.Do.Triple, Std.Do.WP.wp] using h
    rw [hr]
  | .fail _, h => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Std.Do.Triple, Std.Do.WP.wp, PostCond.noThrow, PredTrans.apply])

set_option maxHeartbeats 4000000 in
/-- **Helper 4.** Outer `createi K` wrapper around Helper 3 producing the
    full `multiply_matrix_by_column` result. -/
theorem multiply_matrix_by_column_eq
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (hAlen : matrix_A.length = (K.val * K.val : Nat)) :
    hacspec_ml_kem.matrix.multiply_matrix_by_column
        (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt)
      = .ok ⟨(List.range K.val).map (fun i =>
              (⟨(List.range 256).map (fun ℓ =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i
                      (ℓ / 16) (ℓ % 16))
                    (lift_fe_mont (1353#i16 : Std.I16))),
                by simp [List.length_map, List.length_range]⟩ :
              Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    fun i => ⟨(List.range 256).map (fun ℓ =>
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i
                    (ℓ / 16) (ℓ % 16))
                  (lift_fe_mont (1353#i16 : Std.I16))),
              by simp [List.length_map, List.length_range]⟩ with hf_def
  have hpure : ∀ k : Nat, k < K.val →
      (hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256
        K).FnMutInst.call_mut
        (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt)) := by
    intro k hk
    show hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
        (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt))
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    -- Reduce to: multiply_matrix_by_column_at lift_M lift_S ⟨k⟩.
    have hk_val : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have hK_lt : K.val < 2^System.Platform.numBits := by
        have h := K.hBounds
        simp [] at h
        omega
      exact Nat.lt_of_lt_of_le hk (Nat.le_of_lt hK_lt)
    -- Need: multiply_matrix_by_column_at lift_M lift_S ⟨k⟩ = .ok (f k).
    have hk_lt : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < K.val := by
      rw [hk_val]; exact hk
    have h_mmbc_at := multiply_matrix_by_column_at_eq matrix_A s_as_ntt hAlen
      (⟨BitVec.ofNat _ k⟩ : Std.Usize) hk_lt
    show (do let a ← hacspec_ml_kem.matrix.multiply_matrix_by_column_at
              (lift_matrix_from_slice matrix_A K) (lift_vec s_as_ntt)
              (⟨BitVec.ofNat _ k⟩ : Std.Usize)
             .ok (a, (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt))) =
         .ok (f k, _)
    rw [h_mmbc_at]; simp only [bind_tc_ok]
    rw [hk_val]
  unfold hacspec_ml_kem.matrix.multiply_matrix_by_column
  unfold hacspec_ml_kem.parameters.createi
  have h_from_fn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
    (T := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (F := hacspec_ml_kem.matrix.multiply_matrix_by_column.closure K)
    (N := K)
    (inst := (hacspec_ml_kem.matrix.multiply_matrix_by_column.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K).FnMutInst)
    (c := (lift_matrix_from_slice matrix_A K, lift_vec s_as_ntt))
    (f := f)
    hpure
  show core.array.from_fn K _ _ = _
  exact h_from_fn

set_option maxHeartbeats 32000000 in
/-- **Helper 5 (main bridge).** Given the per-row, per-lane characterization
    of `t_as_ntt_final`, proves the hacspec `compute_As_plus_e` equation that
    L7.1's POST demands. -/
theorem hacspec_compute_As_plus_e_eq_of_lane_eq
    {K : Std.Usize}
    (matrix_A : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt t_as_ntt_final : Std.Array
                                              (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                                                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (h_lane_eq : ∀ r : Nat, r < K.val → ∀ ℓ : Nat, ℓ < 256 →
      (lift_poly t_as_ntt_final.val[r]!).val[ℓ]!
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r (ℓ / 16) (ℓ % 16))
              (lift_fe_mont (1353#i16 : Std.I16)))
            ((lift_poly error_as_ntt.val[r]!).val[ℓ]!)) :
    hacspec_ml_kem.matrix.compute_As_plus_e
        (lift_matrix_from_slice matrix_A K)
        (lift_vec s_as_ntt) (lift_vec error_as_ntt)
      = .ok (lift_vec t_as_ntt_final) := by
  unfold hacspec_ml_kem.matrix.compute_As_plus_e
  -- Step 1: replace `multiply_matrix_by_column ... = .ok (P_arr)` via Helper 4.
  rw [multiply_matrix_by_column_eq matrix_A s_as_ntt hAlen]
  simp only [bind_tc_ok]
  -- Step 2: unfold add_vectors and apply from_fn_pure_eq.
  set P_arr : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    ⟨(List.range K.val).map (fun i =>
      (⟨(List.range 256).map (fun ℓ =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt i
              (ℓ / 16) (ℓ % 16))
            (lift_fe_mont (1353#i16 : Std.I16))),
        by simp [List.length_map, List.length_range]⟩ :
      Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)),
     by simp [List.length_map, List.length_range]⟩ with hP_def
  -- For lookup at row r < K.val.
  have h_P_at : ∀ r : Nat, r < K.val →
      P_arr.val[r]! = (⟨(List.range 256).map (fun ℓ =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r
              (ℓ / 16) (ℓ % 16))
            (lift_fe_mont (1353#i16 : Std.I16))),
        by simp [List.length_map, List.length_range]⟩ :
      Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) := by
    intro r hr
    rw [hP_def]
    show ((List.range K.val).map _)[r]! = _
    rw [getElem!_pos _ r (by simp [List.length_map, List.length_range, hr])]
    rw [List.getElem_map, List.getElem_range]
  -- For lane lookup inside P_arr[r].
  have h_P_at_lane : ∀ r : Nat, r < K.val → ∀ ℓ : Nat, ℓ < 256 →
      (P_arr.val[r]!).val[ℓ]!
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r
              (ℓ / 16) (ℓ % 16))
            (lift_fe_mont (1353#i16 : Std.I16)) := by
    intro r hr ℓ hℓ
    rw [h_P_at r hr]
    show ((List.range 256).map (fun ℓ' =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r
                (ℓ' / 16) (ℓ' % 16))
              (lift_fe_mont (1353#i16 : Std.I16))))[ℓ]! = _
    rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
    rw [List.getElem_map, List.getElem_range]
  -- Now: hacspec_ml_kem.matrix.add_vectors P_arr (lift_vec error_as_ntt) = .ok (lift_vec t_as_ntt_final).
  unfold hacspec_ml_kem.matrix.add_vectors
  unfold hacspec_ml_kem.parameters.createi
  set f_out : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    fun r => (lift_vec t_as_ntt_final).val[r]! with hf_def
  -- Per-call_mut equation.
  have hpure : ∀ r : Nat, r < K.val →
      (hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K).FnMutInst.call_mut
        (P_arr, lift_vec error_as_ntt) ⟨BitVec.ofNat _ r⟩
        = .ok (f_out r, (P_arr, lift_vec error_as_ntt)) := by
    intro r hr
    show hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
            (P_arr, lift_vec error_as_ntt) ⟨BitVec.ofNat _ r⟩
        = .ok (f_out r, (P_arr, lift_vec error_as_ntt))
    unfold hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnMutTupleUsizeArrayFieldElement256.call_mut
    unfold hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256.call
    have hr_val : (⟨BitVec.ofNat _ r⟩ : Std.Usize).val = r := by
      show (BitVec.ofNat _ r).toNat = r
      apply Nat.mod_eq_of_lt
      have hK_lt : K.val < 2^System.Platform.numBits := by
        have h := K.hBounds
        simp [] at h
        omega
      exact Nat.lt_of_lt_of_le hr (Nat.le_of_lt hK_lt)
    have hP_len : P_arr.length = K.val := by
      rw [hP_def]
      show ((List.range K.val).map _).length = K.val
      simp [List.length_map, List.length_range]
    have hE_len : (lift_vec error_as_ntt).length = K.val := by
      unfold lift_vec
      show (error_as_ntt.val.map lift_poly).length = K.val
      rw [List.length_map, error_as_ntt.property]
    have hr_lt_P : (⟨BitVec.ofNat _ r⟩ : Std.Usize).val < P_arr.length := by
      rw [hr_val, hP_len]; exact hr
    have hr_lt_E : (⟨BitVec.ofNat _ r⟩ : Std.Usize).val < (lift_vec error_as_ntt).length := by
      rw [hr_val, hE_len]; exact hr
    have h_idx_P : Std.Array.index_usize P_arr (⟨BitVec.ofNat _ r⟩ : Std.Usize)
                    = .ok (P_arr.val[r]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq P_arr
                  (⟨BitVec.ofNat _ r⟩ : Std.Usize) hr_lt_P
      rw [hr_val] at this; exact this
    have h_idx_E : Std.Array.index_usize (lift_vec error_as_ntt) (⟨BitVec.ofNat _ r⟩ : Std.Usize)
                    = .ok ((lift_vec error_as_ntt).val[r]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (lift_vec error_as_ntt)
                  (⟨BitVec.ofNat _ r⟩ : Std.Usize) hr_lt_E
      rw [hr_val] at this; exact this
    -- Apply matrix_add_polynomials_eq_ok.
    have h_add := matrix_add_polynomials_eq_ok
      (P_arr.val[r]!) ((lift_vec error_as_ntt).val[r]!)
    -- Reduce: the closure destructures (a, a1) := (P_arr, lift_vec error_as_ntt).
    -- Use `show` to expose the destructure outcome (a → P_arr, a1 → lift_vec error_as_ntt).
    show (do let fe ← (do
                let a2 ← Std.Array.index_usize P_arr (⟨BitVec.ofNat _ r⟩ : Std.Usize)
                let a3 ← Std.Array.index_usize (lift_vec error_as_ntt) (⟨BitVec.ofNat _ r⟩ : Std.Usize)
                hacspec_ml_kem.matrix.add_polynomials a2 a3)
             .ok (fe, P_arr, lift_vec error_as_ntt)) = _
    rw [h_idx_P]; simp only [bind_tc_ok]
    rw [h_idx_E]; simp only [bind_tc_ok]
    rw [h_add]; simp only [bind_tc_ok]
    -- Now need: ok (⟨...add_pure ⟩, P, E) = ok (f_out r, P, E).
    -- Beta-reduce f_out r.
    show Result.ok (⟨List.map _ (List.range 256), _⟩, P_arr, lift_vec error_as_ntt) =
         Result.ok ((lift_vec t_as_ntt_final).val[r]!, P_arr, lift_vec error_as_ntt)
    have h_lift_t_at : (lift_vec t_as_ntt_final).val[r]! = lift_poly t_as_ntt_final.val[r]! := by
      unfold lift_vec
      show (t_as_ntt_final.val.map lift_poly)[r]! = _
      rw [getElem!_pos _ r (by rw [List.length_map, t_as_ntt_final.property]; exact hr)]
      rw [List.getElem_map]
      congr 1
      rw [getElem!_pos _ r (by rw [t_as_ntt_final.property]; exact hr)]
    rw [h_lift_t_at]
    congr 1
    -- Now: (⟨...⟩, P, E) = (lift_poly t.val[r]!, P, E). Reduce the tuple.
    refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, rfl⟩
    -- Now we need: ⟨(List.range 256).map _, _⟩ = lift_poly t_as_ntt_final.val[r]!.
    -- Apply per-lane equality via h_lane_eq.
    -- Goal: ⟨List.map (fun k => add_pure ...), _⟩ = lift_poly t_as_ntt_final.val[r]!
    -- Both sides are Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize.
    -- Use Subtype.ext + manual val-level rewrites via rfl-shape lemmas.
    have h_coe_mk : ∀ (l : List hacspec_ml_kem.parameters.FieldElement)
        (h : l.length = (256#usize : Std.Usize).val),
        ((⟨l, h⟩ : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) : List _) = l :=
      fun _ _ => rfl
    have h_make : ∀ (l : List hacspec_ml_kem.parameters.FieldElement)
        (h : l.length = (256#usize : Std.Usize).val),
        ((Std.Array.make 256#usize l h : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) : List _) = l :=
      fun _ _ => rfl
    apply Subtype.ext
    unfold lift_poly
    rw [h_coe_mk, h_make]
    apply List.map_congr_left
    intro ℓ hℓ_mem
    have hℓ : ℓ < 256 := List.mem_range.mp hℓ_mem
    have h_lane := h_lane_eq r hr ℓ hℓ
    rw [h_P_at_lane r hr ℓ hℓ]
    have h_lift_e_at : (lift_vec error_as_ntt).val[r]! = lift_poly error_as_ntt.val[r]! := by
      unfold lift_vec
      show (error_as_ntt.val.map lift_poly)[r]! = _
      rw [getElem!_pos _ r (by rw [List.length_map, error_as_ntt.property]; exact hr)]
      rw [List.getElem_map]
      congr 1
      rw [getElem!_pos _ r (by rw [error_as_ntt.property]; exact hr)]
    rw [h_lift_e_at]
    rw [← h_lane]
    -- Goal: (lift_poly t_as_ntt_final.val[r]!).val[ℓ]! = lift_fe (...).
    -- After unfolding lift_poly the LHS reduces to ((List.range 256).map ...)[ℓ]!
    -- which rewrites to lift_fe (...) via getElem!_pos + getElem_map + getElem_range.
    unfold lift_poly
    show (((List.range 256).map
            (fun j => lift_fe
              ((t_as_ntt_final.val[r]!.coefficients.val[j / 16]!).elements.val[j % 16]!)))[ℓ]!
            : hacspec_ml_kem.parameters.FieldElement) =
          lift_fe ((t_as_ntt_final.val[r]!.coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!)
    rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
    rw [List.getElem_map, List.getElem_range]
  have h_from_fn := libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
    (T := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (F := hacspec_ml_kem.matrix.add_vectors.closure K)
    (N := K)
    (inst := (hacspec_ml_kem.matrix.add_vectors.closure.Insts.CoreOpsFunctionFnTupleUsizeArrayFieldElement256 K).FnMutInst)
    (c := (P_arr, lift_vec error_as_ntt))
    (f := f_out)
    hpure
  show core.array.from_fn K _ _ = _
  rw [h_from_fn]
  -- Now need: .ok ⟨(List.range K.val).map f_out, _⟩ = .ok (lift_vec t_as_ntt_final).
  -- f_out r = (lift_vec t_as_ntt_final).val[r]!. So the LHS is the
  -- array whose `.val[r] = (lift_vec t_as_ntt_final).val[r]!` for r < K.val.
  congr 1
  apply Subtype.ext
  unfold lift_vec
  change (List.range K.val).map f_out = t_as_ntt_final.val.map lift_poly
  apply List.ext_getElem
  · simp [List.length_map, List.length_range, t_as_ntt_final.property]
  intro n h_n_lhs _
  have h_n_lt : n < K.val := by
    rw [List.length_map, List.length_range] at h_n_lhs; exact h_n_lhs
  rw [List.getElem_map, List.getElem_range]
  rw [hf_def]
  -- f_out n = (lift_vec t_as_ntt_final).val[n]! = lift_poly t_as_ntt_final.val[n]!.
  unfold lift_vec
  show (t_as_ntt_final.val.map lift_poly)[n]! = (t_as_ntt_final.val.map lift_poly)[n]
  rw [getElem!_pos _ n (by rw [List.length_map, t_as_ntt_final.property]; exact h_n_lt)]

end Stage4MatrixAddFC

/-! ## §L7 — matrix-level targets (4 theorems).

    These are the ultimate FC obligations: the impl matrix functions
    must compute the same hacspec ring-element vector / single ring
    element as their spec counterparts. -/

/-- L7.1 — `matrix.compute_As_plus_e`: product `A · s + e` of the
    public-key generation step. Impl returns
    `(t_as_ntt, s_cache, accumulator)`; project on `t_as_ntt`.

    PRE:
    - `hAlen` : flat slice has K·K entries.
    - `hK` : `K.val ≤ 4` (ML-KEM 768/1024 etc.; drives `K · 2^25 ≤ 2^27`
      bound for `poly_reducing_from_i32_array_fc`).
    - `h_matrix_bnd` : per-lane bound on `matrix_A`'s entries
      (consumed by L6.3c `accumulating_ntt_multiply_*_poly_fc`).
    - `h_s_bnd`      : per-lane bound on `s_as_ntt`'s entries.
    - `h_error_bnd`  : per-lane bound on `error_as_ntt`'s entries
      (the 29439 = 9 · 3271 ceiling required by L6.5
      `add_standard_error_reduce_fc`).
    - `h_acc_bnd`    : per-lane additive-budget bound on initial
      `accumulator` (consumed by row-0 forward dep `Stage 1`, whose PRE
      requires `acc[n] + K · 2^25 ≤ 2^30`; rows 1..K-1 re-zero the
      accumulator inside `compute_As_plus_e_loop1`).

    POST (`VecMatches`-output form). The spec is run on the lifted
    *inputs* (`lift_matrix_from_slice` / `lift_vec` — irreducible, since the
    hacspec spec is typed in `FieldElement`), yielding some `spec_out`. The
    output side is stated via the shared `VecMatches` predicate (row-wise
    `PolyMatches`, lane-wise `LaneMatches`): for every row `r` and lane `ℓ`, the
    raw impl coefficient `x := (p.1 … lane r ℓ).val : Int` is the *unique centered
    Barrett representative* of the spec residue — `|x| ≤ 1664 = ⌊q/2⌋` (a complete
    residue system, so `x` is pinned uniquely) **and** `(x : ZMod q) =
    zmodOfFE (spec_out … lane r ℓ)`.

    REVIEWING THE POST: `VecMatches`/`PolyMatches`/`LaneMatches` (in `Spec/Lift.lean`)
    reduce to a magnitude bound plus a residue equality in `ZMod q` (no `.toNat`).
    The centered bound `|x| ≤ 1664` is threaded up from `barrett_reduce_core` via
    `barrett_reduce_fc` through `add_standard_error_reduce_fc`, the loop
    invariants, and `row0_finalize`/`loop1`. The residue equality is discharged by
    `Spec/Lift.lean`'s `laneMatches_lift_fe` (from `lift_fe_spec`) composed with
    the §Audit getters `lift_vec_getElem`/`lift_poly_getElem`. The INPUT bridge is
    still audited from `§Audit`'s `lift_fe_spec`/`lift_fe_inj_mod` lifted through
    `lift_matrix_from_slice_{spec,inj_mod}` and `lift_vec_{spec,inj_mod}`. -/
@[spec]
theorem compute_As_plus_e_fc
    {K : Std.Usize}
    (t_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (matrix_A : Slice
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (s_as_ntt error_as_ntt s_cache : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (hAlen : matrix_A.length = (K.val * K.val : Nat))
    (hK : K.val ≤ 4)
    (h_matrix_bnd : ∀ k : Fin matrix_A.length, ∀ i j : Fin 16,
        ((matrix_A.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_s_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((s_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_error_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((error_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 29439)
    (h_acc_bnd : ∀ n : Fin 256,
        (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_acc_zero : ∀ n : Nat, n < 256 → accumulator.val[n]! = (0#i32 : Std.I32))
    (hK_pos : 0 < K.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_As_plus_e
      (vectortraitsOperationsInst := portable_ops_inst)
      t_as_ntt matrix_A s_as_ntt error_as_ntt s_cache accumulator
    ⦃ ⇓ p => ⌜ ∃ spec_out,
                  hacspec_ml_kem.matrix.compute_As_plus_e
                    (lift_matrix_from_slice matrix_A K)
                    (lift_vec s_as_ntt) (lift_vec error_as_ntt) = .ok spec_out
                ∧ VecMatches p.1.val spec_out ⌝ ⦄ := by
  -- Length facts.
  have h_t_len : t_as_ntt.length = K.val := Std.Array.length_eq t_as_ntt
  have h_err_len : error_as_ntt.length = K.val := Std.Array.length_eq error_as_ntt
  -- Re-shape PRE bounds for sub-lemmas (Fin 16 ↔ Nat).
  have h_s_bnd' : ∀ k : Fin K.val, ∀ a b : Fin 16,
      ((s_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
    h_s_bnd
  have h_error_bnd' : ∀ k : Fin K.val, ∀ a b : Fin 16,
      ((error_as_ntt.val[k.val]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs
        ≤ 29439 := h_error_bnd
  -- ── S1: row-0 column loop (loop0). acc_init = input `accumulator` (zero). ──
  obtain ⟨⟨cache1, acc2⟩, h_loop0_eq, h_row0⟩ := triple_exists_ok_fc
    (compute_As_plus_e_loop0_fc matrix_A s_as_ntt s_cache accumulator hAlen
      h_matrix_bnd h_s_bnd h_acc_bnd)
  dsimp only at h_loop0_eq h_row0
  -- Destructure row0_inv: (1) lane, (2) acc bound, (3) cache populated, (4) cache unchanged.
  obtain ⟨_h_row0_lane, h_acc2_bnd_raw, h_cache_done, _h_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
      Stage1FillCacheFC.row0_inv, ← List.getElem!_eq_getElem?_getD] using h_row0
  -- Cache-post bridge for loop1: row0_inv conjunct (3) at k = K.
  have h_cache_post : ∀ c : Nat, c < K.val →
      accumulating_ntt_multiply_poly_cache_post (s_as_ntt.val[c]!) (cache1.val[c]!) := by
    intro c hc; exact h_cache_done c hc
  -- acc2 lane bound: ≤ 2^16·3328 (from acc2[n] ≤ acc_init[n] + K·2^25, acc_init = 0).
  have h_acc2_lane_bnd : ∀ n : Nat, n < 256 →
      (acc2.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
    intro n hn
    have hb := h_acc2_bnd_raw n hn
    have hz : (accumulator.val[n]!).val.natAbs = 0 := by
      rw [h_acc_zero n hn]; rfl
    rw [hz] at hb
    have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
    have h2 : (4 : Nat) * 2^25 ≤ 2^16 * 3328 := by decide
    omega
  -- ── Row-0 finalize: produces `a` with row-0 lane eq + rows>0 unchanged
  --    + row-0 Barrett output bound. ──
  obtain ⟨a, h_fin_eq, h_a0_lane, h_a_unch, h_a0_bnd⟩ := triple_exists_ok_fc
    (compute_As_plus_e_row0_finalize_fc t_as_ntt matrix_A s_as_ntt error_as_ntt s_cache
      accumulator acc2 cache1 hK_pos h_error_bnd h_acc_zero h_acc2_lane_bnd h_row0)
  dsimp only at h_fin_eq h_a0_lane h_a_unch h_a0_bnd
  -- ── S2: outer rows loop [1, K). t_as_ntt_init = a. acc seed = acc2 (loop1 re-zeros). ──
  obtain ⟨⟨t_as_ntt2, accumulator2⟩, h_loop1_eq, h_rows⟩ := triple_exists_ok_fc
    (compute_As_plus_e_loop1_fc a matrix_A s_as_ntt error_as_ntt cache1 acc2 1#usize hK
      (by show (1#usize : Std.Usize).val ≤ K.val; exact hK_pos) hAlen
      h_matrix_bnd h_s_bnd h_error_bnd h_cache_post)
  dsimp only at h_loop1_eq h_rows
  -- Destructure rows_inv: (1) done rows [1,K), (2) unchanged rows,
  -- (3) per-done-row Barrett output bound |lane| ≤ 1664.
  obtain ⟨h_rows_done, h_rows_undone, h_rows_bnd⟩ := by
    simpa [Stage3MontStripFC.rows_inv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
      ← List.getElem!_eq_getElem?_getD] using h_rows
  -- t_as_ntt2[0] = a[0] (loop1 starts at 1, leaves row 0 unchanged).
  have h_t2_at0 : t_as_ntt2.val[0]! = a.val[0]! := by
    exact h_rows_undone 0 (by omega) (Or.inl (by decide))
  -- ── Per-row, per-lane characterization of t_as_ntt2. ──
  have h_lane_eq : ∀ r : Nat, r < K.val → ∀ ℓ : Nat, ℓ < 256 →
      (lift_poly t_as_ntt2.val[r]!).val[ℓ]!
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (Stage3MontStripFC.canonical_row_sum_lane matrix_A s_as_ntt r (ℓ / 16) (ℓ % 16))
              (lift_fe_mont (1353#i16 : Std.I16)))
            ((lift_poly error_as_ntt.val[r]!).val[ℓ]!) := by
    intro r hr ℓ hℓ
    by_cases h0 : r = 0
    · subst h0
      rw [h_t2_at0]
      exact h_a0_lane ℓ hℓ
    · have hr1 : (1#usize : Std.Usize).val ≤ r := by
        have : (1#usize : Std.Usize).val = 1 := rfl
        rw [this]; omega
      exact h_rows_done r hr1 hr ℓ hℓ
  -- ── PART A: the hacspec equation. ──
  have h_hacspec := Stage4MatrixAddFC.hacspec_compute_As_plus_e_eq_of_lane_eq
    matrix_A s_as_ntt error_as_ntt t_as_ntt2 hAlen h_lane_eq
  -- ── Package: reduce the impl do-block to .ok (t_as_ntt2, cache1, accumulator2). ──
  apply triple_of_ok_fc (v := (t_as_ntt2, cache1, accumulator2))
  · unfold libcrux_iot_ml_kem.matrix.compute_As_plus_e
    rw [h_loop0_eq]; simp only [Aeneas.Std.bind_tc_ok]
    show (do
        let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice acc2)
        let (pre, index_mut_back) ← Aeneas.Std.Array.index_mut_usize t_as_ntt 0#usize
        let pre1 ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                     portable_ops_inst s pre
        let (pre2, index_mut_back1) ← Aeneas.Std.Array.index_mut_usize (index_mut_back pre1) 0#usize
        let pre3 ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
        let pre4 ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                     portable_ops_inst pre2 pre3
        let (t2', accumulator2') ← libcrux_iot_ml_kem.matrix.compute_As_plus_e_loop1
          portable_ops_inst { start := 1#usize, «end» := K } (index_mut_back1 pre4) matrix_A
          s_as_ntt error_as_ntt cache1 acc2
        Aeneas.Std.Result.ok (t2', cache1, accumulator2'))
      = Aeneas.Std.Result.ok (t_as_ntt2, cache1, accumulator2)
    -- Step through binds: invert h_fin_eq step by step to extract per-step equations.
    simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at h_fin_eq
    -- Step 0: index_mut_usize t_as_ntt 0
    cases h0 : Aeneas.Std.Array.index_mut_usize t_as_ntt (0#usize : Std.Usize) with
    | fail e => rw [h0] at h_fin_eq; simp at h_fin_eq
    | div => rw [h0] at h_fin_eq; simp at h_fin_eq
    | ok v0 =>
      obtain ⟨pre0, imb0⟩ := v0
      simp only [h0, Aeneas.Std.bind_tc_ok] at h_fin_eq
      -- Reduce the let-pair destructure (let (a, b) := (x, y)) to concrete form:
      change (do
          let pre1 ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
              portable_ops_inst (Aeneas.Std.Array.to_slice acc2) pre0
          let (pre2', index_mut_back1) ← (imb0 pre1).index_mut_usize 0#usize
          let pre3' ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
          let pre4' ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
              portable_ops_inst pre2' pre3'
          Aeneas.Std.Result.ok (index_mut_back1 pre4')) = Aeneas.Std.Result.ok a at h_fin_eq
      -- Step 1: reducing_from_i32_array
      cases h1 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
          portable_ops_inst (Aeneas.Std.Array.to_slice acc2) pre0 with
      | fail e => rw [h1] at h_fin_eq; simp at h_fin_eq
      | div => rw [h1] at h_fin_eq; simp at h_fin_eq
      | ok t1 =>
        simp only [h1, Aeneas.Std.bind_tc_ok] at h_fin_eq
        -- Step 2: index_mut_usize (imb0 t1) 0
        cases h2 : Aeneas.Std.Array.index_mut_usize (imb0 t1) (0#usize : Std.Usize) with
        | fail e => rw [h2] at h_fin_eq; simp at h_fin_eq
        | div => rw [h2] at h_fin_eq; simp at h_fin_eq
        | ok v2 =>
          obtain ⟨pre2, imb1⟩ := v2
          simp only [h2, Aeneas.Std.bind_tc_ok] at h_fin_eq
          -- Reduce the let-pair destructure for step 2:
          change (do
              let pre3' ← Aeneas.Std.Array.index_usize error_as_ntt 0#usize
              let pre4' ← libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                  portable_ops_inst pre2 pre3'
              Aeneas.Std.Result.ok (imb1 pre4')) = Aeneas.Std.Result.ok a at h_fin_eq
          -- Step 3: index_usize error_as_ntt 0
          cases h3 : Aeneas.Std.Array.index_usize error_as_ntt (0#usize : Std.Usize) with
          | fail e => rw [h3] at h_fin_eq; simp at h_fin_eq
          | div => rw [h3] at h_fin_eq; simp at h_fin_eq
          | ok pre3 =>
            simp only [h3, Aeneas.Std.bind_tc_ok] at h_fin_eq
            -- Step 4: add_standard_error_reduce
            cases h4 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_standard_error_reduce
                portable_ops_inst pre2 pre3 with
            | fail e => rw [h4] at h_fin_eq; simp at h_fin_eq
            | div => rw [h4] at h_fin_eq; simp at h_fin_eq
            | ok pre4 =>
              simp only [h4, Aeneas.Std.bind_tc_ok] at h_fin_eq
              -- h_fin_eq : .ok (imb1 pre4) = .ok a  →  imb1 pre4 = a
              have h_a_eq : imb1 pre4 = a := Aeneas.Std.Result.ok.inj h_fin_eq
              -- Step through the goal using the same step equations:
              simp [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok, h1, h2, h4, h_a_eq,
                h_loop1_eq]
  · -- POST (canonical-output form). p.1 = t_as_ntt2. Witness spec_out := lift_vec t_as_ntt2
    -- (so the hacspec equation is `h_hacspec`), then show every impl output lane,
    -- sign-corrected into [0, q), equals the spec residue `.val.val`.
    refine ⟨lift_vec t_as_ntt2, h_hacspec, ?_⟩
    unfold VecMatches PolyMatches
    intro r hr ℓ hℓ
    have hj : ℓ / 16 < 16 := Nat.div_lt_iff_lt_mul (by decide : 0 < 16) |>.mpr hℓ
    have hm : ℓ % 16 < 16 := Nat.mod_lt _ (by decide : 0 < 16)
    -- (a) Tight centered Barrett output bound on this lane: |t_as_ntt2[r] lane| ≤ 1664.
    have hbnd :
        (((t_as_ntt2.val[r]!).coefficients.val[ℓ / 16]!).elements.val[ℓ % 16]!.val).natAbs ≤ 1664 := by
      by_cases h0 : r = 0
      · subst h0
        rw [h_t2_at0]
        exact h_a0_bnd (ℓ / 16) hj (ℓ % 16) hm
      · have hr1 : (1#usize : Std.Usize).val ≤ r := by
          have h1v : (1#usize : Std.Usize).val = 1 := rfl
          omega
        exact h_rows_bnd r hr1 hr (ℓ / 16) hj (ℓ % 16) hm
    -- (b) The spec residue is `zmodOfFE` of the lifted lane; rewrite the RHS
    -- through the §Audit getters, then discharge `LaneMatches` with the tight
    -- bound via `laneMatches_lift_fe`.
    rw [lift_vec_getElem t_as_ntt2 r hr, lift_poly_getElem _ ℓ hℓ]
    exact laneMatches_lift_fe _ hbnd

/--
info: 'libcrux_iot_ml_kem.Matrix.ComputeAsPlusE.compute_As_plus_e_fc' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms compute_As_plus_e_fc

/- L7.2 — `matrix.compute_vector_u`: product `Aᵀ · r + e₁` of the
   encryption step. Proven as
   `libcrux_iot_ml_kem.Matrix.ComputeVectorU.FC.compute_vector_u_fc` in
   `Matrix/ComputeVectorU/FC.lean`, axiom-clean modulo the
   sanctioned `sample_matrix_entry_fc` / `Spec.sample_matrix_A_pure`
   boundary. The proof lives downstream because the `L7/` bridge tree
   imports `FCTargets`.

   POST (canonical-output form, no output `lift`): `∃ spec_out,
   hacspec_ml_kem.matrix.compute_vector_u (lift_matrix_from_seed seed K)
   (lift_vec_slice r_as_ntt K) (lift_vec_slice error_1 K) = .ok spec_out
   ∧ VecMatches p.2.1.val spec_out` — each impl output lane `x` is the unique
   centered Barrett representative of the spec residue
   (`|x| ≤ 1664 ∧ (x : ZMod q) = <spec lane>`). -/

/- L7.3 — `matrix.compute_ring_element_v`: `t · r + e₂ + message` (the
   decryption-side ring element `v`). Proven as
   `libcrux_iot_ml_kem.Matrix.ComputeRingElementV.FC.compute_ring_element_v_fc` in
   `Matrix/ComputeRingElementV/FC.lean` (PRE bounds `hK ≤ 4` /
   per-lane `≤ 3328` on `r_as_ntt`/`error_2`/`message` + the
   `accumulating_ntt_multiply_poly_cache_post` cache precondition +
   zero accumulator). The proof lives downstream because the L7.3
   bridge tree imports `FCTargets`. Axiom-clean modulo the sanctioned
   `deserialize_to_reduced_ring_element_fc` (A2) /
   `Spec.t_as_ntt_from_public_key_pure` spec-stub boundary.

   POST (canonical-output form, no output `lift`): `∃ spec_out,
   hacspec_ml_kem.matrix.compute_ring_element_v
   (lift_t_as_ntt_from_public_key public_key K) (lift_vec_slice r_as_ntt K)
   (lift_poly error_2) (lift_poly message) = .ok spec_out
   ∧ PolyMatches p.2.1 spec_out` — each impl output lane `x` is the unique
   centered Barrett representative of the spec residue
   (`|x| ≤ 1664 ∧ (x : ZMod q) = <spec lane>`). -/

/- L7.4 — `matrix.compute_message`: `v - secret · u` then NTT-inverse.
   Proven (with explicit PRE bounds `hK ≤ 4` + per-lane `≤ 3328`) as
   `libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc` in
   `Matrix/ComputeMessage/FC.lean`. The proof lives downstream
   because the L7 bridge tree imports `FCTargets`.

   POST (canonical-output form, no output `lift`): `∃ spec_out,
   hacspec_ml_kem.matrix.compute_message (lift_poly v) (lift_vec secret_as_ntt)
   (lift_vec u_as_ntt) = .ok spec_out
   ∧ PolyMatches p.1 spec_out` — each impl output lane `x` is the unique
   centered Barrett representative of the spec residue
   (`|x| ≤ 1664 ∧ (x : ZMod q) = <spec lane>`). -/

/-! ## Roll-up

    Theorems written by layer:
      §L0 — 4
      §L1 — 10
      §L2 — 5
      §L3 — 4  (four PortableVector-specialised)
      §L6 — 6  (L6.1, L6.2, L6.4, L6.5, L6.6, L6.7)
      §L2.8 — 1 (NTT-multiply vector base case, scaffold)
      §L6.3 — 1 (NTT-multiply polynomial wrapper, scaffold)
      §L7 — 4

    Total theorems: 35.
    Open sorries: 6 proof-level (= 2 prior def stubs +
    4 L7 theorem bodies). scaffolds (L2.8, L6.3, helpers) all
    closed at HEAD; the 4 L7 Triples remain open.
-/


end libcrux_iot_ml_kem.Matrix.ComputeAsPlusE
