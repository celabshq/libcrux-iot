/-
  # `Matrix/ComputeVectorU/Impl.lean` — L7.2 row-0 fill-loop FC.

  Loop FC for `matrix.compute_vector_u_loop0`: the row-0
  column loop of `matrix.compute_vector_u`. Iterates over `j ∈ [0, K)`; each
  step SAMPLES the matrix entry `matrix_entry1 = sample_matrix_entry seed 0 j`
  (rather than reading a stored slice, as L7.1 does), reads `r_as_ntt[j]`,
  `cache.index_mut j`, runs `accumulating_ntt_multiply_fill_cache` to add
  column j's contribution to the I32[256] accumulator AND populate
  `cache[j]`, then stores the new cache chunk.

  Mirrors the L7.1 sibling `compute_As_plus_e_loop0_fc` +
  `compute_As_plus_e_loop0_step_lemma_fc` + `Stage1FillCacheFC.row0_inv`.
  Structural deltas vs L7.1:

  * `r_as_ntt`, `cache` are `Slice` (not `Array K`); we use
    `Slice.index_usize` / `Slice.index_mut_usize` / `Slice.set`.
  * the matrix entry per column `c` comes from `sample_matrix_entry`, whose
    only stable characterization is the AXIOM `sample_matrix_entry_fc`: `lift_poly (sample seed 0 c) =
    (lift_matrix_from_seed seed K).val[0]!.val[c]!` (ROW-major). Since the
    sampled polys are NOT retained by the impl, the acc invariant cannot use
    `lift_chunk_mont (matrix_entry.coefs[j])` of a stored poly (as L7.1 does
    with the input slice `matrix_A`); instead conjunct (1) characterizes the
    matrix factor by the canonical `Spec.chunk_at` of the axiom-pinned
    `(lift_matrix_from_seed seed K).val[0]!.val[c]!`. The step lemma bridges
    the impl-side mont-domain `accumulating_ntt_multiply_poly_post` (which
    uses `lift_chunk_mont (matrix_entry1.coefs[j])`) to this canonical
    matrix factor via the axiom + the `chunk_at_lift_poly` identity, leaving
    the `r` factor in `lift_chunk_mont` exactly as L6.3c emits it.
  * the loop additionally threads `matrix_entry` (the last-sampled poly).
  * `cache` characterization conjunct (3) mirrors L7.1 verbatim — it depends
    only on `r_as_ntt[c]`, not on the matrix entry.
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
import LibcruxIotMlKem.Sampling
import LibcruxIotMlKem.Serialize
import LibcruxIotMlKem.Matrix.ComputeMessage.Impl
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec
import LibcruxIotMlKem.Matrix.ComputeVectorU.Hacspec

namespace libcrux_iot_ml_kem.Matrix.ComputeVectorU.Impl
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

set_option mvcgen.warning false
set_option linter.unusedVariables false

/-- Local copy of FCTargets' `private triple_exists_ok_fc`. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Local copy of FCTargets' `private triple_of_ok_fc`. -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-- Local re-derivation of FCTargets' `private chunk_at_lift_poly_fc`: `Spec.chunk_at (lift_poly re) k = lift_chunk re.coefs[k]`. -/
private theorem chunk_at_lift_poly_local
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Nat) (hk : k < 16) :
    Spec.chunk_at (lift_poly re) k = lift_chunk (re.coefficients.val[k]!) := by
  unfold Spec.chunk_at lift_poly lift_chunk
  apply Subtype.ext
  have h_chunk_len : (re.coefficients.val[k]!).elements.val.length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
  show (List.range 16).map
        (fun j => ((List.range 256).map
          (fun j' => lift_fe (re.coefficients.val[j' / 16]!).elements.val[j' % 16]!))[16 * k + j]!)
      = (re.coefficients.val[k]!).elements.val.map lift_fe
  apply List.ext_getElem
  · simp
  · intro i hi1 _hi2
    have hi : i < 16 := by
      have : i < ((List.range 16).map _).length := hi1
      simpa using this
    have h_idx_lt : 16 * k + i < 256 := by
      have hk' : k ≤ 15 := by omega
      have : 16 * k ≤ 16 * 15 := Nat.mul_le_mul_left _ hk'
      omega
    have h_list_len : ((List.range 256).map (fun j =>
          lift_fe ((re.coefficients.val[j / 16]!).elements.val[j % 16]!))).length = 256 := by
      simp
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    rw [getElem!_pos _ (16 * k + i) (by rw [h_list_len]; exact h_idx_lt)]
    rw [List.getElem_map, List.getElem_range]
    have h_div : (16 * k + i) / 16 = k := by omega
    have h_mod : (16 * k + i) % 16 = i := by omega
    rw [h_div, h_mod]
    congr 1
    rw [getElem!_pos _ i (by rw [h_chunk_len]; exact hi)]

/-! ## §L7.2-loop0 — row-0 column-loop scaffolding (namespace `Row0FillFC`).

    Mirrors `Stage1FillCacheFC`. The matrix factor in conjunct (1)
    is the canonical `Spec.chunk_at (lm.val[c]!) j` of the axiom-pinned
    row-0 matrix row `lm = (lift_matrix_from_seed seed K).val[0]!`, NOT a
    `lift_chunk_mont` of a stored poly. -/

namespace Row0FillFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 5-conjunct invariant for the row-0 column loop of `compute_vector_u`,
    in the RESOLVED all-mont/existential form.

    `lm0` is the row-0 matrix row `(lift_matrix_from_seed seed K).val[0]!`
    (a `K`-array of `FieldElement 256` polys). Because the impl SAMPLES the
    matrix entry each column and then DISCARDS the sampled poly (only the
    buffer + r-side cache survive), the accumulator characterization cannot
    reference the canonical `Spec.chunk_at (lm0[c]) j` (that is off by a
    factor `2285`: `chunk_at (lift_poly p) j = 2285 · lift_chunk_mont p[j]`).
    Instead we existentially quantify over the ACTUAL sampled polys
    `mp : Array Poly K`, tie them to the canonical matrix row via the axiom
    (`lift_poly (mp[c]) = lm0[c]`), and characterize the accumulator in the
    SAME all-mont form L7.1 uses (`lift_chunk_mont (mp[c].coefs[j])`).

    Tracks:
    (∃ mp) for `c < k`: `lift_poly (mp[c]) = lm0[c]` ∧ per-lane bound 3328.
    (1) accumulator: for each (chunk j, lane ℓ), `mont_reduce_pure (lift_fe_int
        acc[16j+ℓ].val)` equals init plus the all-mont sum of column
        contributions `ntt_multiply_pure_no_acc (lift_chunk_mont mp[c].coefs[j])
        (lift_chunk_mont r[c].coefs[j]) zetas` from columns `[0, k)`.
    (2) accumulator bound: `|acc[n]| ≤ |acc_init[n]| + k · 2^25`.
    (3) cache populated for `c < k`: `accumulating_ntt_multiply_poly_cache_post
        r_arr[c] cache[c]`.
    (4) cache unchanged for `c ∈ [k, K)`: `cache[c] = cache_init[c]`. -/
def row0_inv {K : Std.Usize}
    (lm0 : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (cache_init : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (acc_init : Acc) :
    Std.Usize → Acc →
    Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) →
    Result Prop :=
  fun k acc cache => pure (
    (∃ mp : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
       (∀ c : Nat, c < k.val →
          lift_poly (mp.val[c]!) = lm0.val[c]!
          ∧ (∀ a : Fin 16, ∀ b : Fin 16,
               ((mp.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
       ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
           Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
             = (List.range k.val).foldl
                 (fun s c =>
                   libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                     ((Spec.ntt_multiply_pure_no_acc
                         (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                         (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                         (Spec.zeta_at (64 + 4 * j))
                         (Spec.zeta_at (64 + 4 * j + 1))
                         (Spec.zeta_at (64 + 4 * j + 2))
                         (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                 (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k.val * 2^25)
    ∧ (∀ c : Nat, c < k.val →
        accumulating_ntt_multiply_poly_cache_post
          (r_arr.val[c]!) (cache.val[c]!))
    ∧ (∀ c : Nat, k.val ≤ c → c < K.val →
        cache.val[c]! = cache_init.val[c]!))

/-- Step-post for `loop_range_spec_usize` over `(matrix_entry, cache, acc)`. -/
def row0_step_post {K : Std.Usize}
    (lm0 : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (cache_init : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (acc_init : Acc)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) ×
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
        Acc)
      ((libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
        Acc)) :
    Prop :=
  match r with
  | .cont (iter', _matrix_entry', cache', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (row0_inv lm0 r_arr cache_init acc_init iter'.start acc' cache').holds
        ∧ cache'.length = K.val
  | .done y => (row0_inv lm0 r_arr cache_init acc_init K y.2.2 y.2.1).holds
        ∧ y.2.1.length = K.val

end Row0FillFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Mirrors `L7_1a_irreducible`
-- — heavy POST predicates and the per-column forward dep are
-- made locally irreducible across the step lemma + outer Triple so that
-- elaboration does not whnf-explode through the 4-conjunct `row0_inv` body or
-- the nested accumulator characterization. -- we do NOT mark
-- `Row0FillFC.row0_inv` / `row0_step_post` irreducible — keeping them reducible
-- preserves the `simpa`-based destructure of `h_inv`.
section L7_2a_irreducible
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the row-0 SAMPLED column loop of
    `compute_vector_u`. Given the `row0_inv` invariant at step k and the
    strengthened PRE bounds, executing one body iteration of
    `matrix.compute_vector_u_loop0.body` produces the `row0_step_post`
    (either `.cont` advancing the invariant to k+1 or `.done` capping at K).

    Mirrors `compute_As_plus_e_loop0_step_lemma_fc` with two
    structural deltas:
    1. The matrix entry is SAMPLED via `sample_matrix_entry` (whose only stable
       characterization is the axiom `sample_matrix_entry_fc`), not read from a
       stored slice. We `triple_exists_ok_fc` the axiom at `(i, j) = (0, k)`,
       obtaining `me1` with `lift_poly me1 = lm0[k]` and per-lane bounds, and
       store `me1` in the invariant's existential witness `mp.set k me1`. Hence
       the column-k accumulator term matches the all-mont form VERBATIM (no
       `chunk_at` bridge needed).
    2. `r_as_ntt`, `cache` are `Slice` — use `Slice.index_usize` /
       `Slice.index_mut_usize` / `Slice.set`. The carried `r_arr : Array Poly K`
       is bridged to `r_as_ntt[k]` via `h_r_arr`. -/
private theorem compute_vector_u_loop0_step_lemma_fc
    {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry0 : Row0FillFC.Poly)
    (seed : Slice Std.U8)
    (r_as_ntt cache_init : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Row0FillFC.Acc)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (matrix_entry : Row0FillFC.Poly)
    (acc : Row0FillFC.Acc)
    (cache : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (k : Std.Usize) (h_le : k.val ≤ K.val)
    (h_cache_len : cache.length = K.val)
    (h_inv : (Row0FillFC.row0_inv (lift_matrix_from_seed seed K).val[0]! r_arr cache_init acc_init
                k acc cache).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
      { start := k, «end» := K } matrix_entry cache acc
    ⦃ ⇓ r => ⌜ Row0FillFC.row0_step_post (lift_matrix_from_seed seed K).val[0]! r_arr cache_init
                acc_init k r ⌝ ⦄ := by
  set lm0 : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    (lift_matrix_from_seed seed K).val[0]! with hlm0_def
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 4-conjunct invariant (the first is the ∃-witness pack).
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_acc_bnd, h_inv_cache_done, h_inv_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch.
    have hK_pos : 0 < K.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt
    -- (1) IteratorRange.next reduces to .ok (some k, { start := s_iter, end := K }).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        CoreModels.core.iter.range.IteratorRange.next
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
    -- (2) Sample the matrix entry at (i, j) = (0, k) via the axiom.
    have h_0K : (0#usize : Std.Usize).val < K.val := by
      show (0 : Nat) < K.val; omega
    obtain ⟨me1, h_me_eq, h_me_lift, h_me_bnd⟩ :=
      triple_exists_ok_fc
        (sample_matrix_entry_fc hash_functionsHashInst matrix_entry seed 0#usize k K
          h_seed_len h_0K h_lt)
    -- h_me_lift : lift_poly me1 = (lift_matrix_from_seed seed K).val[0].val[k]
    have h_me_lift' : lift_poly me1 = lm0.val[k.val]! := by
      rw [hlm0_def]; exact h_me_lift
    -- (3) Slice.index_usize r_as_ntt k reduces to .ok r_as_ntt[k.val]!.
    set t_r : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      r_as_ntt.val[k.val]! with ht_r_def
    have h_idx_r : Aeneas.Std.Slice.index_usize r_as_ntt k = .ok t_r :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq r_as_ntt k
        (by show k.val < r_as_ntt.length; rw [h_r_len]; exact h_lt)
    -- (4) Slice.index_mut_usize cache k splits into (cache[k]!, cache.set k).
    set t_cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.val[k.val]! with ht_cache_def
    have h_idx_cache : Aeneas.Std.Slice.index_usize cache k = .ok t_cache :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq cache k
        (by show k.val < cache.length; rw [h_cache_len]; exact h_lt)
    have h_imt_cache : Aeneas.Std.Slice.index_mut_usize cache k
        = .ok (t_cache, cache.set k) := by
      unfold Aeneas.Std.Slice.index_mut_usize
      rw [h_idx_cache]; rfl
    -- (5) Apply L6.3c per-column forward dep at column k.
    have h_me_bnd' : ∀ a : Fin 16, ∀ b : Fin 16,
        ((me1.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_me_bnd a.val a.isLt b.val b.isLt
    have h_t_r_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_r.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_r_bnd k.val h_lt a b
    -- Current acc bound ≤ 2^30: combine inv conjunct (2) with budget PRE.
    have h_acc_cur_bnd : ∀ n : Fin 256, (acc.val[n.val]!).val.natAbs ≤ 2^30 := by
      intro n
      have hb := h_inv_acc_bnd n.val n.isLt
      have hp := h_acc_bnd n
      have hk_le : k.val * 2^25 ≤ K.val * 2^25 := Nat.mul_le_mul_right _ h_le
      omega
    obtain ⟨p_pair, h_p_eq, h_p_bnd_rel, h_p_acc_post, h_p_cache_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_fill_cache_poly_fc me1 t_r t_cache acc
          h_me_bnd' h_t_r_bnd h_acc_cur_bnd)
    set acc1 : Row0FillFC.Acc := p_pair.1 with hacc1_def
    set cache_chunk1 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      p_pair.2 with hcc1_def
    -- (6) cache1 := cache.set k cache_chunk1.
    set cache1 : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :=
      cache.set k cache_chunk1 with hcache1_def
    have h_cache1_at : cache1.val[k.val]! = cache_chunk1 := by
      rw [hcache1_def]
      simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
        Aeneas.Std.Slice.getElem!_Nat_set_eq cache k k.val cache_chunk1
          ⟨rfl, by show k.val < cache.length; rw [h_cache_len]; exact h_lt⟩
    have h_cache1_ne : ∀ j : Nat, j ≠ k.val →
        cache1.val[j]! = cache.val[j]! := by
      intro j hj
      rw [hcache1_def]
      simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
        Aeneas.Std.Slice.getElem!_Nat_set_ne cache k j cache_chunk1 (fun h => hj h.symm)
    -- (7) Body equation.
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          { start := k, «end» := K } matrix_entry cache acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), me1, cache1, acc1)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
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
              let matrix_entry1 ←
                libcrux_iot_ml_kem.matrix.sample_matrix_entry portable_ops_inst
                  hash_functionsHashInst matrix_entry seed 0#usize k
              let pre ← Aeneas.Std.Slice.index_usize r_as_ntt k
              let (pre1, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize cache k
              let (accumulator1, pre2) ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
                  portable_ops_inst matrix_entry1 pre acc pre1
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          matrix_entry1, index_mut_back pre2, accumulator1)))
            : Result _) = _
      rw [h_me_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_r]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_imt_cache]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let (accumulator1, pre2) ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_fill_cache
                  portable_ops_inst me1 t_r acc t_cache
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me1, (cache.set k) pre2, accumulator1)))
            : Result _) = _
      rw [h_p_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rfl
    apply triple_of_ok_fc h_body
    -- (8) Discharge the step_post.
    show Row0FillFC.row0_step_post lm0 r_arr cache_init acc_init k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), me1, cache1, acc1))
    refine ⟨h_lt, rfl, hs_iter_val, ?_,
      by rw [hcache1_def, Aeneas.Std.Slice.set_length]; exact h_cache_len⟩
    -- (9) Re-establish `row0_inv` at s_iter (= k+1).
    show (Row0FillFC.row0_inv lm0 r_arr cache_init acc_init s_iter acc1 cache1).holds
    unfold Row0FillFC.row0_inv
    -- New existential witness: mp.set k me1.
    set mp1 : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
      mp.set k me1 with hmp1_def
    have h_mp_len : mp.length = K.val := Std.Array.length_eq mp
    have h_mp1_at : mp1.val[k.val]! = me1 := by
      rw [hmp1_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq mp k k.val me1
          ⟨rfl, by rw [h_mp_len]; exact h_lt⟩
    have h_mp1_ne : ∀ j : Nat, j ≠ k.val → mp1.val[j]! = mp.val[j]! := by
      intro j hj
      rw [hmp1_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne mp k j me1 (fun h => hj h.symm)
    -- column-k r factor: r_arr[k] = r_as_ntt[k] = t_r.
    have h_r_arr_k : r_arr.val[k.val]! = t_r := by
      rw [ht_r_def]; exact h_r_arr k.val h_lt
    have h_inv_pure :
        (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
           (∀ c : Nat, c < s_iter.val →
              lift_poly (mp'.val[c]!) = lm0.val[c]!
              ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                   ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
           ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
               Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
                 = (List.range s_iter.val).foldl
                     (fun s c =>
                       libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                         ((Spec.ntt_multiply_pure_no_acc
                             (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                             (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                             (Spec.zeta_at (64 + 4 * j))
                             (Spec.zeta_at (64 + 4 * j + 1))
                             (Spec.zeta_at (64 + 4 * j + 2))
                             (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                     (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + s_iter.val * 2^25)
        ∧ (∀ c : Nat, c < s_iter.val →
            accumulating_ntt_multiply_poly_cache_post
              (r_arr.val[c]!) (cache1.val[c]!))
        ∧ (∀ c : Nat, s_iter.val ≤ c → c < K.val →
            cache1.val[c]! = cache_init.val[c]!) := by
      refine ⟨⟨mp1, ?_, ?_⟩, ?_, ?_, ?_⟩
      · -- agreement at columns [0, s_iter).
        intro c hc
        rw [hs_iter_val] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
        · -- c < k: mp1[c] = mp[c], use h_mp_agree.
          have hc_ne : c ≠ k.val := by omega
          rw [h_mp1_ne c hc_ne]
          exact h_mp_agree c hc_lt
        · -- c = k: mp1[k] = me1, use h_me_lift' + h_me_bnd.
          subst hc_eq
          rw [h_mp1_at]
          exact ⟨h_me_lift', fun a b => h_me_bnd a.val a.isLt b.val b.isLt⟩
      · -- (a) Accumulator characterization at s_iter = k+1.
        intro j hj ℓ hℓ
        have h_step_acc :
            Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val))
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (me1.coefficients.val[j]!))
                      (lift_chunk_mont (t_r.coefficients.val[j]!))
                      (Spec.zeta_at (64 + 4 * j))
                      (Spec.zeta_at (64 + 4 * j + 1))
                      (Spec.zeta_at (64 + 4 * j + 2))
                      (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!) := by
          have := h_p_acc_post
          unfold accumulating_ntt_multiply_poly_post at this
          exact this j hj ℓ hℓ
        have h_ih := h_inv_acc j hj ℓ hℓ
        rw [h_step_acc, h_ih]
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        rw [List.range_succ, List.foldl_append]
        -- Generic foldl congruence: over a list whose elements are all < k, the
        -- step functions using `mp` and `mp1` agree (since `mp1[c] = mp[c]` for c < k).
        have h_foldl_congr : ∀ (L : List Nat) (init : hacspec_ml_kem.parameters.FieldElement),
            (∀ c ∈ L, c < k.val) →
            L.foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (mp1.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                init
              = L.foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                init := by
          intro L
          induction L with
          | nil => intro init _; rfl
          | cons hd tl ih =>
            intro init hmem
            have hhd : hd < k.val := hmem hd (List.mem_cons_self)
            have htl : ∀ c ∈ tl, c < k.val := fun c hc => hmem c (List.mem_cons_of_mem hd hc)
            have hhd_ne : hd ≠ k.val := by omega
            simp only [List.foldl_cons]
            rw [h_mp1_ne hd hhd_ne]
            exact ih _ htl
        rw [h_foldl_congr (List.range k.val)
              (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
              (fun c hc => by simpa using hc)]
        -- Now: column-k term me1/t_r matches mp1[k]/r_arr[k].
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((List.range k.val).foldl _ _) _
            = (List.foldl _ ((List.range k.val).foldl _ _) [k.val])
        rw [List.foldl_cons, List.foldl_nil]
        rw [h_mp1_at, h_r_arr_k]
      · -- (b) Bound.
        intro n hn
        have h_p_bnd_n := h_p_bnd_rel ⟨n, hn⟩
        have h_p_bnd_n' : (acc1.val[n]!).val.natAbs ≤ (acc.val[n]!).val.natAbs + 2^25 :=
          h_p_bnd_n
        have h_inv_n := h_inv_acc_bnd n hn
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        have h_arith : (k.val + 1) * 2^25 = k.val * 2^25 + 2^25 := by ring
        rw [h_arith]
        linarith [h_p_bnd_n', h_inv_n]
      · -- (c) Cache populated for [0, s_iter).
        intro c hc
        rw [hs_iter_val] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
        · have hc_ne : c ≠ k.val := by omega
          rw [h_cache1_ne c hc_ne]
          exact h_inv_cache_done c hc_lt
        · subst hc_eq
          rw [h_cache1_at, h_r_arr_k]
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
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          { start := k, «end» := K } matrix_entry cache acc
        = .ok (ControlFlow.done (matrix_entry, cache, acc)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
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
    show Row0FillFC.row0_step_post lm0 r_arr cache_init acc_init k
      (.done (matrix_entry, cache, acc))
    show (Row0FillFC.row0_inv lm0 r_arr cache_init acc_init K acc cache).holds
            ∧ cache.length = K.val
    refine ⟨?_, h_cache_len⟩
    unfold Row0FillFC.row0_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
           (∀ c : Nat, c < K.val →
              lift_poly (mp'.val[c]!) = lm0.val[c]!
              ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                   ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
           ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
               Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
                 = (List.range K.val).foldl
                     (fun s c =>
                       libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                         ((Spec.ntt_multiply_pure_no_acc
                             (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                             (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                             (Spec.zeta_at (64 + 4 * j))
                             (Spec.zeta_at (64 + 4 * j + 1))
                             (Spec.zeta_at (64 + 4 * j + 2))
                             (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                     (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25)
        ∧ (∀ c : Nat, c < K.val →
            accumulating_ntt_multiply_poly_cache_post
              (r_arr.val[c]!) (cache.val[c]!))
        ∧ (∀ c : Nat, K.val ≤ c → c < K.val →
            cache.val[c]! = cache_init.val[c]!) := by
      refine ⟨⟨mp, ?_, ?_⟩, ?_, ?_, ?_⟩
      · intro c hc
        exact h_mp_agree c (by rw [hk_eq]; exact hc)
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
      · intro c hc
        exact h_inv_cache_done c (by rw [hk_eq]; exact hc)
      · intro c hc_ge hc_lt; omega
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

/-- L7.2 Stage 1 — `matrix.compute_vector_u_loop0`: the row-0 SAMPLED column
    loop of `compute_vector_u`. Iterates over `j ∈ [0, K)`; each step SAMPLES
    the matrix entry via `sample_matrix_entry seed 0 j` (axiomatized), reads
    `r_as_ntt[j]`, runs `accumulating_ntt_multiply_fill_cache` to add column j's
    contribution to the I32 accumulator AND populate `cache[j]`.

    POST: the RESOLVED all-mont/existential `row0_inv` holds at k = K — i.e.
    there exists a `K`-array `mp` of sampled polys with `lift_poly mp[c] =
    (lift_matrix_from_seed seed K).val[0].val[c]` (axiom-pinned, ROW-major) such
    that for all (j, ℓ) ∈ [0, 16)², `mont_reduce_pure (lift_fe_int acc[16j+ℓ])`
    equals the K-column all-mont sum of `ntt_multiply_pure_no_acc` outputs over
    `lift_chunk_mont mp[c].coefs[j]` × `lift_chunk_mont r_arr[c].coefs[j]`,
    plus the per-column cache population. This is the form consumed
    by the downstream `compute_vector_u` acc-bridge.

    PRE: `seed.length = 32` (axiom requirement), `r_as_ntt.length = K`, the
    array/slice bridge `h_r_arr`, the standard 16×16 bound (3328) on `r_as_ntt`,
    and the accumulator BUDGET `(acc[n]).val.natAbs + K·2^25 ≤ 2^30`. The matrix
    bound is supplied internally by the sample axiom's POST.

    Mirrors `compute_As_plus_e_loop0_fc`. -/
theorem compute_vector_u_loop0_fc {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry : Row0FillFC.Poly) (seed : Slice Std.U8)
    (r_as_ntt cache : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Row0FillFC.Acc)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop0
      (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      { start := 0#usize, «end» := K } matrix_entry seed r_as_ntt cache accumulator
    ⦃ ⇓ p => ⌜ (Row0FillFC.row0_inv (lift_matrix_from_seed seed K).val[0]! r_arr cache accumulator
                  K p.2.2 p.2.1).holds ⌝ ⦄ := by
  set lm0 : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    (lift_matrix_from_seed seed K).val[0]! with hlm0_def
  -- Combined invariant: `row0_inv` ∧ cache-length-preservation (the latter is
  -- needed to discharge the per-iteration `Slice.index_mut_usize` bound, which
  -- the `row0_inv` does not carry; `Slice.set` preserves length).
  set inv2 : Std.Usize →
      ((libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
        Row0FillFC.Acc) → Result Prop :=
    fun k p => pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator k p.2.2 p.2.1).holds
                      ∧ p.2.1.length = K.val) with hinv2_def
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          iter1 p.1 p.2.1 p.2.2)
      (β := (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
              (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
              Row0FillFC.Acc)
      (matrix_entry, cache, accumulator)
      0#usize K
      inv2
      (by
        have h0 : (0#usize : Std.Usize).val = 0 := rfl
        rw [h0]; exact Nat.zero_le _)
      (by
        -- Base case at k = 0.
        rw [hinv2_def]
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, h_cache_len⟩
        show (Row0FillFC.row0_inv lm0 r_arr cache accumulator 0#usize accumulator cache).holds
        unfold Row0FillFC.row0_inv
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨⟨Std.Array.repeat K matrix_entry, ?_, ?_⟩, ?_, ?_, ?_⟩
        · intro c hc
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0'] at hc
          exact absurd hc (Nat.not_lt_zero c)
        · intro j hj ℓ hℓ
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
  · -- Post entailment: extract the `row0_inv` part of the combined invariant at K.
    rw [PostCond.entails_noThrow]
    intro r hh
    rw [hinv2_def] at hh
    have h_pair : (Row0FillFC.row0_inv lm0 r_arr cache accumulator K r.2.2 r.2.1).holds
                    ∧ r.2.1.length = K.val := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hh
    show (Row0FillFC.row0_inv lm0 r_arr cache accumulator K r.2.2 r.2.1).holds
    exact h_pair.1
  · -- Step entailment.
    intro p k _h_ge h_le hinv
    rw [hinv2_def] at hinv
    have hinv_pair : (Row0FillFC.row0_inv lm0 r_arr cache accumulator k p.2.2 p.2.1).holds
                      ∧ p.2.1.length = K.val := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
    obtain ⟨hinv_row0, hinv_clen⟩ := hinv_pair
    have h_step := compute_vector_u_loop0_step_lemma_fc
      hash_functionsHashInst matrix_entry seed r_as_ntt cache r_arr accumulator
      h_seed_len h_r_len h_r_arr h_r_bnd h_acc_bnd p.1 p.2.2 p.2.1 k h_le hinv_clen
      (by rw [hlm0_def] at hinv_row0; exact hinv_row0)
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', me', cache', acc'⟩ | y
    · have hP : Row0FillFC.row0_step_post lm0 r_arr cache accumulator k
                  (.cont (iter', me', cache', acc')) := by
        rw [hlm0_def]
        simpa [Std.Do.SPred.down_pure] using hh
      obtain ⟨h_klt, h_end, h_start, h_inv', h_clen'⟩ := by
        simpa [Row0FillFC.row0_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      refine ⟨h_klt, h_end, h_start, ?_⟩
      rw [hinv2_def]
      exact (by
        show (pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator iter'.start acc' cache').holds
                      ∧ cache'.length = K.val) : Result Prop).holds
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
          (⟨h_inv', h_clen'⟩ :
            (Row0FillFC.row0_inv lm0 r_arr cache accumulator iter'.start acc' cache').holds
              ∧ cache'.length = K.val))
    · have hP : Row0FillFC.row0_step_post lm0 r_arr cache accumulator k
                  (.done (y.1, y.2.1, y.2.2)) := by
        rw [hlm0_def]
        simpa [Std.Do.SPred.down_pure] using hh
      obtain ⟨h_done_inv, h_done_clen⟩ := by
        simpa [Row0FillFC.row0_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      rw [hinv2_def]
      show (pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator K y.2.2 y.2.1).holds
                    ∧ y.2.1.length = K.val) : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
        (⟨h_done_inv, h_done_clen⟩ :
          (Row0FillFC.row0_inv lm0 r_arr cache accumulator K y.2.2 y.2.1).holds
            ∧ y.2.1.length = K.val)

end L7_2a_irreducible

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow in
set_option maxHeartbeats 1600000 in
/-- **L7.2 Stage 1 cache-length companion.** `compute_vector_u_loop0` preserves
    the cache length. Reuses the private per-iteration step lemma
    `compute_vector_u_loop0_step_lemma_fc` (whose `row0_step_post` carries
    `cache'.length = K`), threading a `row0_inv ∧ length` invariant identical to
    `compute_vector_u_loop0_fc`'s `inv2`. Needed by the L7.2 main glue to
    discharge the `cache.length = K` PRE of the row-i USE-CACHE loop. -/
theorem compute_vector_u_loop0_cache_len_fc {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry : Row0FillFC.Poly) (seed : Slice Std.U8)
    (r_as_ntt cache : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Row0FillFC.Acc)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop0
      (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      { start := 0#usize, «end» := K } matrix_entry seed r_as_ntt cache accumulator
    ⦃ ⇓ p => ⌜ p.2.1.length = K.val ⌝ ⦄ := by
  set lm0 : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    (lift_matrix_from_seed seed K).val[0]! with hlm0_def
  set inv2 : Std.Usize →
      ((libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
        Row0FillFC.Acc) → Result Prop :=
    fun k p => pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator k p.2.2 p.2.1).holds
                      ∧ p.2.1.length = K.val) with hinv2_def
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          iter1 p.1 p.2.1 p.2.2)
      (β := (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
              (Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)) ×
              Row0FillFC.Acc)
      (matrix_entry, cache, accumulator)
      0#usize K
      inv2
      (by have h0 : (0#usize : Std.Usize).val = 0 := rfl; rw [h0]; exact Nat.zero_le _)
      (by
        rw [hinv2_def]
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, h_cache_len⟩
        show (Row0FillFC.row0_inv lm0 r_arr cache accumulator 0#usize accumulator cache).holds
        unfold Row0FillFC.row0_inv
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨⟨Std.Array.repeat K matrix_entry, ?_, ?_⟩, ?_, ?_, ?_⟩
        · intro c hc
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0'] at hc; exact absurd hc (Nat.not_lt_zero c)
        · intro j hj ℓ hℓ
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']
          show Spec.mont_reduce_pure _ = (List.range 0).foldl _ _
          simp [List.range_zero, List.foldl_nil]
        · intro n _; have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']; omega
        · intro c hc
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0'] at hc; exact absurd hc (Nat.not_lt_zero c)
        · intro c _ _; trivial)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r hh
    rw [hinv2_def] at hh
    have h_pair : (Row0FillFC.row0_inv lm0 r_arr cache accumulator K r.2.2 r.2.1).holds
                    ∧ r.2.1.length = K.val := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hh
    exact h_pair.2
  · intro p k _h_ge h_le hinv
    rw [hinv2_def] at hinv
    have hinv_pair : (Row0FillFC.row0_inv lm0 r_arr cache accumulator k p.2.2 p.2.1).holds
                      ∧ p.2.1.length = K.val := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
    obtain ⟨hinv_row0, hinv_clen⟩ := hinv_pair
    have h_step := compute_vector_u_loop0_step_lemma_fc
      hash_functionsHashInst matrix_entry seed r_as_ntt cache r_arr accumulator
      h_seed_len h_r_len h_r_arr h_r_bnd h_acc_bnd p.1 p.2.2 p.2.1 k h_le hinv_clen
      (by rw [hlm0_def] at hinv_row0; exact hinv_row0)
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', me', cache', acc'⟩ | y
    · have hP : Row0FillFC.row0_step_post lm0 r_arr cache accumulator k
                  (.cont (iter', me', cache', acc')) := by
        rw [hlm0_def]; simpa [Std.Do.SPred.down_pure] using hh
      obtain ⟨h_klt, h_end, h_start, h_inv', h_clen'⟩ := by
        simpa [Row0FillFC.row0_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      refine ⟨h_klt, h_end, h_start, ?_⟩
      rw [hinv2_def]
      show (pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator iter'.start acc' cache').holds
                    ∧ cache'.length = K.val) : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
        (⟨h_inv', h_clen'⟩ :
          (Row0FillFC.row0_inv lm0 r_arr cache accumulator iter'.start acc' cache').holds
            ∧ cache'.length = K.val)
    · have hP : Row0FillFC.row0_step_post lm0 r_arr cache accumulator k
                  (.done (y.1, y.2.1, y.2.2)) := by
        rw [hlm0_def]; simpa [Std.Do.SPred.down_pure] using hh
      obtain ⟨h_done_inv, h_done_clen⟩ := by
        simpa [Row0FillFC.row0_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      rw [hinv2_def]
      show (pure ((Row0FillFC.row0_inv lm0 r_arr cache accumulator K y.2.2 y.2.1).holds
                    ∧ y.2.1.length = K.val) : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
        (⟨h_done_inv, h_done_clen⟩ :
          (Row0FillFC.row0_inv lm0 r_arr cache accumulator K y.2.2 y.2.1).holds
            ∧ y.2.1.length = K.val)

/-! ## §L7.2 — row-0 acc-bridge (REUSES L7.4 `compute_message_acc_bridge`). -/

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do

/-- Local abbrev for a single 256-lane field-element poly (matrix-row entry).
    Factored to keep the `256#usize` literal out of statement signatures
    (SKILL §7.7 macro-retrigger trap). -/
private abbrev FEPoly := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize

/-- Helper: the `lift_vec` of the existential witness `mp` collapses to the
    canonical matrix row `lm0`, given the per-column agreement `h_agree`
    (`lift_poly mp[c] = lm0[c]` for `c < K`). Both are `Std.Array … K`; reduce
    to the lists `mp.val.map lift_poly = lm0.val` by `List.ext_getElem`. -/
private theorem lift_vec_mp_eq {K : Std.Usize}
    (mp : Std.Array
            (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (lm0 : Std.Array FEPoly K)
    (h_agree : ∀ c : Nat, c < K.val → lift_poly (mp.val[c]!) = lm0.val[c]!) :
    lift_vec mp = lm0 := by
  apply Subtype.ext
  show mp.val.map lift_poly = lm0.val
  have h_mp_len : mp.val.length = K.val := Std.Array.length_eq mp
  have h_lm0_len : lm0.val.length = K.val := Std.Array.length_eq lm0
  apply List.ext_getElem
  · rw [List.length_map, h_mp_len, h_lm0_len]
  · intro i hi1 _hi2
    have hi : i < K.val := by
      have : i < (mp.val.map lift_poly).length := hi1
      rw [List.length_map, h_mp_len] at this; exact this
    rw [List.getElem_map]
    have h_lhs : lift_poly (mp.val[i]) = lift_poly (mp.val[i]!) := by
      rw [getElem!_pos mp.val i (by rw [h_mp_len]; exact hi)]
    have h_rhs : lm0.val[i] = lm0.val[i]! := by
      rw [getElem!_pos lm0.val i (by rw [h_lm0_len]; exact hi)]
    rw [h_lhs, h_rhs]; exact h_agree i hi

/-- Helper: `lift_vec` of the carried `r_arr` equals the `lift_vec_slice` of
    the impl `Slice` `r_as_ntt`, given the per-column tie `h_r_arr`
    (`r_arr[c] = r_as_ntt[c]` for `c < K`). -/
private theorem lift_vec_r_arr_eq {K : Std.Usize}
    (r_as_ntt : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!) :
    lift_vec r_arr = lift_vec_slice r_as_ntt K := by
  apply Subtype.ext
  show r_arr.val.map lift_poly = (List.range K.val).map (fun i => lift_poly r_as_ntt.val[i]!)
  have h_r_len : r_arr.val.length = K.val := Std.Array.length_eq r_arr
  apply List.ext_getElem
  · rw [List.length_map, h_r_len, List.length_map, List.length_range]
  · intro i hi1 _hi2
    have hi : i < K.val := by
      have : i < (r_arr.val.map lift_poly).length := hi1
      rw [List.length_map, h_r_len] at this; exact this
    rw [List.getElem_map, List.getElem_map, List.getElem_range]
    have h_lhs : lift_poly (r_arr.val[i]) = lift_poly (r_arr.val[i]!) := by
      rw [getElem!_pos r_arr.val i (by rw [h_r_len]; exact hi)]
    rw [h_lhs, h_r_arr i hi]

set_option maxHeartbeats 1000000 in
/-- **L7.2 row-0 acc-bridge.** Reconciles the hacspec `multiply_vectors` of the
    axiom-pinned row-0 matrix row against the loop0 accumulator scaled by
    `R = 2285`. A thin wrapper that REUSES L7.4 `compute_message_acc_bridge`:
    the existential witness `mp` of `row0_inv` supplies the secret-as-ntt array,
    `r_arr` the u-as-ntt array, and `row0_inv`'s conjuncts (1)+(2) are exactly
    `S1LoopFC.loop_inv mp r_arr`'s two conjuncts. The two vector args are
    rewritten via `lift_vec_mp_eq` / `lift_vec_r_arr_eq`. -/
theorem compute_vector_u_row0_acc_bridge {K : Std.Usize}
    (seed : Slice Std.U8)
    (r_as_ntt : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (cache_init cache2 : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (acc_init acc2 : Std.Array Std.I32 256#usize)
    (h_acc_init_zero : ∀ n : Nat, n < 256 → (acc_init.val[n]!).val = 0)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_row0 : (Row0FillFC.row0_inv (lift_matrix_from_seed seed K).val[0]! r_arr cache_init acc_init
                K acc2 cache2).holds) :
    hacspec_ml_kem.matrix.multiply_vectors
        ((lift_matrix_from_seed seed K).val[0]!) (lift_vec_slice r_as_ntt K)
      = .ok (scaleZ 2285 (Impl.mont_strip_pure
               (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)))) := by
  set lm0 : Std.Array FEPoly K := (lift_matrix_from_seed seed K).val[0]! with hlm0_def
  -- Destructure `row0_inv`'s 4 conjuncts; the first is the ∃-witness pack.
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_bnd, _h_cache_done, _h_cache_undone⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_row0
  -- `h_inv_acc` (mont foldl) and `h_inv_bnd` (bound) are exactly
  -- `S1LoopFC.loop_inv mp r_arr acc_init K acc2`'s two conjuncts.
  have h_char : (S1LoopFC.loop_inv mp r_arr acc_init K acc2).holds := by
    show (pure
        ((∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            Spec.mont_reduce_pure (lift_fe_int (acc2.val[16 * j + ℓ]!).val)
              = (List.range K.val).foldl
                  (fun s c =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                      ((Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                          (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                          (Spec.zeta_at (64 + 4 * j))
                          (Spec.zeta_at (64 + 4 * j + 1))
                          (Spec.zeta_at (64 + 4 * j + 2))
                          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                  (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
          ∧ (∀ n : Nat, n < 256 →
              (acc2.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25))
        : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
      (⟨h_inv_acc, h_inv_bnd⟩ : _ ∧ _)
  -- secret-side bounds from the ∃-witness `mp`'s per-lane bound (conjunct 1.2).
  have h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((mp.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; exact (h_mp_agree k.val k.isLt).2 i j
  -- u-side bounds from `h_r_bnd` rewritten through `h_r_arr`.
  have h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((r_arr.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; rw [h_r_arr k.val k.isLt]; exact h_r_bnd k.val k.isLt i j
  -- Apply the L7.4 bridge on `(mp, r_arr)`.
  have h_bridge :=
    compute_message_acc_bridge mp r_arr acc_init acc2 h_acc_init_zero h_secret_bnd h_u_bnd h_char
  -- Rewrite the two vector args: `lift_vec mp = lm0`, `lift_vec r_arr = lift_vec_slice r_as_ntt K`.
  have h_mp_vec : lift_vec mp = lm0 :=
    lift_vec_mp_eq mp lm0 (fun c hc => (h_mp_agree c hc).1)
  have h_r_vec : lift_vec r_arr = lift_vec_slice r_as_ntt K :=
    lift_vec_r_arr_eq r_as_ntt r_arr h_r_arr
  rw [h_mp_vec, h_r_vec] at h_bridge
  rw [hlm0_def]
  exact h_bridge

/-! ## §L7.2-loop1-loop0 — row-i (i ≥ 1) SAMPLED column-loop scaffolding
    (namespace `RowIFillFC`).

    The USE-CACHE variant of the row-0 column loop. Combines:
    * the EXISTENTIAL/sample machinery of `Row0FillFC` (the matrix entry is
      SAMPLED via `sample_matrix_entry seed i j`, axiomatized; the discarded
      sampled polys are threaded through an existential witness `mp`), and
    * the USE-CACHE structure of `Stage2UseCacheFC` (the cache is INPUT only — read
      via `Slice.index_usize`, never mutated; the per-column forward dep is
      `accumulating_ntt_multiply_use_cache_poly_fc`, which requires the
      cache-post PRE `accumulating_ntt_multiply_poly_cache_post (r[c]) (cache[c])`).

    Mirrors `Row0FillFC` minus the two cache-state conjuncts (3)/(4), with the
    matrix row pinned to `(lift_matrix_from_seed seed K).val[i.val]!` (ROW i,
    not row 0). The loop carries the 2-tuple `(matrix_entry, acc)`. -/

namespace RowIFillFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc
abbrev Poly := UseCacheFC.Poly

/-- 2-conjunct invariant for the row-i (i ≥ 1) SAMPLED column loop of
    `compute_vector_u`, in the RESOLVED all-mont/existential form.

    `lm_i` is the row-i matrix row `(lift_matrix_from_seed seed K).val[i.val]!`.
    As in `Row0FillFC.row0_inv`, because the impl SAMPLES and DISCARDS the matrix
    entry each column, we existentially quantify over the ACTUAL sampled polys
    `mp : Array Poly K`, tie them to the canonical matrix row via the axiom
    (`lift_poly (mp[c]) = lm_i[c]`), and characterize the accumulator in the
    all-mont form. NO cache conjuncts (cache is read-only here). -/
def row_i_inv {K : Std.Usize}
    (lm_i : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∃ mp : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
       (∀ c : Nat, c < k.val →
          lift_poly (mp.val[c]!) = lm_i.val[c]!
          ∧ (∀ a : Fin 16, ∀ b : Fin 16,
               ((mp.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
       ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
           Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
             = (List.range k.val).foldl
                 (fun s c =>
                   libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                     ((Spec.ntt_multiply_pure_no_acc
                         (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                         (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                         (Spec.zeta_at (64 + 4 * j))
                         (Spec.zeta_at (64 + 4 * j + 1))
                         (Spec.zeta_at (64 + 4 * j + 2))
                         (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                 (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k.val * 2^25))

/-- Step-post for `loop_range_spec_usize` over `(matrix_entry, acc)`
    (2-tuple, no cache). -/
def row_i_step_post {K : Std.Usize}
    (lm_i : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K)
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) ×
        (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        Acc)
      ((libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        Acc)) :
    Prop :=
  match r with
  | .cont (iter', _matrix_entry', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (row_i_inv lm_i r_arr acc_init iter'.start acc').holds
  | .done y => (row_i_inv lm_i r_arr acc_init K y.2).holds

end RowIFillFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Mirrors `L7_2a_irreducible`
-- and `L7_1b_irreducible`. we
-- do NOT mark `RowIFillFC.row_i_inv` / `row_i_step_post` irreducible.
section L7_2b_irreducible
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] accumulating_ntt_multiply_poly_cache_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the row-i (i ≥ 1) SAMPLED column loop of
    `compute_vector_u`. Combines `compute_vector_u_loop0_step_lemma_fc`'s
    existential/sample/foldl machinery with `compute_As_plus_e_loop1_loop0_step_lemma_fc`'s
    use-cache structure:
    1. The matrix entry is SAMPLED at `(i, k)` via `sample_matrix_entry_fc`
       (NOT `(0, k)`), pinned to `lm_i[k] = (lift_matrix_from_seed seed K).val[i.val].val[k]`.
    2. NO cache mutation — `cache` is read via `Slice.index_usize` only.
    3. The per-column forward dep is `accumulating_ntt_multiply_use_cache_poly_fc`,
       which needs the cache-post PRE at column k: `accumulating_ntt_multiply_poly_cache_post
       (r_as_ntt[k]!) (cache[k]!)` (passed through `h_cache`). -/
private theorem compute_vector_u_loop1_loop0_step_lemma_fc
    {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (seed : Slice Std.U8)
    (r_as_ntt cache : Slice
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : RowIFillFC.Acc)
    (i : Std.Usize) (h_i : i.val < K.val)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!))
    (matrix_entry : RowIFillFC.Poly)
    (acc : RowIFillFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ K.val)
    (h_cache_len : cache.length = K.val)
    (h_inv : (RowIFillFC.row_i_inv (lift_matrix_from_seed seed K).val[i.val]! r_arr acc_init
                k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
      (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
      cache i { start := k, «end» := K } matrix_entry acc
    ⦃ ⇓ r => ⌜ RowIFillFC.row_i_step_post (lift_matrix_from_seed seed K).val[i.val]! r_arr
                acc_init k r ⌝ ⦄ := by
  set lm_i : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    (lift_matrix_from_seed seed K).val[i.val]! with hlm_i_def
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 2-conjunct invariant (the first is the ∃-witness pack).
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch.
    have hK_pos : 0 < K.val := Nat.lt_of_le_of_lt (Nat.zero_le _) h_lt
    -- (1) IteratorRange.next reduces to .ok (some k, { start := s_iter, end := K }).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        CoreModels.core.iter.range.IteratorRange.next
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
    -- (2) Sample the matrix entry at (i, k) via the axiom.
    obtain ⟨me1, h_me_eq, h_me_lift, h_me_bnd⟩ :=
      triple_exists_ok_fc
        (sample_matrix_entry_fc hash_functionsHashInst matrix_entry seed i k K
          h_seed_len h_i h_lt)
    -- h_me_lift : lift_poly me1 = (lift_matrix_from_seed seed K).val[i].val[k]
    have h_me_lift' : lift_poly me1 = lm_i.val[k.val]! := by
      rw [hlm_i_def]; exact h_me_lift
    -- (3) Slice.index_usize r_as_ntt k reduces to .ok r_as_ntt[k.val]!.
    set t_r : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      r_as_ntt.val[k.val]! with ht_r_def
    have h_idx_r : Aeneas.Std.Slice.index_usize r_as_ntt k = .ok t_r :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq r_as_ntt k
        (by show k.val < r_as_ntt.length; rw [h_r_len]; exact h_lt)
    -- (4) Slice.index_usize cache k reduces to .ok cache[k.val]! (READ, not mut).
    set t_cache : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      cache.val[k.val]! with ht_cache_def
    have h_idx_cache : Aeneas.Std.Slice.index_usize cache k = .ok t_cache :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq cache k
        (by show k.val < cache.length; rw [h_cache_len]; exact h_lt)
    -- (5) Apply L6.3c per-column use-cache forward dep at column k.
    have h_me_bnd' : ∀ a : Fin 16, ∀ b : Fin 16,
        ((me1.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_me_bnd a.val a.isLt b.val b.isLt
    have h_t_r_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_r.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_r_bnd k.val h_lt a b
    -- Cache-post hypothesis at column k.
    have h_cache_at_k : accumulating_ntt_multiply_poly_cache_post t_r t_cache :=
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
        (accumulating_ntt_multiply_use_cache_poly_fc me1 t_r t_cache acc
          h_me_bnd' h_t_r_bnd h_acc_cur_bnd h_cache_at_k)
    -- (6) Body equation.
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          cache i { start := k, «end» := K } matrix_entry acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), me1, acc1)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
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
              let matrix_entry1 ←
                libcrux_iot_ml_kem.matrix.sample_matrix_entry portable_ops_inst
                  hash_functionsHashInst matrix_entry seed i k
              let pre ← Aeneas.Std.Slice.index_usize r_as_ntt k
              let pre1 ← Aeneas.Std.Slice.index_usize cache k
              let accumulator1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply_use_cache
                  portable_ops_inst matrix_entry1 pre acc pre1
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          matrix_entry1, accumulator1)))
            : Result _) = _
      rw [h_me_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_r]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_cache]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_acc1_eq]
      rfl
    apply triple_of_ok_fc h_body
    -- (7) Discharge the step_post.
    show RowIFillFC.row_i_step_post lm_i r_arr acc_init k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), me1, acc1))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    -- (8) Re-establish `row_i_inv` at s_iter (= k+1).
    show (RowIFillFC.row_i_inv lm_i r_arr acc_init s_iter acc1).holds
    unfold RowIFillFC.row_i_inv
    -- New existential witness: mp.set k me1.
    set mp1 : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K :=
      mp.set k me1 with hmp1_def
    have h_mp_len : mp.length = K.val := Std.Array.length_eq mp
    have h_mp1_at : mp1.val[k.val]! = me1 := by
      rw [hmp1_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_eq mp k k.val me1
          ⟨rfl, by rw [h_mp_len]; exact h_lt⟩
    have h_mp1_ne : ∀ j : Nat, j ≠ k.val → mp1.val[j]! = mp.val[j]! := by
      intro j hj
      rw [hmp1_def]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using
        Aeneas.Std.Array.getElem!_Nat_set_ne mp k j me1 (fun h => hj h.symm)
    -- column-k r factor: r_arr[k] = r_as_ntt[k] = t_r.
    have h_r_arr_k : r_arr.val[k.val]! = t_r := by
      rw [ht_r_def]; exact h_r_arr k.val h_lt
    have h_inv_pure :
        (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
           (∀ c : Nat, c < s_iter.val →
              lift_poly (mp'.val[c]!) = lm_i.val[c]!
              ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                   ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
           ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
               Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
                 = (List.range s_iter.val).foldl
                     (fun s c =>
                       libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                         ((Spec.ntt_multiply_pure_no_acc
                             (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                             (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                             (Spec.zeta_at (64 + 4 * j))
                             (Spec.zeta_at (64 + 4 * j + 1))
                             (Spec.zeta_at (64 + 4 * j + 2))
                             (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                     (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
        ∧ (∀ n : Nat, n < 256 →
            (acc1.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + s_iter.val * 2^25) := by
      refine ⟨⟨mp1, ?_, ?_⟩, ?_⟩
      · -- agreement at columns [0, s_iter).
        intro c hc
        rw [hs_iter_val] at hc
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with hc_lt | hc_eq
        · -- c < k: mp1[c] = mp[c], use h_mp_agree.
          have hc_ne : c ≠ k.val := by omega
          rw [h_mp1_ne c hc_ne]
          exact h_mp_agree c hc_lt
        · -- c = k: mp1[k] = me1, use h_me_lift' + h_me_bnd.
          subst hc_eq
          rw [h_mp1_at]
          exact ⟨h_me_lift', fun a b => h_me_bnd a.val a.isLt b.val b.isLt⟩
      · -- (a) Accumulator characterization at s_iter = k+1.
        intro j hj ℓ hℓ
        have h_step_acc :
            Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
              = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val))
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (me1.coefficients.val[j]!))
                      (lift_chunk_mont (t_r.coefficients.val[j]!))
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
        -- Generic foldl congruence: over a list whose elements are all < k, the
        -- step functions using `mp` and `mp1` agree (since `mp1[c] = mp[c]` for c < k).
        have h_foldl_congr : ∀ (L : List Nat) (init : hacspec_ml_kem.parameters.FieldElement),
            (∀ c ∈ L, c < k.val) →
            L.foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (mp1.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                init
              = L.foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                        (Spec.zeta_at (64 + 4 * j))
                        (Spec.zeta_at (64 + 4 * j + 1))
                        (Spec.zeta_at (64 + 4 * j + 2))
                        (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                init := by
          intro L
          induction L with
          | nil => intro init _; rfl
          | cons hd tl ih =>
            intro init hmem
            have hhd : hd < k.val := hmem hd (List.mem_cons_self)
            have htl : ∀ c ∈ tl, c < k.val := fun c hc => hmem c (List.mem_cons_of_mem hd hc)
            have hhd_ne : hd ≠ k.val := by omega
            simp only [List.foldl_cons]
            rw [h_mp1_ne hd hhd_ne]
            exact ih _ htl
        rw [h_foldl_congr (List.range k.val)
              (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))
              (fun c hc => by simpa using hc)]
        -- Now: column-k term me1/t_r matches mp1[k]/r_arr[k].
        show libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((List.range k.val).foldl _ _) _
            = (List.foldl _ ((List.range k.val).foldl _ _) [k.val])
        rw [List.foldl_cons, List.foldl_nil]
        rw [h_mp1_at, h_r_arr_k]
      · -- (b) Bound.
        intro n hn
        have h_acc1_bnd_n := h_acc1_bnd_rel ⟨n, hn⟩
        have h_acc1_bnd_n' : (acc1.val[n]!).val.natAbs ≤ (acc.val[n]!).val.natAbs + 2^25 :=
          h_acc1_bnd_n
        have h_inv_n := h_inv_acc_bnd n hn
        have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
        rw [hs_iter_eq]
        have h_arith : (k.val + 1) * 2^25 = k.val * 2^25 + 2^25 := by ring
        rw [h_arith]
        linarith [h_acc1_bnd_n, h_inv_n]
    show (pure _ : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch: k ≥ K, done.
    have hk_ge : k.val ≥ K.val := Nat.not_lt.mp h_lt
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
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          cache i { start := k, «end» := K } matrix_entry acc
        = .ok (ControlFlow.done (matrix_entry, acc)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
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
    show RowIFillFC.row_i_step_post lm_i r_arr acc_init k
      (.done (matrix_entry, acc))
    show (RowIFillFC.row_i_inv lm_i r_arr acc_init K acc).holds
    unfold RowIFillFC.row_i_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∃ mp' : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K,
           (∀ c : Nat, c < K.val →
              lift_poly (mp'.val[c]!) = lm_i.val[c]!
              ∧ (∀ a : Fin 16, ∀ b : Fin 16,
                   ((mp'.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328))
           ∧ (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
               Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
                 = (List.range K.val).foldl
                     (fun s c =>
                       libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                         ((Spec.ntt_multiply_pure_no_acc
                             (lift_chunk_mont (mp'.val[c]!.coefficients.val[j]!))
                             (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                             (Spec.zeta_at (64 + 4 * j))
                             (Spec.zeta_at (64 + 4 * j + 1))
                             (Spec.zeta_at (64 + 4 * j + 2))
                             (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                     (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val))))
        ∧ (∀ n : Nat, n < 256 →
            (acc.val[n]!).val.natAbs
              ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25) := by
      refine ⟨⟨mp, ?_, ?_⟩, ?_⟩
      · intro c hc
        exact h_mp_agree c (by rw [hk_eq]; exact hc)
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

/-- L7.2 Stage 2 — `matrix.compute_vector_u_loop1_loop0`: the row-i (i ≥ 1)
    SAMPLED column loop of `compute_vector_u` (USE-CACHE variant). Iterates over
    `j ∈ [0, K)`; each step SAMPLES the matrix entry via `sample_matrix_entry
    seed i j` (axiomatized), reads `r_as_ntt[j]` and `cache[j]` (read-only), and
    runs `accumulating_ntt_multiply_use_cache` to add column j's contribution to
    the I32 accumulator.

    POST: the RESOLVED all-mont/existential `row_i_inv` holds at k = K — i.e.
    there exists a `K`-array `mp` of sampled polys with `lift_poly mp[c] =
    (lift_matrix_from_seed seed K).val[i].val[c]` (axiom-pinned, ROW-major) such
    that for all (j, ℓ) ∈ [0, 16)², `mont_reduce_pure (lift_fe_int acc[16j+ℓ])`
    equals the K-column all-mont sum of `ntt_multiply_pure_no_acc` outputs.

    PRE: `seed.length = 32`, `r_as_ntt.length = K`, `cache.length = K`, the
    array/slice bridge `h_r_arr`, the 16×16 bound (3328) on `r_as_ntt`, the
    accumulator BUDGET, and the cache-post hypothesis `h_cache` (the cache was
    populated by Stage 1's row-0 column loop and is consumed read-only).

    Mirrors `compute_As_plus_e_loop1_loop0_fc` + the local
    `compute_vector_u_loop0_fc`. -/
theorem compute_vector_u_loop1_loop0_fc {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (matrix_entry : RowIFillFC.Poly) (seed : Slice Std.U8)
    (r_as_ntt cache : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                              libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : RowIFillFC.Acc)
    (i : Std.Usize) (h_i : i.val < K.val)
    (h_seed_len : seed.length = 32)
    (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256, (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0
      (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      { start := 0#usize, «end» := K } matrix_entry seed r_as_ntt cache accumulator i
    ⦃ ⇓ p => ⌜ (RowIFillFC.row_i_inv (lift_matrix_from_seed seed K).val[i.val]! r_arr accumulator
                  K p.2).holds ⌝ ⦄ := by
  set lm_i : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K :=
    (lift_matrix_from_seed seed K).val[i.val]! with hlm_i_def
  -- Combined invariant: `row_i_inv` ∧ cache-length-preservation (needed to
  -- discharge the per-iteration `Slice.index_usize cache` bound; the cache is
  -- never mutated so its length is constant, but the `row_i_inv`
  -- does not carry it).
  set inv2 : Std.Usize →
      ((libcrux_iot_ml_kem.polynomial.PolynomialRingElement
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
        RowIFillFC.Acc) → Result Prop :=
    fun k p => pure ((RowIFillFC.row_i_inv lm_i r_arr accumulator k p.2).holds) with hinv2_def
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0.body
          (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst seed r_as_ntt
          cache i iter1 p.1 p.2)
      (β := (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) ×
              RowIFillFC.Acc)
      (matrix_entry, accumulator)
      0#usize K
      inv2
      (by
        have h0 : (0#usize : Std.Usize).val = 0 := rfl
        rw [h0]; exact Nat.zero_le _)
      (by
        -- Base case at k = 0.
        rw [hinv2_def]
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        show (RowIFillFC.row_i_inv lm_i r_arr accumulator 0#usize accumulator).holds
        unfold RowIFillFC.row_i_inv
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨⟨Std.Array.repeat K matrix_entry, ?_, ?_⟩, ?_⟩
        · intro c hc
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0'] at hc
          exact absurd hc (Nat.not_lt_zero c)
        · intro j hj ℓ hℓ
          have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']
          show Spec.mont_reduce_pure _ = (List.range 0).foldl _ _
          simp [List.range_zero, List.foldl_nil]
        · intro n _; have h0' : (0#usize : Std.Usize).val = 0 := rfl
          rw [h0']; omega)
      ?_)
  · -- Post entailment: extract the `row_i_inv` at K.
    rw [PostCond.entails_noThrow]
    intro r hh
    rw [hinv2_def] at hh
    have h_inv_holds : (RowIFillFC.row_i_inv lm_i r_arr accumulator K r.2).holds := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hh
    show (RowIFillFC.row_i_inv lm_i r_arr accumulator K r.2).holds
    exact h_inv_holds
  · -- Step entailment.
    intro p k _h_ge h_le hinv
    rw [hinv2_def] at hinv
    have hinv_row : (RowIFillFC.row_i_inv lm_i r_arr accumulator k p.2).holds := by
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
    have h_step := compute_vector_u_loop1_loop0_step_lemma_fc
      hash_functionsHashInst seed r_as_ntt cache r_arr accumulator i h_i
      h_seed_len h_r_len h_r_arr h_r_bnd h_acc_bnd h_cache p.1 p.2 k h_le h_cache_len
      (by rw [hlm_i_def] at hinv_row; exact hinv_row)
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', me', acc'⟩ | y
    · have hP : RowIFillFC.row_i_step_post lm_i r_arr accumulator k
                  (.cont (iter', me', acc')) := by
        rw [hlm_i_def]
        simpa [Std.Do.SPred.down_pure] using hh
      obtain ⟨h_klt, h_end, h_start, h_inv'⟩ := by
        simpa [RowIFillFC.row_i_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      refine ⟨h_klt, h_end, h_start, ?_⟩
      rw [hinv2_def]
      show (pure ((RowIFillFC.row_i_inv lm_i r_arr accumulator iter'.start acc').holds)
              : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv'
    · have hP : RowIFillFC.row_i_step_post lm_i r_arr accumulator k
                  (.done (y.1, y.2)) := by
        rw [hlm_i_def]
        simpa [Std.Do.SPred.down_pure] using hh
      have h_done_inv : (RowIFillFC.row_i_inv lm_i r_arr accumulator K y.2).holds := by
        simpa [RowIFillFC.row_i_step_post] using hP
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      rw [hinv2_def]
      show (pure ((RowIFillFC.row_i_inv lm_i r_arr accumulator K y.2).holds)
              : Result Prop).holds
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_done_inv

end L7_2b_irreducible

/-! ## §L7.2 — finalize glue (F1/F2) + row-i acc-bridge.

    The two scalar-glue lemmas (F1/F2) mirror the L7.4 FC chain
    (`FC/ComputeMessage.lean` lines 230-249) restricted to the C+B+compose
    head (F1) and the D'' tail (F2). The row-i acc-bridge mirrors
    `compute_vector_u_row0_acc_bridge` for the cache-free `RowIFillFC.row_i_inv`
    (2 conjuncts) and matrix row `i`. -/

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do

/-- `scaleZ c p` lanes are `feOfZMod _`, hence canonical (local copy of the
    `private canonArr_scaleZ'` in ComputeMessage/Hacspec; mirrors the
    `FC/ComputeMessage.lean` private helper). -/
private theorem scaleZ_canon (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical ((scaleZ c p).val[j]!) := by
  unfold scaleZ
  show libcrux_iot_ml_kem.Spec.Pure.Canonical
    (((List.range 256).map (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))))[j]!)
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  rw [List.getElem_map, List.getElem_range]
  unfold libcrux_iot_ml_kem.Spec.Pure.Canonical feOfZMod
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (BitVec.ofNat 16 ((c * zmodOfFE (p.val[j]!)).val)).toNat < 3329
  set z := c * zmodOfFE (p.val[j]!)
  have h_lt16 : z.val < 2 ^ 16 := by have := ZMod.val_lt z; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt16]
  exact ZMod.val_lt _

/-- `lift_poly x` lanes are `lift_fe _ = feOfZMod _`, hence canonical (local
    copy mirroring the `FC/ComputeMessage.lean` private helper). -/
private theorem lift_poly_canon
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (hj : j < 256) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical ((lift_poly re).val[j]!) := by
  unfold lift_poly
  show libcrux_iot_ml_kem.Spec.Pure.Canonical
    (((List.range 256).map (fun i =>
        lift_fe (re.coefficients.val[i / 16]!).elements.val[i % 16]!))[j]!)
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  rw [List.getElem_map, List.getElem_range]
  unfold lift_fe libcrux_iot_ml_kem.Spec.Pure.Canonical feOfZMod
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]
  show (⟨BitVec.ofNat 16 ((i16_to_spec_fe_plain
          (re.coefficients.val[j / 16]!).elements.val[j % 16]!).val)⟩ : Std.U16).val < 3329
  show (BitVec.ofNat 16 ((i16_to_spec_fe_plain
          (re.coefficients.val[j / 16]!).elements.val[j % 16]!).val)).toNat < 3329
  set z := i16_to_spec_fe_plain (re.coefficients.val[j / 16]!).elements.val[j % 16]!
  have h_lt16 : z.val < 2 ^ 16 := by
    have := ZMod.val_lt z; omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt16]
  exact ZMod.val_lt _

/-- **L7.2 F1 (ntt_inverse glue).** Mirrors the L7.4 C+B+compose head
    (`FC/ComputeMessage.lean` 230-243) minus the subtract tail:
    `ntt_inverse (scaleZ 2285 result1) = .ok (scaleZ 512 result2)` given the
    invert-pure tie `invert_pure result1 = result2`. -/
theorem compute_vector_u_ntt_inverse_eq
    (result1 result2 : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_inv : Spec.invert_ntt_montgomery_pure (lift_poly result1) = lift_poly result2) :
    hacspec_ml_kem.invert_ntt.ntt_inverse (scaleZ 2285 (lift_poly result1))
      = .ok (scaleZ 512 (lift_poly result2)) := by
  -- C: ntt_inverse (scaleZ 2285 x) = .ok (scaleZ 3303 (invert_pure (scaleZ 2285 x))).
  rw [ntt_inverse_eq_scaleZ_invert_pure (scaleZ 2285 (lift_poly result1))
        (fun j hj => scaleZ_canon 2285 (lift_poly result1) j hj)]
  -- B: invert_pure (scaleZ 2285 x) = scaleZ 2285 (invert_pure x).
  rw [invert_ntt_montgomery_pure_scaleZ 2285 (lift_poly result1)
        (fun j hj => lift_poly_canon result1 j hj)]
  -- compose: scaleZ 3303 (scaleZ 2285 y) = scaleZ 512 y.
  rw [scaleZ_compose 3303 2285 (Spec.invert_ntt_montgomery_pure (lift_poly result1)),
      glue_3303_2285]
  -- tie: invert_pure result1 = result2.
  rw [h_inv]

/-- **L7.2 F2 (add glue).** Trivial wrapper of `add_polynomials_scaleZ_eq`
    (D''): `add_polynomials (scaleZ 512 result2) error_i = .ok result_i` given
    the add-error-reduce tie. -/
theorem compute_vector_u_add_eq
    (result2 error_i result_i : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_tail : Spec.add_error_reduce_pure (lift_poly result2) (lift_poly error_i)
                = lift_poly result_i) :
    hacspec_ml_kem.matrix.add_polynomials (scaleZ 512 (lift_poly result2)) (lift_poly error_i)
      = .ok (lift_poly result_i) := by
  rw [add_polynomials_scaleZ_eq (lift_poly result2) (lift_poly error_i)
        (fun j hj => lift_poly_canon result2 j hj), h_tail]

set_option maxHeartbeats 1000000 in
/-- **L7.2 row-i acc-bridge.** Mirror of `compute_vector_u_row0_acc_bridge` for
    the cache-free `RowIFillFC.row_i_inv` (2 conjuncts) and matrix row `i`. The
    `∃ mp` witness of `row_i_inv` supplies the secret-as-ntt array; `r_arr` the
    u-as-ntt array; the two `row_i_inv` conjuncts are exactly
    `S1LoopFC.loop_inv mp r_arr`'s two conjuncts. The two vector args are
    rewritten via `lift_vec_mp_eq` / `lift_vec_r_arr_eq`. -/
theorem compute_vector_u_rowi_acc_bridge {K : Std.Usize}
    (seed : Slice Std.U8)
    (r_as_ntt : Slice (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))
    (r_arr : Std.Array (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init acc2 : Std.Array Std.I32 256#usize)
    (i : Std.Usize)
    (h_acc_init_zero : ∀ n : Nat, n < 256 → (acc_init.val[n]!).val = 0)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_rowi : (RowIFillFC.row_i_inv (lift_matrix_from_seed seed K).val[i.val]! r_arr acc_init
                K acc2).holds) :
    hacspec_ml_kem.matrix.multiply_vectors
        ((lift_matrix_from_seed seed K).val[i.val]!) (lift_vec_slice r_as_ntt K)
      = .ok (scaleZ 2285 (Impl.mont_strip_pure
               (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)))) := by
  set lm_i : Std.Array FEPoly K := (lift_matrix_from_seed seed K).val[i.val]! with hlm_i_def
  -- Destructure `row_i_inv`'s 2 conjuncts; the first is the ∃-witness pack.
  obtain ⟨⟨mp, h_mp_agree, h_inv_acc⟩, h_inv_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_rowi
  -- `h_inv_acc` (mont foldl) and `h_inv_bnd` (bound) are exactly
  -- `S1LoopFC.loop_inv mp r_arr acc_init K acc2`'s two conjuncts.
  have h_char : (S1LoopFC.loop_inv mp r_arr acc_init K acc2).holds := by
    show (pure
        ((∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
            Spec.mont_reduce_pure (lift_fe_int (acc2.val[16 * j + ℓ]!).val)
              = (List.range K.val).foldl
                  (fun s c =>
                    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                      ((Spec.ntt_multiply_pure_no_acc
                          (lift_chunk_mont (mp.val[c]!.coefficients.val[j]!))
                          (lift_chunk_mont (r_arr.val[c]!.coefficients.val[j]!))
                          (Spec.zeta_at (64 + 4 * j))
                          (Spec.zeta_at (64 + 4 * j + 1))
                          (Spec.zeta_at (64 + 4 * j + 2))
                          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
                  (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
          ∧ (∀ n : Nat, n < 256 →
              (acc2.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + K.val * 2^25))
        : Result Prop).holds
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using
      (⟨h_inv_acc, h_inv_bnd⟩ : _ ∧ _)
  -- secret-side bounds from the ∃-witness `mp`'s per-lane bound (conjunct 1.2).
  have h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((mp.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; exact (h_mp_agree k.val k.isLt).2 i j
  -- u-side bounds from `h_r_bnd` rewritten through `h_r_arr`.
  have h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
      ((r_arr.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328 := by
    intro k i j; rw [h_r_arr k.val k.isLt]; exact h_r_bnd k.val k.isLt i j
  -- Apply the L7.4 bridge on `(mp, r_arr)`.
  have h_bridge :=
    compute_message_acc_bridge mp r_arr acc_init acc2 h_acc_init_zero h_secret_bnd h_u_bnd h_char
  -- Rewrite the two vector args: `lift_vec mp = lm_i`, `lift_vec r_arr = lift_vec_slice r_as_ntt K`.
  have h_mp_vec : lift_vec mp = lm_i :=
    lift_vec_mp_eq mp lm_i (fun c hc => (h_mp_agree c hc).1)
  have h_r_vec : lift_vec r_arr = lift_vec_slice r_as_ntt K :=
    lift_vec_r_arr_eq r_as_ntt r_arr h_r_arr
  rw [h_mp_vec, h_r_vec] at h_bridge
  rw [hlm_i_def]
  exact h_bridge

/-! ## §L7.2 Stage 3 — outer rows loop FC (`compute_vector_u_loop1`).

    The OUTER rows loop `[start, K)` of `compute_vector_u`. Each row `i1` does:
    re-zero the accumulator (`Array.repeat 256 i_zero`, `i_zero = classify 0`),
    run the USE-CACHE inner column loop (`compute_vector_u_loop1_loop0`), then
    the per-row finalize `reducing_from_i32_array → invert_ntt_montgomery →
    add_error_reduce`, storing `result[i1] := result_poly`.

    Mirrors `compute_As_plus_e_loop1_fc` structurally — the
    rows loop `loop_range_spec_usize` wrapper + the re-zero-per-row pattern +
    the (done-rows ∧ unchanged-rows) `rows_inv`. L7.1's per-row finalize is
    reducing→add (no invert); ours is reducing→INVERT→add (the L7.4 glue WALK,
    `FC/ComputeMessage.lean` 168-251, adapted to add-error instead of subtract).

    The per-row hacspec value is captured by `AllRowsFillFC.row_spec` (a `Result`
    do-block: multiply_vectors → ntt_inverse → add_polynomials), and the
    invariant says `row_spec lm r_as_ntt error_1 r = .ok (lift_poly result[r])`
    for completed rows `r ∈ [start, k)`, with all other rows unchanged. -/

namespace AllRowsFillFC

open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Sampling libcrux_iot_ml_kem.Serialize libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-- The 256-lane I32 accumulator carried by the rows loop. -/
abbrev Acc := Std.Array Std.I32 256#usize

/-- The portable-vector poly type (matrix row entry / scratch). -/
abbrev Poly :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- A single 256-lane field-element poly. -/
abbrev FEPoly := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize

/-- The raw scratch vector carried by the rows loop (NOT a poly wrapper). -/
abbrev Scratch := libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- The per-row hacspec value (as a `Result`): the matrix-row `r` times the
    secret vector, ntt-inverted, plus the per-row error. -/
noncomputable def row_spec {K : Std.Usize}
    (lm : Std.Array (Std.Array FEPoly K) K)
    (r_as_ntt error_1 : Slice Poly) (r : Nat) : Result FEPoly :=
  (do
    let prod ← hacspec_ml_kem.matrix.multiply_vectors (lm.val[r]!) (lift_vec_slice r_as_ntt K)
    let inv ← hacspec_ml_kem.invert_ntt.ntt_inverse prod
    hacspec_ml_kem.matrix.add_polynomials inv (lift_poly (error_1.val[r]!)))

/-- 2-conjunct invariant for the outer rows loop. Tracks:
    (1) Per-completed-row characterization: for each row `r ∈ [start, k)`,
        `row_spec lm r_as_ntt error_1 r = .ok (lift_poly result[r]!)`.
    (2) Unchanged rows: for each `r ∈ [0, K)` with `r < start ∨ k ≤ r`,
        `result[r]! = result_init[r]!`.
    (3) Length preservation: `result.length = K.val` (needed to discharge the
        per-iteration `Slice.index_mut result k` bound; the conjuncts (1)/(2) do not carry it).
    (4) Per-completed-row output bound: for each row `r ∈ [start, k)`, every lane
        `|result[r][j][m]| ≤ 1664` — the Barrett-reduced output bound, carried so
        the top-level L7.2 POST can state the impl output in canonical form (no
        output `lift`). -/
def rows_inv {K : Std.Usize}
    (lm : Std.Array (Std.Array FEPoly K) K)
    (r_as_ntt error_1 : Slice Poly)
    (result_init : Slice Poly) (start : Std.Usize) :
    Std.Usize → Slice Poly → Scratch → Acc → Result Prop :=
  fun k result _scratch _acc => pure (
    (∀ r : Nat, start.val ≤ r → r < k.val →
        row_spec lm r_as_ntt error_1 r = .ok (lift_poly (result.val[r]!)))
    ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ k.val ≤ r) →
        result.val[r]! = result_init.val[r]!)
    ∧ result.length = K.val
    ∧ (∀ r : Nat, start.val ≤ r → r < k.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
        ((result.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664))

/-- Step-post for `loop_range_spec_usize` over the loop's 4-carry
    `(matrix_entry, result, scratch, accumulator)`. -/
def rows_step_post {K : Std.Usize}
    (lm : Std.Array (Std.Array FEPoly K) K)
    (r_as_ntt error_1 : Slice Poly)
    (result_init : Slice Poly) (start : Std.Usize) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Poly × Slice Poly × Scratch × Acc)
      (Poly × Slice Poly × Scratch × Acc)) :
    Prop :=
  match r with
  | .cont (iter', _me', result', scratch', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (rows_inv lm r_as_ntt error_1 result_init start
            iter'.start result' scratch' acc').holds
  | .done y => (rows_inv lm r_as_ntt error_1 result_init start
                  K y.2.1 y.2.2.1 y.2.2.2).holds

end AllRowsFillFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do

set_option maxHeartbeats 16000000 in
/-- **L7.2 Stage 3 — per-row step lemma.** For the `Some i1` branch (row `k`) of
    `compute_vector_u_loop1.body`: re-zero the accumulator, run the use-cache
    inner column loop (`compute_vector_u_loop1_loop0_fc`), then the per-row
    finalize WALK (`reducing_from_i32_array` → `invert_ntt_montgomery` →
    `add_error_reduce`), and store `result[i1] := result_poly`. Re-establishes
    `rows_inv` at `k+1`. Mirrors `compute_As_plus_e_loop1_step_lemma_fc` + the L7.4 glue finalize (`FC/ComputeMessage.lean` 168-251,
    add-error instead of subtract). -/
private theorem compute_vector_u_loop1_step_lemma_fc {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (i_zero : Std.I32)
    (seed : Slice Std.U8)
    (r_as_ntt error_1 cache : Slice AllRowsFillFC.Poly)
    (r_arr : Std.Array AllRowsFillFC.Poly K)
    (result_init : Slice AllRowsFillFC.Poly)
    (start : Std.Usize)
    (hK : K.val ≤ 4)
    (h_seed_len : seed.length = 32) (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val) (h_err_len : error_1.length = K.val)
    (h_i_zero : i_zero.val = 0)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_err_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((error_1.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!))
    (matrix_entry : AllRowsFillFC.Poly) (result : Slice AllRowsFillFC.Poly)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (accumulator : AllRowsFillFC.Acc)
    (k : Std.Usize) (h_ge : start.val ≤ k.val) (h_le : k.val ≤ K.val)
    (h_inv : (AllRowsFillFC.rows_inv (lift_matrix_from_seed seed K) r_as_ntt error_1
              result_init start k result scratch accumulator).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
      K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      i_zero seed r_as_ntt error_1 cache { start := k, «end» := K } matrix_entry result scratch
      accumulator
    ⦃ ⇓ r => ⌜ AllRowsFillFC.rows_step_post (lift_matrix_from_seed seed K) r_as_ntt error_1
                result_init start k r ⌝ ⦄ := by
  set lm : Std.Array
      (Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) K) K :=
    lift_matrix_from_seed seed K with hlm_def
  -- Destructure the 3-conjunct invariant.
  obtain ⟨h_inv_done, h_inv_undone, h_result_len, h_inv_bnd⟩ := by
    simpa [AllRowsFillFC.rows_inv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp,
      ← List.getElem!_eq_getElem?_getD] using h_inv
  have h_result_len : result.length = K.val := h_result_len
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
  by_cases h_lt : k.val < K.val
  · -- `Some k` branch (row i1 = k).
    -- (1) IteratorRange.next reduces to (some k, {start := s_iter, end := K}).
    have h_iter_step :
        ⦃ ⌜ True ⌝ ⦄
        CoreModels.core.iter.range.IteratorRange.next
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
    -- (2) Re-zeroed accumulator: acc1 := Array.repeat 256 i_zero, all-zero.
    set acc1 : AllRowsFillFC.Acc :=
      Aeneas.Std.Array.repeat 256#usize i_zero with h_acc1_def
    have h_acc1_get : ∀ n : Nat, n < 256 → acc1.val[n]! = i_zero := by
      intro n hn
      rw [h_acc1_def]
      show (Aeneas.Std.Array.repeat 256#usize i_zero).val[n]! = i_zero
      rw [Aeneas.Std.Array.repeat_val]
      rw [getElem!_pos _ n (by rw [List.length_replicate]; exact hn)]
      exact List.getElem_replicate _
    have h_acc1_zero : ∀ n : Nat, n < 256 → (acc1.val[n]!).val = 0 := by
      intro n hn; rw [h_acc1_get n hn]; exact h_i_zero
    have h_acc1_natAbs : ∀ n : Nat, n < 256 → (acc1.val[n]!).val.natAbs = 0 := by
      intro n hn; rw [h_acc1_zero n hn]; rfl
    have h_acc1_bnd : ∀ n : Fin 256,
        (acc1.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30 := by
      intro n
      rw [h_acc1_natAbs n.val n.isLt]
      have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
      have : (4 : Nat) * 2^25 ≤ 2^30 := by decide
      omega
    -- (3) Run the use-cache inner column loop at row k with the zeroed acc.
    have h_stage2 :=
      compute_vector_u_loop1_loop0_fc hash_functionsHashInst matrix_entry seed r_as_ntt cache
        r_arr acc1 k h_lt h_seed_len h_r_len h_cache_len h_r_arr h_r_bnd h_acc1_bnd h_cache
    obtain ⟨me_acc, h_me_acc_eq, h_rowi⟩ := triple_exists_ok_fc h_stage2
    set me1 : AllRowsFillFC.Poly := me_acc.1 with h_me1_def
    set acc2 : AllRowsFillFC.Acc := me_acc.2 with h_acc2_def
    -- (4) Bound on acc2 from row_i_inv conjunct 2 (acc1 zero, K ≤ 4).
    have h_rowi' : (RowIFillFC.row_i_inv (lift_matrix_from_seed seed K).val[k.val]! r_arr acc1
                    K acc2).holds := h_rowi
    obtain ⟨_h_exists, h_acc2_bnd_raw⟩ := by
      simpa [RowIFillFC.row_i_inv, Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        using h_rowi'
    have h_acc2_bnd : ∀ n : Nat, n < 256 → (acc2.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
      intro n hn
      have hb := h_acc2_bnd_raw n hn
      simp only [← List.getElem!_eq_getElem?_getD] at hb
      rw [h_acc1_natAbs n hn] at hb
      have hK4 : K.val * 2^25 ≤ 4 * 2^25 := Nat.mul_le_mul_right _ hK
      have h2 : (4 : Nat) * 2^25 ≤ 2^16 * 3328 := by decide
      omega
    -- (5) acc-bridge: multiply_vectors row k = .ok (scaleZ 2285 (mont_strip (poly_reducing ...))).
    set acc_slice : Slice Std.I32 := Aeneas.Std.Array.to_slice acc2 with h_acc_slice_def
    have h_acc_slice_len : acc_slice.length = 256 := by
      rw [h_acc_slice_def, Aeneas.Std.Array.length_to_slice]; rfl
    have h_acc_slice_val : acc_slice.val = acc2.val :=
      Aeneas.Std.Array.val_to_slice acc2
    have h_acc_slice_bnd : ∀ n : Nat, n < 256 →
        (acc_slice.val[n]!).val.natAbs ≤ 2^16 * 3328 := by
      intro n hn; rw [h_acc_slice_val]; exact h_acc2_bnd n hn
    have h_bridge :=
      compute_vector_u_rowi_acc_bridge seed r_as_ntt r_arr acc1 acc2 k
        h_acc1_zero h_r_arr h_r_bnd h_rowi'
    -- (6) Index_mut result k → (result[k]!, result.set k).
    set pre : AllRowsFillFC.Poly := result.val[k.val]! with h_pre_def
    have h_idx_result : Aeneas.Std.Slice.index_usize result k = .ok pre :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq result k
        (by show k.val < result.length; rw [h_result_len]; exact h_lt)
    have h_imt_result : Aeneas.Std.Slice.index_mut_usize result k
        = .ok (pre, result.set k) := by
      unfold Aeneas.Std.Slice.index_mut_usize
      rw [h_idx_result]; rfl
    -- (7) reducing step: result1.
    obtain ⟨result1, h_result1_eq, h_result1_mont, h_result1_lane_bnd⟩ :=
      triple_exists_ok_fc
        (poly_reducing_from_i32_array_fc acc_slice pre h_acc_slice_len h_acc_slice_bnd)
    have h_result1_lift : lift_poly result1
        = Impl.mont_strip_pure (Spec.poly_reducing_from_i32_array_pure acc_slice) := by
      rw [← h_result1_mont, Impl.mont_strip_lift_poly_mont_eq_lift_poly]
    -- result1 := result.set k result1 (the new slice after the reducing store).
    set rslice1 : Slice AllRowsFillFC.Poly := result.set k result1 with h_rslice1_def
    have h_rslice1_at : rslice1.val[k.val]! = result1 := by
      rw [h_rslice1_def]
      simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
        Aeneas.Std.Slice.getElem!_Nat_set_eq result k k.val result1
          ⟨rfl, by show k.val < result.length; rw [h_result_len]; exact h_lt⟩
    have h_rslice1_len : rslice1.length = K.val := by
      rw [h_rslice1_def]
      show (result.set k result1).length = K.val
      rw [Aeneas.Std.Slice.set_length]; exact h_result_len
    -- (8) index_mut rslice1 k → (result1, rslice1.set k).
    set pre2 : AllRowsFillFC.Poly := rslice1.val[k.val]! with h_pre2_def
    have h_idx_rslice1 : Aeneas.Std.Slice.index_usize rslice1 k = .ok pre2 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq rslice1 k
        (by show k.val < rslice1.length; rw [h_rslice1_len]; exact h_lt)
    have h_imt_rslice1 : Aeneas.Std.Slice.index_mut_usize rslice1 k
        = .ok (pre2, rslice1.set k) := by
      unfold Aeneas.Std.Slice.index_mut_usize
      rw [h_idx_rslice1]; rfl
    have h_pre2_eq : pre2 = result1 := h_pre2_def.trans h_rslice1_at
    -- (9) invert step: result2.
    have h_result1_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((result1.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 13312 := by
      intro chunk hchunk ℓ hℓ
      have := h_result1_lane_bnd chunk hchunk ℓ hℓ; omega
    obtain ⟨⟨result2, scratch1⟩, h_inv_eq, h_result2_lift, h_result2_bnd⟩ :=
      triple_exists_ok_fc
        (invert_ntt_montgomery_fc (K := K) result1 scratch h_result1_bnd)
    dsimp only at h_inv_eq h_result2_lift h_result2_bnd
    -- result2 := rslice1.set k result2.
    set rslice2 : Slice AllRowsFillFC.Poly := rslice1.set k result2 with h_rslice2_def
    have h_rslice2_at : rslice2.val[k.val]! = result2 := by
      rw [h_rslice2_def]
      simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
        Aeneas.Std.Slice.getElem!_Nat_set_eq rslice1 k k.val result2
          ⟨rfl, by show k.val < rslice1.length; rw [h_rslice1_len]; exact h_lt⟩
    have h_rslice2_len : rslice2.length = K.val := by
      rw [h_rslice2_def]
      show (rslice1.set k result2).length = K.val
      rw [Aeneas.Std.Slice.set_length]; exact h_rslice1_len
    -- (10) index_mut rslice2 k → (result2, rslice2.set k).
    set pre4 : AllRowsFillFC.Poly := rslice2.val[k.val]! with h_pre4_def
    have h_idx_rslice2 : Aeneas.Std.Slice.index_usize rslice2 k = .ok pre4 :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq rslice2 k
        (by show k.val < rslice2.length; rw [h_rslice2_len]; exact h_lt)
    have h_imt_rslice2 : Aeneas.Std.Slice.index_mut_usize rslice2 k
        = .ok (pre4, rslice2.set k) := by
      unfold Aeneas.Std.Slice.index_mut_usize
      rw [h_idx_rslice2]; rfl
    have h_pre4_eq : pre4 = result2 := h_pre4_def.trans h_rslice2_at
    -- (11) index error_1 k → error_1[k]!.
    set err_k : AllRowsFillFC.Poly := error_1.val[k.val]! with h_err_k_def
    have h_idx_err : Aeneas.Std.Slice.index_usize error_1 k = .ok err_k :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq error_1 k
        (by show k.val < error_1.length; rw [h_err_len]; exact h_lt)
    -- (12) add_error_reduce step: result_poly.
    have h_result2_self_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((result2.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 32767 := by
      intro chunk hchunk ℓ hℓ
      have := h_result2_bnd chunk hchunk ℓ hℓ; omega
    have h_err_k_bnd : ∀ chunk : Nat, chunk < 16 → ∀ ℓ : Nat, ℓ < 16 →
        ((err_k.coefficients.val[chunk]!).elements.val[ℓ]!).val.natAbs ≤ 29439 :=
      fun chunk hchunk ℓ hℓ =>
        h_err_bnd k.val h_lt ⟨chunk, hchunk⟩ ⟨ℓ, hℓ⟩
    obtain ⟨result_poly, h_add_eq, h_result_poly_lift, h_result_poly_bnd⟩ :=
      triple_exists_ok_fc
        (add_error_reduce_fc result2 err_k h_result2_self_bnd h_err_k_bnd)
    -- result_poly slice: rnew := rslice2.set k result_poly.
    set rnew : Slice AllRowsFillFC.Poly := rslice2.set k result_poly with h_rnew_def
    have h_rnew_at : rnew.val[k.val]! = result_poly := by
      rw [h_rnew_def]
      simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
        Aeneas.Std.Slice.getElem!_Nat_set_eq rslice2 k k.val result_poly
          ⟨rfl, by show k.val < rslice2.length; rw [h_rslice2_len]; exact h_lt⟩
    have h_rnew_ne : ∀ j : Nat, j ≠ k.val → rnew.val[j]! = result.val[j]! := by
      intro j hj
      have e1 : rnew.val[j]! = rslice2.val[j]! := by
        rw [h_rnew_def]
        simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
          Aeneas.Std.Slice.getElem!_Nat_set_ne rslice2 k j result_poly (fun h => hj h.symm)
      have e2 : rslice2.val[j]! = rslice1.val[j]! := by
        rw [h_rslice2_def]
        simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
          Aeneas.Std.Slice.getElem!_Nat_set_ne rslice1 k j result2 (fun h => hj h.symm)
      have e3 : rslice1.val[j]! = result.val[j]! := by
        rw [h_rslice1_def]
        simpa [Aeneas.Std.Slice.getElem!_Nat_eq] using
          Aeneas.Std.Slice.getElem!_Nat_set_ne result k j result1 (fun h => hj h.symm)
      rw [e1, e2, e3]
    -- (13) row_spec equation: row_spec lm r_as_ntt error_1 k = .ok (lift_poly result_poly).
    have h_invrel : Spec.invert_ntt_montgomery_pure (lift_poly result1) = lift_poly result2 :=
      h_result2_lift.symm
    have h_tailrel : Spec.add_error_reduce_pure (lift_poly result2) (lift_poly err_k)
        = lift_poly result_poly := h_result_poly_lift.symm
    have h_row_spec : AllRowsFillFC.row_spec lm r_as_ntt error_1 k.val
        = .ok (lift_poly result_poly) := by
      unfold AllRowsFillFC.row_spec
      -- multiply_vectors = .ok (scaleZ 2285 (lift_poly result1)).
      have hA : hacspec_ml_kem.matrix.multiply_vectors (lm.val[k.val]!) (lift_vec_slice r_as_ntt K)
          = .ok (scaleZ 2285 (lift_poly result1)) := by
        rw [hlm_def, h_result1_lift, h_acc_slice_def]
        exact h_bridge
      rw [hA]; simp only [Aeneas.Std.bind_tc_ok]
      -- ntt_inverse (scaleZ 2285 (lift_poly result1)) = .ok (scaleZ 512 (lift_poly result2)).
      rw [compute_vector_u_ntt_inverse_eq result1 result2 h_invrel]
      simp only [Aeneas.Std.bind_tc_ok]
      -- add_polynomials (scaleZ 512 (lift_poly result2)) (lift_poly err_k) = .ok (lift_poly result_poly).
      rw [← h_err_k_def]
      exact compute_vector_u_add_eq result2 err_k result_poly h_tailrel
    -- (14) Body equation: reduce loop1.body to .ok (.cont (..., me1, rnew, scratch1, acc2)).
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
          K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
          i_zero seed r_as_ntt error_1 cache { start := k, «end» := K } matrix_entry result scratch
          accumulator
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize),
                        me1, rnew, scratch1, acc2)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
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
      -- Enter the `Some k` branch; inner column loop (acc folded to `acc1`).
      show ((do
              let (matrix_entry1, accumulator2) ←
                libcrux_iot_ml_kem.matrix.compute_vector_u_loop1_loop0
                  (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
                  { start := 0#usize, «end» := K } matrix_entry seed r_as_ntt cache
                  (Aeneas.Std.Array.repeat 256#usize i_zero) k
              let s ← Aeneas.Std.lift (Aeneas.Std.Array.to_slice accumulator2)
              let (pre, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize result k
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst s pre
              let result1 := index_mut_back pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Slice.index_mut_usize result1 k
              let (pre3, scratch1) ←
                libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery K portable_ops_inst pre2 scratch
              let result2 := index_mut_back1 pre3
              let (pre4, index_mut_back2) ← Aeneas.Std.Slice.index_mut_usize result2 k
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              let s1 := index_mut_back2 pre6
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          matrix_entry1, s1, scratch1, accumulator2)))
            : Result _) = _
      rw [← h_acc1_def, h_me_acc_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      show ((do
              let s := Aeneas.Std.Array.to_slice me_acc.2
              let (pre, index_mut_back) ← Aeneas.Std.Slice.index_mut_usize result k
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst s pre
              let result1 := index_mut_back pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Slice.index_mut_usize result1 k
              let (pre3, scratch1) ←
                libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery K portable_ops_inst pre2 scratch
              let result2 := index_mut_back1 pre3
              let (pre4, index_mut_back2) ← Aeneas.Std.Slice.index_mut_usize result2 k
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              let s1 := index_mut_back2 pre6
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me_acc.1, s1, scratch1, me_acc.2)))
            : Result _) = _
      rw [← h_acc2_def, ← h_acc_slice_def, h_imt_result]
      simp only [Aeneas.Std.bind_tc_ok]
      -- Reducing store: `index_mut_back := result.set k`.
      show ((do
              let pre1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
                  portable_ops_inst acc_slice pre
              let result1 := (result.set k) pre1
              let (pre2, index_mut_back1) ← Aeneas.Std.Slice.index_mut_usize result1 k
              let (pre3, scratch1) ←
                libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery K portable_ops_inst pre2 scratch
              let result2 := index_mut_back1 pre3
              let (pre4, index_mut_back2) ← Aeneas.Std.Slice.index_mut_usize result2 k
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me_acc.1, index_mut_back2 pre6, scratch1, acc2)))
            : Result _) = _
      have h_red_eq :
          libcrux_iot_ml_kem.polynomial.PolynomialRingElement.reducing_from_i32_array
            (vectortraitsOperationsInst := portable_ops_inst) acc_slice pre = .ok result1 :=
        h_result1_eq
      rw [h_red_eq]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [show (result.set k) result1 = rslice1 from rfl, h_imt_rslice1]
      simp only [Aeneas.Std.bind_tc_ok]
      -- Invert store: `index_mut_back1 := rslice1.set k`, applied to result2.
      show ((do
              let (pre3, scratch1) ←
                libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery K portable_ops_inst pre2 scratch
              let result2 := (rslice1.set k) pre3
              let (pre4, index_mut_back2) ← Aeneas.Std.Slice.index_mut_usize result2 k
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me_acc.1, index_mut_back2 pre6, scratch1, acc2)))
            : Result _) = _
      rw [show pre2 = result1 from h_pre2_eq]
      have h_inv_eq' :
          libcrux_iot_ml_kem.invert_ntt.invert_ntt_montgomery
            K (vectortraitsOperationsInst := portable_ops_inst) result1 scratch
            = .ok (result2, scratch1) := h_inv_eq
      rw [h_inv_eq']
      simp only [Aeneas.Std.bind_tc_ok]
      -- Reduce the `(pre3, scratch1) := (result2, scratch1)` destructuring.
      show ((do
              let (pre4, index_mut_back2) ←
                Aeneas.Std.Slice.index_mut_usize ((rslice1.set k) result2) k
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me_acc.1, index_mut_back2 pre6, scratch1, acc2)))
            : Result _) = _
      rw [show (rslice1.set k) result2 = rslice2 from rfl, h_imt_rslice2]
      simp only [Aeneas.Std.bind_tc_ok]
      -- Add-error store: `index_mut_back2 := rslice2.set k`, applied to result_poly.
      show ((do
              let pre5 ← Aeneas.Std.Slice.index_usize error_1 k
              let pre6 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
                  portable_ops_inst pre4 pre5
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                          me_acc.1, (rslice2.set k) pre6, scratch1, acc2)))
            : Result _) = _
      rw [show pre4 = result2 from h_pre4_eq]
      rw [show (Aeneas.Std.Slice.index_usize error_1 k) = .ok err_k from h_idx_err]
      simp only [Aeneas.Std.bind_tc_ok]
      have h_add_eq' :
          libcrux_iot_ml_kem.polynomial.PolynomialRingElement.add_error_reduce
            (vectortraitsOperationsInst := portable_ops_inst) result2 err_k = .ok result_poly :=
        h_add_eq
      rw [h_add_eq']
      simp only [Aeneas.Std.bind_tc_ok]
      rw [show (rslice2.set k) result_poly = rnew from rfl]
    apply triple_of_ok_fc h_body
    -- (15) Discharge step_post: rows_inv at s_iter (= k+1).
    show AllRowsFillFC.rows_step_post lm r_as_ntt error_1 result_init start k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), me1, rnew, scratch1, acc2))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    show (AllRowsFillFC.rows_inv lm r_as_ntt error_1 result_init start
            s_iter rnew scratch1 acc2).holds
    unfold AllRowsFillFC.rows_inv
    show (pure _ : Result Prop).holds
    have hs_iter_eq : s_iter.val = k.val + 1 := hs_iter_val
    have h_rnew_len : rnew.length = K.val := by
      rw [h_rnew_def, Aeneas.Std.Slice.set_length, h_rslice2_def,
        Aeneas.Std.Slice.set_length, h_rslice1_def, Aeneas.Std.Slice.set_length]
      exact h_result_len
    have h_inv_pure :
        (∀ r : Nat, start.val ≤ r → r < s_iter.val →
            AllRowsFillFC.row_spec lm r_as_ntt error_1 r = .ok (lift_poly (rnew.val[r]!)))
        ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ s_iter.val ≤ r) →
            rnew.val[r]! = result_init.val[r]!)
        ∧ rnew.length = K.val
        ∧ (∀ r : Nat, start.val ≤ r → r < s_iter.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
            ((rnew.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, h_rnew_len, ?_⟩
      · -- Completed rows [start, k+1).
        intro r hr_ge hr_lt
        rw [hs_iter_eq] at hr_lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hr_lt_k | hr_eq_k
        · -- r < k: unchanged this iteration; use IH (1).
          have hr_ne : r ≠ k.val := by omega
          rw [h_rnew_ne r hr_ne]
          exact h_inv_done r hr_ge hr_lt_k
        · -- r = k: the row written this iteration.
          subst hr_eq_k
          rw [h_rnew_at]
          exact h_row_spec
      · -- Unchanged rows.
        intro r hr_lt_K hr_cond
        rw [hs_iter_eq] at hr_cond
        have hr_ne : r ≠ k.val := by omega
        rw [h_rnew_ne r hr_ne]
        exact h_inv_undone r hr_lt_K (by omega)
      · -- Per-completed-row output bound [start, k+1).
        intro r hr_ge hr_lt j hj m hm
        rw [hs_iter_eq] at hr_lt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hr_lt with hr_lt_k | hr_eq_k
        · -- r < k: unchanged this iteration; use IH (4).
          have hr_ne : r ≠ k.val := by omega
          rw [h_rnew_ne r hr_ne]
          exact h_inv_bnd r hr_ge hr_lt_k j hj m hm
        · -- r = k: the Barrett-reduced row written this iteration (|·| ≤ 1664).
          subst hr_eq_k
          rw [h_rnew_at]
          exact h_result_poly_bnd j hj m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure
  · -- `None` branch (k = K): loop ends, done.
    have hk_eq : k.val = K.val := le_antisymm h_le (Nat.not_lt.mp h_lt)
    have h_iter_none :
        ⦃ ⌜ True ⌝ ⦄
        CoreModels.core.iter.range.IteratorRange.next
          core.Usize.Insts.CoreIterRangeStep
          ({ start := k, «end» := K } : CoreModels.core.ops.range.Range Std.Usize)
        ⦃ ⇓ r => ⌜ r = (none,
                      ({ start := k, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize)) ⌝ ⦄ :=
      libcrux_iot_ml_kem.Util.LoopSpecs.IteratorRange_next_spec_usize k K
        (fun hlt => absurd hlt (Nat.not_lt.mpr (Nat.le_of_eq hk_eq.symm)))
        (fun _ => by dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
    obtain ⟨v_iter, hv_iter_eq, hv_iter_post⟩ := triple_exists_ok_fc h_iter_none
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
          K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
          i_zero seed r_as_ntt error_1 cache { start := k, «end» := K } matrix_entry result scratch
          accumulator
        = .ok (ControlFlow.done (matrix_entry, result, scratch, accumulator)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
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
    show AllRowsFillFC.rows_step_post lm r_as_ntt error_1 result_init start k
      (.done (matrix_entry, result, scratch, accumulator))
    show (AllRowsFillFC.rows_inv lm r_as_ntt error_1 result_init start K result scratch
            accumulator).holds
    unfold AllRowsFillFC.rows_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ r : Nat, start.val ≤ r → r < K.val →
            AllRowsFillFC.row_spec lm r_as_ntt error_1 r = .ok (lift_poly (result.val[r]!)))
        ∧ (∀ r : Nat, r < K.val → (r < start.val ∨ K.val ≤ r) →
            result.val[r]! = result_init.val[r]!)
        ∧ result.length = K.val
        ∧ (∀ r : Nat, start.val ≤ r → r < K.val → ∀ j : Nat, j < 16 → ∀ m : Nat, m < 16 →
            ((result.val[r]!).coefficients.val[j]!).elements.val[m]!.val.natAbs ≤ 1664) := by
      refine ⟨?_, ?_, h_result_len, ?_⟩
      · intro r hr_ge hr_lt
        exact h_inv_done r hr_ge (by rw [hk_eq]; exact hr_lt)
      · intro r hr_lt_K hr_cond
        exact h_inv_undone r hr_lt_K (by
          rcases hr_cond with h | h
          · exact Or.inl h
          · exact Or.inr (by rw [hk_eq]; exact h))
      · intro r hr_ge hr_lt j hj m hm
        exact h_inv_bnd r hr_ge (by rw [hk_eq]; exact hr_lt) j hj m hm
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv_pure

set_option maxHeartbeats 1600000 in
/-- **L7.2 Stage 3 — outer rows loop FC** (`compute_vector_u_loop1`). Mirrors
    `compute_As_plus_e_loop1_fc`: the rows loop `[start, K)`,
    each row re-zeroing the accumulator, running the use-cache inner column loop,
    and finalizing (reducing → invert → add_error). POST is the resolved
    `AllRowsFillFC.rows_inv` at `k = K`: every row `r ∈ [start, K)` matches
    `row_spec lm r_as_ntt error_1 r = .ok (lift_poly result[r])`, and rows
    outside `[start, K)` are unchanged from the input. -/
theorem compute_vector_u_loop1_fc {K : Std.Usize} {Hasher : Type}
    (hash_functionsHashInst : libcrux_iot_ml_kem.hash_functions.Hash Hasher)
    (i_zero : Std.I32)
    (matrix_entry : AllRowsFillFC.Poly) (seed : Slice Std.U8)
    (r_as_ntt error_1 result : Slice AllRowsFillFC.Poly)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (cache : Slice AllRowsFillFC.Poly)
    (accumulator : AllRowsFillFC.Acc)
    (r_arr : Std.Array AllRowsFillFC.Poly K)
    (start : Std.Usize)
    (hK : K.val ≤ 4) (h_start : 1 ≤ start.val) (h_start_le : start.val ≤ K.val)
    (h_seed_len : seed.length = 32) (h_r_len : r_as_ntt.length = K.val)
    (h_cache_len : cache.length = K.val) (h_result_len : result.length = K.val)
    (h_err_len : error_1.length = K.val)
    (h_i_zero : i_zero.val = 0)
    (h_r_arr : ∀ c : Nat, c < K.val → r_arr.val[c]! = r_as_ntt.val[c]!)
    (h_r_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((r_as_ntt.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328)
    (h_err_bnd : ∀ c : Nat, c < K.val → ∀ a : Fin 16, ∀ b : Fin 16,
        ((error_1.val[c]!.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 29439)
    (h_cache : ∀ c : Nat, c < K.val →
        accumulating_ntt_multiply_poly_cache_post (r_as_ntt.val[c]!) (cache.val[c]!)) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_vector_u_loop1
      K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
      i_zero { start := start, «end» := K } matrix_entry seed r_as_ntt error_1 result scratch cache
      accumulator
    ⦃ ⇓ p => ⌜ (AllRowsFillFC.rows_inv (lift_matrix_from_seed seed K) r_as_ntt error_1 result start
                  K p.2.1 p.2.2.1 p.2.2.2).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.matrix.compute_vector_u_loop1
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, p) =>
        libcrux_iot_ml_kem.matrix.compute_vector_u_loop1.body
          K (vectortraitsOperationsInst := portable_ops_inst) hash_functionsHashInst
          i_zero seed r_as_ntt error_1 cache iter1 p.1 p.2.1 p.2.2.1 p.2.2.2)
      (β := AllRowsFillFC.Poly × Slice AllRowsFillFC.Poly × AllRowsFillFC.Scratch × AllRowsFillFC.Acc)
      (matrix_entry, result, scratch, accumulator)
      start K
      (fun k p => AllRowsFillFC.rows_inv (lift_matrix_from_seed seed K) r_as_ntt error_1 result start
                    k p.2.1 p.2.2.1 p.2.2.2)
      h_start_le
      (by
        -- Base case at k = start: rows_inv holds trivially.
        show (pure _ : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        refine ⟨?_, ?_, h_result_len, ?_⟩
        · intro r hr_ge hr_lt; omega
        · intro r _ _; trivial
        · intro r hr_ge hr_lt; omega)
      ?_)
  · -- Post entailment: at k = K, rows_inv holds.
    rw [PostCond.entails_noThrow]
    intro p hh
    have h_inv_holds : (AllRowsFillFC.rows_inv (lift_matrix_from_seed seed K) r_as_ntt error_1 result
                          start K p.2.1 p.2.2.1 p.2.2.2).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    exact h_inv_holds
  · -- Step entailment.
    intro p k h_ge h_le hinv
    have h_step := compute_vector_u_loop1_step_lemma_fc
      hash_functionsHashInst i_zero seed r_as_ntt error_1 cache r_arr result start hK
      h_seed_len h_r_len h_cache_len h_err_len h_i_zero h_r_arr h_r_bnd h_err_bnd h_cache
      p.1 p.2.1 p.2.2.1 p.2.2.2 k h_ge h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', rest⟩ | y
    · have hP : AllRowsFillFC.rows_step_post (lift_matrix_from_seed seed K) r_as_ntt error_1
                  result start k (.cont (iter', rest.1, rest.2.1, rest.2.2.1, rest.2.2.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AllRowsFillFC.rows_step_post] using hP
    · have hP : AllRowsFillFC.rows_step_post (lift_matrix_from_seed seed K) r_as_ntt error_1
                  result start k (.done (y.1, y.2.1, y.2.2.1, y.2.2.2)) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [AllRowsFillFC.rows_step_post] using hP

end libcrux_iot_ml_kem.Matrix.ComputeVectorU.Impl