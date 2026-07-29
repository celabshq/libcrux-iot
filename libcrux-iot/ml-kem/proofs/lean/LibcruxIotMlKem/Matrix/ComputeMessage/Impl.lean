/-
  # `Matrix/ComputeMessage/Impl.lean` — L7.4 S1 loop FC.

  Houses the S1 loop FC for `matrix.compute_message_loop`: the cache-free
  analog of `compute_As_plus_e_loop0_fc`. The loop folds over
  `i ∈ [0, K)`, each iteration applying
  `accumulating_ntt_multiply secret_as_ntt[i] u_as_ntt[i] acc` into a
  single I32[256] accumulator (no cache, no matrix). The POST is the
  K-fold of the per-step POST of `accumulating_ntt_multiply_poly_fc`: a
  `mont_reduce_pure`-per-lane `List.range`-foldl characterization plus
  the running bound `≤ accumulator[n] + k·2^25`.

  Mirrors `Stage2UseCacheFC.row_i_inv` / `compute_As_plus_e_loop1_loop0_fc` — the
  2-conjunct, accumulator-only (no cache) precedent — but drops the
  matrix-row index (two source arrays `secret_as_ntt[c]`, `u_as_ntt[c]`
  indexed directly by `c`), and uses the plain
  `accumulating_ntt_multiply_poly_fc` per-step lemma instead of the
  `_use_cache_poly_fc` variant.
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
import LibcruxIotMlKem.Matrix.ComputeMessage.Bridges

namespace libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-- Local copy of FCTargets' `private triple_exists_ok_fc`: a `True`-pre
    Triple yielding `.ok` with the post is equivalent to an existential
    `.ok` witness. The L7 files cannot see the private original, so this is
    re-derived from the public `Std.Do.Triple`/`WP.wp` unfolding. -/
private theorem triple_exists_ok_fc {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-- Local copy of FCTargets' `private triple_of_ok_fc`: a `True`-pre Triple
    follows from an `.ok` reduction plus the post on the witness. -/
private theorem triple_of_ok_fc {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

/-! ## S1 — the corrected loop FC for `matrix.compute_message_loop`.

    Namespace `S1LoopFC` provides the loop invariant + step-post predicates
    used to characterize `matrix.compute_message_loop` via
    `loop_range_spec_usize`. The accumulator state is a single I32[256]
    array (no cache) — `Acc := Std.Array Std.I32 256#usize`. -/

namespace S1LoopFC

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Std.Do Result ControlFlow

abbrev Acc := UseCacheFC.Acc

/-- 2-conjunct invariant for the message-accumulation loop. Tracks:
    (1) accumulator characterization: for each (chunk j, lane ℓ) in
        `[0, 16)²`, `Spec.mont_reduce_pure (lift_fe_int acc[16j+ℓ].val)`
        equals init plus the canonical-form sum of column contributions
        `secret_as_ntt[c] ⊛ u_as_ntt[c]` from columns `[0, k)`.
    (2) accumulator bound: `|acc.val[n]| ≤ |acc_init.val[n]| + k · 2^25`.

    Cache-free analog of `Stage2UseCacheFC.row_i_inv` with the
    matrix-row index dropped: both source arrays are indexed directly by
    the column `c`. -/
def loop_inv {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    -- (1) Per-(chunk j, lane ℓ) accumulator: canonical-form k-column sum.
    (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
      Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
        = (List.range k.val).foldl
            (fun s c =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                ((Spec.ntt_multiply_pure_no_acc
                    (lift_chunk_mont (secret_as_ntt.val[c]!.coefficients.val[j]!))
                    (lift_chunk_mont (u_as_ntt.val[c]!.coefficients.val[j]!))
                    (Spec.zeta_at (64 + 4 * j))
                    (Spec.zeta_at (64 + 4 * j + 1))
                    (Spec.zeta_at (64 + 4 * j + 2))
                    (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!))
            (Spec.mont_reduce_pure (lift_fe_int (acc_init.val[16 * j + ℓ]!).val)))
    -- (2) Accumulator bound grows by 2^25 per column iteration.
    ∧ (∀ n : Nat, n < 256 →
        (acc.val[n]!).val.natAbs ≤ (acc_init.val[n]!).val.natAbs + k.val * 2^25))

/-- Step-post for `loop_range_spec_usize` over the accumulator only. -/
def step_post {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Acc) (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) :
    Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < K.val ∧ iter'.«end» = K
        ∧ iter'.start.val = k.val + 1
        ∧ (loop_inv secret_as_ntt u_as_ntt acc_init iter'.start acc').holds
  | .done y => (loop_inv secret_as_ntt u_as_ntt acc_init K y).holds

end S1LoopFC

-- Memory hygiene (rule 1 / SKILL §5.7 Idiom 2). Mirrors `L7_1b_irreducible`
-- — heavy POST predicates are made locally irreducible
-- across the step lemma + outer Triple so that elaboration does not
-- whnf-explode through the 2-conjunct `loop_inv` body or the nested
-- `∀ j, ∀ ℓ` accumulator characterization. -- we do NOT mark
-- `S1LoopFC.loop_inv` / `step_post` irreducible.
section L7_4_irreducible
attribute [local irreducible] accumulating_ntt_multiply_poly_post
attribute [local irreducible] Spec.ntt_multiply_pure_no_acc
attribute [local irreducible] Spec.mont_reduce_pure

set_option maxHeartbeats 16000000 in
/-- Per-iteration FC step lemma for the message-accumulation loop. Given the
    `loop_inv` invariant at step k and the strengthened PRE bounds, executing
    one body iteration of `matrix.compute_message_loop.body` produces the
    `step_post` (either `.cont` advancing the invariant to k+1 or `.done`
    capping at K).

    Mirrors `compute_As_plus_e_loop1_loop0_step_lemma_fc`
    but cache-free: no `matrix.entry` (read `secret_as_ntt[k]`, `u_as_ntt[k]`
    directly), no cache read, and the per-column forward dep is
    `accumulating_ntt_multiply_poly_fc` which returns a
    single accumulator (no pair). -/
private theorem compute_message_loop_step_lemma_fc
    {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
                  (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : S1LoopFC.Acc)
    (h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((secret_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((u_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (acc_init.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30)
    (acc : S1LoopFC.Acc)
    (k : Std.Usize) (h_le : k.val ≤ K.val)
    (h_inv : (S1LoopFC.loop_inv secret_as_ntt u_as_ntt acc_init k acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_message_loop.body
      (vectortraitsOperationsInst := portable_ops_inst) secret_as_ntt u_as_ntt
      { start := k, «end» := K } acc
    ⦃ ⇓ r => ⌜ S1LoopFC.step_post secret_as_ntt u_as_ntt acc_init k r ⌝ ⦄ := by
  have h_secret_len : secret_as_ntt.length = K.val := Std.Array.length_eq secret_as_ntt
  have h_u_len : u_as_ntt.length = K.val := Std.Array.length_eq u_as_ntt
  have h_acc_len : acc.length = 256 := Std.Array.length_eq acc
  have h_acc_init_len : acc_init.length = 256 := Std.Array.length_eq acc_init
  -- Destructure the 2-conjunct invariant.
  obtain ⟨h_inv_acc, h_inv_acc_bnd⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_inv
  unfold libcrux_iot_ml_kem.matrix.compute_message_loop.body
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
    -- (2) Array.index_usize secret_as_ntt k reduces to .ok secret_as_ntt[k.val]!.
    set t_secret : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      secret_as_ntt.val[k.val]! with ht_secret_def
    have h_idx_secret : Aeneas.Std.Array.index_usize secret_as_ntt k = .ok t_secret :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq secret_as_ntt k
        (by rw [h_secret_len]; exact h_lt)
    -- (3) Array.index_usize u_as_ntt k reduces to .ok u_as_ntt[k.val]!.
    set t_u : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      u_as_ntt.val[k.val]! with ht_u_def
    have h_idx_u : Aeneas.Std.Array.index_usize u_as_ntt k = .ok t_u :=
      libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq u_as_ntt k
        (by rw [h_u_len]; exact h_lt)
    -- (4) Apply L6.3 per-column forward dep at column k.
    have h_t_secret_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_secret.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_secret_bnd ⟨k.val, h_lt⟩ a b
    have h_t_u_bnd : ∀ a : Fin 16, ∀ b : Fin 16,
        ((t_u.coefficients.val[a.val]!).elements.val[b.val]!).val.natAbs ≤ 3328 :=
      fun a b => h_u_bnd ⟨k.val, h_lt⟩ a b
    -- Current acc bound ≤ 2^30: combine inv conjunct (2) with budget PRE.
    have h_acc_cur_bnd : ∀ n : Fin 256, (acc.val[n.val]!).val.natAbs ≤ 2^30 := by
      intro n
      have hb := h_inv_acc_bnd n.val n.isLt
      have hp := h_acc_bnd n
      have hk_le : k.val * 2^25 ≤ K.val * 2^25 := Nat.mul_le_mul_right _ h_le
      omega
    obtain ⟨acc1, h_acc1_eq, h_acc1_bnd_rel, h_acc1_post⟩ :=
      triple_exists_ok_fc
        (accumulating_ntt_multiply_poly_fc t_secret t_u acc
          h_t_secret_bnd h_t_u_bnd h_acc_cur_bnd)
    -- (5) Body equation.
    have h_body :
        libcrux_iot_ml_kem.matrix.compute_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) secret_as_ntt u_as_ntt
          { start := k, «end» := K } acc
        = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                        : CoreModels.core.ops.range.Range Std.Usize), acc1)) := by
      unfold libcrux_iot_ml_kem.matrix.compute_message_loop.body
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
              let pre ← Aeneas.Std.Array.index_usize secret_as_ntt k
              let pre1 ← Aeneas.Std.Array.index_usize u_as_ntt k
              let accumulator1 ←
                libcrux_iot_ml_kem.polynomial.PolynomialRingElement.accumulating_ntt_multiply
                  portable_ops_inst pre pre1 acc
              .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize), accumulator1)))
            : Result _) = _
      rw [h_idx_secret]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_idx_u]
      simp only [Aeneas.Std.bind_tc_ok]
      rw [h_acc1_eq]
      rfl
    apply triple_of_ok_fc h_body
    -- (6) Discharge the step_post.
    show S1LoopFC.step_post secret_as_ntt u_as_ntt acc_init k
      (.cont (({ start := s_iter, «end» := K }
                : CoreModels.core.ops.range.Range Std.Usize), acc1))
    refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
    -- (7) Re-establish `loop_inv` at s_iter (= k+1).
    show (S1LoopFC.loop_inv secret_as_ntt u_as_ntt acc_init s_iter acc1).holds
    unfold S1LoopFC.loop_inv
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc1.val[16 * j + ℓ]!).val)
            = (List.range s_iter.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (secret_as_ntt.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (u_as_ntt.val[c]!.coefficients.val[j]!))
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
                      (lift_chunk_mont (t_secret.coefficients.val[j]!))
                      (lift_chunk_mont (t_u.coefficients.val[j]!))
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
                  (lift_chunk_mont (t_secret.coefficients.val[j]!))
                  (lift_chunk_mont (t_u.coefficients.val[j]!))
                  (Spec.zeta_at (64 + 4 * j))
                  (Spec.zeta_at (64 + 4 * j + 1))
                  (Spec.zeta_at (64 + 4 * j + 2))
                  (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]!)
            = (List.foldl _ ((List.range k.val).foldl _ _) [k.val])
        show _ = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  ((List.range k.val).foldl _ _)
                  ((Spec.ntt_multiply_pure_no_acc
                      (lift_chunk_mont (secret_as_ntt.val[k.val]!.coefficients.val[j]!))
                      (lift_chunk_mont (u_as_ntt.val[k.val]!.coefficients.val[j]!))
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
        libcrux_iot_ml_kem.matrix.compute_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) secret_as_ntt u_as_ntt
          { start := k, «end» := K } acc
        = .ok (ControlFlow.done acc) := by
      unfold libcrux_iot_ml_kem.matrix.compute_message_loop.body
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
    show S1LoopFC.step_post secret_as_ntt u_as_ntt acc_init k (.done acc)
    show (S1LoopFC.loop_inv secret_as_ntt u_as_ntt acc_init K acc).holds
    unfold S1LoopFC.loop_inv
    show (pure _ : Result Prop).holds
    have h_inv_pure :
        (∀ j : Nat, j < 16 → ∀ ℓ : Nat, ℓ < 16 →
          Spec.mont_reduce_pure (lift_fe_int (acc.val[16 * j + ℓ]!).val)
            = (List.range K.val).foldl
                (fun s c =>
                  libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
                    ((Spec.ntt_multiply_pure_no_acc
                        (lift_chunk_mont (secret_as_ntt.val[c]!.coefficients.val[j]!))
                        (lift_chunk_mont (u_as_ntt.val[c]!.coefficients.val[j]!))
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

/-- L7.4 S1 — `matrix.compute_message_loop`: the message-accumulation loop.
    Iterates over `i ∈ [0, K)`, accumulating column-i's contribution
    `secret_as_ntt[i] ⊛ u_as_ntt[i]` to the single I32[256] accumulator via
    `accumulating_ntt_multiply` (NO cache, NO matrix). The cache-free analog
    of `compute_As_plus_e_loop0`.

    POST: `loop_inv` holds at k = K, i.e. for all (j, ℓ) ∈ [0, 16)²:
    `mont_reduce_pure (lift_fe_int acc2[16j+ℓ].val)` equals the K-column
    canonical-form sum of `ntt_multiply_pure_no_acc` outputs over
    `(secret_as_ntt[c], u_as_ntt[c])`, starting from the initial
    accumulator's `mont_reduce_pure` lift, AND the running bound
    `≤ accumulator[n] + K·2^25`.

    PRE: the standard 16×16 bound (3328) on `secret_as_ntt`/`u_as_ntt`
    entries plus the additive accumulator BUDGET
    `(accumulator[n]).val.natAbs + K·2^25 ≤ 2^30`. The budget is consumed by
    the per-column forward dep (`accumulating_ntt_multiply_poly_fc`, PRE
    `≤ 2^30`) at every iteration: the running accumulator satisfies
    `acc[n] ≤ accumulator[n] + k·2^25 ≤ accumulator[n] + K·2^25 ≤ 2^30`.

    Mirrors `compute_As_plus_e_loop1_loop0_fc` cache-free,
    with two source arrays indexed directly by the column. -/
@[spec]
theorem compute_message_loop_fc
    {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (accumulator : Std.Array Std.I32 256#usize)
    (h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((secret_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((u_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_acc_bnd : ∀ n : Fin 256,
        (accumulator.val[n.val]!).val.natAbs + K.val * 2^25 ≤ 2^30) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.matrix.compute_message_loop
      (vectortraitsOperationsInst := portable_ops_inst)
      { start := 0#usize, «end» := K } secret_as_ntt u_as_ntt accumulator
    ⦃ ⇓ acc2 => ⌜ (S1LoopFC.loop_inv secret_as_ntt u_as_ntt accumulator K acc2).holds ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.matrix.compute_message_loop
  apply Std.Do.Triple.of_entails_right _
    (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.matrix.compute_message_loop.body
          (vectortraitsOperationsInst := portable_ops_inst) secret_as_ntt u_as_ntt
          iter1 acc1)
      (β := S1LoopFC.Acc)
      accumulator
      0#usize K
      (fun k acc => S1LoopFC.loop_inv secret_as_ntt u_as_ntt accumulator k acc)
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
    have h_inv_holds : (S1LoopFC.loop_inv secret_as_ntt u_as_ntt accumulator K r).holds := by
      simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
    show (S1LoopFC.loop_inv secret_as_ntt u_as_ntt accumulator K r).holds
    exact h_inv_holds
  · -- Step entailment.
    intro acc k _h_ge h_le hinv
    have h_step := compute_message_loop_step_lemma_fc
      secret_as_ntt u_as_ntt accumulator h_secret_bnd h_u_bnd h_acc_bnd acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : S1LoopFC.step_post secret_as_ntt u_as_ntt accumulator k
                  (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [S1LoopFC.step_post] using hP
    · have hP : S1LoopFC.step_post secret_as_ntt u_as_ntt accumulator k
                  (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [S1LoopFC.step_post] using hP

end L7_4_irreducible

/-! ## A — the acc-bridge ("crux"): R-factor reconciliation.

    Relates the hacspec `multiply_vectors` (on `lift_vec`-lifted inputs) to
    the loop accumulator's reduced value, scaled by `R = 2285`
    (`multiply_vectors = 2285 · result1`, where `result1 = reducing(acc2)`).
    The RHS `mont_strip_pure (poly_reducing(to_slice acc2))` equals
    `lift_poly result1` via the proven `reducing_from_i32_array_fc` POST
    (in the `lift_poly_mont` domain) composed with
    `Impl.mont_strip_lift_poly_mont_eq_lift_poly`. -/

/-- Per-lane R-factor reconciliation.

    For any 256-FE array `p` and lane `j < 256`,
    `scaleZ 2285 (mont_strip_pure p)` and
    `mul_pure (p[j]) (mul_pure 1353 1353)` agree in `ZMod 3329`. The
    factor identity unpacks as: the `mont_strip`
    factor `zmodOfFE (lift_fe_mont 1353) = 1353·169 = 2285 = R`, the
    `multiply_ntts`-canonical factor `mul_pure 1353 1353 = 2285² = 1353`,
    and `2285 · 2285 = 1353` in `ZMod 3329`).

    This bridges the hacspec `multiply_vectors` lane
    (`= mul_pure (loop_inv-foldl-sum) (mul_pure 1353 1353)`, via
    `Spec.multiply_ntts_pure_eq_chunked_no_acc` + `foldl_add_mul_distrib`)
    to `scaleZ 2285 (mont_strip_pure (poly_reducing(acc2)))` lane
    (`= mul_pure (loop_inv-foldl-sum) (lift_fe_mont 1353)` then `·2285`),
    where the shared foldl-sum is exactly S1's `S1LoopFC.loop_inv`
    characterization. -/
theorem compute_message_recon_lane
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) :
    zmodOfFE ((scaleZ 2285 (Impl.mont_strip_pure p)).val[j]!)
      = zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (p.val[j]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (lift_fe_mont (1353#i16 : Std.I16)) (lift_fe_mont (1353#i16 : Std.I16)))) := by
  rw [scaleZ_lane 2285 _ j hj]
  unfold Impl.mont_strip_pure
  have hms : ((Std.Array.make 256#usize
      ((List.range 256).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (p.val[i]!) (lift_fe_mont (1353#i16 : Std.I16)))) (by simp)).val[j]!)
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (p.val[j]!) (lift_fe_mont (1353#i16 : Std.I16)) := by
    show ((List.range 256).map (fun i =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (p.val[i]!) (lift_fe_mont (1353#i16 : Std.I16))))[j]! = _
    rw [getElem!_pos _ j (by simp [hj])]
    rw [List.getElem_map, List.getElem_range]
  rw [hms]
  rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure, zmodOfFE_mul_pure, zmodOfFE_lift_fe_mont]
  have h1353 : (((1353#i16 : Std.I16).val : Int) : ZMod 3329) = 1353 := by decide
  rw [h1353]
  have hc : (2285 : ZMod 3329) * (1353 * 169) = 1353 * 169 * (1353 * 169) := by decide
  rw [show (2285 : ZMod 3329) * (zmodOfFE (p.val[j]!) * (1353 * 169))
        = zmodOfFE (p.val[j]!) * ((2285 : ZMod 3329) * (1353 * 169)) from by ring]
  rw [hc]

/-! ### `multiply_vectors` loop reduction (mirror of
    `multiply_matrix_by_column_at_eq`,, but cache/matrix-free:
    the two source vectors are indexed directly by the column `j`). -/

/-- Per-lane partial sum produced by the `multiply_vectors` loop at step `k`:
    the `add_pure` foldl of the per-column `multiply_ntts_pure` lane values,
    seeded at the zero FE. Mirrors `col_loop_lane_at_step`
    but folds the raw `multiply_ntts_pure` lane (the loop body adds the
    `multiply_ntts` product directly — no pre-applied canonical factor). -/
private noncomputable def vec_loop_lane_at_step {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Nat) (ℓ : Nat) : hacspec_ml_kem.parameters.FieldElement :=
  (List.range k).foldl
    (fun s c =>
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s
        ((Spec.multiply_ntts_pure
            (lift_poly secret_as_ntt.val[c]!) (lift_poly u_as_ntt.val[c]!)).val[ℓ]!))
    ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement)

/-- The per-step `multiply_vectors` accumulator array: lane ℓ is
    `vec_loop_lane_at_step ... k ℓ`. -/
private noncomputable def vec_loop_result_at_step {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Nat) : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  ⟨(List.range 256).map (fun ℓ => vec_loop_lane_at_step secret_as_ntt u_as_ntt k ℓ),
   by simp [List.length_map, List.length_range]⟩

private theorem vec_loop_result_at_step_val_lane {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Nat) (ℓ : Nat) (hℓ : ℓ < 256) :
    (vec_loop_result_at_step secret_as_ntt u_as_ntt k).val[ℓ]!
      = vec_loop_lane_at_step secret_as_ntt u_as_ntt k ℓ := by
  unfold vec_loop_result_at_step
  show ((List.range 256).map
          (fun ℓ' => vec_loop_lane_at_step secret_as_ntt u_as_ntt k ℓ'))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]

/-- Base case: at step 0, every lane is `⟨0#u16⟩`. -/
private theorem vec_loop_lane_at_step_zero {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (ℓ : Nat) :
    vec_loop_lane_at_step secret_as_ntt u_as_ntt 0 ℓ
      = ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement) := by
  unfold vec_loop_lane_at_step
  rw [List.range_zero, List.foldl_nil]

/-- Step lemma: one column iteration `add_polynomials result (multiply_ntts …)`
    advances `vec_loop_result_at_step ... k` to `... (k+1)`, lane-wise. -/
private theorem vec_loop_lane_at_step_succ {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (k : Nat) (ℓ : Nat) :
    vec_loop_lane_at_step secret_as_ntt u_as_ntt (k + 1) ℓ
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (vec_loop_lane_at_step secret_as_ntt u_as_ntt k ℓ)
          ((Spec.multiply_ntts_pure
              (lift_poly secret_as_ntt.val[k]!) (lift_poly u_as_ntt.val[k]!)).val[ℓ]!) := by
  unfold vec_loop_lane_at_step
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 1000 in
/-- **.** `multiply_vectors (lift_vec s) (lift_vec u)` reduces to the
    pure per-lane `add_pure`-foldl array `vec_loop_result_at_step ... K.val`.
    Composes `multiply_ntts_eq_pure_array` + `matrix_add_polynomials_eq_ok`
    through `loop_range_spec_usize`; mirrors `multiply_matrix_by_column_at_eq`. -/
private theorem multiply_vectors_eq {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K) :
    hacspec_ml_kem.matrix.multiply_vectors (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
      = .ok (vec_loop_result_at_step secret_as_ntt u_as_ntt K.val) := by
  unfold hacspec_ml_kem.matrix.multiply_vectors
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  -- Reduce the loop via `loop_range_spec_usize` with the invariant
  -- `result = vec_loop_result_at_step ... k.val`.
  have h_triple : ⦃ ⌜ True ⌝ ⦄
      hacspec_ml_kem.matrix.multiply_vectors_loop
        ({ start := 0#usize, «end» := K }
          : CoreModels.core.ops.range.Range Std.Usize)
        (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
        (Std.Array.repeat (256#usize : Std.Usize)
          ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement))
      ⦃ ⇓ r => ⌜ r = vec_loop_result_at_step secret_as_ntt u_as_ntt K.val ⌝ ⦄ := by
    unfold hacspec_ml_kem.matrix.multiply_vectors_loop
    apply Std.Do.Triple.of_entails_right _
      (libcrux_iot_ml_kem.Util.LoopSpecs.loop_range_spec_usize
        (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                   Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
          hacspec_ml_kem.matrix.multiply_vectors_loop.body
            (lift_vec secret_as_ntt) (lift_vec u_as_ntt) p.1 p.2)
        (β := Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
        (Std.Array.repeat (256#usize : Std.Usize)
          ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement))
        0#usize K
        (fun k result => pure (result = vec_loop_result_at_step secret_as_ntt u_as_ntt k.val))
        (Nat.zero_le _)
        (by
          -- Base: init = vec_loop_result_at_step ... 0.
          show (pure _ : Result Prop).holds
          simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
          intro _
          apply Subtype.ext
          rw [Std.Array.repeat_val]
          unfold vec_loop_result_at_step
          show List.replicate 256 _ = (List.range 256).map _
          apply List.ext_getElem
          · rw [List.length_replicate, List.length_map, List.length_range]
          intro n h_n_lhs _
          have h_n_lt : n < 256 := by
            rw [List.length_replicate] at h_n_lhs; exact h_n_lhs
          rw [List.getElem_replicate, List.getElem_map, List.getElem_range]
          show _ = vec_loop_lane_at_step secret_as_ntt u_as_ntt 0 n
          rw [vec_loop_lane_at_step_zero])
        ?_)
    · -- Post entailment.
      rw [PostCond.entails_noThrow]
      intro r hh
      have h_eq : (pure (r = vec_loop_result_at_step secret_as_ntt u_as_ntt K.val)
                  : Result Prop).holds := by
        simpa [PostCond.noThrow, Std.Do.SPred.down_pure] using hh
      simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_eq
    · -- Step.
      intro acc k _h_ge h_le hinv
      have h_acc_eq : acc = vec_loop_result_at_step secret_as_ntt u_as_ntt k.val := by
        simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using hinv
      subst h_acc_eq
      unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
      by_cases h_lt : k.val < K.val
      · -- `Some k` branch.
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
        -- index_usize v1 k = lift_poly secret[k]; index_usize v2 k = lift_poly u[k].
        have h_lift_S_len : (lift_vec secret_as_ntt).length = K.val := Std.Array.length_eq _
        have h_lift_U_len : (lift_vec u_as_ntt).length = K.val := Std.Array.length_eq _
        set a1 : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          lift_poly secret_as_ntt.val[k.val]! with h_a1_def
        set a2 : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          lift_poly u_as_ntt.val[k.val]! with h_a2_def
        have h_lift_S_val : (lift_vec secret_as_ntt).val[k.val]! = a1 := by
          rw [h_a1_def]; unfold lift_vec
          show (secret_as_ntt.val.map lift_poly)[k.val]! = _
          have h_len_s : secret_as_ntt.val.length = K.val := Std.Array.length_eq _
          rw [getElem!_pos _ k.val (by rw [List.length_map, h_len_s]; exact h_lt)]
          rw [List.getElem_map]
          rw [show secret_as_ntt.val[k.val] = secret_as_ntt.val[k.val]! from
                (getElem!_pos _ k.val (by rw [h_len_s]; exact h_lt)).symm]
        have h_lift_U_val : (lift_vec u_as_ntt).val[k.val]! = a2 := by
          rw [h_a2_def]; unfold lift_vec
          show (u_as_ntt.val.map lift_poly)[k.val]! = _
          have h_len_u : u_as_ntt.val.length = K.val := Std.Array.length_eq _
          rw [getElem!_pos _ k.val (by rw [List.length_map, h_len_u]; exact h_lt)]
          rw [List.getElem_map]
          rw [show u_as_ntt.val[k.val] = u_as_ntt.val[k.val]! from
                (getElem!_pos _ k.val (by rw [h_len_u]; exact h_lt)).symm]
        have h_idx_a1 : Aeneas.Std.Array.index_usize (lift_vec secret_as_ntt) k = .ok a1 := by
          have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (lift_vec secret_as_ntt) k
            (by rw [h_lift_S_len]; exact h_lt)
          rw [h_lift_S_val] at this; exact this
        have h_idx_a2 : Aeneas.Std.Array.index_usize (lift_vec u_as_ntt) k = .ok a2 := by
          have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq (lift_vec u_as_ntt) k
            (by rw [h_lift_U_len]; exact h_lt)
          rw [h_lift_U_val] at this; exact this
        have h_mult_eq : hacspec_ml_kem.ntt.multiply_ntts a1 a2
            = .ok (Spec.multiply_ntts_pure a1 a2) := by
          unfold Spec.multiply_ntts_pure
          rw [HelpersFC.multiply_ntts_eq_pure_array]
        have h_add_eq := Stage4MatrixAddFC.matrix_add_polynomials_eq_ok
          (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val)
          (Spec.multiply_ntts_pure a1 a2)
        set new_acc : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
          ⟨(List.range 256).map (fun n =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val).val[n]!
                (Spec.multiply_ntts_pure a1 a2).val[n]!),
           by simp [List.length_map, List.length_range]⟩ with h_new_acc_def
        have h_new_acc_eq : new_acc
            = vec_loop_result_at_step secret_as_ntt u_as_ntt (k.val + 1) := by
          unfold vec_loop_result_at_step
          apply Subtype.ext
          rw [h_new_acc_def]
          apply List.map_congr_left
          intro n hn_mem
          have hn_lt : n < 256 := List.mem_range.mp hn_mem
          rw [vec_loop_result_at_step_val_lane _ _ _ _ hn_lt]
          rw [vec_loop_lane_at_step_succ]
        have h_body :
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body
                (lift_vec secret_as_ntt) (lift_vec u_as_ntt) p.1 p.2)
              ({ start := k, «end» := K },
                vec_loop_result_at_step secret_as_ntt u_as_ntt k.val)
            = .ok (ControlFlow.cont (({ start := s_iter, «end» := K }
                          : CoreModels.core.ops.range.Range Std.Usize),
                  vec_loop_result_at_step secret_as_ntt u_as_ntt (k.val + 1))) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body
                (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
                { start := k, «end» := K }
                (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
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
                  let a ← Aeneas.Std.Array.index_usize (lift_vec secret_as_ntt) k
                  let a1' ← Aeneas.Std.Array.index_usize (lift_vec u_as_ntt) k
                  let product ← hacspec_ml_kem.ntt.multiply_ntts a a1'
                  let result1 ← hacspec_ml_kem.matrix.add_polynomials
                    (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val) product
                  Aeneas.Std.Result.ok (ControlFlow.cont
                    (({ start := s_iter, «end» := K }
                      : CoreModels.core.ops.range.Range Std.Usize), result1)))
                : Result _) = _
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
        refine ⟨h_lt, rfl, hs_iter_val, ?_⟩
        show (pure (vec_loop_result_at_step secret_as_ntt u_as_ntt (k.val + 1)
                      = vec_loop_result_at_step secret_as_ntt u_as_ntt s_iter.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hs_iter_val]
        rfl
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
            (fun p : CoreModels.core.ops.range.Range Std.Usize ×
                       Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize =>
              hacspec_ml_kem.matrix.multiply_vectors_loop.body
                (lift_vec secret_as_ntt) (lift_vec u_as_ntt) p.1 p.2)
              ({ start := k, «end» := K },
                vec_loop_result_at_step secret_as_ntt u_as_ntt k.val)
            = .ok (ControlFlow.done
                (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val)) := by
          show hacspec_ml_kem.matrix.multiply_vectors_loop.body
                (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
                { start := k, «end» := K }
                (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val) = _
          unfold hacspec_ml_kem.matrix.multiply_vectors_loop.body
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
        show (pure (vec_loop_result_at_step secret_as_ntt u_as_ntt k.val
                      = vec_loop_result_at_step secret_as_ntt u_as_ntt K.val)
              : Result Prop).holds
        simp only [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp]
        intro _
        rw [hk_eq]
        rfl
  obtain ⟨v, hv_eq, hv_post⟩ := triple_exists_ok_fc h_triple
  rw [hv_eq, hv_post]

/-! ### re-derived Helper 1 (`multiply_ntts_lane_eq_canonical_factor`).

    The chunk-lift bilinearity bridge `multiply_ntts_lane_eq_canonical_factor` and its two dependencies (`chunk_at_lift_poly_lane`,
    `ntt_multiply_pure_no_acc_lane_scale`) are `private` to FCTargets. We
    re-derive a public-callable copy here from public primitives
    (`Spec.multiply_ntts_pure_eq_chunked_no_acc`, `zmodOfFE_{add,mul}_pure`,
    `lift_fe_mont_mul_1353_eq_lift_fe`, `PortableVector_elements_length`). -/

/-- `Canonical x → x.val.val < 3329` and the canonical round-trip closer
    (re-derived from public `Canonical`/`FIELD_MODULUS`). -/
private theorem L7_4_Hlp.canon_lt
    (x : hacspec_ml_kem.parameters.FieldElement)
    (hx : libcrux_iot_ml_kem.Spec.Pure.Canonical x) : x.val.val < 3329 := by
  unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hx
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq] at hx; exact hx

private theorem L7_4_Hlp.feOfZMod_zmodOfFE_of_lt
    (x : hacspec_ml_kem.parameters.FieldElement) (hx : x.val.val < 3329) :
    feOfZMod (zmodOfFE x) = x := by
  unfold feOfZMod zmodOfFE
  have hzval : ((x.val.val : ZMod 3329)).val = x.val.val := ZMod.val_natCast_of_lt hx
  rw [hzval]
  have hsval : x.val.val < 2 ^ 16 := by
    have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
    omega
  have hsbv : BitVec.ofNat 16 x.val.val = x.val.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show x.val.val % 2 ^ 16 = x.val.bv.toNat
    rw [Nat.mod_eq_of_lt hsval]; rfl
  show ({ val := ⟨BitVec.ofNat 16 x.val.val⟩ } : hacspec_ml_kem.parameters.FieldElement) = x
  rw [hsbv]

/-- Canonical equality closer: two FEs `< 3329` with equal `zmodOfFE` are equal. -/
private theorem L7_4_Hlp.eq_of_zmod_lt
    (s t : hacspec_ml_kem.parameters.FieldElement)
    (hs : s.val.val < 3329) (ht : t.val.val < 3329) (heq : zmodOfFE s = zmodOfFE t) :
    s = t := by
  rw [← L7_4_Hlp.feOfZMod_zmodOfFE_of_lt s hs,
      ← L7_4_Hlp.feOfZMod_zmodOfFE_of_lt t ht, heq]

/-- Re-derived `ntt_multiply_pure_no_acc_val_q` (the projection is `rfl`-ish). -/
private theorem L7_4_Hlp.no_acc_val_q
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

/-- Re-derived `ntt_multiply_pure_no_acc_lane_scale`: per-lane `c²` bilinearity. -/
private theorem L7_4_Hlp.no_acc_lane_scale
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
  rw [L7_4_Hlp.no_acc_val_q a b _ _ _ _ q h_q,
      L7_4_Hlp.no_acc_val_q am bm _ _ _ _ q h_q]
  rw [h_a (2 * (q / 2)) h_2pi, h_a (2 * (q / 2) + 1) h_2pi1,
      h_b (2 * (q / 2)) h_2pi, h_b (2 * (q / 2) + 1) h_2pi1]
  rcases (show q % 2 = 0 ∨ q % 2 = 1 from by omega) with h_par | h_par
  · rw [if_pos h_par, if_pos h_par]
    apply L7_4_Hlp.eq_of_zmod_lt
    · exact L7_4_Hlp.canon_lt _ (libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _)
    · exact L7_4_Hlp.canon_lt _ (libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _)
    · simp only [zmodOfFE_add_pure, zmodOfFE_mul_pure]; ring
  · have h_par_ne : q % 2 ≠ 0 := by omega
    rw [if_neg h_par_ne, if_neg h_par_ne]
    apply L7_4_Hlp.eq_of_zmod_lt
    · exact L7_4_Hlp.canon_lt _ (libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _)
    · exact L7_4_Hlp.canon_lt _ (libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _)
    · simp only [zmodOfFE_add_pure, zmodOfFE_mul_pure]; ring

set_option maxHeartbeats 1000000 in
/-- Re-derived `chunk_at_lift_poly_lane`. -/
private theorem L7_4_Hlp.chunk_at_lift_poly_lane
    (p : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (j : Nat) (h_j : j < 16) (q : Nat) (h_q : q < 16) :
    (Spec.chunk_at (lift_poly p) j).val[q]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          ((lift_chunk_mont p.coefficients.val[j]!).val[q]!)
          (lift_fe_mont (1353#i16 : Std.I16)) := by
  set x : Std.I16 := (p.coefficients.val[j]!).elements.val[q]! with hx_def
  have h_elem_len : ((p.coefficients.val[j]!).elements.val).length = 16 :=
    libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.PortableVector_elements_length _
  have h_mont : (lift_chunk_mont p.coefficients.val[j]!).val[q]! = lift_fe_mont x := by
    unfold lift_chunk_mont
    show (((p.coefficients.val[j]!).elements.val).map lift_fe_mont)[q]! = lift_fe_mont x
    have h_len : (((p.coefficients.val[j]!).elements.val).map lift_fe_mont).length = 16 := by
      rw [List.length_map]; exact h_elem_len
    rw [getElem!_pos _ q (by rw [h_len]; exact h_q)]
    rw [List.getElem_map]
    rw [show ((p.coefficients.val[j]!).elements.val)[q]
            = ((p.coefficients.val[j]!).elements.val)[q]! from
          (getElem!_pos _ q (by rw [h_elem_len]; exact h_q)).symm]
  have h_plain : (Spec.chunk_at (lift_poly p) j).val[q]! = lift_fe x := by
    unfold Spec.chunk_at
    show ((List.range 16).map (fun j' => (lift_poly p).val[16 * j + j']!))[q]! = lift_fe x
    have h_len_outer : ((List.range 16).map
        (fun j' => (lift_poly p).val[16 * j + j']!)).length = 16 := by simp
    rw [getElem!_pos _ q (by rw [h_len_outer]; exact h_q)]
    rw [List.getElem_map, List.getElem_range]
    have h_lane : 16 * j + q < 256 := by omega
    unfold lift_poly
    show ((List.range 256).map (fun n =>
            lift_fe (p.coefficients.val[n / 16]!).elements.val[n % 16]!))[16 * j + q]! = lift_fe x
    have h_len_inner : ((List.range 256).map (fun n =>
            lift_fe (p.coefficients.val[n / 16]!).elements.val[n % 16]!)).length = 256 := by simp
    rw [getElem!_pos _ (16 * j + q) (by rw [h_len_inner]; exact h_lane)]
    rw [List.getElem_map, List.getElem_range]
    have h_div : (16 * j + q) / 16 = j := by omega
    have h_mod : (16 * j + q) % 16 = q := by omega
    rw [h_div, h_mod]
  rw [h_mont, h_plain]
  rw [Impl.lift_fe_mont_mul_1353_eq_lift_fe]

/-- Re-derived Helper 1: `multiply_ntts_pure (lift_poly a)(lift_poly b)` lane ℓ
    equals the chunk-lift `no_acc` lane scaled by `(lift_fe_mont 1353)²`. -/
private theorem L7_4_Hlp.multiply_ntts_lane_eq_canonical_factor
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
  rw [Spec.multiply_ntts_pure_eq_chunked_no_acc]
  unfold Spec.flatten_chunks
  show ((List.range 256).map (fun j =>
          (((List.range 16).map (fun j' =>
              Spec.ntt_multiply_pure_no_acc
                (Spec.chunk_at (lift_poly a) j') (Spec.chunk_at (lift_poly b) j')
                (Spec.zeta_at (64 + 4 * j')) (Spec.zeta_at (64 + 4 * j' + 1))
                (Spec.zeta_at (64 + 4 * j' + 2)) (Spec.zeta_at (64 + 4 * j' + 3)))
              )[j / 16]!).val[j % 16]!))[ℓ]! = _
  rw [getElem!_pos _ ℓ (by simp [List.length_map, List.length_range, hℓ])]
  rw [List.getElem_map, List.getElem_range]
  rw [getElem!_pos _ (ℓ / 16) (by simp [List.length_map, List.length_range, h_div_lt])]
  rw [List.getElem_map, List.getElem_range]
  exact L7_4_Hlp.no_acc_lane_scale
    (Spec.chunk_at (lift_poly a) (ℓ / 16)) (lift_chunk_mont a.coefficients.val[ℓ / 16]!)
    (Spec.chunk_at (lift_poly b) (ℓ / 16)) (lift_chunk_mont b.coefficients.val[ℓ / 16]!)
    (lift_fe_mont (1353#i16 : Std.I16))
    (fun k h_k => L7_4_Hlp.chunk_at_lift_poly_lane a (ℓ / 16) h_div_lt k h_k)
    (fun k h_k => L7_4_Hlp.chunk_at_lift_poly_lane b (ℓ / 16) h_div_lt k h_k)
    (Spec.zeta_at (64 + 4 * (ℓ / 16))) (Spec.zeta_at (64 + 4 * (ℓ / 16) + 1))
    (Spec.zeta_at (64 + 4 * (ℓ / 16) + 2)) (Spec.zeta_at (64 + 4 * (ℓ / 16) + 3))
    (ℓ % 16) h_mod_lt

/-! ### local canonical-determination helper + per-lane bridge. -/

/-- Local copy of `eq_of_zmod_lane_canon` (private in ComputeMessage.Hacspec):
    two canonical 256-FE arrays that agree on every `zmodOfFE` lane are equal. -/
private theorem eq_of_zmod_lane_canon_local
    (u v : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hcu : ∀ j : Nat, j < 256 → libcrux_iot_ml_kem.Spec.Pure.Canonical (u.val[j]!))
    (hcv : ∀ j : Nat, j < 256 → libcrux_iot_ml_kem.Spec.Pure.Canonical (v.val[j]!))
    (hz : ∀ j : Nat, j < 256 → zmodOfFE (u.val[j]!) = zmodOfFE (v.val[j]!)) :
    u = v := by
  have h_canon_round : ∀ (x : hacspec_ml_kem.parameters.FieldElement),
      libcrux_iot_ml_kem.Spec.Pure.Canonical x → feOfZMod (zmodOfFE x) = x :=
    fun x hx => L7_4_Hlp.feOfZMod_zmodOfFE_of_lt x (L7_4_Hlp.canon_lt x hx)
  apply Subtype.ext
  apply List.ext_getElem
  · rw [Aeneas.Std.Array.length_eq u, Aeneas.Std.Array.length_eq v]
  · intro j hj1 _hj2
    have hj : j < 256 := by rw [Aeneas.Std.Array.length_eq u] at hj1; simpa using hj1
    have heq : u.val[j]! = v.val[j]! := by
      rw [← h_canon_round (u.val[j]!) (hcu j hj),
          ← h_canon_round (v.val[j]!) (hcv j hj), hz j hj]
    have huj : u.val[j]! = u.val[j] :=
      getElem!_pos u.val j (by rw [Aeneas.Std.Array.length_eq u]; exact hj)
    have hvj : v.val[j]! = v.val[j] :=
      getElem!_pos v.val j (by rw [Aeneas.Std.Array.length_eq v]; exact hj)
    rw [← huj, ← hvj]; exact heq

/-- Foldl congruence in `ZMod 3329` across a common multiplicative `factor`:
    if the seeds and every per-step summand of two `add_pure`-foldls relate by
    `zmodOfFE (aₓ) = factor * zmodOfFE (bₓ)`, then so do the foldl results. -/
private theorem zmodOfFE_foldl_add_pure_factor {α : Type} (L : List α)
    (fa fb : α → hacspec_ml_kem.parameters.FieldElement)
    (seedA seedB : hacspec_ml_kem.parameters.FieldElement) (factor : ZMod 3329)
    (h_seed : zmodOfFE seedA = factor * zmodOfFE seedB)
    (h_step : ∀ c ∈ L, zmodOfFE (fa c) = factor * zmodOfFE (fb c)) :
    zmodOfFE (L.foldl
        (fun s c => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s (fa c)) seedA)
      = factor * zmodOfFE (L.foldl
          (fun s c => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s (fb c)) seedB) := by
  induction L generalizing seedA seedB with
  | nil => simpa using h_seed
  | cons h t ih =>
    simp only [List.foldl_cons]
    apply ih
    · rw [zmodOfFE_add_pure, zmodOfFE_add_pure, h_seed, h_step h (by simp)]
      ring
    · intro c hc; exact h_step c (by simp [hc])

/-- Any `add_pure`-foldl over a canonical seed is canonical (the `nil` case is
    the seed; every `cons` step is an `add_pure`, hence canonical). -/
private theorem foldl_add_pure_canonical {α : Type} (L : List α)
    (f : α → hacspec_ml_kem.parameters.FieldElement)
    (seed : hacspec_ml_kem.parameters.FieldElement)
    (h_seed : libcrux_iot_ml_kem.Spec.Pure.Canonical seed) :
    libcrux_iot_ml_kem.Spec.Pure.Canonical
      (L.foldl
        (fun s c => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s (f c)) seed) := by
  induction L generalizing seed with
  | nil => simpa using h_seed
  | cons h t ih =>
    simp only [List.foldl_cons]
    exact ih _ (libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _)

private theorem zero_fe_canonical :
    libcrux_iot_ml_kem.Spec.Pure.Canonical
      ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement) := by
  unfold libcrux_iot_ml_kem.Spec.Pure.Canonical
  have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
  rw [hq]; decide

set_option maxHeartbeats 1000000 in
/-- **A — acc-bridge / "crux" (CLOSED).**

    Relates the hacspec `multiply_vectors` (on `lift_vec`-lifts) to the loop
    accumulator's reduced value, scaled by `R = 2285`. Statement numerically
    Factor 2285 = R. RHS kept in the
    `scaleZ 2285 (mont_strip ∘ poly_reducing ∘ to_slice acc2)` form per the
    FC-glue requirement.

    Proof: reduces `multiply_vectors` to the per-lane `add_pure`-foldl
    array `vec_loop_result_at_step`; both sides are canonical, so equality
    follows lane-wise in `ZMod 3329`. The per-lane match composes:
    `Spec.multiply_ntts_pure_eq_chunked_no_acc`/`multiply_ntts_lane_eq_canonical_factor`
    (LHS lane = `mul_pure (no_acc-lane) (1353·1353)`), `h_char` (the S1 loop
    invariant: `poly_reducing(acc2)` lane = the same `no_acc` foldl-sum), and
    the `2285 = R` factor identity (`zmodOfFE (lift_fe_mont 1353) = 1353·169`,
    `2285·(1353·169·169·169) ≡ 1353·169·169` collapse), all in `ZMod 3329`. -/
theorem compute_message_acc_bridge {K : Std.Usize}
    (secret_as_ntt u_as_ntt : Std.Array
      (libcrux_iot_ml_kem.polynomial.PolynomialRingElement
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) K)
    (acc_init : Std.Array Std.I32 256#usize)
    (acc2 : Std.Array Std.I32 256#usize)
    (h_acc_init_zero : ∀ n : Nat, n < 256 → (acc_init.val[n]!).val = 0)
    (_h_secret_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((secret_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (_h_u_bnd : ∀ k : Fin K.val, ∀ i j : Fin 16,
        ((u_as_ntt.val[k.val]!.coefficients.val[i.val]!).elements.val[j.val]!).val.natAbs ≤ 3328)
    (h_char : (S1LoopFC.loop_inv secret_as_ntt u_as_ntt acc_init K acc2).holds) :
    hacspec_ml_kem.matrix.multiply_vectors (lift_vec secret_as_ntt) (lift_vec u_as_ntt)
      = .ok (scaleZ 2285 (Impl.mont_strip_pure
               (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)))) := by
  rw [multiply_vectors_eq secret_as_ntt u_as_ntt]
  -- Destructure `h_char`'s conjunct (1): the per-lane `no_acc` foldl characterization.
  obtain ⟨h_inv_acc, _⟩ := by
    simpa [Aeneas.Std.Result.holds, Std.Do.Triple, Std.Do.WP.wp] using h_char
  -- Abbreviations.
  set P : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    Impl.mont_strip_pure
      (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)) with hP_def
  congr 1
  -- Equality of two canonical 256-arrays by per-lane `zmodOfFE`.
  apply eq_of_zmod_lane_canon_local
  · -- LHS lanes canonical (`add_pure`-foldl ⇒ canonical via the cons step;
    --  the empty foldl is the seed `⟨0#u16⟩`, also canonical).
    intro n hn
    rw [vec_loop_result_at_step_val_lane _ _ _ _ hn]
    unfold vec_loop_lane_at_step
    exact foldl_add_pure_canonical _ _ _ zero_fe_canonical
  · -- RHS lanes canonical (`scaleZ` lane = `feOfZMod _`, always `< 3329`).
    intro n hn
    unfold scaleZ
    show libcrux_iot_ml_kem.Spec.Pure.Canonical
      (((List.range 256).map (fun j => feOfZMod ((2285 : ZMod 3329) * zmodOfFE (P.val[j]!))))[n]!)
    rw [getElem!_pos _ n (by simp [List.length_map, List.length_range, hn])]
    rw [List.getElem_map, List.getElem_range]
    unfold feOfZMod libcrux_iot_ml_kem.Spec.Pure.Canonical
    have hq : hacspec_ml_kem.parameters.FIELD_MODULUS.val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; rfl
    rw [hq]
    show (⟨BitVec.ofNat 16 (((2285 : ZMod 3329) * zmodOfFE (P.val[n]!)).val)⟩
            : Std.U16).val < 3329
    have h_lt16 : (((2285 : ZMod 3329) * zmodOfFE (P.val[n]!)).val) < 2 ^ 16 := by
      have := ZMod.val_lt ((2285 : ZMod 3329) * zmodOfFE (P.val[n]!))
      omega
    show (BitVec.ofNat 16 (((2285 : ZMod 3329) * zmodOfFE (P.val[n]!)).val)).toNat < 3329
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h_lt16]
    exact ZMod.val_lt _
  · -- Per-lane `zmodOfFE` equality.
    intro n hn
    -- RHS lane zmod = 2285 * zmodOfFE (mont_strip lane).
    rw [hP_def, scaleZ_lane 2285 _ n hn]
    -- mont_strip lane = mul_pure (poly_reducing lane) (lift_fe_mont 1353).
    have h_ms : (Impl.mont_strip_pure
        (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2))).val[n]!
        = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)).val[n]!)
            (lift_fe_mont (1353#i16 : Std.I16)) := by
      unfold Impl.mont_strip_pure
      show ((List.range 256).map (fun i =>
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            ((Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)).val[i]!)
            (lift_fe_mont (1353#i16 : Std.I16))))[n]! = _
      rw [getElem!_pos _ n (by simp [List.length_map, List.length_range, hn])]
      rw [List.getElem_map, List.getElem_range]
    rw [h_ms, zmodOfFE_mul_pure, zmodOfFE_lift_fe_mont]
    have h1353 : (((1353#i16 : Std.I16).val : ZMod 3329)) = 1353 := by decide
    rw [h1353]
    -- poly_reducing lane = mont_reduce_pure (lift_fe_int acc2[n].val) (via to_slice .val).
    have h_pr : (Spec.poly_reducing_from_i32_array_pure (Aeneas.Std.Array.to_slice acc2)).val[n]!
        = Spec.mont_reduce_pure (lift_fe_int (acc2.val[n]!).val) := by
      unfold Spec.poly_reducing_from_i32_array_pure
      show ((List.range 256).map (fun i =>
          Spec.mont_reduce_pure (lift_fe_int ((Aeneas.Std.Array.to_slice acc2).val[i]!).val)))[n]!
        = _
      rw [getElem!_pos _ n (by simp [List.length_map, List.length_range, hn])]
      rw [List.getElem_map, List.getElem_range]
      rw [Aeneas.Std.Array.val_to_slice]
    rw [h_pr]
    -- LHS lane = vec_loop foldl over `multiply_ntts_pure` lanes.
    rw [vec_loop_result_at_step_val_lane _ _ _ _ hn]
    unfold vec_loop_lane_at_step
    -- Per-lane (n = 16*(n/16) + n%16) shorthands.
    set j := n / 16 with hj_def
    set ℓ := n % 16 with hℓ_def
    have hj_lt : j < 16 := by omega
    have hℓ_lt : ℓ < 16 := Nat.mod_lt _ (by decide)
    have hn_eq : n = 16 * j + ℓ := by rw [hj_def, hℓ_def]; omega
    -- `h_char` at (j, ℓ): the `no_acc` foldl equals `mont_reduce_pure (lift_fe_int acc2[n])`.
    have h_char_jℓ := h_inv_acc j hj_lt ℓ hℓ_lt
    rw [show 16 * j + ℓ = n from hn_eq.symm] at h_char_jℓ
    -- Rewrite RHS foldl-FE using h_char.
    rw [h_char_jℓ]
    -- Now: zmodOfFE (LHS foldl over multiply_ntts_pure lanes)
    --    = 2285 * (zmodOfFE (RHS foldl over no_acc lanes) * (1353 * 169)).
    -- Apply the factor-foldl congruence with factor = (1353*169)^2 = 1353.
    set fb : Nat → hacspec_ml_kem.parameters.FieldElement := fun c =>
      (Spec.ntt_multiply_pure_no_acc
          (lift_chunk_mont (secret_as_ntt.val[c]!.coefficients.val[j]!))
          (lift_chunk_mont (u_as_ntt.val[c]!.coefficients.val[j]!))
          (Spec.zeta_at (64 + 4 * j))
          (Spec.zeta_at (64 + 4 * j + 1))
          (Spec.zeta_at (64 + 4 * j + 2))
          (Spec.zeta_at (64 + 4 * j + 3))).val[ℓ]! with hfb_def
    set fa : Nat → hacspec_ml_kem.parameters.FieldElement := fun c =>
      (Spec.multiply_ntts_pure
          (lift_poly secret_as_ntt.val[c]!) (lift_poly u_as_ntt.val[c]!)).val[n]! with hfa_def
    set seedB : hacspec_ml_kem.parameters.FieldElement :=
      Spec.mont_reduce_pure (lift_fe_int (acc_init.val[n]!).val) with hseedB_def
    have h_factor_congr :
        zmodOfFE ((List.range K.val).foldl
            (fun s c => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s (fa c))
            ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement))
          = (1353 : ZMod 3329)
            * zmodOfFE ((List.range K.val).foldl
                (fun s c => libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure s (fb c))
                seedB) := by
      apply zmodOfFE_foldl_add_pure_factor
      · -- seeds: both have zmod 0.
        rw [hseedB_def]
        have h0 : (acc_init.val[n]!).val = 0 := h_acc_init_zero n hn
        rw [h0]
        -- zmodOfFE ⟨0#u16⟩ = 0 and 1353 * zmodOfFE (mont_reduce_pure (lift_fe_int 0)) = 0.
        have hL : zmodOfFE ({ val := 0#u16 } : hacspec_ml_kem.parameters.FieldElement) = 0 := by
          unfold zmodOfFE; decide
        have hR : zmodOfFE (Spec.mont_reduce_pure (lift_fe_int (0 : Int))) = 0 := by
          unfold Spec.mont_reduce_pure lift_fe_int
          rw [zmodOfFE_feOfZMod, zmodOfFE_feOfZMod]
          push_cast; ring
        rw [hL, hR]; ring
      · -- per-step factor: zmodOfFE (fa c) = 1353 * zmodOfFE (fb c).
        intro c _
        simp only [hfa_def, hfb_def]
        -- Helper 1: multiply_ntts_pure lane n = mul_pure (no_acc-lane at ℓ) (1353²).
        rw [show n = 16 * j + ℓ from hn_eq]
        have h_lane := L7_4_Hlp.multiply_ntts_lane_eq_canonical_factor
          secret_as_ntt.val[c]! u_as_ntt.val[c]! (16 * j + ℓ) (by omega)
        have hdiv : (16 * j + ℓ) / 16 = j := by omega
        have hmod : (16 * j + ℓ) % 16 = ℓ := by omega
        rw [hdiv, hmod] at h_lane
        rw [h_lane, zmodOfFE_mul_pure, zmodOfFE_mul_pure, zmodOfFE_lift_fe_mont]
        have h1353' : (((1353#i16 : Std.I16).val : ZMod 3329)) = 1353 := by decide
        rw [h1353']
        -- (no_acc-lane) * (1353*169 * (1353*169)) = 1353 * (no_acc-lane).
        have hfac : ((1353 : ZMod 3329) * 169) * ((1353 : ZMod 3329) * 169) = 1353 := by decide
        rw [show (zmodOfFE _ * ((1353 : ZMod 3329) * 169 * (1353 * 169)))
              = (1353 : ZMod 3329) * 169 * (1353 * 169) * zmodOfFE _ from by ring]
        rw [hfac]
    rw [h_factor_congr]
    -- Goal: 1353 * zmodOfFE (foldl_fb) = 2285 * (zmodOfFE (foldl_fb) * (1353 * 169)).
    -- Both sides equal 1353 * zmodOfFE(foldl_fb) since 2285 * (1353*169) = 2285*2285 = 1353.
    have hRfac : (2285 : ZMod 3329) * ((1353 : ZMod 3329) * 169) = 1353 := by decide
    rw [show (2285 : ZMod 3329) * (zmodOfFE _ * (1353 * 169))
          = (2285 : ZMod 3329) * (1353 * 169) * zmodOfFE _ from by ring]
    rw [hRfac]

end libcrux_iot_ml_kem.Matrix.ComputeMessage.Impl