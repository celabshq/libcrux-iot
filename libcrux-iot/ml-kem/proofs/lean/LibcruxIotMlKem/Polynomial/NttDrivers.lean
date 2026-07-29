/-
  # `Equivalence/L3_NTTDrivers.lean` — Layer 3 NTT driver-loop Triples.

  L3.x Triples for the `ntt_at_layer_N` driver loops in `ntt.rs`:

  - **L3.1 `ntt_at_layer_1_spec`** — innermost layer: a 16-iter loop over
    a `PolynomialRingElement`'s 16 PortableVectors, each call dispatched
    via the trait's `ntt_layer_1_step` (which forwards to L2.2's
    `vector.portable.ntt.ntt_layer_1_step`). Per-coefficient bound goes
    `7·3328 → 8·3328`; `zeta_i.val : 63 → 127`.
  - **L3.2 `ntt_at_layer_2_spec`** — 2 ζ lookups/iter, dispatches
    `ntt_layer_2_step`. Bound `6·3328 → 7·3328`; `zeta_i : 31 → 63`.
  - **L3.3 `ntt_at_layer_3_spec`** — 1 ζ lookup/iter, dispatches
    `ntt_layer_3_step`. Bound `5·3328 → 6·3328`; `zeta_i : 15 → 31`.

  Specialised to `Vector := PortableVector` with the concrete
  `Libcrux_iot_ml_kemVectorTraitsOperations` instance. The instance's
  `ntt_layer_N_step` field reduces (via `@[reducible]`) to
  `…Operations.ntt_layer_N_step`, which is itself a thin wrapper for
  `vector.portable.ntt.ntt_layer_N_step` — L2.2 / L2.3 / L2.4 fire directly.

  1516-1525) for F*-port references.
-/
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Polynomial.PolyOps

set_option mvcgen.warning false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace libcrux_iot_ml_kem.Polynomial.NttDrivers
open libcrux_iot_ml_kem.Polynomial.PolyOps libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open CoreModels Aeneas Aeneas.Std Result ControlFlow Std.Do
open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper

/-! ## Inhabited instances — needed for `.val[j]!` projections.

`Std.Array α n` uses `List.get!` under the hood, which requires
`Inhabited α`. The L2/L1 layers don't trigger this because they only
project into `Array I16 16`. The L3 layer projects into `Array
PortableVector 16` and `Array (PolynomialRingElement PortableVector) K`,
so we register the canonical zero-witness instances locally. -/

instance : Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

instance {Vector : Type} [Inhabited Vector] {K : Std.Usize} :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## Local helpers — Triple ↔ Result.ok bridges, pure-prop holds. -/

private theorem triple_of_ok_l3 {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply, hp]

private theorem triple_exists_ok_l3 {α : Type} {x : Result α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) :
    ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v => exact ⟨v, rfl, (by subst hx; simpa [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply] using h)⟩
  | .fail _ => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div => exact absurd h (by simp [Std.Do.Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

private theorem pure_prop_holds_l3 {P : Prop} (h : P) : (pure P : Result Prop).holds := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp]; intro _; exact h

private theorem of_pure_prop_holds_l3 {P : Prop}
    (h : (pure P : Result Prop).holds) : P := by
  simp only [Aeneas.Std.Result.holds, Std.Do.Triple, WP.wp] at h; exact h trivial

/-! ## Small `Usize.add` helper — produces `.val`-form equations. -/

private theorem usize_add_ok_eq (x y : Std.Usize)
    (h_max : x.val + y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x + y : Result Std.Usize) = .ok z ∧ z.val = x.val + y.val := by
  have hT := Std.Usize.add_spec h_max
  -- hT : x + y ⦃ z => (↑z : Nat) = ↑x + ↑y ⦄ — this is `WP.spec`, not Triple.
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  refine ⟨z, h_eq, ?_⟩
  show z.val = x.val + y.val
  exact h_v

/-! ## `polynomial.zeta_spec` helper

The `ZETAS_TIMES_MONTGOMERY_R` table has 128 `Std.I16` entries. Each is
in absolute value at most 1664 (in fact, all entries here are < 1700;
each fits in a Montgomery-reduced field element). `polynomial.zeta i`
performs a single bounded `Array.index_usize` on that table.

We expose this through a single decidable bound: the table's underlying
`.val` (a 128-element `List Std.I16`) has every element ≤ 1664 in
absolute value. After unsealing the `@[irreducible]` table this is a
finite check that `decide` discharges.
-/

unseal libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R in
private theorem ZETAS_TIMES_MONTGOMERY_R_bound :
    ∀ i : Nat, i < 128 →
      ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i]!).val.natAbs ≤ 1664 := by
  intro i hi
  interval_cases i <;> decide

@[spec]
theorem polynomial.zeta_spec (i : Std.Usize) (hi : i.val < 128) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.polynomial.zeta i
    ⦃ ⇓ r => ⌜ r.val.natAbs ≤ 1664 ⌝ ⦄ := by
  -- `polynomial.zeta i = Array.index_usize ZETAS_TIMES_MONTGOMERY_R i`.
  have h_len :
      (libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).length = 128 :=
    Std.Array.length_eq _
  have h_idx :
      Aeneas.Std.Array.index_usize
        libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R i
      = .ok ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!) :=
    array_index_usize_ok_eq _ i (by rw [h_len]; exact hi)
  have h_ok :
      libcrux_iot_ml_kem.polynomial.zeta i
        = .ok ((libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R).val[i.val]!) := by
    unfold libcrux_iot_ml_kem.polynomial.zeta
    rw [h_idx]
  exact triple_of_ok_l3 h_ok (ZETAS_TIMES_MONTGOMERY_R_bound i.val hi)

/-! ## L3.1 — `ntt_at_layer_1_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up four ζ-values via
`polynomial.zeta` (indices `zeta_i.val + 1 .. zeta_i.val + 4`),
dispatches `OpsInst.ntt_layer_1_step`, and writes back. `zeta_i.val`
advances by 4; the bound per coefficient goes `7·3328 → 8·3328`.

We specialise to `Vector := PortableVector` and the concrete trait
instance. The `@[reducible]` instance field reduces
`OpsInst.ntt_layer_1_step a z0 z1 z2 z3` to
`vector.portable.ntt.ntt_layer_1_step a z0 z1 z2 z3` (mod a trivial
`Result.ok` wrap), which is L2.2's target.

Loop invariant after `k` iterations (`k.val ∈ [0, 16]`), state
`(cur_zeta_i, cur_re)`:
  - `cur_zeta_i.val = 63 + 4 * k.val`
  - For `j < k.val`, all 16 elements of
    `cur_re.coefficients[j]` are bounded by `8 * 3328`.
  - For `j ≥ k.val`, `cur_re.coefficients[j] = re.coefficients[j]`
    (so per `h_pre`, all 16 elements are bounded by `7 * 3328`). -/

namespace Layer1

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

/-- Step-local accumulator type — explicitly named to keep `loop_range_spec_usize`'s
    `β` parameter mounted to a concrete type for inference. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 63 + 4 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 8 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Step post (named to keep the `match` constant canonical across sites). -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end Layer1

/-- Per-iteration step lemma: each body call advances `zeta_i` by 4 and
    transforms `re.coefficients[k]` from a `≤ 7·3328` PortableVector to
    a `≤ 8·3328` one (preserving all other indices and the bound chain). -/
private theorem ntt_at_layer_1_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328)
    (acc : Layer1.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 63 + 4 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 8 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer1.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`.
    -- Bound chain: acc.1.val = 63 + 4*k.val with k.val < 16, so
    -- acc.1.val ≤ 123 and acc.1.val + 4 ≤ 127. Each Usize.add stays
    -- well within Std.Usize.max (≥ 2^32 - 1).
    have h_acc1_lt : acc.1.val ≤ 123 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_um3 : (3#usize : Std.Usize).val = 3 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val arithmetic: zi1.val = acc.1.val + 1 = 64 + 4*k.val ≤ 124.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    -- 5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- 6) `zi1 + 2`.
    have h_zi5_max : zi1.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]; scalar_tac
    obtain ⟨zi5, h_zi5_eq, h_zi5_val⟩ :=
      usize_add_ok_eq zi1 2#usize h_zi5_max
    have h_zi5_val_arith : zi5.val = acc.1.val + 3 := by
      rw [h_zi5_val, h_um2, h_zi1_val_arith]
    have h_zi5_lt : zi5.val < 128 := by rw [h_zi5_val_arith]; omega
    -- 7) `polynomial.zeta zi5`.
    obtain ⟨z3, h_z3_eq, h_z3_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi5 h_zi5_lt)
    -- 8) `zi1 + 3`.
    have h_zi7_max : zi1.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um3]; scalar_tac
    obtain ⟨zi7, h_zi7_eq, h_zi7_val⟩ :=
      usize_add_ok_eq zi1 3#usize h_zi7_max
    have h_zi7_val_arith : zi7.val = acc.1.val + 4 := by
      rw [h_zi7_val, h_um3, h_zi1_val_arith]
    have h_zi7_lt : zi7.val < 128 := by rw [h_zi7_val_arith]; omega
    -- 9) `polynomial.zeta zi7`.
    obtain ⟨z4, h_z4_eq, h_z4_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi7 h_zi7_lt)
    -- 10) `OpsInst.ntt_layer_1_step t z1 z2 z3 z4`. Reduces via the
    -- @[reducible] instance to `vector.portable.ntt.ntt_layer_1_step`,
    -- to which L2.2 applies. Pre: t's elements ≤ 7·3328 (it's
    -- `re.coefficients[k]` via h_acc_undone + h_pre).
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 7 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_1_step_spec t z1 z2 z3 z4
        h_z1_bd h_z2_bd h_z3_bd h_z4_bd h_t_bd)
    -- Set the next-state values.
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer1.Acc := (zi7, { coefficients := a }) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      -- Force complete let-Prod-match-on-Some normalization via plain
      -- `simp` (NOT `simp only`) — this engages β-iota reductions that
      -- `simp only` skips. Compose all step hypotheses simultaneously.
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq,
            h_z2_eq, h_zi5_eq, h_z3_eq, h_zi7_eq, h_z4_eq]
      -- After simp, only the final `OpsInst.ntt_layer_1_step` remains
      -- (the trait instance's outer `do`-wrapper is `@[reducible]` and
      -- forwards to `vector.portable.ntt.ntt_layer_1_step`; simp doesn't
      -- unfold by default). Unfold the instance projection definitionally,
      -- then close via `h_t1_eq`.
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step t z1 z2 z3 z4
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi7,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer1.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer1.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    -- Now: invariant at (s, acc').
    apply pure_prop_holds_l3
    -- Three conjuncts of Layer1.inv at (s, acc').
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi7.val = 63 + 4 * s.val.
      show zi7.val = 63 + 4 * s.val
      rw [h_zi7_val_arith, h_zeta_acc, hs_val]; ring
    · -- All j < s.val are bounded by 8*3328.
      intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k.val: unchanged by the set, use h_acc_done.
        have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · -- j = k.val: it's t1.
        subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · -- All j ≥ s.val are unchanged.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    -- Need (acc.1, acc.2) = acc as a pair; for a Prod, this is definitional.
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show Layer1.step_post re k (.done acc)
    unfold Layer1.step_post
    show (Layer1.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_1_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 63)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 127
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 8 * 3328 ⌝ ⦄ := by
  -- Reduce the top wrapper to the inner loop.
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer1.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer1.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · -- Step lemma application.
    intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_1_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer1.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1.step_post] using hP
    · have hP : Layer1.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1.step_post] using hP

/-! ## L3.1.B — `ntt_at_layer_1_spec_B`

Nat-`bnd`-parameterised mirror of `ntt_at_layer_1_spec` (L3.1). Same
driver loop (16 iterations) and same ζ-thread (`63 → 127`); the
per-coefficient input bound `7 * 3328` is replaced by a `Nat`
parameter `bnd` and the output bound becomes `bnd + 3328`. The
precondition `bnd ≤ 8 * 3328` matches the upstream
`ntt_layer_1_step_spec_bnd` requirement.

The existing `ntt_at_layer_1_spec` is the `bnd = 7 * 3328`
instantiation and is left untouched. -/

namespace Layer1Bounded

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant (Nat-bnd parameterised). Done lanes ≤ `bnd + 3328`;
    undone lanes still equal `re.coefficients[j]` (per `h_pre`, these
    are ≤ `bnd`). -/
def inv_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 63 + 4 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv_B bnd re iter'.start acc').holds
  | .done y => (inv_B bnd re 16#usize y).holds

end Layer1Bounded

/-- Per-iteration step lemma (Nat-bnd parameterised). Mirrors
    `ntt_at_layer_1_step_lemma` but threads `bnd` and dispatches via
    `ntt_layer_1_step_spec_bnd`. -/
private theorem ntt_at_layer_1_step_lemma_B
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd)
    (acc : Layer1Bounded.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 63 + 4 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer1Bounded.step_post_B bnd re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`.
    have h_acc1_lt : acc.1.val ≤ 123 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_um3 : (3#usize : Std.Usize).val = 3 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    -- 5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- 6) `zi1 + 2`.
    have h_zi5_max : zi1.val + (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]; scalar_tac
    obtain ⟨zi5, h_zi5_eq, h_zi5_val⟩ :=
      usize_add_ok_eq zi1 2#usize h_zi5_max
    have h_zi5_val_arith : zi5.val = acc.1.val + 3 := by
      rw [h_zi5_val, h_um2, h_zi1_val_arith]
    have h_zi5_lt : zi5.val < 128 := by rw [h_zi5_val_arith]; omega
    -- 7) `polynomial.zeta zi5`.
    obtain ⟨z3, h_z3_eq, h_z3_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi5 h_zi5_lt)
    -- 8) `zi1 + 3`.
    have h_zi7_max : zi1.val + (3#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um3]; scalar_tac
    obtain ⟨zi7, h_zi7_eq, h_zi7_val⟩ :=
      usize_add_ok_eq zi1 3#usize h_zi7_max
    have h_zi7_val_arith : zi7.val = acc.1.val + 4 := by
      rw [h_zi7_val, h_um3, h_zi1_val_arith]
    have h_zi7_lt : zi7.val < 128 := by rw [h_zi7_val_arith]; omega
    -- 9) `polynomial.zeta zi7`.
    obtain ⟨z4, h_z4_eq, h_z4_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi7 h_zi7_lt)
    -- 10) `OpsInst.ntt_layer_1_step t z1 z2 z3 z4` — `_bnd` form.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ bnd := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_1_step_spec_bnd t z1 z2 z3 z4 bnd h_bnd
        h_z1_bd h_z2_bd h_z3_bd h_z4_bd h_t_bd)
    -- Set the next-state values.
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer1Bounded.Acc := (zi7, { coefficients := a }) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq,
            h_z2_eq, h_zi5_eq, h_z3_eq, h_zi7_eq, h_z4_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_1_step t z1 z2 z3 z4
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi7,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer1Bounded.step_post_B bnd re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer1Bounded.step_post_B
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · show zi7.val = 63 + 4 * s.val
      rw [h_zi7_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer1Bounded.step_post_B bnd re k (.done acc)
    unfold Layer1Bounded.step_post_B
    show (Layer1Bounded.inv_B bnd re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_1_spec_B
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 63)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_1
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 127
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_1_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer1Bounded.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer1Bounded.inv_B bnd re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_1_step_lemma_B re bnd h_bnd h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer1Bounded.step_post_B bnd re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1Bounded.step_post_B] using hP
    · have hP : Layer1Bounded.step_post_B bnd re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer1Bounded.step_post_B] using hP

/-! ## L3.2 — `ntt_at_layer_2_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up two ζ-values via
`polynomial.zeta` (indices `zeta_i.val + 1` and `zeta_i.val + 2`),
dispatches `OpsInst.ntt_layer_2_step`, and writes back. `zeta_i.val`
advances by 2 per iter (state stores `zeta_i1 + 1 = zeta_i + 2`); the
bound per coefficient goes `6·3328 → 7·3328`. -/

namespace Layer2

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 31 + 2 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 7 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end Layer2

private theorem ntt_at_layer_2_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328)
    (acc : Layer2.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 31 + 2 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 7 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer2.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`. Bound chain: acc.1.val = 31 + 2*k.val with
    -- k.val < 16, so acc.1.val ≤ 61 and acc.1.val + 2 ≤ 63.
    have h_acc1_lt : acc.1.val ≤ 61 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val = acc.1.val + 1 = 32 + 2*k.val ≤ 62 < 128.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `zi1 + 1`.
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    -- 5) `polynomial.zeta zi3`.
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- 6) `OpsInst.ntt_layer_2_step t z1 z2`. L2.3 fires after instance
    -- reduces. Pre: t's elements ≤ 6·3328.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 6 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_2_step_spec t z1 z2 h_z1_bd h_z2_bd h_t_bd)
    -- Next-state values: state stores `zi3` (= zeta_i + 2).
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer2.Acc := (zi3, { coefficients := a }) with hacc'_def
    -- Compose the whole body into one `.ok` equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq, h_z2_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step t z1 z2
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi3,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer2.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer2.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi3.val = 31 + 2 * s.val.
      show zi3.val = 31 + 2 * s.val
      rw [h_zi3_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer2.step_post re k (.done acc)
    unfold Layer2.step_post
    show (Layer2.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_2_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 31)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 63
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 7 * 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer2.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer2.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_2_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer2.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2.step_post] using hP
    · have hP : Layer2.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2.step_post] using hP

/-! ## L3.2.B — `ntt_at_layer_2_spec_B`

Nat-`bnd`-parameterised mirror of `ntt_at_layer_2_spec` (L3.2). Same
driver loop (16 iterations) and same ζ-thread (`31 → 63`); per-iter
two ζ lookups, dispatches `ntt_layer_2_step_spec_bnd`. Input bound
`6 * 3328` → `bnd`; output bound `7 * 3328` → `bnd + 3328`. -/

namespace Layer2Bounded

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 31 + 2 * k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv_B bnd re iter'.start acc').holds
  | .done y => (inv_B bnd re 16#usize y).holds

end Layer2Bounded

private theorem ntt_at_layer_2_step_lemma_B
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd)
    (acc : Layer2Bounded.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 31 + 2 * k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer2Bounded.step_post_B bnd re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_acc1_lt : acc.1.val ≤ 61 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    have h_zi3_max : zi1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi3, h_zi3_eq, h_zi3_val⟩ :=
      usize_add_ok_eq zi1 1#usize h_zi3_max
    have h_zi3_val_arith : zi3.val = acc.1.val + 2 := by
      rw [h_zi3_val, h_um, h_zi1_val_arith]
    have h_zi3_lt : zi3.val < 128 := by rw [h_zi3_val_arith]; omega
    obtain ⟨z2, h_z2_eq, h_z2_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi3 h_zi3_lt)
    -- `OpsInst.ntt_layer_2_step t z1 z2` — `_bnd` form.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ bnd := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_2_step_spec_bnd t z1 z2 bnd h_bnd
        h_z1_bd h_z2_bd h_t_bd)
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer2Bounded.Acc := (zi3, { coefficients := a }) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq, h_zi3_eq, h_z2_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_2_step t z1 z2
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi3,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer2Bounded.step_post_B bnd re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer2Bounded.step_post_B
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · show zi3.val = 31 + 2 * s.val
      rw [h_zi3_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer2Bounded.step_post_B bnd re k (.done acc)
    unfold Layer2Bounded.step_post_B
    show (Layer2Bounded.inv_B bnd re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_2_spec_B
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 31)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_2
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 63
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_2_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer2Bounded.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer2Bounded.inv_B bnd re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_2_step_lemma_B re bnd h_bnd h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer2Bounded.step_post_B bnd re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2Bounded.step_post_B] using hP
    · have hP : Layer2Bounded.step_post_B bnd re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer2Bounded.step_post_B] using hP

/-! ## L3.3 — `ntt_at_layer_3_spec`

Driver loop: 16 iterations over `re.coefficients`. Each iteration reads
`re.coefficients[k]` (a `PortableVector`), looks up one ζ-value via
`polynomial.zeta` (index `zeta_i.val + 1`), dispatches
`OpsInst.ntt_layer_3_step`, and writes back. `zeta_i.val` advances by 1
per iter (state stores `zeta_i1 = zeta_i + 1`); the bound per
coefficient goes `5·3328 → 6·3328`. -/

namespace Layer3

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 15 + k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 6 * 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv re iter'.start acc').holds
  | .done y => (inv re 16#usize y).holds

end Layer3

private theorem ntt_at_layer_3_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 5 * 3328)
    (acc : Layer3.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 15 + k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 6 * 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer3.step_post re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    -- 1) `zeta_i + 1`. Bound chain: acc.1.val = 15 + k.val with
    -- k.val < 16, so acc.1.val ≤ 30 and acc.1.val + 1 ≤ 31.
    have h_acc1_lt : acc.1.val ≤ 30 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    -- 2) `Array.index_mut_usize re.coefficients k`.
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    -- zi1.val = acc.1.val + 1 = 16 + k.val ≤ 31 < 128.
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    -- 3) `polynomial.zeta zi1`.
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- 4) `OpsInst.ntt_layer_3_step t z1`. L2.4 fires after instance
    -- reduces. Pre: t's elements ≤ 5·3328.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ 5 * 3328 := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_3_step_spec t z1 h_z1_bd h_t_bd)
    -- Next-state values: state stores `zi1` (= zeta_i + 1).
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer3.Acc := (zi1, { coefficients := a }) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step t z1
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi1,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer3.step_post re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer3.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · -- acc'.1.val = zi1.val = 15 + s.val.
      show zi1.val = 15 + s.val
      rw [h_zi1_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer3.step_post re k (.done acc)
    unfold Layer3.step_post
    show (Layer3.inv re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_3_spec
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (h_zeta : zeta_i.val = 15)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 5 * 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 31
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6 * 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer3.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer3.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_3_step_lemma re h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer3.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3.step_post] using hP
    · have hP : Layer3.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3.step_post] using hP

/-! ## L3.3.B — `ntt_at_layer_3_spec_B`

Nat-`bnd`-parameterised mirror of `ntt_at_layer_3_spec` (L3.3). Same
driver loop (16 iterations) and same ζ-thread (`15 → 31`); per-iter
single ζ lookup, dispatches `ntt_layer_3_step_spec_bnd`. Input bound
`5 * 3328` → `bnd`; output bound `6 * 3328` → `bnd + 3328`. -/

namespace Layer3Bounded

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

def inv_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    acc.1.val = 15 + k.val
    ∧ (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    ∧ (∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!))

def step_post_B
    (bnd : Nat)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (k : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      k.val < (16#usize : Std.Usize).val ∧ iter'.«end» = 16#usize
        ∧ iter'.start.val = k.val + 1
        ∧ (inv_B bnd re iter'.start acc').holds
  | .done y => (inv_B bnd re 16#usize y).holds

end Layer3Bounded

private theorem ntt_at_layer_3_step_lemma_B
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd)
    (acc : Layer3Bounded.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (16#usize : Std.Usize).val)
    (h_zeta_acc : acc.1.val = 15 + k.val)
    (h_acc_done : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    (h_acc_undone : ∀ j : Nat, k.val ≤ j → j < 16 →
        acc.2.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := k, «end» := 16#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer3Bounded.step_post_B bnd re k r ⌝ ⦄ := by
  have h16 : (16#usize : Std.Usize).val = 16 := rfl
  have h_coef_len : acc.2.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
  by_cases h_lt : k.val < (16#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_16 : k.val < 16 := by rw [h16] at h_lt; exact h_lt
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq k h_lt
    have h_acc1_lt : acc.1.val ≤ 30 := by rw [h_zeta_acc]; omega
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_z_max : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]; scalar_tac
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ :=
      usize_add_ok_eq acc.1 1#usize h_z_max
    have h_idx :
        Aeneas.Std.Array.index_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.2.coefficients k (by rw [h_coef_len]; exact hk_16)
    have h_imt_ok :
        Aeneas.Std.Array.index_mut_usize acc.2.coefficients k
          = .ok (acc.2.coefficients.val[k.val]!, acc.2.coefficients.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_idx]
      rfl
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.2.coefficients.val[k.val]! with ht_def
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by rw [h_zi1_val_arith]; omega
    obtain ⟨z1, h_z1_eq, h_z1_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zi1 h_zi1_lt)
    -- `OpsInst.ntt_layer_3_step t z1` — `_bnd` form.
    have h_t_eq : t = re.coefficients.val[k.val]! := by
      show acc.2.coefficients.val[k.val]! = re.coefficients.val[k.val]!
      exact h_acc_undone k.val (Nat.le_refl _) hk_16
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        (t.elements.val[ℓ]!).val.natAbs ≤ bnd := by
      intro ℓ hℓ
      rw [h_t_eq]; exact h_pre k.val hk_16 ℓ hℓ
    obtain ⟨t1, h_t1_eq, h_t1_bd⟩ :=
      triple_exists_ok_l3 (ntt_layer_3_step_spec_bnd t z1 bnd h_bnd h_z1_bd h_t_bd)
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.2.coefficients.set k t1 with ha_def
    set acc' : Layer3Bounded.Acc := (zi1, { coefficients := a }) with hacc'_def
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      simp [bind_tc_ok, h_zi1_eq, h_imt_ok, h_z1_eq]
      show (do
            let t1' ←
              libcrux_iot_ml_kem.vector.portable.ntt.ntt_layer_3_step t z1
            ok (cont (({ start := s, «end» := 16#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                      zi1,
                      ({ coefficients := acc.2.coefficients.set k t1' }
                        : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector))))
            = _
      rw [h_t1_eq]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer3Bounded.step_post_B bnd re k
      (.cont (({ start := s, «end» := 16#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer3Bounded.step_post_B
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · show zi1.val = 15 + s.val
      rw [h_zi1_val_arith, h_zeta_acc, hs_val]; ring
    · intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · have h_ne : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_set_ne :
            (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
        have h_set_ne_val :
            (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
        show ((acc.2.coefficients.set k t1).val[j]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_ne_val]
        exact h_acc_done j hj_lt_k ℓ hℓ
      · subst hj_eq_k
        have h_lt' : k.val < acc.2.coefficients.length := by
          rw [h_coef_len]; exact hk_16
        have h_set_eq :
            (acc.2.coefficients.set k t1)[k.val]! = t1 :=
          Aeneas.Std.Array.getElem!_Nat_set_eq acc.2.coefficients k k.val t1
            ⟨rfl, h_lt'⟩
        have h_set_eq_val :
            (acc.2.coefficients.set k t1).val[k.val]! = t1 := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_eq
        show ((acc.2.coefficients.set k t1).val[k.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_set_eq_val]
        exact h_t1_bd ℓ hℓ
    · intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_ne : k.val ≠ j := by omega
      have h_ge' : k.val ≤ j := by omega
      have h_set_ne :
          (acc.2.coefficients.set k t1)[j]! = (acc.2.coefficients)[j]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.2.coefficients k j t1 h_ne
      have h_set_ne_val :
          (acc.2.coefficients.set k t1).val[j]! = acc.2.coefficients.val[j]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_ne
      show (acc.2.coefficients.set k t1).val[j]! = re.coefficients.val[j]!
      rw [h_set_ne_val]
      exact h_acc_undone j h_ge' hj_lt
  · -- None branch (k ≥ 16).
    have hk_ge : k.val ≥ (16#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 16 := by rw [h16] at hk_ge; omega
    have h_iter_none := iter_next_none_eq k hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := k, «end» := 16#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer3Bounded.step_post_B bnd re k (.done acc)
    unfold Layer3Bounded.step_post_B
    show (Layer3Bounded.inv_B bnd re 16#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [hk_eq] at h_zeta_acc; rw [show (16#usize : Std.Usize).val = 16 from rfl]
      exact h_zeta_acc
    · intro j hj ℓ hℓ; rw [h16] at hj
      apply h_acc_done j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_ge hj_lt; rw [h16] at hj_ge
      apply h_acc_undone j _ hj_lt; rw [hk_eq]; exact hj_ge

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_3_spec_B
    (zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (initial_coefficient_bound : Std.Usize)
    (bnd : Nat) (h_bnd : bnd ≤ 29439)
    (h_zeta : zeta_i.val = 15)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_3
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re initial_coefficient_bound
    ⦃ ⇓ p => ⌜ p.1.val = 31
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_3_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          iter1 acc1.1 acc1.2)
      (β := Layer3Bounded.Acc)
      (zeta_i, re)
      0#usize 16#usize
      (Layer3Bounded.inv_B bnd re)
      (by decide : (0#usize : Std.Usize).val ≤ (16#usize : Std.Usize).val)
      (pure_prop_holds_l3 ⟨by rw [h_zeta]; rfl,
        fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
        fun _ _ _ => rfl⟩)
      ?_)
  · rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨?_, ?_⟩
    · have h16 : (16#usize : Std.Usize).val = 16 := rfl
      rw [h16] at h_zeta_eq; omega
    · intro i hi j hj
      apply h_done i (by rw [show (16#usize : Std.Usize).val = 16 from rfl]; exact hi) j hj
  · intro acc k h_ge h_le hinv
    obtain ⟨h_zeta_acc, h_acc_done, h_acc_undone⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_3_step_lemma_B re bnd h_bnd h_pre acc k h_le h_zeta_acc
        h_acc_done h_acc_undone
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer3Bounded.step_post_B bnd re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3Bounded.step_post_B] using hP
    · have hP : Layer3Bounded.step_post_B bnd re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer3Bounded.step_post_B] using hP

/-! ## L3.5 — `ntt_at_layer_7_spec`

Outermost layer of the forward NTT. No `zeta_i` (single fixed Montgomery
multiplier `-1600`). Driver loop runs 8 iterations (`step = 16/2 = 8`)
over the first half of `re.coefficients`; per iter touches lanes `j`
and `j+8`. Per-coefficient bound goes `3 → 4803` (= `3 + 1600·3`).

Per-iter body (j = k.val, i = j+8, all reads/writes from re/acc):
  scratch1 := re[i]
  scratch2 := -1600 * scratch1                       (L1.7)
  re[i]    := re[j]                                  (lane swap)
  t2       := re[j] + scratch2                       (L1.1)
  re[j]    := t2
  t4       := <re[i] now holds old re[j]> - scratch2 (L1.2)
  re[i]    := t4
So new re[j] = old re[j] + (-1600) * old re[i]; new re[i] = old re[j] -
(-1600) * old re[i] = old re[j] + 1600 * old re[i]. Both bounded by
3 + 4800 = 4803 in absolute value under |old re[*][ℓ]| ≤ 3. -/


/-! ### Local helpers: `Usize.div` reduction + generic-`«end»` iter-next. -/

private theorem usize_div_ok_eq (x y : Std.Usize) (hy : y.val ≠ 0) :
    ∃ z : Std.Usize, (x / y : Result Std.Usize) = .ok z ∧ z.val = x.val / y.val := by
  have hT := Std.UScalar.div_spec x hy
  obtain ⟨z, h_eq, h_v⟩ := hT
  exact ⟨z, h_eq, h_v⟩

/-- `i.val < e.val`: `IteratorRange.next` returns `.ok (some i, iter')` with
    `iter'.end = e` and `iter'.start.val = i.val + 1`. Generic version of
    `iter_next_some_eq` (which is specialised to `«end» := 16#usize`). -/
private theorem iter_next_some_eq_gen
    (i e : Std.Usize) (h_lt : i.val < e.val) :
    ∃ s : Std.Usize, s.val = i.val + 1 ∧
      core.iter.range.IteratorRange.next
        core.Usize.Insts.CoreIterRangeStep
        ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
      = .ok (some i,
          ({ start := s, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      ∃ s : Std.Usize, s.val = i.val + 1
        ∧ oi = (some i,
                ({ start := s, «end» := e }
                  : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun _ s hs => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure]
      exact ⟨s, hs, rfl⟩)
    (fun hge => absurd h_lt (Nat.not_lt.mpr hge))
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_l3 hT
  obtain ⟨s, hs_val, hpair⟩ := hP
  exact ⟨s, hs_val, by rw [hveq, hpair]⟩

/-- `i.val ≥ e.val`: `IteratorRange.next` returns `.ok (none, _)`. Generic
    version of `iter_next_none_eq`. -/
private theorem iter_next_none_eq_gen
    (i e : Std.Usize) (h_ge : i.val ≥ e.val) :
    core.iter.range.IteratorRange.next
      core.Usize.Insts.CoreIterRangeStep
      ({ start := i, «end» := e } : CoreModels.core.ops.range.Range Std.Usize)
    = .ok ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) := by
  have hT := IteratorRange_next_spec_usize i e
    (Q := PostCond.noThrow fun (oi : Option Std.Usize × _) => ⌜
      oi = ((none : Option Std.Usize),
            ({ start := i, «end» := e }
              : CoreModels.core.ops.range.Range Std.Usize)) ⌝)
    (fun hlt => absurd hlt (Nat.not_lt.mpr h_ge))
    (fun _ => by
      dsimp only [PostCond.noThrow, Std.Do.SPred.down_pure])
  obtain ⟨v, hveq, hP⟩ := triple_exists_ok_l3 hT
  rw [hveq, hP]

namespace Layer7

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

/-- Step-local accumulator: a `PolynomialRingElement × scratch`. -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Loop invariant after `k` iterations (`k.val ∈ [0, 8]`):
    - Lanes `j ∈ [0, k.val)` are processed: bounded by 4803.
    - Lanes `j ∈ [8, 8 + k.val)` are processed: bounded by 4803.
    - Lanes `j ∈ [k.val, 8)` are untouched: bounded by 3 (from `re`).
    - Lanes `j ∈ [8 + k.val, 16)` are untouched: bounded by 3 (from `re`). -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector) :
    Std.Usize → Acc → Result Prop :=
  fun k acc => pure (
    (∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    ∧ (∀ j : Nat, 8 ≤ j → j < 8 + k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    ∧ (∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
    ∧ (∀ j : Nat, 8 + k.val ≤ j → j < 16 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!))

/-- Per-iter step post. -/
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

end Layer7

set_option maxHeartbeats 16000000 in
private theorem ntt_at_layer_7_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3)
    (acc : Layer7.Acc)
    (k : Std.Usize) (h_le : k.val ≤ (8#usize : Std.Usize).val)
    (h_done_lo : ∀ j : Nat, j < k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    (h_done_hi : ∀ j : Nat, 8 ≤ j → j < 8 + k.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[j]!).elements.val[ℓ]!).val.natAbs ≤ 4803)
    (h_undone_lo : ∀ j : Nat, k.val ≤ j → j < 8 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!)
    (h_undone_hi : ∀ j : Nat, 8 + k.val ≤ j → j < 16 →
        acc.1.coefficients.val[j]! = re.coefficients.val[j]!) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      8#usize { start := k, «end» := 8#usize } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer7.step_post re k r ⌝ ⦄ := by
  have h8 : (8#usize : Std.Usize).val = 8 := rfl
  have h_coef_len : acc.1.coefficients.length = 16 :=
    Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
  by_cases h_lt : k.val < (8#usize : Std.Usize).val
  · -- Some round = k branch.
    have hk_8 : k.val < 8 := by rw [h8] at h_lt; exact h_lt
    have hk_16 : k.val < 16 := by omega
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq_gen k 8#usize h_lt
    -- 1) `i = j + 8`: where j = k.
    have h_um8 : (8#usize : Std.Usize).val = 8 := rfl
    have h_i_max : k.val + (8#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um8]; scalar_tac
    obtain ⟨i, h_i_eq, h_i_val⟩ := usize_add_ok_eq k 8#usize h_i_max
    have h_i_val_arith : i.val = k.val + 8 := by rw [h_i_val, h_um8]
    have h_i_lt_16 : i.val < 16 := by rw [h_i_val_arith]; omega
    have h_i_lt_coef : i.val < acc.1.coefficients.length := by rw [h_coef_len]; exact h_i_lt_16
    -- 2) Read scratch1 = acc.1[i].
    have h_idx_i :
        Aeneas.Std.Array.index_usize acc.1.coefficients i
          = .ok (acc.1.coefficients.val[i.val]!) :=
      array_index_usize_ok_eq acc.1.coefficients i h_i_lt_coef
    have h_acc_i_eq : acc.1.coefficients.val[i.val]! = re.coefficients.val[i.val]! := by
      apply h_undone_hi i.val
      · rw [h_i_val_arith]; omega
      · exact h_i_lt_16
    have h_scratch1_bd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 := by
      intro ℓ hℓ
      rw [h_acc_i_eq]
      exact h_pre i.val h_i_lt_16 ℓ hℓ
    -- 3) scratch2 = multiply_by_constant scratch1 (-1600). L1.7.
    have h_neg1600_val : ((-1600)#i16 : Std.I16).val = -1600 := by decide
    have h_mul_pre : ∀ ℓ : Nat, ℓ < 16 →
        (((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val
            * ((-1600)#i16 : Std.I16).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      have h_x_abs : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 :=
        h_scratch1_bd ℓ hℓ
      rw [h_neg1600_val]
      have h_abs_mul : (((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val * (-1600) : Int).natAbs
                       = ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600 := by
        rw [Int.natAbs_mul]; rfl
      rw [h_abs_mul]
      have h_mul : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600
                    ≤ 3 * 1600 :=
        Nat.mul_le_mul_right 1600 h_x_abs
      omega
    obtain ⟨scratch2, h_scratch2_eq, h_scratch2_post⟩ :=
      triple_exists_ok_l3 (multiply_by_constant_spec (acc.1.coefficients.val[i.val]!)
                            ((-1600)#i16 : Std.I16) h_mul_pre)
    have h_scratch2_bd : ∀ ℓ : Nat, ℓ < 16 →
        (scratch2.elements.val[ℓ]!).val
          = (acc.1.coefficients.val[i.val]!).elements.val[ℓ]!.val * (-1600 : Int)
        ∧ (scratch2.elements.val[ℓ]!).val.natAbs ≤ 4800 := by
      intro ℓ hℓ
      have h_per := h_scratch2_post ℓ hℓ
      have h_v_eq : (scratch2.elements.val[ℓ]!).val
                      = (acc.1.coefficients.val[i.val]!).elements.val[ℓ]!.val * (-1600 : Int) := by
        rw [h_per.1, h_neg1600_val]
      refine ⟨h_v_eq, ?_⟩
      have h_x_abs : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 :=
        h_scratch1_bd ℓ hℓ
      have h_abs_eq : (scratch2.elements.val[ℓ]!).val.natAbs
                      = ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600 := by
        rw [h_v_eq, Int.natAbs_mul]; rfl
      rw [h_abs_eq]
      have h_mul : ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs * 1600
                    ≤ 3 * 1600 :=
        Nat.mul_le_mul_right 1600 h_x_abs
      omega
    -- 4) t = re.coefficients[j] = acc.1.coef[k]!
    have h_k_lt_coef : k.val < acc.1.coefficients.length := by rw [h_coef_len]; exact hk_16
    have h_idx_k :
        Aeneas.Std.Array.index_usize acc.1.coefficients k
          = .ok (acc.1.coefficients.val[k.val]!) :=
      array_index_usize_ok_eq acc.1.coefficients k h_k_lt_coef
    have h_acc_k_eq : acc.1.coefficients.val[k.val]! = re.coefficients.val[k.val]! :=
      h_undone_lo k.val (Nat.le_refl _) hk_8
    -- Per-element bound at lane k: ≤ 3 from h_pre via h_acc_k_eq.
    have h_t_bd : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[k.val]!).elements.val[ℓ]!).val.natAbs ≤ 3 := by
      intro ℓ hℓ
      rw [h_acc_k_eq]
      exact h_pre k.val hk_16 ℓ hℓ
    -- Set t (for readability in downstream bounds).
    set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
      acc.1.coefficients.val[k.val]! with ht_def
    -- 5) a = acc.1.coef.set i t.
    have h_upd_i :
        Aeneas.Std.Array.update acc.1.coefficients i t
          = .ok (acc.1.coefficients.set i t) :=
      array_update_ok_eq acc.1.coefficients i t h_i_lt_coef
    set a : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      acc.1.coefficients.set i t with ha_def
    -- 6) (t1, back1) = index_mut_usize a j.
    have h_a_k_lt : k.val < a.length := by
      change k.val < (acc.1.coefficients.set i t).length
      rw [Std.Array.set_length]; rw [h_coef_len]; exact hk_16
    have h_a_k_idx :
        Aeneas.Std.Array.index_usize a k = .ok (a.val[k.val]!) :=
      array_index_usize_ok_eq a k h_a_k_lt
    have h_imt_a_k :
        Aeneas.Std.Array.index_mut_usize a k = .ok (a.val[k.val]!, a.set k) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_a_k_idx]; rfl
    have h_k_ne_i : k.val ≠ i.val := by rw [h_i_val_arith]; omega
    have h_i_ne_k : i.val ≠ k.val := fun h => h_k_ne_i h.symm
    have h_a_k_val_eq : a.val[k.val]! = acc.1.coefficients.val[k.val]! := by
      change (acc.1.coefficients.set i t).val[k.val]! = acc.1.coefficients.val[k.val]!
      have h_ne : (acc.1.coefficients.set i t)[k.val]! = (acc.1.coefficients)[k.val]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i k.val t h_i_ne_k
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_ne
    -- t1 = a.val[k.val]! (result of index_mut). Bound: t1 = acc.1.coef[k]! = t.
    have h_t1_eq_t : a.val[k.val]! = t := by
      change a.val[k.val]! = acc.1.coefficients.val[k.val]!
      exact h_a_k_val_eq
    have h_add_pre : ∀ ℓ : Nat, ℓ < 16 →
        (((a.val[k.val]!).elements.val[ℓ]!).val + (scratch2.elements.val[ℓ]!).val : Int).natAbs
          ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      rw [h_t1_eq_t]
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    obtain ⟨t2, h_t2_eq, h_t2_post⟩ :=
      triple_exists_ok_l3 (add_spec (a.val[k.val]!) scratch2 h_add_pre)
    have h_t2_bd : ∀ ℓ : Nat, ℓ < 16 → (t2.elements.val[ℓ]!).val.natAbs ≤ 4803 := by
      intro ℓ hℓ
      have h_per := h_t2_post ℓ hℓ
      have h_v := h_per.1
      rw [h_t1_eq_t] at h_v
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    -- 8/9) a1 = a.set k t2 (definitional); (t3, back2) = index_mut_usize a1 i.
    -- Use `have ... : ... := ` to define a1 as a syntactically-distinct term,
    -- but state the index_mut hypothesis directly with `a.set k t2` so simp
    -- can match the goal pattern.
    have h_a1_i_lt : i.val < (a.set k t2).length := by
      rw [Std.Array.set_length]
      change i.val < (acc.1.coefficients.set i t).length
      rw [Std.Array.set_length, h_coef_len]; exact h_i_lt_16
    have h_a1_i_idx :
        Aeneas.Std.Array.index_usize (a.set k t2) i
          = .ok ((a.set k t2).val[i.val]!) :=
      array_index_usize_ok_eq (a.set k t2) i h_a1_i_lt
    have h_imt_a1_i :
        Aeneas.Std.Array.index_mut_usize (a.set k t2) i
          = .ok ((a.set k t2).val[i.val]!, (a.set k t2).set i) := by
      unfold Aeneas.Std.Array.index_mut_usize
      rw [h_a1_i_idx]; rfl
    have h_a1_i_val_eq : (a.set k t2).val[i.val]! = t := by
      have h_set_k_ne : (a.set k t2)[i.val]! = a[i.val]! :=
        Aeneas.Std.Array.getElem!_Nat_set_ne a k i.val t2 h_k_ne_i
      have h_a_i_eq : a[i.val]! = t := by
        change (acc.1.coefficients.set i t)[i.val]! = t
        exact Aeneas.Std.Array.getElem!_Nat_set_eq acc.1.coefficients i i.val t ⟨rfl, h_i_lt_coef⟩
      have h_chain : (a.set k t2).val[i.val]! = a.val[i.val]! := by
        simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_set_k_ne
      rw [h_chain]
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_a_i_eq
    -- 10) t4 = sub t3 scratch2. State with the raw `a.set k t2` term (no `let a1`).
    have h_sub_pre : ∀ ℓ : Nat, ℓ < 16 →
        ((((a.set k t2).val[i.val]!).elements.val[ℓ]!).val
          - (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
      intro ℓ hℓ
      rw [h_a1_i_val_eq]
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    obtain ⟨t4, h_t4_eq, h_t4_post⟩ :=
      triple_exists_ok_l3 (sub_spec ((a.set k t2).val[i.val]!) scratch2 h_sub_pre)
    have h_t4_bd : ∀ ℓ : Nat, ℓ < 16 → (t4.elements.val[ℓ]!).val.natAbs ≤ 4803 := by
      intro ℓ hℓ
      have h_per := h_t4_post ℓ hℓ
      have h_v := h_per.1
      rw [h_a1_i_val_eq] at h_v
      have h_t_b := h_t_bd ℓ hℓ
      have h_s2_b := (h_scratch2_bd ℓ hℓ).2
      have h_t_int_lb : -(3 : Int) ≤ (t.elements.val[ℓ]!).val := by omega
      have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ (3 : Int) := by omega
      have h_s2_int_lb : -(4800 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
      have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (4800 : Int) := by omega
      omega
    -- Introduce a1 alias AFTER stating h_t4_eq (so h_t4_eq has raw form).
    let a1 : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a.set k t2
    have ha1_def : a1 = a.set k t2 := rfl
    -- 11) a2 = a1.set i t4.
    set a2 : Std.Array
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
      a1.set i t4 with ha2_def
    set acc' : Layer7.Acc := ({ coefficients := a2 }, scratch2) with hacc'_def
    -- Compose into a single .ok equation.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := 8#usize }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
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
      -- L3.1's pattern: full `simp` reduces match-on-Some + lets + Prod-binds
      -- and threads all arithmetic equations in one call. Disable two simp
      -- lemmas that would push the goal into a form our hypotheses don't match:
      --  * `List.getElem!_eq_getElem?_getD` — would unfold `[i]!` to `?.getD default`.
      --  * `Std.Array.set_val_eq` — would push `↑` inside `(a.set i x)` to
      --    yield `(↑a).set (↑i) x`, breaking the `(a.set k t2).val[i.val]!`
      --    pattern in our index_mut hypothesis.
      simp [-List.getElem!_eq_getElem?_getD, -Std.Array.set_val_eq,
        bind_tc_ok,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.multiply_by_constant,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.add,
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.sub,
        h_i_eq, h_idx_i, h_scratch2_eq, h_idx_k, h_upd_i, h_imt_a_k, h_t2_eq,
        h_imt_a1_i, h_t4_eq]
      -- Goal collapses to `({coefficients := (a.set k t2).set i t4}, scratch2) = acc'`;
      -- `acc'` is `({coefficients := (a.set k t2).set i t4}, scratch2)` definitionally
      -- (via the `let`-chain a1 = a.set k t2, a2 = a1.set i t4).
      rfl
    apply triple_of_ok_l3 h_body
    show Layer7.step_post re k
      (.cont (({ start := s, «end» := 8#usize }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer7.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Lanes j ∈ [0, s.val): processed.
      intro j hj ℓ hℓ
      rw [hs_val] at hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj_lt_k | hj_eq_k
      · -- j < k: unchanged by both writes.
        have h_k_ne_j : k.val ≠ j := Nat.ne_of_gt hj_lt_k
        have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
        have h_chain :
            acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
          show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
          have h1 : (a1.set i t4)[j]! = a1[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
          have h2 : (a.set k t2)[j]! = a[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
          have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
          have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          have h2' : a1.val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
          have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
          rw [h1', h2', h3']
        rw [h_chain]
        exact h_done_lo j hj_lt_k ℓ hℓ
      · -- j = k: new value is t2.
        subst hj_eq_k
        have h_chain : acc'.1.coefficients.val[k.val]! = t2 := by
          show (a1.set i t4).val[k.val]! = t2
          have h1 : (a1.set i t4)[k.val]! = a1[k.val]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i k.val t4 h_i_ne_k
          have h1' : (a1.set i t4).val[k.val]! = a1.val[k.val]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          rw [h1']
          show (a.set k t2).val[k.val]! = t2
          have h2 : (a.set k t2)[k.val]! = t2 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq a k k.val t2 ⟨rfl, h_a_k_lt⟩
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        rw [h_chain]
        exact h_t2_bd ℓ hℓ
    · -- Lanes j ∈ [8, 8 + s.val): processed.
      intro j hj_lo hj_hi ℓ hℓ
      rw [hs_val] at hj_hi
      have hj_lt : j < 8 + k.val + 1 := by omega
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hj_lt_ki | hj_eq_ki
      · -- j ∈ [8, 8 + k.val): unchanged by both writes.
        have h_k_ne_j : k.val ≠ j := by omega
        have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
        have h_chain :
            acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
          show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
          have h1 : (a1.set i t4)[j]! = a1[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
          have h2 : (a.set k t2)[j]! = a[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
          have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
            Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
          have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
          have h2' : a1.val[j]! = a.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
          have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
            simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
          rw [h1', h2', h3']
        rw [h_chain]
        exact h_done_hi j hj_lo hj_lt_ki ℓ hℓ
      · -- j = 8 + k.val = i.val: new value is t4.
        have hj_eq_i : j = i.val := by rw [h_i_val_arith]; omega
        subst hj_eq_i
        have h_chain : acc'.1.coefficients.val[i.val]! = t4 := by
          show (a1.set i t4).val[i.val]! = t4
          have h1 : (a1.set i t4)[i.val]! = t4 :=
            Aeneas.Std.Array.getElem!_Nat_set_eq a1 i i.val t4 ⟨rfl, h_a1_i_lt⟩
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        rw [h_chain]
        exact h_t4_bd ℓ hℓ
    · -- Lanes j ∈ [s.val, 8): untouched.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_k_lt_j : k.val < j := by omega
      have h_k_ne_j : k.val ≠ j := by omega
      have h_i_ne_j : i.val ≠ j := by rw [h_i_val_arith]; omega
      have h_chain :
          acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
        show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
        have h1 : (a1.set i t4)[j]! = a1[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
        have h2 : (a.set k t2)[j]! = a[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
        have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
        have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        have h2' : a1.val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
        rw [h1', h2', h3']
      rw [h_chain]
      have h_undone_j : k.val ≤ j := by omega
      exact h_undone_lo j h_undone_j hj_lt
    · -- Lanes j ∈ [8 + s.val, 16): untouched.
      intro j hj_ge hj_lt
      rw [hs_val] at hj_ge
      have h_i_lt_j : i.val < j := by rw [h_i_val_arith]; omega
      have h_k_ne_j : k.val ≠ j := by omega
      have h_i_ne_j : i.val ≠ j := by omega
      have h_chain :
          acc'.1.coefficients.val[j]! = acc.1.coefficients.val[j]! := by
        show (a1.set i t4).val[j]! = acc.1.coefficients.val[j]!
        have h1 : (a1.set i t4)[j]! = a1[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a1 i j t4 h_i_ne_j
        have h2 : (a.set k t2)[j]! = a[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne a k j t2 h_k_ne_j
        have h3 : (acc.1.coefficients.set i t)[j]! = (acc.1.coefficients)[j]! :=
          Aeneas.Std.Array.getElem!_Nat_set_ne acc.1.coefficients i j t h_i_ne_j
        have h1' : (a1.set i t4).val[j]! = a1.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
        have h2' : a1.val[j]! = a.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
        have h3' : a.val[j]! = acc.1.coefficients.val[j]! := by
          simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3
        rw [h1', h2', h3']
      rw [h_chain]
      have h_undone_j : 8 + k.val ≤ j := by omega
      exact h_undone_hi j h_undone_j hj_lt
  · -- None branch (k ≥ 8).
    have hk_ge : k.val ≥ (8#usize : Std.Usize).val := Nat.not_lt.mp h_lt
    have hk_eq : k.val = 8 := by rw [h8] at hk_ge; omega
    have h_iter_none := iter_next_none_eq_gen k 8#usize hk_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize { start := k, «end» := 8#usize } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
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
    apply triple_of_ok_l3 h_body
    show Layer7.step_post re k (.done acc)
    unfold Layer7.step_post
    show (Layer7.inv re 8#usize acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj ℓ hℓ
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj
      apply h_done_lo j _ ℓ hℓ; rw [hk_eq]; exact hj
    · intro j hj_lo hj_hi ℓ hℓ
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_hi
      apply h_done_hi j hj_lo _ ℓ hℓ; rw [hk_eq]; exact hj_hi
    · intro j hj_ge hj_lt
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_ge
      apply h_undone_lo j _ hj_lt; rw [hk_eq]; exact hj_ge
    · intro j hj_ge hj_lt
      rw [show (8#usize : Std.Usize).val = 8 from rfl] at hj_ge
      apply h_undone_hi j _ hj_lt; rw [hk_eq]; exact hj_ge

private theorem vectors_in_ring_element_eq :
    libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT = .ok (16#usize : Std.Usize) := by
  unfold libcrux_iot_ml_kem.polynomial.VECTORS_IN_RING_ELEMENT
  unfold libcrux_iot_ml_kem.constants.COEFFICIENTS_IN_RING_ELEMENT
  unfold libcrux_iot_ml_kem.vector.traits.FIELD_ELEMENTS_IN_VECTOR
  rfl

set_option maxHeartbeats 16000000 in
@[spec]
theorem ntt_at_layer_7_spec
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_7
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      re scratch
    ⦃ ⇓ p => ⌜ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 4803 ⌝ ⦄ := by
  -- Reduce the top wrapper: i = VECTORS_IN_RING_ELEMENT = 16#usize, step = i/2 = 8#usize.
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7
  rw [vectors_in_ring_element_eq]
  simp only [bind_tc_ok]
  -- step = 16#usize / 2#usize = 8#usize.
  have h_two_nz : (2#usize : Std.Usize).val ≠ 0 := by decide
  obtain ⟨step, h_step_eq, h_step_val⟩ :=
    usize_div_ok_eq (16#usize : Std.Usize) (2#usize : Std.Usize) h_two_nz
  have h_step_val_8 : step.val = 8 := by
    rw [h_step_val]; decide
  have h_step_eq_8 : step = 8#usize := by
    apply Std.UScalar.eq_of_val_eq
    rw [h_step_val_8]; rfl
  rw [h_step_eq]
  simp only [bind_tc_ok]
  rw [h_step_eq_8]
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_7_loop.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          8#usize iter1 acc1.1 acc1.2)
      (β := Layer7.Acc)
      (re, scratch)
      0#usize 8#usize
      (Layer7.inv re)
      (by decide : (0#usize : Std.Usize).val ≤ (8#usize : Std.Usize).val)
      (pure_prop_holds_l3
        ⟨fun j hj _ _ => absurd hj (Nat.not_lt_zero j),
         fun j _hj_lo hj_hi _ _ => by
            have h0 : (0#usize : Std.Usize).val = 0 := rfl
            rw [h0] at hj_hi
            omega,
         fun _ _ _ => rfl,
         fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_done_lo, h_done_hi, _h_undone_lo, _h_undone_hi⟩ := of_pure_prop_holds_l3 h
    intro i hi j hj
    have h8 : (8#usize : Std.Usize).val = 8 := rfl
    by_cases hi_lt_8 : i < 8
    · apply h_done_lo i (by rw [h8]; exact hi_lt_8) j hj
    · have hi_ge_8 : 8 ≤ i := Nat.not_lt.mp hi_lt_8
      apply h_done_hi i hi_ge_8 (by rw [h8]; omega) j hj
  · -- Step lemma application.
    intro acc k h_ge h_le hinv
    obtain ⟨h_done_lo, h_done_hi, h_undone_lo, h_undone_hi⟩ := of_pure_prop_holds_l3 hinv
    have h_step := ntt_at_layer_7_step_lemma re h_pre acc k h_le
                    h_done_lo h_done_hi h_undone_lo h_undone_hi
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer7.step_post re k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer7.step_post] using hP
    · have hP : Layer7.step_post re k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer7.step_post] using hP

/-! ## L3.4 — `ntt_at_layer_4_plus_spec`

Generic outer-NTT layer for `layer ∈ {4, 5, 6}`. Nested loop:
  - Outer loop iterates `outer_count = 128 >>> layer` rounds.
  - Inner loop iterates `step_vec = (1 <<< layer) / 16` butterfly positions.

For `layer = 4`: step=16, step_vec=1, outer_count=8.
For `layer = 5`: step=32, step_vec=2, outer_count=4.
For `layer = 6`: step=64, step_vec=4, outer_count=2.

In all cases, the total butterflies executed = `outer_count * step_vec = 8`,
covering 16 coefficients (each lane touched once via pairs spanning `step_vec`
apart). Per-coefficient bound goes `bnd → bnd + 3328`.

Per-iter body (inner loop, j = inner-counter):
  i  = a_offset + j     (one of the "low" lanes of the butterfly pair)
  i1 = b_offset + j     (one of the "high" lanes)
  i2 = polynomial.zeta zeta_i  (the Montgomery-domain twiddle)
  ntt_layer_int_vec_step OpsInst re.coefficients i i1 scratch i2

Per-iter body (outer loop, round = outer-counter):
  zeta_i1   = zeta_i + 1
  i         = round * 2
  a_offset  = i * step_vec
  b_offset  = a_offset + step_vec
  ntt_at_layer_4_plus_loop0_loop0 ... {0..step_vec} zeta_i1 ...
-/

/-! ### per-step helper `ntt_layer_int_vec_step_spec` -/

/-- A single butterfly on a `coefficients` array at lanes `a ≠ b`:
    new `coefficients[a]` = old `coefficients[a]` + zeta*coefficients[b]
    new `coefficients[b]` = old `coefficients[a]` - zeta*coefficients[b]
    Per-element bound transformation: if `|coefficients[a][ℓ]| ≤ B*3328`
    (`B ≤ 4`, so `B+1 ≤ 5`, well-within `9*3328 < 2^15`), the output at
    both lanes a and b is bounded by `(B+1)*3328`. Other lanes unchanged.
    Returns the new coefficients and the scratch value (unused downstream). -/
private theorem ntt_layer_int_vec_step_spec
    (coefficients : Std.Array
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize)
    (a b : Std.Usize) (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_r : Std.I16)
    (h_a : a.val < 16) (h_b : b.val < 16) (h_ne : a.val ≠ b.val)
    (h_zeta : zeta_r.val.natAbs ≤ 1664)
    (bnd : Nat) (h_bnd : bnd ≤ 8 * 3328)
    (h_pre_a : ∀ ℓ : Nat, ℓ < 16 →
      ((coefficients.val[a.val]!).elements.val[ℓ]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      coefficients a b scratch zeta_r
    ⦃ ⇓ p => ⌜ (∀ ℓ : Nat, ℓ < 16 →
                  ((p.1.val[a.val]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
              ∧ (∀ ℓ : Nat, ℓ < 16 →
                  ((p.1.val[b.val]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
              ∧ (∀ k : Nat, k < 16 → k ≠ a.val → k ≠ b.val →
                  p.1.val[k]! = coefficients.val[k]!) ⌝ ⦄ := by
  have h_coef_len : coefficients.length = 16 := Std.Array.length_eq _
  have h_a_lt : a.val < coefficients.length := by rw [h_coef_len]; exact h_a
  have h_b_lt : b.val < coefficients.length := by rw [h_coef_len]; exact h_b
  -- Read coefficients[b].
  have h_idx_b : Aeneas.Std.Array.index_usize coefficients b
                  = .ok (coefficients.val[b.val]!) :=
    array_index_usize_ok_eq coefficients b h_b_lt
  set scratch1 : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[b.val]! with hs1_def
  -- scratch2 = OpsInst.montgomery_multiply_by_constant scratch1 zeta_r.
  -- This reduces to: do classify zeta_r; arithmetic.montgomery_multiply_by_constant scratch1 zeta_r.
  -- Use L1.4.
  have h_classify : libcrux_secrets.traits.Classify.Blanket.classify zeta_r = .ok zeta_r := rfl
  obtain ⟨scratch2, h_scratch2_eq, h_scratch2_post⟩ :=
    triple_exists_ok_l3 (montgomery_multiply_by_constant_spec scratch1 zeta_r h_zeta)
  have h_scratch2_bd : ∀ ℓ : Nat, ℓ < 16 → (scratch2.elements.val[ℓ]!).val.natAbs ≤ 3328 := by
    intro ℓ hℓ; exact (h_scratch2_post ℓ hℓ).1
  -- Read coefficients[a] (= t).
  have h_idx_a : Aeneas.Std.Array.index_usize coefficients a
                  = .ok (coefficients.val[a.val]!) :=
    array_index_usize_ok_eq coefficients a h_a_lt
  set t : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
    coefficients.val[a.val]! with ht_def
  -- Bound at t: per h_pre_a, |t[ℓ]| ≤ bnd.
  have h_t_bd : ∀ ℓ : Nat, ℓ < 16 → (t.elements.val[ℓ]!).val.natAbs ≤ bnd :=
    h_pre_a
  -- coefficients1 = coefficients.update b t.
  have h_upd_b : Aeneas.Std.Array.update coefficients b t
                  = .ok (coefficients.set b t) :=
    array_update_ok_eq coefficients b t h_b_lt
  set c1 : Std.Array
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    coefficients.set b t with hc1_def
  -- index_mut_usize c1 a returns (c1.val[a.val]!, c1.set a).
  have h_a_ne_b : a.val ≠ b.val := h_ne
  have h_b_ne_a : b.val ≠ a.val := fun h => h_a_ne_b h.symm
  have h_c1_a_lt : a.val < c1.length := by
    change a.val < (coefficients.set b t).length; rw [Std.Array.set_length]; exact h_a_lt
  have h_c1_a_idx : Aeneas.Std.Array.index_usize c1 a = .ok (c1.val[a.val]!) :=
    array_index_usize_ok_eq c1 a h_c1_a_lt
  have h_imt_c1_a : Aeneas.Std.Array.index_mut_usize c1 a
                      = .ok (c1.val[a.val]!, c1.set a) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_c1_a_idx]; rfl
  have h_c1_a_val_eq : c1.val[a.val]! = t := by
    show (coefficients.set b t).val[a.val]! = t
    have h_ne_set : (coefficients.set b t)[a.val]! = coefficients[a.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne coefficients b a.val t h_b_ne_a
    have h_eq_val : (coefficients.set b t).val[a.val]! = coefficients.val[a.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_ne_set
    rw [h_eq_val]
  -- t2 = OpsInst.add (c1.val[a.val]!) scratch2.
  have h_add_pre : ∀ ℓ : Nat, ℓ < 16 →
      (((c1.val[a.val]!).elements.val[ℓ]!).val
        + (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
    intro ℓ hℓ
    rw [h_c1_a_val_eq]
    have h_t_b := h_t_bd ℓ hℓ
    have h_s2_b := h_scratch2_bd ℓ hℓ
    have h_t_int_lb : -((bnd : Nat) : Int) ≤ (t.elements.val[ℓ]!).val := by omega
    have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ ((bnd : Nat) : Int) := by omega
    have h_s2_int_lb : -(3328 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
    have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (3328 : Int) := by omega
    -- bnd + 3328 ≤ 4*3328 + 3328 = 5*3328 = 16640 < 2^15.
    omega
  obtain ⟨t2, h_t2_eq, h_t2_post⟩ :=
    triple_exists_ok_l3 (add_spec (c1.val[a.val]!) scratch2 h_add_pre)
  -- Bound on t2: ≤ bnd + 3328.
  have h_t2_bd : ∀ ℓ : Nat, ℓ < 16 → (t2.elements.val[ℓ]!).val.natAbs ≤ bnd + 3328 := by
    intro ℓ hℓ
    have h_per := h_t2_post ℓ hℓ
    have h_v := h_per.1
    rw [h_c1_a_val_eq] at h_v
    have h_t_b := h_t_bd ℓ hℓ
    have h_s2_b := h_scratch2_bd ℓ hℓ
    have h_t_int_lb : -((bnd : Nat) : Int) ≤ (t.elements.val[ℓ]!).val := by omega
    have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ ((bnd : Nat) : Int) := by omega
    have h_s2_int_lb : -(3328 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
    have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (3328 : Int) := by omega
    omega
  -- coefficients2 = c1.set a t2.
  set c2 : Std.Array
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    c1.set a t2 with hc2_def
  -- index_mut_usize c2 b returns (c2.val[b.val]!, c2.set b).
  have h_c2_b_lt : b.val < c2.length := by
    change b.val < (c1.set a t2).length; rw [Std.Array.set_length]
    change b.val < (coefficients.set b t).length; rw [Std.Array.set_length]; exact h_b_lt
  have h_c2_b_idx : Aeneas.Std.Array.index_usize c2 b = .ok (c2.val[b.val]!) :=
    array_index_usize_ok_eq c2 b h_c2_b_lt
  have h_imt_c2_b : Aeneas.Std.Array.index_mut_usize c2 b
                      = .ok (c2.val[b.val]!, c2.set b) := by
    unfold Aeneas.Std.Array.index_mut_usize; rw [h_c2_b_idx]; rfl
  -- c2.val[b.val]! = c1.val[b.val]! (since c2 sets a ≠ b)
  --                = (coefficients.set b t).val[b.val]! = t.
  have h_c2_b_val_eq : c2.val[b.val]! = t := by
    show (c1.set a t2).val[b.val]! = t
    have h_ne1 : (c1.set a t2)[b.val]! = c1[b.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne c1 a b.val t2 h_a_ne_b
    have h_ne1_val : (c1.set a t2).val[b.val]! = c1.val[b.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_ne1
    rw [h_ne1_val]
    change (coefficients.set b t).val[b.val]! = t
    have h_eq : (coefficients.set b t)[b.val]! = t :=
      Aeneas.Std.Array.getElem!_Nat_set_eq coefficients b b.val t ⟨rfl, h_b_lt⟩
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_eq
  -- t4 = OpsInst.sub (c2.val[b.val]!) scratch2.
  have h_sub_pre : ∀ ℓ : Nat, ℓ < 16 →
      (((c2.val[b.val]!).elements.val[ℓ]!).val
        - (scratch2.elements.val[ℓ]!).val : Int).natAbs ≤ 2 ^ 15 - 1 := by
    intro ℓ hℓ
    rw [h_c2_b_val_eq]
    have h_t_b := h_t_bd ℓ hℓ
    have h_s2_b := h_scratch2_bd ℓ hℓ
    have h_t_int_lb : -((bnd : Nat) : Int) ≤ (t.elements.val[ℓ]!).val := by omega
    have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ ((bnd : Nat) : Int) := by omega
    have h_s2_int_lb : -(3328 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
    have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (3328 : Int) := by omega
    omega
  obtain ⟨t4, h_t4_eq, h_t4_post⟩ :=
    triple_exists_ok_l3 (sub_spec (c2.val[b.val]!) scratch2 h_sub_pre)
  have h_t4_bd : ∀ ℓ : Nat, ℓ < 16 → (t4.elements.val[ℓ]!).val.natAbs ≤ bnd + 3328 := by
    intro ℓ hℓ
    have h_per := h_t4_post ℓ hℓ
    have h_v := h_per.1
    rw [h_c2_b_val_eq] at h_v
    have h_t_b := h_t_bd ℓ hℓ
    have h_s2_b := h_scratch2_bd ℓ hℓ
    have h_t_int_lb : -((bnd : Nat) : Int) ≤ (t.elements.val[ℓ]!).val := by omega
    have h_t_int_ub : (t.elements.val[ℓ]!).val ≤ ((bnd : Nat) : Int) := by omega
    have h_s2_int_lb : -(3328 : Int) ≤ (scratch2.elements.val[ℓ]!).val := by omega
    have h_s2_int_ub : (scratch2.elements.val[ℓ]!).val ≤ (3328 : Int) := by omega
    omega
  -- coefficients3 = c2.set b t4.
  set c3 : Std.Array
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector 16#usize :=
    c2.set b t4 with hc3_def
  -- Compose into single .ok equation.
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
        coefficients a b scratch zeta_r
      = .ok (c3, scratch2) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_layer_int_vec_step
    -- mont_mul_fe reduces to: classify zeta_r >>= λi → arithmetic.mont_mul scratch1 i.
    simp only [bind_tc_ok, h_idx_b]
    -- Force unfold the trait wrappers (montgomery_multiply_fe, .add, .sub).
    unfold libcrux_iot_ml_kem.vector.traits.montgomery_multiply_fe
    show
      (do
        let _scratch2 ←
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.montgomery_multiply_by_constant
            scratch1 zeta_r
        let _t ← Aeneas.Std.Array.index_usize coefficients a
        let _c1 ← Aeneas.Std.Array.update coefficients b _t
        let (_t1, _back1) ← Aeneas.Std.Array.index_mut_usize _c1 a
        let _t2 ←
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.add
            _t1 _scratch2
        let _c2 := _back1 _t2
        let (_t3, _back2) ← Aeneas.Std.Array.index_mut_usize _c2 b
        let _t4 ←
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.sub
            _t3 _scratch2
        let _c3 := _back2 _t4
        ok (_c3, _scratch2))
        = _
    unfold
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.montgomery_multiply_by_constant
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.add
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations.sub
    -- Now the body is in terms of `classify`, `arithmetic.mont_mul_by_const`, `arithmetic.add`, `arithmetic.sub`.
    simp only [bind_tc_ok, h_classify]
    -- Now scratch2 = arithmetic.mont_mul_by_const scratch1 zeta_r;
    -- L1.4 gives h_scratch2_eq for that.
    rw [h_scratch2_eq]
    simp only [bind_tc_ok, h_idx_a, h_upd_b, h_imt_c1_a, h_t2_eq]
    -- After threading through index_mut_back1 := c1.set a, the remaining
    -- shape is `(c1.set a t2).index_mut_usize b >>= …`. Now apply h_imt_c2_b
    -- (whose LHS is `c2.index_mut_usize b` = `(c1.set a t2).index_mut_usize b`).
    show ((c1.set a t2).index_mut_usize b >>= _) = _
    rw [show (c1.set a t2).index_mut_usize b = c2.index_mut_usize b from rfl, h_imt_c2_b]
    simp only [bind_tc_ok, h_t4_eq]
    rfl
  apply triple_of_ok_l3 h_body
  -- Now prove the post for (c3, scratch2):
  --   1) c3[a] bounded by (B+1)*3328
  --   2) c3[b] bounded by (B+1)*3328
  --   3) c3[k] = coefficients[k] for k ≠ a, k ≠ b.
  -- Key chain: c3 = c2.set b t4, c2 = c1.set a t2, c1 = coefficients.set b t.
  have h_c3_a_val_eq : c3.val[a.val]! = t2 := by
    show (c2.set b t4).val[a.val]! = t2
    have h_ne1 : (c2.set b t4)[a.val]! = c2[a.val]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne c2 b a.val t4 h_b_ne_a
    have h_ne1_val : (c2.set b t4).val[a.val]! = c2.val[a.val]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_ne1
    rw [h_ne1_val]
    -- c2.val[a.val]! = (c1.set a t2)[a.val]! = t2.
    show (c1.set a t2).val[a.val]! = t2
    have h_eq : (c1.set a t2)[a.val]! = t2 := by
      have h_a_lt_c1 : a.val < c1.length := h_c1_a_lt
      exact Aeneas.Std.Array.getElem!_Nat_set_eq c1 a a.val t2 ⟨rfl, h_a_lt_c1⟩
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_eq
  have h_c3_b_val_eq : c3.val[b.val]! = t4 := by
    show (c2.set b t4).val[b.val]! = t4
    have h_eq : (c2.set b t4)[b.val]! = t4 :=
      Aeneas.Std.Array.getElem!_Nat_set_eq c2 b b.val t4 ⟨rfl, h_c2_b_lt⟩
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h_eq
  refine ⟨?_, ?_, ?_⟩
  · intro ℓ hℓ
    rw [h_c3_a_val_eq]; exact h_t2_bd ℓ hℓ
  · intro ℓ hℓ
    rw [h_c3_b_val_eq]; exact h_t4_bd ℓ hℓ
  · intro k h_k_lt h_k_ne_a h_k_ne_b
    -- c3[k] = (c2.set b t4)[k] = c2[k] (k ≠ b)
    --       = (c1.set a t2)[k] = c1[k] (k ≠ a)
    --       = (coefficients.set b t)[k] = coefficients[k] (k ≠ b).
    show (c2.set b t4).val[k]! = coefficients.val[k]!
    have h1 : (c2.set b t4)[k]! = c2[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne c2 b k t4 (fun h => h_k_ne_b h.symm)
    have h1' : (c2.set b t4).val[k]! = c2.val[k]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h1
    rw [h1']
    show (c1.set a t2).val[k]! = coefficients.val[k]!
    have h2 : (c1.set a t2)[k]! = c1[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne c1 a k t2 (fun h => h_k_ne_a h.symm)
    have h2' : (c1.set a t2).val[k]! = c1.val[k]! := by
      simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h2
    rw [h2']
    show (coefficients.set b t).val[k]! = coefficients.val[k]!
    have h3 : (coefficients.set b t)[k]! = coefficients[k]! :=
      Aeneas.Std.Array.getElem!_Nat_set_ne coefficients b k t (fun h => h_k_ne_b h.symm)
    simpa [Aeneas.Std.Array.getElem!_Nat_eq] using h3

/-! ### inner loop helper

The inner loop `ntt_at_layer_4_plus_loop0_loop0` iterates over `j ∈ [0, step_vec)`,
each iter calling `ntt_layer_int_vec_step` on lanes `(a_offset+j, b_offset+j)`
with a **fixed** `zeta_r = polynomial.zeta zeta_i`. The invariant after `j` iters
has four zones (all bounds in absolute value):
  - lanes `[a_offset, a_offset+j)` and `[b_offset, b_offset+j)`: processed,
    each bounded by `(B+1)*3328`.
  - lanes `[a_offset+j, a_offset+step_vec)` and `[b_offset+j, b_offset+step_vec)`:
    untouched, equal to `re.coefficients` at the same index (so bounded by `B*3328`).
  - other lanes: untouched.

We require `[a_offset, a_offset+step_vec)` and `[b_offset, b_offset+step_vec)`
to be disjoint and lie within `[0, 16)` — i.e. `a_offset + step_vec ≤ b_offset`
and `b_offset + step_vec ≤ 16` (with `a_offset ≤ b_offset` from L3.4's caller).
-/

namespace Layer4PlusInner

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

/-- Inner-loop accumulator: a `(PolynomialRingElement × scratch)`. -/
abbrev Acc :=
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Inner-loop invariant after `j` iters. `bnd` is the absolute input bound;
    processed lanes are at `bnd + 3328`. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize) (bnd : Nat) :
    Std.Usize → Acc → Result Prop :=
  fun j acc => pure (
    -- Processed-a zone: lanes [a_offset, a_offset + j).
    (∀ ℓ' : Nat, ℓ' < j.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[a_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs
          ≤ bnd + 3328)
    -- Processed-b zone: lanes [b_offset, b_offset + j).
    ∧ (∀ ℓ' : Nat, ℓ' < j.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[b_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs
          ≤ bnd + 3328)
    -- Untouched lanes [a_offset+j, a_offset+step_vec) match re.
    ∧ (∀ ℓ' : Nat, j.val ≤ ℓ' → ℓ' < step_vec.val →
        acc.1.coefficients.val[a_offset.val + ℓ']!
          = re.coefficients.val[a_offset.val + ℓ']!)
    -- Untouched lanes [b_offset+j, b_offset+step_vec) match re.
    ∧ (∀ ℓ' : Nat, j.val ≤ ℓ' → ℓ' < step_vec.val →
        acc.1.coefficients.val[b_offset.val + ℓ']!
          = re.coefficients.val[b_offset.val + ℓ']!)
    -- Lanes outside the two ranges are unchanged from re.
    ∧ (∀ k : Nat, k < 16 →
        (k < a_offset.val ∨ a_offset.val + step_vec.val ≤ k ∧ k < b_offset.val
          ∨ b_offset.val + step_vec.val ≤ k) →
        acc.1.coefficients.val[k]! = re.coefficients.val[k]!))

/-- Inner-loop step post. -/
def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (a_offset b_offset step_vec : Std.Usize) (bnd : Nat) (j : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      j.val < step_vec.val ∧ iter'.«end» = step_vec
        ∧ iter'.start.val = j.val + 1
        ∧ (inv re a_offset b_offset step_vec bnd iter'.start acc').holds
  | .done y => (inv re a_offset b_offset step_vec bnd step_vec y).holds

end Layer4PlusInner

/-- Inner-loop step lemma. Each body iter calls `ntt_layer_int_vec_step` on
    lanes `(a_offset+j, b_offset+j)`, transforming both bounds from `bnd` to
    `bnd + 3328`. We only need the bound on `re` for lanes in the
    a-window `[a_offset, a_offset+step_vec)`. -/
private theorem ntt_at_layer_4_plus_inner_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i a_offset b_offset step_vec : Std.Usize) (bnd : Nat) (h_bnd : bnd ≤ 8 * 3328)
    (h_zeta_lt : zeta_i.val < 128)
    (h_ranges : a_offset.val + step_vec.val ≤ b_offset.val
                 ∧ b_offset.val + step_vec.val ≤ 16)
    (h_pre_a : ∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[a_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs ≤ bnd)
    (acc : Layer4PlusInner.Acc)
    (j : Std.Usize) (h_le : j.val ≤ step_vec.val)
    (hinv : (Layer4PlusInner.inv re a_offset b_offset step_vec bnd j acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i a_offset b_offset { start := j, «end» := step_vec } acc.1 acc.2
    ⦃ ⇓ r => ⌜ Layer4PlusInner.step_post re a_offset b_offset step_vec bnd j r ⌝ ⦄ := by
  obtain ⟨h_a_disj, h_b_le_16⟩ := h_ranges
  -- The 5 invariant conjuncts.
  obtain ⟨h_a_done, h_b_done, h_a_undone, h_b_undone, h_other⟩ :=
    of_pure_prop_holds_l3 hinv
  have h_coef_len : acc.1.coefficients.length = 16 := Std.Array.length_eq _
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
  by_cases h_lt : j.val < step_vec.val
  · -- Some j branch.
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq_gen j step_vec h_lt
    -- 1) i = a_offset + j.
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_step_vec_le_16 : step_vec.val ≤ 16 := by omega
    have h_a_plus_j_lt_16 : a_offset.val + j.val < 16 := by omega
    have h_b_plus_j_lt_16 : b_offset.val + j.val < 16 := by omega
    have h_i_max : a_offset.val + j.val ≤ Std.Usize.max := by
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i, h_i_eq, h_i_val⟩ := usize_add_ok_eq a_offset j h_i_max
    have h_i_val_arith : i.val = a_offset.val + j.val := h_i_val
    -- 2) i1 = b_offset + j.
    have h_i1_max : b_offset.val + j.val ≤ Std.Usize.max := by
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨i1, h_i1_eq, h_i1_val⟩ := usize_add_ok_eq b_offset j h_i1_max
    have h_i1_val_arith : i1.val = b_offset.val + j.val := h_i1_val
    -- 3) i2 = polynomial.zeta zeta_i.
    obtain ⟨zeta_r, h_zeta_eq, h_zeta_bd⟩ :=
      triple_exists_ok_l3 (polynomial.zeta_spec zeta_i h_zeta_lt)
    -- 4) ntt_layer_int_vec_step on (i, i1).
    have h_i_lt : i.val < 16 := by rw [h_i_val_arith]; exact h_a_plus_j_lt_16
    have h_i1_lt : i1.val < 16 := by rw [h_i1_val_arith]; exact h_b_plus_j_lt_16
    have h_i_ne_i1 : i.val ≠ i1.val := by rw [h_i_val_arith, h_i1_val_arith]; omega
    -- Precondition for ntt_layer_int_vec_step: acc[i] (= acc[a_offset+j]) is at B*3328.
    -- From h_a_undone, acc.coef[a_offset+j] = re.coef[a_offset+j], hence bounded by h_pre.
    have h_acc_i_eq :
        acc.1.coefficients.val[i.val]! = re.coefficients.val[i.val]! := by
      rw [h_i_val_arith]
      exact h_a_undone j.val (Nat.le_refl _) h_lt
    have h_pre_i : ∀ ℓ : Nat, ℓ < 16 →
        ((acc.1.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ bnd := by
      intro ℓ hℓ
      rw [h_acc_i_eq]
      show ((re.coefficients.val[i.val]!).elements.val[ℓ]!).val.natAbs ≤ bnd
      rw [show i.val = a_offset.val + j.val from h_i_val_arith]
      exact h_pre_a j.val h_lt ℓ hℓ
    obtain ⟨step_out, h_step_eq, h_step_post⟩ :=
      triple_exists_ok_l3
        (ntt_layer_int_vec_step_spec acc.1.coefficients i i1 acc.2 zeta_r
          h_i_lt h_i1_lt h_i_ne_i1 h_zeta_bd bnd h_bnd h_pre_i)
    obtain ⟨h_step_a_bd, h_step_b_bd, h_step_other⟩ := h_step_post
    -- Next-state.
    set acc' : Layer4PlusInner.Acc :=
      ({ coefficients := step_out.1 }, step_out.2) with hacc'_def
    -- Compose the body into one .ok.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          zeta_i a_offset b_offset { start := j, «end» := step_vec } acc.1 acc.2
        = .ok (cont (({ start := s, «end» := step_vec }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := j, «end» := step_vec }
                : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := j, «end» := step_vec }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [bind_tc_ok, h_i_eq, h_i1_eq, h_zeta_eq, h_step_eq, hacc'_def]
      -- step_out is a Prod (Array PortableVector 16, PortableVector); the
      -- `let (a, scratch1) := step_out` destructure equals (step_out.1, step_out.2)
      -- definitionally.
      rfl
    apply triple_of_ok_l3 h_body
    show Layer4PlusInner.step_post re a_offset b_offset step_vec bnd j
      (.cont (({ start := s, «end» := step_vec }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer4PlusInner.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    -- We need to show inv at s = j+1.
    -- The 5 conjuncts:
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- A. acc'.coef[a_offset+ℓ'] bounded for ℓ' < s.val = j.val + 1.
    · intro ℓ' hℓ' ℓ hℓ
      rw [hs_val] at hℓ'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ' with hℓ'_lt_j | hℓ'_eq_j
      · -- ℓ' < j.val: unchanged by step (i = a_offset+j; ℓ' < j ⇒ a_offset+ℓ' ≠ i, ≠ i1).
        have h_idx_lt_16 : a_offset.val + ℓ' < 16 := by omega
        have h_ne_i : a_offset.val + ℓ' ≠ i.val := by rw [h_i_val_arith]; omega
        have h_ne_i1 : a_offset.val + ℓ' ≠ i1.val := by rw [h_i1_val_arith]; omega
        have h_unchanged :
            step_out.1.val[a_offset.val + ℓ']! = acc.1.coefficients.val[a_offset.val + ℓ']! :=
          h_step_other (a_offset.val + ℓ') h_idx_lt_16 h_ne_i h_ne_i1
        show (step_out.1.val[a_offset.val + ℓ']!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_unchanged]
        exact h_a_done ℓ' hℓ'_lt_j ℓ hℓ
      · -- ℓ' = j.val: this is lane i = a_offset+j. Apply h_step_a_bd.
        subst hℓ'_eq_j
        have h_eq : a_offset.val + j.val = i.val := h_i_val_arith.symm
        show (step_out.1.val[a_offset.val + j.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_eq]; exact h_step_a_bd ℓ hℓ
    -- B. acc'.coef[b_offset+ℓ'] bounded for ℓ' < s.val = j.val + 1.
    · intro ℓ' hℓ' ℓ hℓ
      rw [hs_val] at hℓ'
      rcases Nat.lt_succ_iff_lt_or_eq.mp hℓ' with hℓ'_lt_j | hℓ'_eq_j
      · have h_idx_lt_16 : b_offset.val + ℓ' < 16 := by omega
        have h_ne_i : b_offset.val + ℓ' ≠ i.val := by rw [h_i_val_arith]; omega
        have h_ne_i1 : b_offset.val + ℓ' ≠ i1.val := by rw [h_i1_val_arith]; omega
        have h_unchanged :
            step_out.1.val[b_offset.val + ℓ']! = acc.1.coefficients.val[b_offset.val + ℓ']! :=
          h_step_other (b_offset.val + ℓ') h_idx_lt_16 h_ne_i h_ne_i1
        show (step_out.1.val[b_offset.val + ℓ']!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_unchanged]
        exact h_b_done ℓ' hℓ'_lt_j ℓ hℓ
      · subst hℓ'_eq_j
        have h_eq : b_offset.val + j.val = i1.val := h_i1_val_arith.symm
        show (step_out.1.val[b_offset.val + j.val]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_eq]; exact h_step_b_bd ℓ hℓ
    -- C. Untouched a-zone for ℓ' ≥ s.val.
    · intro ℓ' hℓ'_ge hℓ'_lt
      rw [hs_val] at hℓ'_ge
      have hℓ'_gt_j : j.val < ℓ' := by omega
      have h_ge' : j.val ≤ ℓ' := Nat.le_of_lt hℓ'_gt_j
      have h_idx_lt_16 : a_offset.val + ℓ' < 16 := by omega
      have h_ne_i : a_offset.val + ℓ' ≠ i.val := by rw [h_i_val_arith]; omega
      have h_ne_i1 : a_offset.val + ℓ' ≠ i1.val := by rw [h_i1_val_arith]; omega
      have h_unchanged :
          step_out.1.val[a_offset.val + ℓ']! = acc.1.coefficients.val[a_offset.val + ℓ']! :=
        h_step_other (a_offset.val + ℓ') h_idx_lt_16 h_ne_i h_ne_i1
      show step_out.1.val[a_offset.val + ℓ']! = re.coefficients.val[a_offset.val + ℓ']!
      rw [h_unchanged]
      exact h_a_undone ℓ' h_ge' hℓ'_lt
    -- D. Untouched b-zone for ℓ' ≥ s.val.
    · intro ℓ' hℓ'_ge hℓ'_lt
      rw [hs_val] at hℓ'_ge
      have hℓ'_gt_j : j.val < ℓ' := by omega
      have h_ge' : j.val ≤ ℓ' := Nat.le_of_lt hℓ'_gt_j
      have h_idx_lt_16 : b_offset.val + ℓ' < 16 := by omega
      have h_ne_i : b_offset.val + ℓ' ≠ i.val := by rw [h_i_val_arith]; omega
      have h_ne_i1 : b_offset.val + ℓ' ≠ i1.val := by rw [h_i1_val_arith]; omega
      have h_unchanged :
          step_out.1.val[b_offset.val + ℓ']! = acc.1.coefficients.val[b_offset.val + ℓ']! :=
        h_step_other (b_offset.val + ℓ') h_idx_lt_16 h_ne_i h_ne_i1
      show step_out.1.val[b_offset.val + ℓ']! = re.coefficients.val[b_offset.val + ℓ']!
      rw [h_unchanged]
      exact h_b_undone ℓ' h_ge' hℓ'_lt
    -- E. Other lanes unchanged from re.
    · intro k h_k_lt h_k_other
      have h_ne_i : k ≠ i.val := by
        rw [h_i_val_arith]
        rcases h_k_other with h1 | ⟨h2a, h2b⟩ | h3
        · omega
        · omega
        · omega
      have h_ne_i1 : k ≠ i1.val := by
        rw [h_i1_val_arith]
        rcases h_k_other with h1 | ⟨h2a, h2b⟩ | h3
        · omega
        · omega
        · omega
      have h_unchanged :
          step_out.1.val[k]! = acc.1.coefficients.val[k]! :=
        h_step_other k h_k_lt h_ne_i h_ne_i1
      show step_out.1.val[k]! = re.coefficients.val[k]!
      rw [h_unchanged]
      exact h_other k h_k_lt h_k_other
  · -- None branch (j ≥ step_vec).
    have hj_ge : j.val ≥ step_vec.val := Nat.not_lt.mp h_lt
    have hj_eq : j.val = step_vec.val := by omega
    have h_iter_none := iter_next_none_eq_gen j step_vec hj_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          zeta_i a_offset b_offset { start := j, «end» := step_vec } acc.1 acc.2
        = .ok (done (acc.1, acc.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := j, «end» := step_vec }
                : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := j, «end» := step_vec }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show Layer4PlusInner.step_post re a_offset b_offset step_vec bnd j (.done acc)
    unfold Layer4PlusInner.step_post
    show (Layer4PlusInner.inv re a_offset b_offset step_vec bnd step_vec acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro ℓ' hℓ' ℓ hℓ; rw [← hj_eq] at hℓ'; exact h_a_done ℓ' hℓ' ℓ hℓ
    · intro ℓ' hℓ' ℓ hℓ; rw [← hj_eq] at hℓ'; exact h_b_done ℓ' hℓ' ℓ hℓ
    · intro ℓ' hℓ'_ge hℓ'_lt
      rw [← hj_eq] at hℓ'_ge; exact h_a_undone ℓ' hℓ'_ge hℓ'_lt
    · intro ℓ' hℓ'_ge hℓ'_lt
      rw [← hj_eq] at hℓ'_ge; exact h_b_undone ℓ' hℓ'_ge hℓ'_lt
    · exact h_other

set_option maxHeartbeats 16000000 in
/-- Inner-loop Triple. Closes by `loop_range_spec_usize` + the step lemma. -/
private theorem ntt_at_layer_4_plus_inner_loop_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (acc_in : Layer4PlusInner.Acc)
    (zeta_i a_offset b_offset step_vec : Std.Usize) (bnd : Nat) (h_bnd : bnd ≤ 8 * 3328)
    (h_zeta_lt : zeta_i.val < 128)
    (h_step_vec_pos : 0 < step_vec.val)
    (h_step_vec_le_16 : step_vec.val ≤ 16)
    (h_a_disj : a_offset.val + step_vec.val ≤ b_offset.val)
    (h_b_le_16 : b_offset.val + step_vec.val ≤ 16)
    (h_pre_a : ∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[a_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs ≤ bnd)
    (h_acc_in_eq : acc_in.1 = re) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := 0#usize, «end» := step_vec } zeta_i acc_in.1 acc_in.2 a_offset b_offset
    ⦃ ⇓ p => ⌜ -- Both a-zone and b-zone fully processed.
              (∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
                  ((p.1.coefficients.val[a_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs
                    ≤ bnd + 3328)
              ∧ (∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
                  ((p.1.coefficients.val[b_offset.val + ℓ']!).elements.val[ℓ]!).val.natAbs
                    ≤ bnd + 3328)
              -- Other lanes unchanged from re.
              ∧ (∀ k : Nat, k < 16 →
                  (k < a_offset.val ∨ a_offset.val + step_vec.val ≤ k ∧ k < b_offset.val
                    ∨ b_offset.val + step_vec.val ≤ k) →
                  p.1.coefficients.val[k]! = re.coefficients.val[k]!) ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          zeta_i a_offset b_offset iter1 acc1.1 acc1.2)
      (β := Layer4PlusInner.Acc)
      acc_in
      0#usize step_vec
      (Layer4PlusInner.inv re a_offset b_offset step_vec bnd)
      (by scalar_tac : (0#usize : Std.Usize).val ≤ step_vec.val)
      (pure_prop_holds_l3
        ⟨fun ℓ' hℓ' _ _ => absurd hℓ' (Nat.not_lt_zero _),
         fun ℓ' hℓ' _ _ => absurd hℓ' (Nat.not_lt_zero _),
         fun ℓ' _ _ => by rw [h_acc_in_eq],
         fun ℓ' _ _ => by rw [h_acc_in_eq],
         fun k _ _ => by rw [h_acc_in_eq]⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_a_done, h_b_done, _h_a_undone, _h_b_undone, h_other⟩ := of_pure_prop_holds_l3 h
    exact ⟨h_a_done, h_b_done, h_other⟩
  · -- Step lemma.
    intro acc k h_ge h_le hinv
    have h_step := ntt_at_layer_4_plus_inner_step_lemma
      re zeta_i a_offset b_offset step_vec bnd h_bnd h_zeta_lt
      ⟨h_a_disj, h_b_le_16⟩ h_pre_a acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer4PlusInner.step_post re a_offset b_offset step_vec bnd k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusInner.step_post] using hP
    · have hP : Layer4PlusInner.step_post re a_offset b_offset step_vec bnd k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusInner.step_post] using hP

/-! ### outer loop helper

The outer loop `ntt_at_layer_4_plus_loop0` iterates `round ∈ [0, outer_count)`,
each iter increments `zeta_i` by 1 and calls the inner loop on the disjoint
lane-pair window `[a_offset, a_offset + step_vec) ∪ [b_offset, b_offset + step_vec)`
where `a_offset = round * 2 * step_vec`, `b_offset = a_offset + step_vec`.
The outer invariant after `round` iters: lanes `[0, 2*round*step_vec)` are
processed at `(B+1)*3328`; lanes `[2*round*step_vec, 16)` unchanged.

We require `2 * outer_count * step_vec = 16` (the L3.4 caller invariant for
layer ∈ {4, 5, 6}).
-/

/-- Local helper: `x * y` reduces to `.ok z` with `z.val = x.val * y.val` under
    no-overflow on `Usize`. Mirrors `usize_add_ok_eq` / `usize_div_ok_eq`. -/
private theorem usize_mul_ok_eq (x y : Std.Usize)
    (h_max : x.val * y.val ≤ Std.Usize.max) :
    ∃ z : Std.Usize, (x * y : Result Std.Usize) = .ok z ∧ z.val = x.val * y.val := by
  have hT := Std.Usize.mul_spec h_max
  obtain ⟨z, h_eq, h_v⟩ := Std.WP.spec_imp_exists hT
  refine ⟨z, h_eq, ?_⟩
  show z.val = x.val * y.val
  exact h_v

namespace Layer4PlusOuter

open libcrux_iot_ml_kem.Spec.ModularArith libcrux_iot_ml_kem.Spec.Montgomery libcrux_iot_ml_kem.Spec.NumericKeystones libcrux_iot_ml_kem.Util.CreateI libcrux_iot_ml_kem.Util.LoopSpecs libcrux_iot_ml_kem.Util.SliceSpecs libcrux_iot_ml_kem.Vector.Portable.Arithmetic.BvMasks libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper Aeneas.Std Result ControlFlow

/-- Outer-loop accumulator: `(zeta_i, PolynomialRingElement, scratch)`. -/
abbrev Acc := Std.Usize ×
  libcrux_iot_ml_kem.polynomial.PolynomialRingElement
    libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector ×
  libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector

/-- Outer-loop invariant after `round` iters: lanes `[0, 2*round*step_vec)`
    are processed; lanes `[2*round*step_vec, 16)` match `re`. -/
def inv
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_init step_vec : Std.Usize) (bnd : Nat) :
    Std.Usize → Acc → Result Prop :=
  fun round acc => pure (
    acc.1.val = zeta_i_init.val + round.val
    ∧ (∀ k : Nat, k < 2 * round.val * step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[k]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328)
    ∧ (∀ k : Nat, 2 * round.val * step_vec.val ≤ k → k < 16 →
        acc.2.1.coefficients.val[k]! = re.coefficients.val[k]!))

def step_post
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_init step_vec outer_count : Std.Usize) (bnd : Nat) (round : Std.Usize)
    (r : ControlFlow
      ((CoreModels.core.ops.range.Range Std.Usize) × Acc) Acc) : Prop :=
  match r with
  | .cont (iter', acc') =>
      round.val < outer_count.val ∧ iter'.«end» = outer_count
        ∧ iter'.start.val = round.val + 1
        ∧ (inv re zeta_i_init step_vec bnd iter'.start acc').holds
  | .done y => (inv re zeta_i_init step_vec bnd outer_count y).holds

end Layer4PlusOuter

set_option maxHeartbeats 16000000 in
/-- Outer-loop step lemma. Each iter calls the inner loop on the window
    `[2*round*step_vec, (2*round+2)*step_vec)`, transforming all 2*step_vec
    lanes in that window from `bnd` to `bnd + 3328`. -/
private theorem ntt_at_layer_4_plus_outer_step_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_init step_vec outer_count : Std.Usize) (bnd : Nat) (h_bnd : bnd ≤ 8 * 3328)
    (h_step_vec_pos : 0 < step_vec.val)
    (h_step_vec_le_16 : step_vec.val ≤ 16)
    (h_outer_count_pos : 0 < outer_count.val)
    (h_two_oc_sv_eq : 2 * outer_count.val * step_vec.val = 16)
    (h_zeta_init_lt : zeta_i_init.val + outer_count.val < 128)
    (h_pre : ∀ i : Nat, i < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[i]!).elements.val[ℓ]!).val.natAbs ≤ bnd)
    (acc : Layer4PlusOuter.Acc)
    (round : Std.Usize) (h_le : round.val ≤ outer_count.val)
    (hinv : (Layer4PlusOuter.inv re zeta_i_init step_vec bnd round acc).holds) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      step_vec { start := round, «end» := outer_count } acc.1 acc.2.1 acc.2.2
    ⦃ ⇓ r => ⌜ Layer4PlusOuter.step_post re zeta_i_init step_vec outer_count bnd round r ⌝ ⦄ := by
  obtain ⟨h_zeta_acc, h_done, h_undone⟩ := of_pure_prop_holds_l3 hinv
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
  by_cases h_lt : round.val < outer_count.val
  · -- Some round branch.
    obtain ⟨s, hs_val, h_iter_some⟩ := iter_next_some_eq_gen round outer_count h_lt
    -- 1) zeta_i1 = zeta_i + 1.
    have h_um : (1#usize : Std.Usize).val = 1 := rfl
    have h_um2 : (2#usize : Std.Usize).val = 2 := rfl
    have h_zeta_lt : acc.1.val + (1#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um]
      have : acc.1.val + 1 ≤ 128 := by rw [h_zeta_acc]; omega
      have : (128 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨zi1, h_zi1_eq, h_zi1_val⟩ := usize_add_ok_eq acc.1 1#usize h_zeta_lt
    have h_zi1_val_arith : zi1.val = acc.1.val + 1 := by rw [h_zi1_val, h_um]
    have h_zi1_lt : zi1.val < 128 := by
      rw [h_zi1_val_arith, h_zeta_acc]; omega
    -- 2) i = round * 2. Bound: round.val < outer_count.val; round * 2 ≤ 16.
    have h_round_2_max : round.val * (2#usize : Std.Usize).val ≤ Std.Usize.max := by
      rw [h_um2]
      have : round.val * 2 ≤ outer_count.val * 2 := Nat.mul_le_mul_right 2 (Nat.le_of_lt h_lt)
      have : outer_count.val * 2 ≤ 16 := by
        have hh : 2 * outer_count.val * step_vec.val = 16 := h_two_oc_sv_eq
        -- 2 * o ≤ 2 * o * s = 16 (using s ≥ 1 via h_step_vec_pos)
        have : 2 * outer_count.val ≤ 2 * outer_count.val * step_vec.val :=
          Nat.le_mul_of_pos_right _ h_step_vec_pos
        omega
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨ri2, h_ri2_eq, h_ri2_val⟩ := usize_mul_ok_eq round 2#usize h_round_2_max
    have h_ri2_val_arith : ri2.val = round.val * 2 := by rw [h_ri2_val, h_um2]
    -- 3) a_offset = ri2 * step_vec. Bound: ri2.val * step_vec.val ≤ 16.
    have h_ri2_lt_oc2 : ri2.val ≤ outer_count.val * 2 := by
      rw [h_ri2_val_arith]; exact Nat.mul_le_mul_right 2 (Nat.le_of_lt h_lt)
    have h_oc2_sv : outer_count.val * 2 * step_vec.val = 16 := by
      have := h_two_oc_sv_eq; grind
    have h_ri2_sv_le_16 : ri2.val * step_vec.val ≤ 16 := by
      calc ri2.val * step_vec.val ≤ (outer_count.val * 2) * step_vec.val :=
            Nat.mul_le_mul_right _ h_ri2_lt_oc2
        _ = 16 := h_oc2_sv
    have h_ao_max : ri2.val * step_vec.val ≤ Std.Usize.max := by
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨a_off, h_ao_eq, h_ao_val⟩ := usize_mul_ok_eq ri2 step_vec h_ao_max
    -- 4) b_offset = a_off + step_vec. Bound: a_off + step_vec ≤ 16.
    have h_ao_val_arith : a_off.val = ri2.val * step_vec.val := h_ao_val
    have h_ao_eq_2rsv : a_off.val = 2 * round.val * step_vec.val := by
      rw [h_ao_val_arith, h_ri2_val_arith]; ring
    have h_bo_max : a_off.val + step_vec.val ≤ Std.Usize.max := by
      have : a_off.val + step_vec.val ≤ 16 := by
        rw [h_ao_eq_2rsv]
        have hh : 2 * (round.val + 1) * step_vec.val ≤ 16 := by
          have := h_two_oc_sv_eq
          calc 2 * (round.val + 1) * step_vec.val
              ≤ 2 * outer_count.val * step_vec.val := by
                apply Nat.mul_le_mul_right; omega
            _ = 16 := h_two_oc_sv_eq
        grind
      have : (16 : Nat) ≤ Std.Usize.max := by scalar_tac
      omega
    obtain ⟨b_off, h_bo_eq, h_bo_val⟩ := usize_add_ok_eq a_off step_vec h_bo_max
    have h_bo_val_arith : b_off.val = a_off.val + step_vec.val := h_bo_val
    -- Disjointness: a_off + step_vec ≤ b_off (definitional).
    have h_a_disj : a_off.val + step_vec.val ≤ b_off.val := by
      rw [h_bo_val_arith]
    -- b_off + step_vec ≤ 16 (definitional via 2*(round+1)*step_vec ≤ 16).
    have h_b_le_16 : b_off.val + step_vec.val ≤ 16 := by
      rw [h_bo_val_arith, h_ao_eq_2rsv]
      have hh : 2 * (round.val + 1) * step_vec.val ≤ 16 := by
        calc 2 * (round.val + 1) * step_vec.val
            ≤ 2 * outer_count.val * step_vec.val := by
              apply Nat.mul_le_mul_right; omega
          _ = 16 := h_two_oc_sv_eq
      grind
    -- 5) Apply inner loop spec, using acc.2.1 as the "re" of the inner call.
    -- We need to prove that the inner-loop precondition holds on acc.2.1's
    -- window `[a_off, a_off+step_vec)` (a-side bound only).
    -- For `ℓ' < step_vec`, the lane `a_off + ℓ' = 2*round*step_vec + ℓ'` is
    -- within `[2*round*step_vec, (2*round+1)*step_vec) ⊆ [2*round*step_vec, 16)`.
    -- The outer invariant's `h_undone` gives `acc.2.1[k] = re[k]` for those.
    have h_pre_a_inner : ∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
        ((acc.2.1.coefficients.val[a_off.val + ℓ']!).elements.val[ℓ]!).val.natAbs ≤ bnd := by
      intro ℓ' hℓ' ℓ hℓ
      -- a_off + ℓ' = 2*round*step_vec + ℓ' ≥ 2*round*step_vec (undone)
      -- a_off + ℓ' ≤ 2*round*step_vec + step_vec - 1 < 16.
      have h_idx_ge : 2 * round.val * step_vec.val ≤ a_off.val + ℓ' := by
        rw [h_ao_eq_2rsv]; omega
      have h_idx_lt : a_off.val + ℓ' < 16 := by
        rw [h_ao_eq_2rsv]
        have hh : 2 * (round.val + 1) * step_vec.val ≤ 16 := by
          calc 2 * (round.val + 1) * step_vec.val
              ≤ 2 * outer_count.val * step_vec.val := by
                apply Nat.mul_le_mul_right; omega
            _ = 16 := h_two_oc_sv_eq
        grind
      have h_eq : acc.2.1.coefficients.val[a_off.val + ℓ']!
                    = re.coefficients.val[a_off.val + ℓ']! :=
        h_undone (a_off.val + ℓ') h_idx_ge h_idx_lt
      rw [h_eq]
      exact h_pre (a_off.val + ℓ') h_idx_lt ℓ hℓ
    -- The inner loop spec.
    have h_inner_spec :
        ⦃ ⌜ True ⌝ ⦄
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0_loop0
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          { start := 0#usize, «end» := step_vec } zi1 acc.2.1 acc.2.2 a_off b_off
        ⦃ ⇓ p => ⌜
          (∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
              ((p.1.coefficients.val[a_off.val + ℓ']!).elements.val[ℓ]!).val.natAbs
                ≤ bnd + 3328)
          ∧ (∀ ℓ' : Nat, ℓ' < step_vec.val → ∀ ℓ : Nat, ℓ < 16 →
              ((p.1.coefficients.val[b_off.val + ℓ']!).elements.val[ℓ]!).val.natAbs
                ≤ bnd + 3328)
          ∧ (∀ k : Nat, k < 16 →
              (k < a_off.val ∨ a_off.val + step_vec.val ≤ k ∧ k < b_off.val
                ∨ b_off.val + step_vec.val ≤ k) →
              p.1.coefficients.val[k]! = acc.2.1.coefficients.val[k]!) ⌝ ⦄ :=
      ntt_at_layer_4_plus_inner_loop_lemma
        acc.2.1 acc.2 zi1 a_off b_off step_vec bnd h_bnd h_zi1_lt
        h_step_vec_pos h_step_vec_le_16 h_a_disj h_b_le_16
        h_pre_a_inner rfl
    obtain ⟨inner_out, h_inner_eq, h_inner_post⟩ := triple_exists_ok_l3 h_inner_spec
    obtain ⟨h_inner_a_bd, h_inner_b_bd, h_inner_other⟩ := h_inner_post
    -- Next-state.
    set acc' : Layer4PlusOuter.Acc := (zi1, inner_out.1, inner_out.2) with hacc'_def
    -- Compose the body into one .ok.
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          step_vec { start := round, «end» := outer_count } acc.1 acc.2.1 acc.2.2
        = .ok (cont (({ start := s, «end» := outer_count }
                        : CoreModels.core.ops.range.Range Std.Usize),
                     acc')) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := round, «end» := outer_count }
                : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := round, «end» := outer_count }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_some]
      simp [bind_tc_ok, h_zi1_eq, h_ri2_eq, h_ao_eq, h_bo_eq, h_inner_eq, hacc'_def]
      rfl
    apply triple_of_ok_l3 h_body
    show Layer4PlusOuter.step_post re zeta_i_init step_vec outer_count bnd round
      (.cont (({ start := s, «end» := outer_count }
                : CoreModels.core.ops.range.Range Std.Usize),
              acc'))
    unfold Layer4PlusOuter.step_post
    refine ⟨h_lt, rfl, hs_val, ?_⟩
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    -- Outer invariant after this iter.
    -- A. acc'.1.val = zeta_i_init + s.val = zeta_i_init + round.val + 1.
    · show zi1.val = zeta_i_init.val + s.val
      rw [h_zi1_val_arith, h_zeta_acc, hs_val]; ring
    -- B. Lanes [0, 2*s.val*step_vec) are processed at (B+1)*3328.
    · intro k hk ℓ hℓ
      -- 2*s*step_vec = 2*(round+1)*step_vec = 2*round*step_vec + 2*step_vec
      --              = a_off + 2*step_vec = b_off + step_vec.
      have h_2s_eq : 2 * s.val * step_vec.val
                      = b_off.val + step_vec.val := by
        rw [hs_val, h_bo_val_arith, h_ao_eq_2rsv]; ring
      -- Cases: k ∈ [0, a_off) [already processed]; k ∈ [a_off, a_off+step_vec) [inner a-zone];
      --        k ∈ [a_off+step_vec, b_off) [empty — a_disj]; k ∈ [b_off, b_off+step_vec) [inner b-zone].
      by_cases h_k_lt_a : k < a_off.val
      · -- Already processed before this iter. Use h_inner_other + h_done.
        have h_k_other : k < a_off.val ∨ a_off.val + step_vec.val ≤ k ∧ k < b_off.val
                         ∨ b_off.val + step_vec.val ≤ k := Or.inl h_k_lt_a
        have h_k_lt_16 : k < 16 := by
          rw [h_2s_eq] at hk
          have : a_off.val ≤ b_off.val + step_vec.val := by
            rw [h_bo_val_arith]; omega
          omega
        have h_eq : inner_out.1.coefficients.val[k]! = acc.2.1.coefficients.val[k]! :=
          h_inner_other k h_k_lt_16 h_k_other
        show (inner_out.1.coefficients.val[k]!).elements.val[ℓ]!.val.natAbs ≤ _
        rw [h_eq]
        -- k < a_off = 2*round*step_vec ⇒ k is in done zone of outer inv.
        have h_k_lt_2rsv : k < 2 * round.val * step_vec.val := by
          rw [h_ao_eq_2rsv] at h_k_lt_a; exact h_k_lt_a
        exact h_done k h_k_lt_2rsv ℓ hℓ
      · -- k ≥ a_off. Either in a-window, gap (empty), or b-window.
        have h_k_ge_a : a_off.val ≤ k := Nat.not_lt.mp h_k_lt_a
        by_cases h_k_lt_aps : k < a_off.val + step_vec.val
        · -- In a-window: k - a_off < step_vec; apply h_inner_a_bd.
          set ℓ' := k - a_off.val with hℓ'_def
          have hℓ'_lt : ℓ' < step_vec.val := by omega
          have h_k_eq : a_off.val + ℓ' = k := by omega
          have := h_inner_a_bd ℓ' hℓ'_lt ℓ hℓ
          rw [h_k_eq] at this
          exact this
        · -- k ≥ a_off + step_vec = b_off. Either in b-window or beyond.
          have h_k_ge_aps : a_off.val + step_vec.val ≤ k := Nat.not_lt.mp h_k_lt_aps
          have h_k_ge_b : b_off.val ≤ k := by rw [h_bo_val_arith]; exact h_k_ge_aps
          have h_k_lt_bps : k < b_off.val + step_vec.val := by
            have : k < 2 * s.val * step_vec.val := hk
            rw [h_2s_eq] at this; exact this
          -- In b-window: k - b_off < step_vec; apply h_inner_b_bd.
          set ℓ' := k - b_off.val with hℓ'_def
          have hℓ'_lt : ℓ' < step_vec.val := by omega
          have h_k_eq : b_off.val + ℓ' = k := by omega
          have := h_inner_b_bd ℓ' hℓ'_lt ℓ hℓ
          rw [h_k_eq] at this
          exact this
    -- C. Lanes [2*s.val*step_vec, 16) match re.
    · intro k hk_ge hk_lt
      -- 2*s*step_vec = b_off + step_vec; so k ≥ b_off + step_vec.
      have h_2s_eq : 2 * s.val * step_vec.val = b_off.val + step_vec.val := by
        rw [hs_val, h_bo_val_arith, h_ao_eq_2rsv]; ring
      have h_k_ge_bps : b_off.val + step_vec.val ≤ k := by rw [← h_2s_eq]; exact hk_ge
      have h_k_other : k < a_off.val ∨ a_off.val + step_vec.val ≤ k ∧ k < b_off.val
                       ∨ b_off.val + step_vec.val ≤ k := Or.inr (Or.inr h_k_ge_bps)
      have h_eq1 : inner_out.1.coefficients.val[k]! = acc.2.1.coefficients.val[k]! :=
        h_inner_other k hk_lt h_k_other
      show inner_out.1.coefficients.val[k]! = re.coefficients.val[k]!
      rw [h_eq1]
      -- k ≥ b_off + step_vec ≥ 2*round*step_vec (since round ≤ outer_count - 1, ...) — actually
      -- this isn't trivially related to outer h_undone. Let's compute:
      -- k ≥ b_off + step_vec = 2*s*step_vec ≥ 2*round*step_vec.
      have h_k_ge_2rsv : 2 * round.val * step_vec.val ≤ k := by
        have h_aux : 2 * round.val * step_vec.val ≤ b_off.val + step_vec.val := by
          rw [h_bo_val_arith, h_ao_eq_2rsv]; omega
        omega
      exact h_undone k h_k_ge_2rsv hk_lt
  · -- None branch (round ≥ outer_count).
    have hr_ge : round.val ≥ outer_count.val := Nat.not_lt.mp h_lt
    have hr_eq : round.val = outer_count.val := by omega
    have h_iter_none := iter_next_none_eq_gen round outer_count hr_ge
    have h_body :
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          step_vec { start := round, «end» := outer_count } acc.1 acc.2.1 acc.2.2
        = .ok (done (acc.1, acc.2.1, acc.2.2)) := by
      unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
      conv_lhs =>
        rw [show
          (core.ops.range.Range.Insts.CoreIterTraitsIteratorIterator.next
              core.Usize.Insts.CoreIterRangeStep
              ({ start := round, «end» := outer_count }
                : CoreModels.core.ops.range.Range Std.Usize))
            = (CoreModels.core.iter.range.IteratorRange.next
                core.Usize.Insts.CoreIterRangeStep
                ({ start := round, «end» := outer_count }
                  : CoreModels.core.ops.range.Range Std.Usize))
          from rfl]
      rw [h_iter_none]; rfl
    have h_acc_eq : (acc.1, acc.2.1, acc.2.2) = acc := rfl
    rw [h_acc_eq] at h_body
    apply triple_of_ok_l3 h_body
    show Layer4PlusOuter.step_post re zeta_i_init step_vec outer_count bnd round (.done acc)
    unfold Layer4PlusOuter.step_post
    show (Layer4PlusOuter.inv re zeta_i_init step_vec bnd outer_count acc).holds
    apply pure_prop_holds_l3
    refine ⟨?_, ?_, ?_⟩
    · rw [h_zeta_acc, hr_eq]
    · intro k hk ℓ hℓ; rw [← hr_eq] at hk; exact h_done k hk ℓ hℓ
    · intro k hk_ge hk_lt; rw [← hr_eq] at hk_ge; exact h_undone k hk_ge hk_lt

set_option maxHeartbeats 16000000 in
/-- Outer-loop closure via `loop_range_spec_usize` + the outer step lemma. -/
private theorem ntt_at_layer_4_plus_outer_loop_lemma
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (zeta_i_init step_vec outer_count : Std.Usize) (bnd : Nat) (h_bnd : bnd ≤ 8 * 3328)
    (h_step_vec_pos : 0 < step_vec.val)
    (h_step_vec_le_16 : step_vec.val ≤ 16)
    (h_outer_count_pos : 0 < outer_count.val)
    (h_two_oc_sv_eq : 2 * outer_count.val * step_vec.val = 16)
    (h_zeta_init_lt : zeta_i_init.val + outer_count.val < 128)
    (h_pre : ∀ i : Nat, i < 16 → ∀ ℓ : Nat, ℓ < 16 →
      ((re.coefficients.val[i]!).elements.val[ℓ]!).val.natAbs ≤ bnd) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      { start := 0#usize, «end» := outer_count } zeta_i_init re scratch step_vec
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i_init.val + outer_count.val
              ∧ ∀ i : Nat, i < 16 → ∀ ℓ : Nat, ℓ < 16 →
                  ((p.2.1.coefficients.val[i]!).elements.val[ℓ]!).val.natAbs ≤ bnd + 3328 ⌝ ⦄ := by
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0
  apply Std.Do.Triple.of_entails_right _
    (loop_range_spec_usize
      (fun (iter1, acc1) =>
        libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus_loop0.body
          libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
          step_vec iter1 acc1.1 acc1.2.1 acc1.2.2)
      (β := Layer4PlusOuter.Acc)
      (zeta_i_init, re, scratch)
      0#usize outer_count
      (Layer4PlusOuter.inv re zeta_i_init step_vec bnd)
      (by scalar_tac : (0#usize : Std.Usize).val ≤ outer_count.val)
      (pure_prop_holds_l3
        ⟨by show zeta_i_init.val = zeta_i_init.val + (0#usize : Std.Usize).val; rfl,
         fun k hk _ _ => by
           have h0 : (0#usize : Std.Usize).val = 0 := rfl
           rw [h0] at hk; omega,
         fun _ _ _ => rfl⟩)
      ?_)
  · -- Post entailment.
    rw [PostCond.entails_noThrow]
    intro r h
    obtain ⟨h_zeta_eq, h_done, _h_undone⟩ := of_pure_prop_holds_l3 h
    refine ⟨h_zeta_eq, ?_⟩
    intro i hi ℓ hℓ
    have h16 : 2 * outer_count.val * step_vec.val = 16 := h_two_oc_sv_eq
    apply h_done i (by rw [h16]; exact hi) ℓ hℓ
  · -- Step lemma.
    intro acc k h_ge h_le hinv
    have h_step := ntt_at_layer_4_plus_outer_step_lemma re zeta_i_init step_vec outer_count
      bnd h_bnd h_step_vec_pos h_step_vec_le_16 h_outer_count_pos h_two_oc_sv_eq h_zeta_init_lt
      h_pre acc k h_le hinv
    apply Std.Do.Triple.of_entails_right _ h_step
    rw [PostCond.entails_noThrow]
    intro r hh
    rcases r with ⟨iter', acc'⟩ | y
    · have hP : Layer4PlusOuter.step_post re zeta_i_init step_vec outer_count bnd k (.cont (iter', acc')) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusOuter.step_post] using hP
    · have hP : Layer4PlusOuter.step_post re zeta_i_init step_vec outer_count bnd k (.done y) := by
        simpa [Std.Do.SPred.down_pure] using hh
      simpa [Layer4PlusOuter.step_post] using hP

/-! ### top-level `ntt_at_layer_4_plus_spec` -/

set_option maxHeartbeats 32000000 in
@[spec]
theorem ntt_at_layer_4_plus_spec
    (layer zeta_i : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (bnd : Std.Usize)
    (h_layer : 4 ≤ layer.val ∧ layer.val ≤ 7)
    (h_bnd : bnd.val ≤ 8 * 3328)
    (h_zeta : zeta_i.val = (1 <<< (7 - layer.val)) - 1)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd.val) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      zeta_i re layer scratch bnd
    ⦃ ⇓ p => ⌜ p.1.val = zeta_i.val + 128 >>> layer.val
              ∧ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                  ((p.2.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ bnd.val + 3328 ⌝ ⦄ := by
  obtain ⟨h_layer_ge, h_layer_le⟩ := h_layer
  unfold libcrux_iot_ml_kem.ntt.ntt_at_layer_4_plus
  -- Compute step = 1 <<< layer.
  have h_layer_lt_numBits : layer.val < Std.UScalarTy.Usize.numBits := by
    show layer.val < System.Platform.numBits
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; omega
    · rw [h64]; omega
  have h_shl_spec :=
    Std.Usize.ShiftLeft_spec (1#usize : Std.Usize) layer h_layer_lt_numBits
  obtain ⟨step, h_step_eq, h_step_props⟩ := Std.WP.spec_imp_exists h_shl_spec
  have h_step_val : step.val = ((1#usize : Std.Usize).val <<< layer.val) % Std.Usize.size :=
    h_step_props.1
  have h_1u_val : (1#usize : Std.Usize).val = 1 := rfl
  have h_step_val_clean : step.val = (1 <<< layer.val) % Std.Usize.size := by
    rw [h_step_val, h_1u_val]
  -- Usize.size ≥ 2^32 > 128 ≥ 1 <<< 7, so modulus is identity.
  have h_size_ge : (1 <<< layer.val : Nat) < Std.Usize.size := by
    have h_pow : (1 <<< layer.val : Nat) = 2 ^ layer.val := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h_pow]
    have h_le_128 : (2 : Nat) ^ layer.val ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) h_layer_le
    have h_128_lt : (128 : Nat) < Std.Usize.size := by
      have h_min : Std.Usize.size ≥ 2 ^ 32 := by scalar_tac
      have : (128 : Nat) < 2 ^ 32 := by decide
      omega
    have : (2 : Nat) ^ 7 = 128 := by decide
    omega
  have h_step_val_eq : step.val = 1 <<< layer.val := by
    rw [h_step_val_clean]; exact Nat.mod_eq_of_lt h_size_ge
  -- step_vec = step / 16.
  have h_16_nz : (16#usize : Std.Usize).val ≠ 0 := by decide
  obtain ⟨step_vec, h_sv_eq, h_sv_val⟩ := usize_div_ok_eq step 16#usize h_16_nz
  have h_sv_val_clean : step_vec.val = (1 <<< layer.val) / 16 := by
    rw [h_sv_val, h_step_val_eq]
    show (1 <<< layer.val) / (16#usize : Std.Usize).val = (1 <<< layer.val) / 16
    rfl
  -- outer_count = 128 >>> layer.
  have h_shr_spec :=
    Std.Usize.ShiftRight_spec (128#usize : Std.Usize) layer h_layer_lt_numBits
  obtain ⟨outer_count, h_oc_eq, h_oc_props⟩ := Std.WP.spec_imp_exists h_shr_spec
  have h_oc_val : outer_count.val = (128#usize : Std.Usize).val >>> layer.val := h_oc_props.1
  have h_128u_val : (128#usize : Std.Usize).val = 128 := rfl
  have h_oc_val_clean : outer_count.val = 128 >>> layer.val := by
    rw [h_oc_val, h_128u_val]
  -- Per-layer arithmetic.
  have h_two_oc_sv_eq : 2 * outer_count.val * step_vec.val = 16 := by
    rw [h_oc_val_clean, h_sv_val_clean]
    interval_cases layer.val <;> decide
  have h_outer_count_pos : 0 < outer_count.val := by
    rw [h_oc_val_clean]
    interval_cases layer.val <;> decide
  have h_step_vec_pos : 0 < step_vec.val := by
    rw [h_sv_val_clean]
    interval_cases layer.val <;> decide
  have h_step_vec_le_16 : step_vec.val ≤ 16 := by
    rw [h_sv_val_clean]
    interval_cases layer.val <;> decide
  have h_zeta_init_lt : zeta_i.val + outer_count.val < 128 := by
    rw [h_zeta, h_oc_val_clean]
    interval_cases layer.val <;> decide
  -- The h_pre bound at `bnd.val` is exactly the precondition we need for the
  -- outer loop lemma (with `bnd := bnd.val`).
  rw [h_step_eq]
  simp only [bind_tc_ok]
  rw [h_sv_eq]
  simp only [bind_tc_ok]
  rw [h_oc_eq]
  simp only [bind_tc_ok]
  -- Apply outer loop lemma.
  have h_outer :=
    ntt_at_layer_4_plus_outer_loop_lemma re scratch zeta_i step_vec outer_count
      bnd.val h_bnd h_step_vec_pos h_step_vec_le_16 h_outer_count_pos
      h_two_oc_sv_eq h_zeta_init_lt h_pre
  apply Std.Do.Triple.of_entails_right _ h_outer
  rw [PostCond.entails_noThrow]
  intro r h
  -- h : (⌜post⌝).down — a plain Prop, not a pure_prop_holds.
  obtain ⟨h_zeta_post, h_bd_post⟩ := h
  refine ⟨?_, ?_⟩
  · -- h_zeta_post : r.1.val = zeta_i.val + outer_count.val.
    -- outer_count.val = 128 >>> layer.val (h_oc_val_clean).
    rw [h_zeta_post, h_oc_val_clean]
  · intro i hi j hj
    exact h_bd_post i hi j hj

/-! ## L3.6 — `ntt_binomially_sampled_ring_element_spec`

Composes the eight forward-NTT driver stages plus the terminal
`poly_barrett_reduce`:

  L3.5 → L3.4(layer=6) → L3.4(layer=5) → L3.4(layer=4)
       → L3.3_B → L3.2_B → L3.1_B → L6.1

Bound cascade (per coefficient):
  ≤ 3 → ≤ 4803 → ≤ 14535 → ≤ 17863 → ≤ 21191
        → ≤ 24519 → ≤ 27847 → ≤ 31175 → ≤ 3328.

Implements the §13.4 "independent equation chains" pattern: each step's
`.ok`-equation derived independently via `triple_exists_ok_l3`, then
composed via `rw` against the unfolded impl `do`-block. -/

set_option maxHeartbeats 32000000 in
@[spec]
theorem ntt_binomially_sampled_ring_element_spec
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      re scratch
    ⦃ ⇓ p => ⌜ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  -- ============================================================
  -- Step 1: L3.5 (ntt_at_layer_7).  re → re1, |re1| ≤ 4803.
  -- ============================================================
  obtain ⟨⟨re1, scratch1⟩, h_step1_eq, h_re1_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_7_spec re scratch h_pre)
  dsimp only at h_re1_bd
  -- ============================================================
  -- Step 2: L3.4(layer=6, zeta_i=1, bnd=11207).  re1 → re2.
  -- zeta_i out: 1 + 128 >>> 6 = 1 + 2 = 3.  |re2| ≤ 14535.
  -- ============================================================
  have h_re1_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re1.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ (11207#usize : Std.Usize).val := by
    intro i hi j hj
    have hb := h_re1_bd i hi j hj
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    omega
  obtain ⟨⟨zeta2, re2, scratch2⟩, h_step2_eq, h_zeta2_val, h_re2_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 6#usize) (zeta_i := 1#usize) re1 scratch1 11207#usize
      (by decide : 4 ≤ (6#usize : Std.Usize).val ∧ (6#usize : Std.Usize).val ≤ 7)
      (by decide : (11207#usize : Std.Usize).val ≤ 8 * 3328)
      (by decide :
        (1#usize : Std.Usize).val = (1 <<< (7 - (6#usize : Std.Usize).val)) - 1)
      h_re1_loose)
  dsimp only at h_zeta2_val h_re2_bd
  have h_zeta2_eq3 : zeta2.val = 3 := by
    have : (1#usize : Std.Usize).val = 1 := rfl
    have h6 : (6#usize : Std.Usize).val = 6 := rfl
    rw [h_zeta2_val, this, h6]; decide
  have h_re2_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 14535 := by
    intro i hi j hj
    have hb := h_re2_bd i hi j hj
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    omega
  -- ============================================================
  -- Step 2.5: i ← 11207 + 3328 = 14535.
  -- ============================================================
  have h_add1_max :
      (11207#usize : Std.Usize).val + (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i14535, h_i14535_eq, h_i14535_val⟩ :=
    usize_add_ok_eq (11207#usize : Std.Usize) (3328#usize : Std.Usize) h_add1_max
  have h_i14535_eq_val : i14535.val = 14535 := by
    rw [h_i14535_val]; decide
  -- ============================================================
  -- Step 3: L3.4(layer=5, zeta_i=3, bnd=14535).  re2 → re3.
  -- zeta_i out: 3 + 128 >>> 5 = 3 + 4 = 7.  |re3| ≤ 17863.
  -- ============================================================
  have h_re2_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ i14535.val := by
    intro i hi j hj
    have hb := h_re2_bd' i hi j hj
    omega
  obtain ⟨⟨zeta3, re3, scratch3⟩, h_step3_eq, h_zeta3_val, h_re3_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 5#usize) (zeta_i := zeta2) re2 scratch2 i14535
      (by decide : 4 ≤ (5#usize : Std.Usize).val ∧ (5#usize : Std.Usize).val ≤ 7)
      (by
        have h5 : (5#usize : Std.Usize).val = 5 := rfl
        rw [h_i14535_eq_val]; decide)
      (by
        have h5 : (5#usize : Std.Usize).val = 5 := rfl
        rw [h_zeta2_eq3, h5]; decide)
      h_re2_loose)
  dsimp only at h_zeta3_val h_re3_bd
  have h_zeta3_eq7 : zeta3.val = 7 := by
    have h5 : (5#usize : Std.Usize).val = 5 := rfl
    rw [h_zeta3_val, h_zeta2_eq3, h5]; decide
  have h_re3_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 17863 := by
    intro i hi j hj
    have hb := h_re3_bd i hi j hj
    omega
  -- ============================================================
  -- Step 3.5: i1 ← 2 * 3328 = 6656, i2 ← 11207 + i1 = 17863.
  -- ============================================================
  have h_mul1_max :
      (2#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (2#usize : Std.Usize).val = 2 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i6656, h_i6656_eq, h_i6656_val⟩ :=
    usize_mul_ok_eq (2#usize : Std.Usize) (3328#usize : Std.Usize) h_mul1_max
  have h_i6656_eq_val : i6656.val = 6656 := by
    rw [h_i6656_val]; decide
  have h_add2_max :
      (11207#usize : Std.Usize).val + i6656.val ≤ Std.Usize.max := by
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    rw [this, h_i6656_eq_val]; scalar_tac
  obtain ⟨i17863, h_i17863_eq, h_i17863_val⟩ :=
    usize_add_ok_eq (11207#usize : Std.Usize) i6656 h_add2_max
  have h_i17863_eq_val : i17863.val = 17863 := by
    rw [h_i17863_val, h_i6656_eq_val]; decide
  -- ============================================================
  -- Step 4: L3.4(layer=4, zeta_i=7, bnd=17863).  re3 → re4.
  -- zeta_i out: 7 + 128 >>> 4 = 7 + 8 = 15.  |re4| ≤ 21191.
  -- ============================================================
  have h_re3_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ i17863.val := by
    intro i hi j hj
    have hb := h_re3_bd' i hi j hj
    omega
  obtain ⟨⟨zeta4, re4, scratch4⟩, h_step4_eq, h_zeta4_val, h_re4_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 4#usize) (zeta_i := zeta3) re3 scratch3 i17863
      (by decide : 4 ≤ (4#usize : Std.Usize).val ∧ (4#usize : Std.Usize).val ≤ 7)
      (by rw [h_i17863_eq_val]; decide)
      (by
        have h4 : (4#usize : Std.Usize).val = 4 := rfl
        rw [h_zeta3_eq7, h4]; decide)
      h_re3_loose)
  dsimp only at h_zeta4_val h_re4_bd
  have h_zeta4_eq15 : zeta4.val = 15 := by
    have h4 : (4#usize : Std.Usize).val = 4 := rfl
    rw [h_zeta4_val, h_zeta3_eq7, h4]; decide
  have h_re4_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re4.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 21191 := by
    intro i hi j hj
    have hb := h_re4_bd i hi j hj
    have h_iv : i17863.val = 17863 := h_i17863_eq_val
    omega
  -- ============================================================
  -- Step 4.5: i3 ← 3 * 3328 = 9984, i4 ← 11207 + i3 = 21191.
  -- ============================================================
  have h_mul2_max :
      (3#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (3#usize : Std.Usize).val = 3 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i9984, h_i9984_eq, h_i9984_val⟩ :=
    usize_mul_ok_eq (3#usize : Std.Usize) (3328#usize : Std.Usize) h_mul2_max
  have h_i9984_eq_val : i9984.val = 9984 := by
    rw [h_i9984_val]; decide
  have h_add3_max :
      (11207#usize : Std.Usize).val + i9984.val ≤ Std.Usize.max := by
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    rw [this, h_i9984_eq_val]; scalar_tac
  obtain ⟨i21191, h_i21191_eq, h_i21191_val⟩ :=
    usize_add_ok_eq (11207#usize : Std.Usize) i9984 h_add3_max
  have h_i21191_eq_val : i21191.val = 21191 := by
    rw [h_i21191_val, h_i9984_eq_val]; decide
  -- ============================================================
  -- Step 5: L3.3_B(zeta_i=15, bnd=21191).  re4 → re5.
  -- zeta_i out: 31.  |re5| ≤ 24519.
  -- ============================================================
  have h_re4_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re4.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 21191 := h_re4_bd'
  obtain ⟨⟨zeta5, re5⟩, h_step5_eq, h_zeta5_val, h_re5_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_3_spec_B
      (zeta_i := zeta4) re4 i21191
      (bnd := 21191) (h_bnd := by decide)
      (h_zeta := h_zeta4_eq15)
      h_re4_loose)
  dsimp only at h_zeta5_val h_re5_bd
  -- ============================================================
  -- Step 5.5: i5 ← 4 * 3328 = 13312, i6 ← 11207 + i5 = 24519.
  -- ============================================================
  have h_mul3_max :
      (4#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (4#usize : Std.Usize).val = 4 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i13312, h_i13312_eq, h_i13312_val⟩ :=
    usize_mul_ok_eq (4#usize : Std.Usize) (3328#usize : Std.Usize) h_mul3_max
  have h_i13312_eq_val : i13312.val = 13312 := by
    rw [h_i13312_val]; decide
  have h_add4_max :
      (11207#usize : Std.Usize).val + i13312.val ≤ Std.Usize.max := by
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    rw [this, h_i13312_eq_val]; scalar_tac
  obtain ⟨i24519, h_i24519_eq, h_i24519_val⟩ :=
    usize_add_ok_eq (11207#usize : Std.Usize) i13312 h_add4_max
  have h_i24519_eq_val : i24519.val = 24519 := by
    rw [h_i24519_val, h_i13312_eq_val]; decide
  -- ============================================================
  -- Step 6: L3.2_B(zeta_i=31, bnd=24519).  re5 → re6.
  -- zeta_i out: 63.  |re6| ≤ 27847.
  -- ============================================================
  obtain ⟨⟨zeta6, re6⟩, h_step6_eq, h_zeta6_val, h_re6_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_2_spec_B
      (zeta_i := zeta5) re5 i24519
      (bnd := 24519) (h_bnd := by decide)
      (h_zeta := h_zeta5_val)
      h_re5_bd)
  dsimp only at h_zeta6_val h_re6_bd
  -- ============================================================
  -- Step 6.5: i7 ← 5 * 3328 = 16640, i8 ← 11207 + i7 = 27847.
  -- ============================================================
  have h_mul4_max :
      (5#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (5#usize : Std.Usize).val = 5 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i16640, h_i16640_eq, h_i16640_val⟩ :=
    usize_mul_ok_eq (5#usize : Std.Usize) (3328#usize : Std.Usize) h_mul4_max
  have h_i16640_eq_val : i16640.val = 16640 := by
    rw [h_i16640_val]; decide
  have h_add5_max :
      (11207#usize : Std.Usize).val + i16640.val ≤ Std.Usize.max := by
    have : (11207#usize : Std.Usize).val = 11207 := rfl
    rw [this, h_i16640_eq_val]; scalar_tac
  obtain ⟨i27847, h_i27847_eq, h_i27847_val⟩ :=
    usize_add_ok_eq (11207#usize : Std.Usize) i16640 h_add5_max
  have h_i27847_eq_val : i27847.val = 27847 := by
    rw [h_i27847_val, h_i16640_eq_val]; decide
  -- ============================================================
  -- Step 7: L3.1_B(zeta_i=63, bnd=27847).  re6 → re7.
  -- zeta_i out: 127.  |re7| ≤ 31175.
  -- ============================================================
  obtain ⟨⟨zeta7, re7⟩, h_step7_eq, _h_zeta7_val, h_re7_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_1_spec_B
      (zeta_i := zeta6) re6 i27847
      (bnd := 27847) (h_bnd := by decide)
      (h_zeta := h_zeta6_val)
      h_re6_bd)
  dsimp only at h_re7_bd
  -- ============================================================
  -- Step 8: L6.1 poly_barrett_reduce.  re7 → re8, |re8| ≤ 3328.
  -- ============================================================
  have h_re7_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re7.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 32767 := by
    intro i hi j hj
    have hb := h_re7_bd i hi j hj
    omega
  obtain ⟨re8, h_step8_eq, h_re8_bd⟩ :=
    triple_exists_ok_l3 (PolynomialRingElement_poly_barrett_reduce_spec re7 h_re7_loose)
  -- ============================================================
  -- Compose: derive the full impl `do`-block equation.
  -- ============================================================
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
        re scratch = .ok (re8, scratch4) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_binomially_sampled_ring_element
    simp [h_step1_eq, h_step2_eq, h_step3_eq, h_step4_eq,
          h_step5_eq, h_step6_eq, h_step7_eq, h_step8_eq,
          h_i14535_eq, h_i6656_eq, h_i17863_eq,
          h_i9984_eq, h_i21191_eq,
          h_i13312_eq, h_i24519_eq,
          h_i16640_eq, h_i27847_eq]
  apply triple_of_ok_l3 h_body
  intro i hi j hj
  exact h_re8_bd i hi j hj

/-! ## L3.7 — `ntt_vector_u_spec`

Composes the seven forward-NTT driver stages plus the terminal
`poly_barrett_reduce`, starting from the already-decompressed bound
`≤ 3328`:

  L3.4(layer=7) → L3.4(layer=6) → L3.4(layer=5) → L3.4(layer=4)
       → L3.3_B → L3.2_B → L3.1_B → L6.1

Bound cascade (per coefficient):
  ≤ 3328 → ≤ 6656 → ≤ 9984 → ≤ 13312 → ≤ 16640
        → ≤ 19968 → ≤ 23296 → ≤ 26624 → ≤ 3328.

Mirrors `ntt_binomially_sampled_ring_element_spec` (L3.6) above, with
one extra L3.4 step (layer=7) replacing the L3.5 (`ntt_at_layer_7`)
prefix that L3.6 uses. Implements the §13.4 "independent equation
chains" pattern. -/

set_option maxHeartbeats 32000000 in
@[spec]
theorem ntt_vector_u_spec
    (VECTOR_U_COMPRESSION_FACTOR : Std.Usize)
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (scratch : libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_pre : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328) :
    ⦃ ⌜ True ⌝ ⦄
    libcrux_iot_ml_kem.ntt.ntt_vector_u
      VECTOR_U_COMPRESSION_FACTOR
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
      re scratch
    ⦃ ⇓ p => ⌜ ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
                ((p.1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 3328 ⌝ ⦄ := by
  -- ============================================================
  -- Step 1: L3.4(layer=7, zeta_i=0, bnd=3328).  re → re1.
  -- zeta_i out: 0 + 128 >>> 7 = 0 + 1 = 1.  |re1| ≤ 6656.
  -- ============================================================
  have h_re_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re.coefficients.val[i]!).elements.val[j]!).val.natAbs
        ≤ (3328#usize : Std.Usize).val := by
    intro i hi j hj
    have hb := h_pre i hi j hj
    have : (3328#usize : Std.Usize).val = 3328 := rfl
    omega
  obtain ⟨⟨zeta1, re1, scratch1⟩, h_step1_eq, h_zeta1_val, h_re1_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 7#usize) (zeta_i := 0#usize) re scratch 3328#usize
      (by decide : 4 ≤ (7#usize : Std.Usize).val ∧ (7#usize : Std.Usize).val ≤ 7)
      (by decide : (3328#usize : Std.Usize).val ≤ 8 * 3328)
      (by decide :
        (0#usize : Std.Usize).val = (1 <<< (7 - (7#usize : Std.Usize).val)) - 1)
      h_re_loose)
  dsimp only at h_zeta1_val h_re1_bd
  have h_zeta1_eq1 : zeta1.val = 1 := by
    have h0 : (0#usize : Std.Usize).val = 0 := rfl
    have h7 : (7#usize : Std.Usize).val = 7 := rfl
    rw [h_zeta1_val, h0, h7]; decide
  have h_re1_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 6656 := by
    intro i hi j hj
    have hb := h_re1_bd i hi j hj
    have : (3328#usize : Std.Usize).val = 3328 := rfl
    omega
  -- ============================================================
  -- Step 1.5: i ← 2 * 3328 = 6656.
  -- ============================================================
  have h_mul1_max :
      (2#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (2#usize : Std.Usize).val = 2 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i6656, h_i6656_eq, h_i6656_val⟩ :=
    usize_mul_ok_eq (2#usize : Std.Usize) (3328#usize : Std.Usize) h_mul1_max
  have h_i6656_eq_val : i6656.val = 6656 := by
    rw [h_i6656_val]; decide
  -- ============================================================
  -- Step 2: L3.4(layer=6, zeta_i=1, bnd=6656).  re1 → re2.
  -- zeta_i out: 1 + 128 >>> 6 = 1 + 2 = 3.  |re2| ≤ 9984.
  -- ============================================================
  have h_re1_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re1.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ i6656.val := by
    intro i hi j hj
    have hb := h_re1_bd' i hi j hj
    omega
  obtain ⟨⟨zeta2, re2, scratch2⟩, h_step2_eq, h_zeta2_val, h_re2_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 6#usize) (zeta_i := zeta1) re1 scratch1 i6656
      (by decide : 4 ≤ (6#usize : Std.Usize).val ∧ (6#usize : Std.Usize).val ≤ 7)
      (by rw [h_i6656_eq_val]; decide)
      (by
        have h6 : (6#usize : Std.Usize).val = 6 := rfl
        rw [h_zeta1_eq1, h6]; decide)
      h_re1_loose)
  dsimp only at h_zeta2_val h_re2_bd
  have h_zeta2_eq3 : zeta2.val = 3 := by
    have h6 : (6#usize : Std.Usize).val = 6 := rfl
    rw [h_zeta2_val, h_zeta1_eq1, h6]; decide
  have h_re2_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 9984 := by
    intro i hi j hj
    have hb := h_re2_bd i hi j hj
    have h_iv : i6656.val = 6656 := h_i6656_eq_val
    omega
  -- ============================================================
  -- Step 2.5: i1 ← 3 * 3328 = 9984.
  -- ============================================================
  have h_mul2_max :
      (3#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (3#usize : Std.Usize).val = 3 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i9984, h_i9984_eq, h_i9984_val⟩ :=
    usize_mul_ok_eq (3#usize : Std.Usize) (3328#usize : Std.Usize) h_mul2_max
  have h_i9984_eq_val : i9984.val = 9984 := by
    rw [h_i9984_val]; decide
  -- ============================================================
  -- Step 3: L3.4(layer=5, zeta_i=3, bnd=9984).  re2 → re3.
  -- zeta_i out: 3 + 128 >>> 5 = 3 + 4 = 7.  |re3| ≤ 13312.
  -- ============================================================
  have h_re2_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re2.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ i9984.val := by
    intro i hi j hj
    have hb := h_re2_bd' i hi j hj
    omega
  obtain ⟨⟨zeta3, re3, scratch3⟩, h_step3_eq, h_zeta3_val, h_re3_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 5#usize) (zeta_i := zeta2) re2 scratch2 i9984
      (by decide : 4 ≤ (5#usize : Std.Usize).val ∧ (5#usize : Std.Usize).val ≤ 7)
      (by rw [h_i9984_eq_val]; decide)
      (by
        have h5 : (5#usize : Std.Usize).val = 5 := rfl
        rw [h_zeta2_eq3, h5]; decide)
      h_re2_loose)
  dsimp only at h_zeta3_val h_re3_bd
  have h_zeta3_eq7 : zeta3.val = 7 := by
    have h5 : (5#usize : Std.Usize).val = 5 := rfl
    rw [h_zeta3_val, h_zeta2_eq3, h5]; decide
  have h_re3_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 13312 := by
    intro i hi j hj
    have hb := h_re3_bd i hi j hj
    have h_iv : i9984.val = 9984 := h_i9984_eq_val
    omega
  -- ============================================================
  -- Step 3.5: i2 ← 4 * 3328 = 13312.
  -- ============================================================
  have h_mul3_max :
      (4#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (4#usize : Std.Usize).val = 4 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i13312, h_i13312_eq, h_i13312_val⟩ :=
    usize_mul_ok_eq (4#usize : Std.Usize) (3328#usize : Std.Usize) h_mul3_max
  have h_i13312_eq_val : i13312.val = 13312 := by
    rw [h_i13312_val]; decide
  -- ============================================================
  -- Step 4: L3.4(layer=4, zeta_i=7, bnd=13312).  re3 → re4.
  -- zeta_i out: 7 + 128 >>> 4 = 7 + 8 = 15.  |re4| ≤ 16640.
  -- ============================================================
  have h_re3_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re3.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ i13312.val := by
    intro i hi j hj
    have hb := h_re3_bd' i hi j hj
    omega
  obtain ⟨⟨zeta4, re4, scratch4⟩, h_step4_eq, h_zeta4_val, h_re4_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_4_plus_spec
      (layer := 4#usize) (zeta_i := zeta3) re3 scratch3 i13312
      (by decide : 4 ≤ (4#usize : Std.Usize).val ∧ (4#usize : Std.Usize).val ≤ 7)
      (by rw [h_i13312_eq_val]; decide)
      (by
        have h4 : (4#usize : Std.Usize).val = 4 := rfl
        rw [h_zeta3_eq7, h4]; decide)
      h_re3_loose)
  dsimp only at h_zeta4_val h_re4_bd
  have h_zeta4_eq15 : zeta4.val = 15 := by
    have h4 : (4#usize : Std.Usize).val = 4 := rfl
    rw [h_zeta4_val, h_zeta3_eq7, h4]; decide
  have h_re4_bd' : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re4.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 16640 := by
    intro i hi j hj
    have hb := h_re4_bd i hi j hj
    have h_iv : i13312.val = 13312 := h_i13312_eq_val
    omega
  -- ============================================================
  -- Step 4.5: i3 ← 5 * 3328 = 16640.
  -- ============================================================
  have h_mul4_max :
      (5#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (5#usize : Std.Usize).val = 5 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i16640, h_i16640_eq, h_i16640_val⟩ :=
    usize_mul_ok_eq (5#usize : Std.Usize) (3328#usize : Std.Usize) h_mul4_max
  have h_i16640_eq_val : i16640.val = 16640 := by
    rw [h_i16640_val]; decide
  -- ============================================================
  -- Step 5: L3.3_B(zeta_i=15, bnd=16640).  re4 → re5.
  -- zeta_i out: 31.  |re5| ≤ 19968.
  -- ============================================================
  obtain ⟨⟨zeta5, re5⟩, h_step5_eq, h_zeta5_val, h_re5_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_3_spec_B
      (zeta_i := zeta4) re4 i16640
      (bnd := 16640) (h_bnd := by decide)
      (h_zeta := h_zeta4_eq15)
      h_re4_bd')
  dsimp only at h_zeta5_val h_re5_bd
  -- ============================================================
  -- Step 5.5: i4 ← 6 * 3328 = 19968.
  -- ============================================================
  have h_mul5_max :
      (6#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (6#usize : Std.Usize).val = 6 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i19968, h_i19968_eq, h_i19968_val⟩ :=
    usize_mul_ok_eq (6#usize : Std.Usize) (3328#usize : Std.Usize) h_mul5_max
  have h_i19968_eq_val : i19968.val = 19968 := by
    rw [h_i19968_val]; decide
  -- ============================================================
  -- Step 6: L3.2_B(zeta_i=31, bnd=19968).  re5 → re6.
  -- zeta_i out: 63.  |re6| ≤ 23296.
  -- ============================================================
  obtain ⟨⟨zeta6, re6⟩, h_step6_eq, h_zeta6_val, h_re6_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_2_spec_B
      (zeta_i := zeta5) re5 i19968
      (bnd := 19968) (h_bnd := by decide)
      (h_zeta := h_zeta5_val)
      h_re5_bd)
  dsimp only at h_zeta6_val h_re6_bd
  -- ============================================================
  -- Step 6.5: i5 ← 7 * 3328 = 23296.
  -- ============================================================
  have h_mul6_max :
      (7#usize : Std.Usize).val * (3328#usize : Std.Usize).val ≤ Std.Usize.max := by
    have : (7#usize : Std.Usize).val = 7 := rfl
    have h2 : (3328#usize : Std.Usize).val = 3328 := rfl
    rw [this, h2]; scalar_tac
  obtain ⟨i23296, h_i23296_eq, h_i23296_val⟩ :=
    usize_mul_ok_eq (7#usize : Std.Usize) (3328#usize : Std.Usize) h_mul6_max
  have h_i23296_eq_val : i23296.val = 23296 := by
    rw [h_i23296_val]; decide
  -- ============================================================
  -- Step 7: L3.1_B(zeta_i=63, bnd=23296).  re6 → re7.
  -- zeta_i out: 127.  |re7| ≤ 26624.
  -- ============================================================
  obtain ⟨⟨zeta7, re7⟩, h_step7_eq, _h_zeta7_val, h_re7_bd⟩ :=
    triple_exists_ok_l3 (ntt_at_layer_1_spec_B
      (zeta_i := zeta6) re6 i23296
      (bnd := 23296) (h_bnd := by decide)
      (h_zeta := h_zeta6_val)
      h_re6_bd)
  dsimp only at h_re7_bd
  -- ============================================================
  -- Step 8: L6.1 poly_barrett_reduce.  re7 → re8, |re8| ≤ 3328.
  -- ============================================================
  have h_re7_loose : ∀ i : Nat, i < 16 → ∀ j : Nat, j < 16 →
      ((re7.coefficients.val[i]!).elements.val[j]!).val.natAbs ≤ 32767 := by
    intro i hi j hj
    have hb := h_re7_bd i hi j hj
    omega
  obtain ⟨re8, h_step8_eq, h_re8_bd⟩ :=
    triple_exists_ok_l3 (PolynomialRingElement_poly_barrett_reduce_spec re7 h_re7_loose)
  -- ============================================================
  -- Compose: derive the full impl `do`-block equation.
  -- ============================================================
  have h_body :
      libcrux_iot_ml_kem.ntt.ntt_vector_u
        VECTOR_U_COMPRESSION_FACTOR
        libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector.Insts.Libcrux_iot_ml_kemVectorTraitsOperations
        re scratch = .ok (re8, scratch4) := by
    unfold libcrux_iot_ml_kem.ntt.ntt_vector_u
    simp [h_step1_eq, h_step2_eq, h_step3_eq, h_step4_eq,
          h_step5_eq, h_step6_eq, h_step7_eq, h_step8_eq,
          h_i6656_eq, h_i9984_eq, h_i13312_eq,
          h_i16640_eq, h_i19968_eq, h_i23296_eq]
  apply triple_of_ok_l3 h_body
  intro i hi j hj
  exact h_re8_bd i hi j hj

end libcrux_iot_ml_kem.Polynomial.NttDrivers