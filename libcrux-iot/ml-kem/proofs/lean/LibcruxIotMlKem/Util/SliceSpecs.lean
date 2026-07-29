/-
  # `Util/SliceSpecs.lean` — Aeneas Std byte / slice `@[spec]` bridges

  Verbatim lift from libcrux-iot SHA-3's
  `LibcruxIotSha3/Sponge/SliceSpecs.lean`, with namespace rewritten
  from `libcrux_iot_sha3.Sponge` → `libcrux_iot_ml_kem.Util` and the
  SHA-3-specific `attribute [local irreducible] keccak.…` / `open …
  libcrux_iot_sha3 hacspec_sha3` lines dropped.

  Installs reusable `@[spec]` Triples for the generic Aeneas/`core_models`
  byte/slice operations that every ML-KEM byte encode/decode and matrix
  routine routes through. The `result_eq_of_triple` helper that the
  original file pulled from `LibcruxIotSha3.Equivalence.I32LoopSpec` is
  re-defined here as a private theorem (it is also re-exported by
  `Util/LoopSpecs.lean` for cross-Util use).

  ## Installed (10 Triples)

  - `core_models_slice_Slice_len_spec` — `core.slice.Slice.len`
    returns the underlying list length.
  - `massert_spec` — `Aeneas.Std.massert b` succeeds (with `()`) when `b`.
  - `core_models_num_U32_from_le_bytes_spec`,
    `core_models_num_U32_to_le_bytes_spec` — byte ↔ u32 LE.
  - `core_models_num_U64_from_le_bytes_spec`,
    `core_models_num_U64_to_le_bytes_spec` — byte ↔ u64 LE.
  - `core_models_Slice_Insts_index_RangeUsize_spec` — slice subindexing
    over `Range<usize>`.
  - `core_models_Slice_Insts_index_mut_RangeUsize_spec` — mutable slice
    subindexing over `Range<usize>`.
  - `core_models_result_Result_unwrap_spec` — `result.Result.unwrap` on
    `.Ok v` yields `v`.
  - `core_models_slice_Slice_copy_from_slice_spec` — write-into-slice;
    the impl model returns the source slice outright when lengths match.
  - `core_models_array_try_from_slice_spec` — `Slice T → Array T N`
    coercion; total when `s.val.length = N.val`.
  - `core_models_try_from_unwrap_spec` — fused
    `try_from + Result.unwrap` Triple.
-/
import LibcruxIotMlKem.Extraction.Funs

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open Result Std.Do

namespace libcrux_iot_ml_kem.Util.SliceSpecs
set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## Local helper: Triple → Result-equation converter

When each `call_mut`'s purity is stated as a Triple (natural for
`hax_mvcgen`-driven proofs), the Result equation needed by the
`try_from`/`createi`/`from_fn` pure-closure pattern follows
directly. This file uses it once (in `core_models_try_from_unwrap_spec`);
`Util/LoopSpecs.lean` and `Util/CreateI.lean` use the same helper. -/

theorem result_eq_of_triple {α : Type} {x : Result α} {v : α}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄) : x = .ok v := by
  match hx : x, h with
  | .ok v', h =>
      have hv' : v' = v := by
        simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply] at h
        exact h
      rw [hv']
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply])

/-! ## Aeneas Std byte/slice `@[spec]` lemmas. -/

/-! ### `core.slice.Slice.len` -/

/-- The hax `core.slice.Slice.len` is a thin `pure`-wrapper around
    `Aeneas.Std.Slice.len`. Always succeeds with the underlying list length
    (as a `Usize`). -/
@[spec]
theorem core_models_slice_Slice_len_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.Slice.len s
    ⦃ ⇓ r => ⌜ r.val = s.val.length ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, core.slice.Slice.len]

/-! ### `Aeneas.Std.massert` -/

/-- `massert b` succeeds with `()` iff `b` holds. -/
@[spec]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
    ⦃ ⌜ True ⌝ ⦄
    massert b
    ⦃ ⇓ r => ⌜ r = () ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply, h]

/-! ### `core.num.U32.from_le_bytes` / `U32.to_le_bytes` -/

/-- The four-byte LE-load `U32.from_le_bytes` always succeeds with
    `core.num.U32.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U32_from_le_bytes_spec (bytes : Std.Array Std.U8 4#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.U32.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.from_le_bytes bytes ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply,
        core.num.U32.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u32]

/-- The four-byte LE-store `U32.to_le_bytes` always succeeds with
    `core.num.U32.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U32_to_le_bytes_spec (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.U32.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.to_le_bytes x ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply,
        core.num.U32.to_le_bytes, rust_primitives.arithmetic.to_le_bytes_u32]

/-! ### `core.num.U64.from_le_bytes` / `U64.to_le_bytes` -/

/-- The eight-byte LE-load `U64.from_le_bytes` always succeeds with
    `core.num.U64.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.U64.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.from_le_bytes bytes ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply,
        core.num.U64.from_le_bytes, rust_primitives.arithmetic.from_le_bytes_u64]

/-- The eight-byte LE-store `U64.to_le_bytes` always succeeds with
    `core.num.U64.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U64_to_le_bytes_spec (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    core.num.U64.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.to_le_bytes x ⌝ ⦄ := by
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply,
        core.num.U64.to_le_bytes, rust_primitives.arithmetic.to_le_bytes_u64]

/-! ### `core.Slice.Insts.CoreOpsIndexIndex.index` over `Range Usize` -/

/-- Slice subindexing over a `Range<usize>` succeeds whenever the range is
    in bounds, returning the sub-`Slice` whose `val` is the contiguous
    slice `s.val[start..end]`. -/
@[spec]
theorem core_models_Slice_Insts_index_RangeUsize_spec
    {T : Type} (s : Slice T) (r : core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.Slice.Insts.CoreOpsIndexIndex.index
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ r' => ⌜ r'.val = s.val.slice r.start.val r.end.val ∧
                r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndex.index
         core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         Aeneas.Std.core.slice.index.Slice.index
         Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp]
  simp [h0', h1', Slice.length]
  simp [List.slice]
  simp [PredTrans.apply]
  omega

/-! ### `core.result.Result.unwrap`

The hax `Result.unwrap` on the `core_models` `result.Result` enum panics on
`Err` and returns the inner `T` on `Ok`. We give a Triple-style spec under
the precondition `r = .Ok v`. -/

/-- `Result.unwrap` of a `.Ok`-valued `r` returns the inner value.

    We state both the precondition (`∃ v, r = .Ok v`) and the post
    (`r = .Ok r'`), leaving `v` quantified inside `mvcgen`'s assertion
    bag. This avoids the mvcgen unification quirk where the explicit
    `v` argument gets eagerly bound to the first matching local of the
    right type. -/
@[spec]
theorem core_models_result_Result_unwrap_spec
    {T E : Type} (dbg : core.fmt.Debug E)
    (r : core.result.Result T E)
    (h : ∃ v, r = .Ok v) :
    ⦃ ⌜ True ⌝ ⦄
    core.result.Result.unwrap dbg r
    ⦃ ⇓ r' => ⌜ r = .Ok r' ⌝ ⦄ := by
  obtain ⟨v, hv⟩ := h
  unfold core.result.Result.unwrap
  subst hv
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply]


/-! ### `core.Slice.Insts.CoreOpsIndexIndexMut.index_mut` over `Range Usize`

Used by Aeneas-extracted loops that obtain a mutable sub-slice and a
write-back closure (e.g. SHA-3's `state.store_block_2u32_loop.body`, and
the ML-KEM byte-encode loops). -/

/-- Mutable slice subindexing over a `Range<usize>` returns both the
    sub-slice (same `val` as the non-mut `index`) and a write-back
    closure that overwrites `s.val[r.start.val..]` with the argument's
    `val`. -/
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeUsize_spec
    {T : Type} (s : Slice T) (r : core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s', (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
         core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         Aeneas.Std.core.slice.index.Slice.index_mut
         Aeneas.Std.core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp]
  simp [h0', h1', Slice.length]
  simp [List.slice]
  simp [PredTrans.apply]
  omega

/-! ### `core.slice.Slice.copy_from_slice` -/

/-- `copy_from_slice dst src` succeeds with the source slice `src`
    whenever both slices have the same length (the impl model returns
    `src` outright when lengths match). -/
@[spec]
theorem core_models_slice_Slice_copy_from_slice_spec
    {T : Type} (cpy : core.marker.Copy T) (dst src : Slice T)
    (h : dst.val.length = src.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    core.slice.Slice.copy_from_slice cpy dst src
    ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  unfold core.slice.Slice.copy_from_slice
  have h' : dst.len = src.len := by
    apply Std.UScalar.eq_of_val_eq
    simp [h]
  simp [Triple, WP.wp, h', PostCond.noThrow, PredTrans.apply]

/-! ### `core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from`

The body invokes `rust_primitives.slice.array_from_fn` on the `try_from`
closure (whose state is just the source `Slice T`). The proof has three
parts:

1. Closure step: `call_mut s i = .ok (s.val[i.val]!, s)` for `i.val <
   s.length` — the closure reads the slice and preserves its state.
2. `foldlM` invariant: induction on `k` shows that folding the closure
   over `List.range' 0 k` (starting from `([], s)`) returns
   `(s.val.take k, s)` when `k ≤ s.length`.
3. Final assembly: `array_from_fn N closure s = .ok (Array.make N s.val)`
   when `s.length = N.val`, hence `try_from N inst s = .ok (.Ok a)` with
   `a.val = s.val`. -/

/-- Numeric helper: `(⟨BitVec.ofNat _ n⟩ : Usize).val = n` when
    `n ≤ Std.Usize.max` (equivalently, `n < 2^Usize.numBits`).
    We state the bit-vector size as `UScalarTy.Usize.numBits` since this
    is the form `Usize.val` unfolds to. -/
private theorem bv_ofNat_usize_val_eq (n : Nat) (hn : n ≤ Std.Usize.max) :
    (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  -- `Std.Usize.max = 2^Std.Usize.numBits - 1`, hence `n ≤ max` means `n < 2^numBits`.
  have hmax : Std.Usize.max + 1 = 2 ^ Std.UScalarTy.Usize.numBits := by
    simp [Std.Usize.max, Std.Usize.numBits]
  omega

/-- Closure step lemma. The `try_from` closure's state is the source
    `Slice T`; `call_mut` reads the `i`-th element and preserves state. -/
private theorem try_from_closure_call_mut_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i =
      .ok (s.val[i.val]!, s) := by
  -- Reduces to `do let t ← slice_index s i; ok (t, s)`.
  unfold core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold rust_primitives.slice.slice_index Std.Slice.index_usize
  -- Now `s[i]?` matches; for `i.val < s.length`, `s[i]? = some s.val[i.val]!`.
  have hsome : s[i]? = some s.val[i.val]! := by
    simp only [Std.Slice.getElem?_Usize_eq]
    rw [List.getElem?_eq_getElem h, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h]
    rfl
  rw [hsome]
  rfl

/-- The closure-fold accumulator at step `k` is `s.val.take k`. We prove
    a slightly stronger invariant: starting from any accumulator `acc`
    with the closure state `s`, folding over `List.range' acc.length k`
    yields `(acc ++ s.val.slice acc.length (acc.length + k), s)` when
    `acc.length + k ≤ s.length` and acc lines up with the slice prefix. -/
private theorem foldlM_try_from_closure_invariant
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T)
    (_hN : s.val.length ≤ Std.Usize.max) :
    ∀ (k start : Nat) (acc : List T),
      acc = s.val.take start →
      start + k ≤ s.val.length →
      start + k ≤ Std.Usize.max →
      (List.range' start k).foldlM
        (fun (p : List T × Slice T) (i : Nat) => do
          let (v, f') ←
            core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
              (T := T) (N := N) cpy p.2 ⟨BitVec.ofNat _ i⟩
          ok (p.1 ++ [v], f'))
        (acc, s)
      = .ok (s.val.take (start + k), s) := by
  intro k
  induction k with
  | zero =>
    intro start acc hacc hk1 hk2
    show List.foldlM _ (acc, s) (List.range' start 0) = _
    rw [show List.range' start 0 = [] from rfl]
    rw [List.foldlM_nil]
    show Result.ok (acc, s) = Result.ok (s.val.take (start + 0), s)
    rw [hacc, Nat.add_zero]
  | succ k ih =>
    intro start acc hacc hk1 hk2
    -- `List.range' start (k+1) = start :: List.range' (start+1) k`
    rw [show List.range' start (k + 1) = start :: List.range' (start + 1) k from rfl]
    simp only [List.foldlM_cons]
    -- The step at `start` calls `call_mut s ⟨BitVec.ofNat _ start⟩`.
    have hstart_lt : start < s.val.length := by omega
    have hstart_max : start ≤ Std.Usize.max := by omega
    have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits start⟩ : Std.Usize).val = start :=
      bv_ofNat_usize_val_eq start hstart_max
    have hcall := try_from_closure_call_mut_eq (T := T) (N := N) cpy s
                    ⟨BitVec.ofNat _ start⟩ (by rw [hval]; exact hstart_lt)
    -- Rewrite both the closure-call output's `.val` and the `i` arg uniformly.
    rw [hval] at hcall
    rw [hcall]
    simp only [bind_tc_ok]
    -- New accumulator is `acc ++ [s.val[start]!] = s.val.take (start + 1)`.
    have hacc' : acc ++ [s.val[start]!] = s.val.take (start + 1) := by
      rw [hacc]
      have : start < s.val.length := hstart_lt
      rw [List.take_add_one]
      simp [List.getElem?_eq_getElem this, List.getElem!_eq_getElem?_getD]
    -- Now apply IH at `start := start + 1`. Note `(start + 1) + k = start + (k + 1)`.
    have ih' := ih (start + 1) (acc ++ [s.val[start]!]) hacc' (by omega) (by omega)
    have h_assoc : (start + 1) + k = start + (k + 1) := by omega
    rw [h_assoc] at ih'
    exact ih'

/-- `array_from_fn N (try_from closure) s = .ok (Array.make N s.val)`
    when `s.length = N.val`. -/
private theorem array_from_fn_try_from_eq_ok
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    rust_primitives.slice.array_from_fn N
      (core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        (T := T) (N := N) cpy) s
    = .ok (Std.Array.make N s.val (by simp [hlen])) := by
  -- Foldl invariant at start=0, k=N.val, acc=[].
  have hN_max : s.val.length ≤ Std.Usize.max := by
    have := s.property; exact this
  have hN_max' : N.val ≤ Std.Usize.max := by
    rw [← hlen]; exact hN_max
  have h_fold :=
    foldlM_try_from_closure_invariant (T := T) (N := N) cpy s hN_max
      N.val 0 [] (by simp) (by omega) (by omega)
  -- Normalize `0 + N.val = N.val` and reduce `take N.val s.val = s.val`.
  simp only [Nat.zero_add] at h_fold
  have h_take : s.val.take N.val = s.val :=
    List.take_of_length_le (by omega)
  rw [h_take] at h_fold
  -- Match `range N.val` with `range' 0 N.val` (`range` is defined as `range' 0 _`).
  have hrange : (List.range N.val) = List.range' 0 N.val := List.range_eq_range'
  -- The `array_from_fn` definition is a `match` on the foldlM result.
  rw [← hrange] at h_fold
  unfold rust_primitives.slice.array_from_fn
  -- Now transport the foldlM equation through the `split`.
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = (s.val, s) := (Result.ok.inj heq).symm
    subst hres
    rfl

/-- The main Triple: `try_from N cpy s` succeeds with `Ok (Array.make N s.val _)`,
    whenever `s.val.length = N.val`. -/
@[spec]
theorem core_models_array_try_from_slice_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  -- Unfold try_from and reduce the `do` chain step-by-step.
  unfold core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  -- `core.slice.Slice.len x` is `pure (Slice.len x)`, returns `.ok (Slice.len s)`.
  unfold core.slice.Slice.len
  -- The if-decision: `Slice.len s = N` reduces to `s.val.length = N.val`.
  have hi_eq : (Std.Slice.len s) = N := by
    apply Std.UScalar.eq_of_val_eq
    simp [hlen]
  -- Reduce the array_from_fn call to .ok.
  have h_afn := array_from_fn_try_from_eq_ok (T := T) (N := N) cpy s hlen
  simp only [Triple, WP.wp, pure, Pure.pure, bind_tc_ok, hi_eq, if_true, h_afn]
  intro _
  trivial

/-- Fused `try_from + Result.unwrap` Triple. The two-step pattern
    `let r ← try_from N cpy s; let a ← Result.unwrap dbg r` is the
    canonical Aeneas idiom for slice → array coercion; we provide a
    direct equation that mvcgen can chain without intermediate metavars. -/
theorem core_models_try_from_unwrap_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : core.marker.Copy T)
    (dbg : core.fmt.Debug core.array.TryFromSliceError)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let r ← core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
                N cpy s
      core.result.Result.unwrap dbg r)
    ⦃ ⇓ a => ⌜ a = Std.Array.make N s.val (by simp [hlen]) ⌝ ⦄ := by
  -- Establish `try_from ... = .ok (.Ok (Array.make N s.val _))` outright.
  have h_try := core_models_array_try_from_slice_spec (T := T) (N := N) cpy s hlen
  -- Then unfold Result.unwrap and reduce.
  unfold core.result.Result.unwrap
  -- Reduce `try_from` to its known .ok form via the local Triple → eq helper.
  have h_eq : (core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
                  N cpy s)
              = .ok (.Ok (Std.Array.make N s.val (by simp [hlen]))) :=
    result_eq_of_triple h_try
  rw [h_eq]
  simp [Triple, WP.wp, PostCond.noThrow, PredTrans.apply]

end libcrux_iot_ml_kem.Util.SliceSpecs