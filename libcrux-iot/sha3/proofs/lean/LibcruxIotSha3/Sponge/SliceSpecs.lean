/-
  # Aeneas Std byte/slice `@[spec]` Triples

  Small `@[spec]` Triples used by the byte ↔ lane bridges in
  `Sponge/Bytes.lean`.

  ## Installed

  - `core_models_slice_Slice_len_spec` — `CoreModels.core.slice.Slice.len`
    returns the underlying list length.
  - `massert_spec` — `Aeneas.Std.massert b` succeeds (with `()`) when `b`.
  - `core_models_num_U32_from_le_bytes_spec`,
    `core_models_num_U32_to_le_bytes_spec` — byte ↔ u32 LE.
  - `core_models_num_U64_from_le_bytes_spec`,
    `core_models_num_U64_to_le_bytes_spec` — byte ↔ u64 LE.
  - `core_models_Slice_Insts_index_RangeUsize_spec` — slice subindexing
    over `Range<usize>` (used by load/store loops).
  - `core_models_Slice_Insts_index_mut_RangeUsize_spec` — mutable slice
    subindexing over `Range<usize>` (used by `store_block_2u32_loop.body`).
  - `core_models_result_Result_unwrap_spec` — `result.Result.unwrap` on
    `.Ok v` yields `v`.
  - `core_models_slice_Slice_copy_from_slice_spec` — write-into-slice;
    the impl model returns the source slice outright when lengths match.
  - `core_models_array_try_from_slice_spec`
    (`Slice T → Result (result.Result (Array T N) ...)`).
    The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the
    `try_from.closure`, whose Triple is established by induction over the
    closure's `call_mut` calls and the `List.range N.val` `foldlM`.
    See the closure-step lemma, the `foldlM` invariant, and the final
    Triple at the bottom of this file. General Aeneas Std bridge with no
    SHA-3 specificity (belongs in `rust-core-models` upstream).
-/
import LibcruxIotSha3.Sponge.Opaque

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

/-! ## Prerequisite — Aeneas Std byte/slice `@[spec]` lemmas. -/

/-! ### `CoreModels.core.slice.Slice.len` -/

/-- The hax `CoreModels.core.slice.Slice.len` is a thin `pure`-wrapper around
    `Aeneas.Std.Slice.len`. Always succeeds with the underlying list length
    (as a `Usize`). -/
@[spec]
theorem core_models_slice_Slice_len_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.slice.Slice.len s
    ⦃ ⇓ r => ⌜ r.val = s.val.length ⌝ ⦄ := by
  unfold CoreModels.core.slice.Slice.len
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `Aeneas.Std.massert` -/

/-- `massert b` succeeds with `()` iff `b` holds. -/
@[spec]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
    ⦃ ⌜ True ⌝ ⦄
    massert b
    ⦃ ⇓ r => ⌜ r = () ⌝ ⦄ := by
  unfold massert
  simp [Triple, WP.wp, PredTrans.apply, h]

/-! ### `CoreModels.core.num.U32.from_le_bytes` / `U32.to_le_bytes` -/

/-- The four-byte LE-load `U32.from_le_bytes` always succeeds with
    `core.num.U32.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U32_from_le_bytes_spec (bytes : Std.Array Std.U8 4#usize) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U32.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.from_le_bytes bytes ⌝ ⦄ := by
  unfold CoreModels.core.num.U32.from_le_bytes CoreModels.rust_primitives.arithmetic.from_le_bytes_u32
  simp [Triple, WP.wp, PredTrans.apply]

/-- The four-byte LE-store `U32.to_le_bytes` always succeeds with
    `core.num.U32.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U32_to_le_bytes_spec (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U32.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.to_le_bytes x ⌝ ⦄ := by
  unfold CoreModels.core.num.U32.to_le_bytes CoreModels.rust_primitives.arithmetic.to_le_bytes_u32
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `CoreModels.core.num.U64.from_le_bytes` / `U64.to_le_bytes` -/

/-- The eight-byte LE-load `U64.from_le_bytes` always succeeds with
    `core.num.U64.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U64.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.from_le_bytes bytes ⌝ ⦄ := by
  unfold CoreModels.core.num.U64.from_le_bytes CoreModels.rust_primitives.arithmetic.from_le_bytes_u64
  simp [Triple, WP.wp, PredTrans.apply]

/-- The eight-byte LE-store `U64.to_le_bytes` always succeeds with
    `core.num.U64.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U64_to_le_bytes_spec (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U64.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.to_le_bytes x ⌝ ⦄ := by
  unfold CoreModels.core.num.U64.to_le_bytes CoreModels.rust_primitives.arithmetic.to_le_bytes_u64
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index` over `Range Usize` -/

/-- Slice subindexing over a `Range<usize>` succeeds whenever the range is
    in bounds, returning the sub-`Slice` whose `val` is the contiguous
    slice `s.val[start..end]`. -/
@[spec]
theorem core_models_Slice_Insts_index_RangeUsize_spec
    {T : Type} (s : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ r' => ⌜ r'.val = s.val.slice r.start.val r.end.val ∧
                r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
         CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         core.slice.index.Slice.index
         core.slice.index.SliceIndexRangeUsizeSlice.index
  simp only []
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp, PredTrans.apply]
  simp [h0', h1', Slice.length]
  simp [List.slice, List.length_drop, List.length_take]
  omega

/-! ### `CoreModels.core.result.Result.unwrap`

The hax `Result.unwrap` on the `core_models` `result.Result` enum panics on
`Err` and returns the inner `T` on `Ok`. We give a Triple-style spec under
the precondition `r = .Ok v`.

NB: the `try_from` Triple (for `Slice T → Array T N`) is proved at the
bottom of this file. -/

/-- `Result.unwrap` of a `.Ok`-valued `r` returns the inner value.

    We state both the precondition (`∃ v, r = .Ok v`) and the post
    (`r = .Ok r'`), leaving `v` quantified inside `mvcgen`'s assertion
    bag. This avoids the mvcgen unification quirk where the explicit
    `v` argument gets eagerly bound to the first matching local of the
    right type. -/
@[spec]
theorem core_models_result_Result_unwrap_spec
    {T E : Type} (dbg : CoreModels.core.fmt.Debug E)
    (r : CoreModels.core.result.Result T E)
    (h : ∃ v, r = .Ok v) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.result.Result.unwrap dbg r
    ⦃ ⇓ r' => ⌜ r = .Ok r' ⌝ ⦄ := by
  obtain ⟨v, hv⟩ := h
  unfold CoreModels.core.result.Result.unwrap
  subst hv
  simp [Triple, WP.wp, PredTrans.apply]



/-! ### `CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut` over `Range Usize`

Used by `state.store_block_2u32_loop.body` (Funs.lean:4373) to obtain a
mutable sub-slice and a write-back closure. -/

/-- Mutable slice subindexing over a `Range<usize>` returns both the
    sub-slice (same `val` as the non-mut `index`) and a write-back
    closure that overwrites `s.val[r.start.val..]` with the argument's
    `val`. -/
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeUsize_spec
    {T : Type} (s : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s', (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
         CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         core.slice.index.Slice.index_mut
         core.slice.index.SliceIndexRangeUsizeSlice.index_mut
  simp only []
  have h0' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).start
              ≤ (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end := by
    simpa [UScalar.le_equiv] using h0
  have h1' : (⟨r.start, r.end⟩ : core.ops.range.Range Std.Usize).end.val ≤ (Slice.length s) := by
    simpa [Slice.length] using h1
  simp only [Triple, WP.wp, PredTrans.apply]
  simp [h0', h1', Slice.length]
  simp [List.slice, List.length_drop, List.length_take]
  omega

/-! ### `CoreModels.core.slice.Slice.copy_from_slice` -/

/-- `copy_from_slice dst src` succeeds with the source slice `src`
    whenever both slices have the same length (the impl model returns
    `src` outright when lengths match). -/
@[spec]
theorem core_models_slice_Slice_copy_from_slice_spec
    {T : Type} (cpy : CoreModels.core.marker.Copy T) (dst src : Slice T)
    (h : dst.val.length = src.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.slice.Slice.copy_from_slice cpy dst src
    ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  unfold CoreModels.core.slice.Slice.copy_from_slice
  have h' : dst.len = src.len := by
    apply Std.UScalar.eq_of_val_eq
    simp [h]
  simp [Triple, WP.wp, PredTrans.apply, h']

/-! ### `CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from`

The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the `try_from`
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
    `Slice T`; `call_mut` reads the `i`-th element and preserves state.

    We state this on the unfolded form `...call_mut.call_mut cpy s i`
    because that's what the FnMut instance's `call_mut` field reduces to
    after Lean unfolds the structure projection. -/
private theorem try_from_closure_call_mut_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i =
      .ok (s.val[i.val]!, s) := by
  -- Reduces to `do let t ← slice_index s i; ok (t, s)`.
  unfold CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold CoreModels.rust_primitives.slice.slice_index Std.Slice.index_usize
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
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T)
    (_hN : s.val.length ≤ Std.Usize.max) :
    ∀ (k start : Nat) (acc : List T),
      acc = s.val.take start →
      start + k ≤ s.val.length →
      start + k ≤ Std.Usize.max →
      (List.range' start k).foldlM
        (fun (p : List T × Slice T) (i : Nat) => do
          let (v, f') ←
            CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
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
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    CoreModels.rust_primitives.slice.array_from_fn N
      (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
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
  -- We can't `rw [hrange]` (dependent motive); instead transfer h_fold to the
  -- `List.range` form first, then unfold and split.
  rw [← hrange] at h_fold
  unfold CoreModels.rust_primitives.slice.array_from_fn
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
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = CoreModels.core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  -- Unfold try_from and reduce the `do` chain step-by-step.
  unfold CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  -- `CoreModels.core.slice.Slice.len x` is `pure (Slice.len x)`, returns `.ok (Slice.len s)`.
  unfold CoreModels.core.slice.Slice.len
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
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (dbg : CoreModels.core.fmt.Debug CoreModels.core.array.TryFromSliceError)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    (do
      let r ← CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
                N cpy s
      CoreModels.core.result.Result.unwrap dbg r)
    ⦃ ⇓ a => ⌜ a = Std.Array.make N s.val (by simp [hlen]) ⌝ ⦄ := by
  -- Establish `try_from ... = .ok (.Ok (Array.make N s.val _))` outright.
  have h_try := core_models_array_try_from_slice_spec (T := T) (N := N) cpy s hlen
  -- Then unfold Result.unwrap and reduce.
  unfold CoreModels.core.result.Result.unwrap
  -- Reduce `try_from` to its known .ok form. The Triple post `h_try` already
  -- encodes this.
  have h_eq : (CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
                  N cpy s)
              = .ok (.Ok (Std.Array.make N s.val (by simp [hlen]))) := by
    exact libcrux_iot_sha3.Foundation.result_eq_of_triple h_try
  rw [h_eq]
  simp [Triple, WP.wp, PredTrans.apply]

/-! ## `!`-valued index override for the sponge layer.

The current Aeneas `Array.index_usize_spec` post is the total `getElem`
`v.val[i]`, whereas the sponge proofs are written with `getElem!`. The
sponge accessors (`get_lane`/`set_lane`/the `Lane2U32` `Index` instance) all
unfold to `Array.index_usize`, so a single high-priority `@[spec]` override
of the index post (which `mvcgen` prefers over the auto-generated default)
makes every unfolded read come out as `!` — the `getElem!` form the sponge
proofs use, with no per-site bridging. `@[spec high]`
ensures it wins over the Aeneas default without disabling it (disabling
would just make `mvcgen` unfold `index_usize` to the total form instead). -/
@[spec high]
theorem index_usize_bang_spec {α : Type _} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (hbound : i.val < v.length) :
    ⦃ ⌜ True ⌝ ⦄ v.index_usize i ⦃ ⇓ x => ⌜ x = v.val[i.val]! ⌝ ⦄ := by
  have h_idx : i.val < v.val.length := hbound
  have hbang : v.val[i.val]! = v.val[i.val]'h_idx := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_idx]; rfl
  obtain ⟨x, hxok, hxval⟩ :=
    Aeneas.Std.WP.spec_imp_exists (Std.Array.index_usize_spec v i hbound)
  have hpost : x = v.val[i.val]! := by rw [hxval, hbang]
  simp [Triple, WP.wp, PredTrans.apply, hxok, hpost]

end libcrux_iot_sha3.Sponge
