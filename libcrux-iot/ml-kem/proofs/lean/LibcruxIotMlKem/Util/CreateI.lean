/-
  # `Util/CreateI.lean` — Pure-closure `createi` / `from_fn` Triples

  Merges the two pure-closure-array-builder Triples from libcrux-iot
  SHA-3's tree (which were split between two unrelated files for
  historical reasons) into one Util module with consistent naming.

  ## Lifted from

  - `createi_pure_eq` + `createi_pure_spec`
    (`LibcruxIotSha3/Equivalence/HacspecBridge.lean:627,663`) —
    the `Fn`-wrapped variant. `createi N inst c` (where `inst` is a
    `core.ops.function.Fn` instance) is the hax extraction of
    `core::array::from_fn` over a *shared* closure.

  - `from_fn_pure_eq` + `from_fn_pure_spec`
    (`LibcruxIotSha3/Sponge/XorBlockSpec.lean:103,137`) —
    the *direct* `FnMut` variant. `core.array.from_fn N inst c`
    (where `inst` is `core.ops.function.FnMut`) is the hax
    extraction of `core::array::from_fn` over a mutable-via-`FnMut`
    closure (e.g. `sponge.xor_block_into_state`).

  Both produce a length-`N` array whose `i`-th cell is `f i`, when the
  closure body is pure (`call_mut` returns `(f i, c)` for input `i`).
  The two specs differ only in the wrapper around `call_mut`.

  Use whichever spec matches the extraction:
  - The hax extraction of `core::array::from_fn` over a *`Fn`*-bounded
    closure goes through `createi` and the `createi_*_spec` should be
    referenced.
  - The hax extraction of `core::array::from_fn` over a *`FnMut`*-bounded
    closure (or one that internally captures by mutable reference)
    goes directly through `core.array.from_fn` and
    `from_fn_*_spec` should be referenced.

  ## Naming (renamed for `Util` namespace)

  - `createi_pure_eq`   (was `libcrux_iot_sha3.Equivalence.createi_pure_eq`)
  - `createi_pure_spec` (was `libcrux_iot_sha3.Equivalence.createi_pure_spec`)
  - `from_fn_pure_eq`   (was `libcrux_iot_sha3.Sponge.from_fn_pure_eq`)
  - `from_fn_pure_spec` (was `libcrux_iot_sha3.Sponge.from_fn_pure_spec`)
-/
import LibcruxIotMlKem.Util.SliceSpecs
-- `hacspec_sha3.createi` is the canonical `core::array::from_fn` wrapper
-- (extracted from `specs/sha3/src/lib.rs:21`). The same wrapper covers
-- ML-KEM's `Fn`-bounded array builders. Importing brings the symbol
-- into scope; the Triples below are stated on it directly.
import HacspecSha3.Extraction.Funs
import HacspecMlKem.Extraction.Funs

open CoreModels Aeneas Aeneas.Std Result Std.Do
open hacspec_ml_kem.parameters (createi)

namespace libcrux_iot_ml_kem.Util.CreateI
open libcrux_iot_ml_kem.Util.SliceSpecs
set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## `Fn`-wrapped variant: `createi N inst c` -/

/-- Per-element foldlM evaluation for pure closures. The closure state `c`
    is invariant; the result list is `acc ++ l.map f`. -/
private theorem createi_foldlM_pure_aux
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]
      rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `createi` over pure closures. Used to power
    `createi_pure_spec` (Triple form). -/
theorem createi_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    createi N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    createi_foldlM_pure_aux inst.FnMutInst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold createi core.array.from_fn rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-- **Generic pure-closure `[spec]` for `createi`.**

For any closure whose `call_mut` is pure (doesn't mutate captured state),
`createi N inst c` succeeds and its `i`-th cell is `f i`. The hypothesis
`hpure` is a Triple over each call_mut so `hax_mvcgen` can recurse into
it via per-closure `@[spec]` lemmas.

Tagged `@[spec]` so `hax_mvcgen` chains through nested `createi` calls. -/
@[spec]
theorem createi_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : CoreModels.core.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    createi N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    fun k hk => result_eq_of_triple (hpure k hk)
  have heq := createi_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

/-! ## `FnMut`-direct variant: `core.array.from_fn N inst c`

Analogous to `createi_*` but takes a `core.ops.function.FnMut`
instance directly (no `Fn` wrapper). Required when the hax extraction
calls `core.array.from_fn` directly with the `FnMut` instance of
its closure (e.g. SHA-3's `sponge.xor_block_into_state`; ML-KEM
matrix/poly constructors). -/

private theorem from_fn_foldlM_pure_aux
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (l : List Nat) (acc : List T)
    (hpure : ∀ k ∈ l,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    l.foldlM
      (fun (s : List T × F) (i : Nat) => do
        let (v, f') ← inst.call_mut s.2 ⟨BitVec.ofNat _ i⟩
        Result.ok (s.1 ++ [v], f'))
      (acc, c) = .ok (acc ++ l.map f, c) := by
  induction l generalizing acc with
  | nil =>
      simp only [List.foldlM_nil, List.map_nil, List.append_nil]; rfl
  | cons h t ih =>
      have hh : inst.call_mut c ⟨BitVec.ofNat _ h⟩ = .ok (f h, c) :=
        hpure h List.mem_cons_self
      have ht : ∀ k ∈ t, inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (List.mem_cons_of_mem _ hk)
      have hih := ih (acc ++ [f h]) ht
      simp only [List.foldlM_cons, hh, bind_tc_ok, List.map_cons]
      rw [hih]
      simp [List.append_assoc]

/-- Lean-level equation for `from_fn` over pure closures. -/
theorem from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    core.array.from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  have hf : ∀ k ∈ List.range N.val,
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) := by
    intro k hk; exact hpure k (List.mem_range.mp hk)
  have h_fold :=
    from_fn_foldlM_pure_aux inst c f (List.range N.val) [] hf
  simp only [List.nil_append] at h_fold
  unfold core.array.from_fn rust_primitives.slice.array_from_fn
  split
  · rename_i e heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [h_fold] at heq; exact absurd heq (by simp)
  · rename_i result heq
    rw [h_fold] at heq
    have hres : result = ((List.range N.val).map f, c) :=
      (Result.ok.inj heq).symm
    subst hres
    rfl

/-- **Generic pure-closure `[spec]` for `core.array.from_fn`.**

For any closure whose `call_mut` is pure (doesn't mutate state),
`from_fn N inst c` succeeds and its `i`-th cell is `f i`. `hpure` is a
Triple over each `call_mut` so `hax_mvcgen` can recurse through it via
per-closure `@[spec]` lemmas. -/
@[spec]
theorem from_fn_pure_spec
    {T F : Type} [Inhabited T] (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      ⦃ ⌜ True ⌝ ⦄
      inst.call_mut c ⟨BitVec.ofNat _ k⟩
      ⦃ ⇓ r => ⌜ r = (f k, c) ⌝ ⦄) :
    ⦃ ⌜ True ⌝ ⦄
    core.array.from_fn N inst c
    ⦃ ⇓ a => ⌜ ∀ i : Nat, i < N.val → a.val[i]! = f i ⌝ ⦄ := by
  have hpure_eq : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
    fun k hk => result_eq_of_triple (hpure k hk)
  have heq := from_fn_pure_eq N inst c f hpure_eq
  rw [heq]
  simp only [Triple, WP.wp]
  apply SPred.pure_intro
  intro i hi
  show ((List.range N.val).map f)[i]! = f i
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range hi]
  rfl

end libcrux_iot_ml_kem.Util.CreateI