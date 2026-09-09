/-
  # `Util/CreateI.lean` — Pure-closure `createi` / `from_fn` Triples

  Merges the two pure-closure-array-builder Triples from libcrux-iot
  SHA-3's tree (which were split between two unrelated files for
  historical reasons) into one Util module with consistent naming.

  ## Lifted from

  - `createi_pure_eq` + `createi_pure_spec`
    (`LibcruxIotSha3/Equivalence/HacspecBridge.lean:627,663`) —
    the `Fn`-wrapped variant. `createi N inst.FnMutInst c` (where `inst` is a
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

open CoreModels Aeneas Aeneas.Std RustM Std.Do
open hacspec_ml_kem.parameters (createi)

namespace libcrux_iot_ml_kem.Util.CreateI
open libcrux_iot_ml_kem.Util.SliceSpecs
set_option mvcgen.warning false
set_option linter.unusedVariables false

/-! ## `Fn`-wrapped variant: `createi N inst.FnMutInst c` -/

/-- Per-index evaluation of `array_from_fn_go` for pure closures: the closure
    state is invariant and the list produced for `n` indices is
    `(List.range n).map f`.

    CoreModels v0.3.12 builds the array by structural recursion over the index
    count plus a length-guarded `if`, rather than by folding `List.range`, so the
    previous `createi_foldlM_pure_aux`/`from_fn_foldlM_pure_aux` characterizations
    (and the `split` over the fold's three outcomes) are replaced by this. -/
private theorem array_from_fn_go_pure
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (n : Nat)
    (hpure : ∀ k : Nat, k < n →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    rust_primitives.slice.array_from_fn_go inst c n
      = .ok ((List.range n).map f, c) := by
  induction n with
  | zero =>
      simp [rust_primitives.slice.array_from_fn_go]
  | succ n ih =>
      have ht : ∀ k : Nat, k < n →
          inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (Nat.lt_succ_of_lt hk)
      simp only [rust_primitives.slice.array_from_fn_go, ih ht, bind_tc_ok,
        hpure n (Nat.lt_succ_self n), List.range_succ, List.map_append, List.map_cons,
        List.map_nil]

/-- Lean-level equation for `createi` over pure closures. Used to power
    `createi_pure_spec` (Triple form). -/
theorem createi_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.Fn F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    createi N inst.FnMutInst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  unfold createi core.array.from_fn rust_primitives.slice.array_from_fn
  rw [array_from_fn_go_pure inst.FnMutInst c f N.val hpure]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp : ((List.range N.val).map f).length = N.val)]

/-- Lean-level equation for `from_fn` over pure closures. -/
theorem from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    core.array.from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  unfold core.array.from_fn rust_primitives.slice.array_from_fn
  rw [array_from_fn_go_pure inst c f N.val hpure]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp : ((List.range N.val).map f).length = N.val)]

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


/-! ## Axiom guards
    Pinned by `#guard_msgs` (replacing the former `AxiomCheck.lean`, which only asserted
    sorry-freedom): the build fails if a result's axiom set drifts. Beyond Lean's standard
    three, only the documented deferred leaves A1 (`sample_matrix_entry_fc` with the opaque
    `matrix.sample_matrix_entry`) and A2 (`deserialize_to_reduced_ring_element_fc`) may
    appear, and only where listed. -/
/--
info: 'libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms createi_pure_eq

end libcrux_iot_ml_kem.Util.CreateI
