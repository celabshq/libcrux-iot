/-
  # Spec-side scaffolding for `sponge.xor_block_into_state`.

  Installed:

  - `from_fn_pure_spec` — generic `@[spec]` analog of `createi_pure_spec`
    (HacspecBridge.lean:663) but stated over the *direct* `FnMut` instance
    (no `Fn` wrapper required). `sponge.xor_block_into_state` uses
    `CoreModels.core.array.from_fn` directly with a `FnMut`, not the `Fn`-wrapped
    `createi`. Reusable for any pure FnMut closure.
  - `list_8_at` / `list_8_at_val_eq_slice` — helpers that extract 8 bytes
    from a list at offset `o`, padded to length 8, with a proof that the
    padded form coincides with the exact slice when `o + 8 ≤ length`.
  - `xor_block_value_at` — the per-cell pure value characterizing the
    closure body (`f`-side for `from_fn_pure_spec`).
  - `xor_block_into_state_closure_call_mut_spec` — the per-cell `@[spec]`
    for the 25-cell `from_fn` body. Drives the inner do-chain
    `div/rem → mul/add → div → if → (slice-index → try_from → unwrap →
    from_le_bytes → lift) | (Array.index_usize)`. In the `b < rate/8`
    branch, matches the constructed 8-byte array's `.val` with
    `list_8_at block.val (8b)` via `list_8_at_val_eq_slice`.

  ## Closure body (Extraction/Funs.lean:1076-1105)

  Given `c = (rate, state, block)` and cell index `k`:

  ```
  x = k / 5
  y = k % 5
  b = 5*y + x   -- = 5*(k%5) + k/5  (the "byte_lane_idx" inverse)
  if b < rate/8 then
    state[k] ^^^ U64.from_le_bytes(block[8b..8b+8])
  else
    state[k]
  ```

  Both branches return `(value, c)` — the closure state is preserved, so
  `from_fn_pure_spec` applies even though the body has an `if`.
-/
import LibcruxIotSha3.Sponge.Interleave
import LibcruxIotSha3.Sponge.SliceSpecs

open Aeneas Aeneas.Std RustM Std.Do libcrux_iot_sha3
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation

attribute [local irreducible] keccak.keccakf1600 keccakFLanes

/-! ## A generic `from_fn` pure-closure spec.

Analogous to `createi_pure_spec` (HacspecBridge.lean:663) but takes
a `FnMut` instance directly (no `Fn` wrapper). Required because
`sponge.xor_block_into_state` calls `CoreModels.core.array.from_fn` directly
with the `FnMut` instance of its closure. -/

private theorem array_from_fn_go_pure
    {T F : Type}
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (n : Nat)
    (hpure : ∀ k : Nat, k < n →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    CoreModels.rust_primitives.slice.array_from_fn_go inst c n
      = .ok ((List.range n).map f, c) := by
  induction n with
  | zero =>
      simp [CoreModels.rust_primitives.slice.array_from_fn_go]
  | succ n ih =>
      have ht : ∀ k : Nat, k < n →
          inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c) :=
        fun k hk => hpure k (Nat.lt_succ_of_lt hk)
      simp only [CoreModels.rust_primitives.slice.array_from_fn_go, ih ht, bind_tc_ok,
        hpure n (Nat.lt_succ_self n), List.range_succ, List.map_append, List.map_cons,
        List.map_nil]

/-- Lean-level equation for `from_fn` over pure closures.

    CoreModels v0.3.12 builds the array by structural recursion over the index
    count (`array_from_fn_go`) plus a length-guarded `if`, rather than by folding
    `List.range`, so the previous `from_fn_foldlM_pure_aux` characterization and
    the `split` over the fold's three outcomes are replaced by the induction
    above. (Kept local, mirroring the parallel copy in
    Foundation/ThetaLiftDefs.lean, rather than adding an import edge.) -/
theorem from_fn_pure_eq
    {T F : Type} (N : Std.Usize)
    (inst : CoreModels.core.ops.function.FnMut F Std.Usize T) (c : F) (f : Nat → T)
    (hpure : ∀ k : Nat, k < N.val →
      inst.call_mut c ⟨BitVec.ofNat _ k⟩ = .ok (f k, c)) :
    CoreModels.core.array.from_fn N inst c =
      .ok ⟨(List.range N.val).map f,
           by simp [List.length_map, List.length_range]⟩ := by
  unfold CoreModels.core.array.from_fn
    CoreModels.rust_primitives.slice.array_from_fn
  rw [array_from_fn_go_pure inst c f N.val hpure]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp : ((List.range N.val).map f).length = N.val)]

/-- **Generic pure-closure `[spec]` for `CoreModels.core.array.from_fn`.**

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
    CoreModels.core.array.from_fn N inst c
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

/-! ## `f`-side per-cell value for `xor_block_into_state.closure`.

The closure body at cell `k` (with `c = (rate, state, block)`) computes
`b := 5*(k%5) + k/5` (the "byte_lane_idx" inverse), then:
- if `b < rate/8`, returns `state[k] ^^^ U64.from_le_bytes(block[8b..8b+8])`;
- otherwise, returns `state[k]`.

We make the function total by using a padded list when the slice access
is out of range. Under the impl precondition `block.val.length = rate.val`
and `rate.val % 8 = 0`, the `b < rate/8` guard implies `8b + 8 ≤ rate.val
= block.val.length`, so the padded case is unreachable. -/

/-- Extract 8 bytes from a list at offset `o`, padded with `0#u8` to length 8.
    Used in `xor_block_value_at` to make the value total. -/
def list_8_at (l : List Std.U8) (o : Nat) : Std.Array Std.U8 8#usize :=
  let raw := (l.drop o).take 8
  let padded := raw ++ List.replicate (8 - raw.length) (0#u8)
  ⟨padded, by
    have h_raw_le : raw.length ≤ 8 := by
      show ((l.drop o).take 8).length ≤ 8
      simp [List.length_take]
    have hlen : padded.length = 8 := by
      show (raw ++ List.replicate (8 - raw.length) (0#u8)).length = 8
      rw [List.length_append, List.length_replicate]
      omega
    simp [hlen]⟩

/-- The padded slice equals an exact slice when the bytes are in range. -/
theorem list_8_at_val_eq_slice
    (l : List Std.U8) (o : Nat) (h : o + 8 ≤ l.length) :
    (list_8_at l o).val = l.slice o (o + 8) := by
  unfold list_8_at
  show ((l.drop o).take 8) ++ List.replicate (8 - ((l.drop o).take 8).length) (0#u8)
        = l.slice o (o + 8)
  have hraw_len : ((l.drop o).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  rw [hraw_len]
  simp only [Nat.sub_self, List.replicate, List.append_nil]
  -- `List.slice o (o+8) l = (l.drop o).take 8`
  show (l.drop o).take 8 = l.slice o (o + 8)
  unfold List.slice
  rw [show o + 8 - o = 8 from by omega]

/-- Pure value at cell `k` of `xor_block_into_state`'s closure body.
    Under the new spec layout, byte-block index `b` equals state index `k`
    (no transpose), so the closure is simply `if k < rate/8 then state[k] ^^^
    block[8*k..8*k+8] else state[k]`. -/
def xor_block_value_at
    (state : Std.Array Std.U64 25#usize) (block : Slice Std.U8) (rate : Std.Usize)
    (k : Nat) : Std.U64 :=
  if k < rate.val / 8 then
    state.val[k]! ^^^ Std.core.num.U64.from_le_bytes (list_8_at block.val (8 * k))
  else
    state.val[k]!

/-! ### The lane model's `xorLanes` is this, cell by cell

`SpongeModel.xorLanes` says the same thing as `xor_block_value_at`, with the
eight bytes read through `mkArr` rather than zero-padded by `list_8_at`; in
range the two agree. -/

theorem list_8_at_eq_mkArr (l : List Std.U8) (o : Nat) (h : o + 8 ≤ l.length) :
    list_8_at l o = mkArr 8#usize (fun j => l[o + j]!) := by
  apply Subtype.ext
  have hraw : ((l.drop o).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  show ((l.drop o).take 8) ++ List.replicate (8 - ((l.drop o).take 8).length) (0#u8)
    = (List.range 8).map (fun j => l[o + j]!)
  rw [hraw]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  apply List.ext_getElem
  · rw [hraw]; simp
  · intro k hk _
    have hk8 : k < 8 := by rw [hraw] at hk; exact hk
    rw [List.getElem_take, List.getElem_drop, List.getElem_map, List.getElem_range,
      getElem!_pos l (o + k) (by omega)]

theorem xorLanes_getElem (state : Std.Array Std.U64 25#usize) (block : Slice Std.U8)
    (rate : Std.Usize) (h_rate_mod : rate.val % 8 = 0)
    (h_blk_len : block.val.length = rate.val) (k : Nat) (hk : k < 25) :
    (xorLanes state block.val rate.val).val[k]!
      = xor_block_value_at state block rate k := by
  rw [xorLanes, mkArr_get 25#usize _ (by simpa using hk)]
  unfold xor_block_value_at blockLane
  by_cases h : k < rate.val / 8
  · rw [if_pos h, if_pos h,
      list_8_at_eq_mkArr block.val (8 * k) (by rw [h_blk_len]; omega)]
  · rw [if_neg h, if_neg h]

end libcrux_iot_sha3.Sponge
