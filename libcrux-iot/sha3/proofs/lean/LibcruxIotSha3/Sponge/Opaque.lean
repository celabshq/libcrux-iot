/-
  # Opaque seal for `keccakf1600`

  Sealed `@[spec]` Triple bridging the impl `keccak.keccakf1600` to the
  hacspec `keccak_f.keccak_f` for use throughout the sponge proofs.

  The post strengthens Bridge 1 (`Composition.keccakf1600_equiv_hacspec`)
  with `r.i.val = 0` — needed because the impl's `keccakf1600` resets
  `s.i := 0#usize` at the end, and every subsequent absorb/squeeze step's
  precondition requires `s.i.val = 0`.

  After the seal proves, `keccak.keccakf1600` and `keccak_f.keccak_f` are
  marked `attribute [local irreducible]` so downstream files cannot peek
  inside.
-/
import LibcruxIotSha3.Composition.HacspecBridge

open Aeneas Aeneas.Std Result Std.Do libcrux_iot_sha3 hacspec_sha3

namespace libcrux_iot_sha3.Sponge

open libcrux_iot_sha3.Foundation libcrux_iot_sha3.Composition

/-! ## Opaque seal for `keccakf1600`. -/

/-- Local shape: `Triple` postshape for `Result α` (matches the one used
    in `HacspecBridge.lean`). -/
private abbrev ResultPSU :=
  PostShape.except Aeneas.Std.Error (PostShape.except PUnit PostShape.pure)

/-- If a `Triple ⦃ True ⦄ x ⦃ noThrow Q ⦄` holds then `x` reduces to some
    `ok v`. Re-derived locally from the private helper of the same
    purpose in `HacspecBridge.lean`. -/
private theorem triple_noThrow_exists_ok_local {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) : ∃ v, x = .ok v := by
  match x, h with
  | .ok v, _ => exact ⟨v, rfl⟩
  | .fail _, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

/-- If `x = .ok v` and `Triple ⦃ True ⦄ x ⦃ noThrow Q ⦄`, then `Q v`
    holds. -/
private theorem triple_noThrow_elim_local {α : Type} {x : Result α}
    {Q : α → Assertion ResultPSU}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ PostCond.noThrow Q ⦄) {v : α} (hv : x = .ok v) :
    (Q v).down := by
  subst hv; simpa [Triple, WP.wp, PredTrans.apply] using h

/-- If `x = .ok v` and we have `P v`, repackage as a Triple with a
    `pure-prop` post. -/
private theorem triple_of_ok_local {α : Type} {x : Result α} {v : α}
    {P : α → Prop} (hx : x = .ok v) (hp : P v) :
    ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄ := by
  subst hx; simp [Triple, WP.wp, PredTrans.apply, hp]

/-- Any successful `keccak.keccakf1600` execution sets `i := 0#usize` in
    its output state. This is by construction: the impl body ends with
    `ok { s1 with i := 0#usize }`.

    This is the *only* place we ever `unfold keccak.keccakf1600`; the
    attribute at the bottom of this file seals it for the rest of
    the sponge proofs. -/
private theorem keccakf1600_i_zero_of_ok
    {s r : state.KeccakState} (h : keccak.keccakf1600 s = .ok r) :
    r.i = 0#usize := by
  unfold keccak.keccakf1600 at h
  -- Body: `do let s1 ← keccakf1600_loop ... ; ok { s1 with i := 0#usize }`.
  cases hl : keccak.keccakf1600_loop { start := 0#i32, «end» := 6#i32 } s with
  | ok s1 =>
      rw [hl] at h
      -- After rewrite: `ok { s1 with i := 0#usize } = .ok r`.
      injection h with h
      rw [← h]
  | fail e =>
      rw [hl] at h; cases h
  | div =>
      rw [hl] at h; cases h

/-- Sealed `@[spec]` Triple bridging the impl-level `keccak.keccakf1600`
    to the hacspec-level `keccak_f.keccak_f`.

    Carries two facts:
    - spec-equality:    `keccak_f.keccak_f (lift s) = .ok (lift r)`
    - i-reset:          `r.i.val = 0`

    The second clause is required for chaining: every subsequent absorb
    or squeeze step's precondition is `s.i.val = 0`. -/
@[spec]
theorem keccakf1600_seal_spec (s : state.KeccakState) (h_i : s.i.val = 0) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r => ⌜ keccak_f.keccak_f (Foundation.lift s) = .ok (Foundation.lift r)
              ∧ r.i.val = 0 ⌝ ⦄ := by
  -- Convert the `.val` form of `h_i` to the bit-vector form Bridge 1 expects.
  have h_i' : s.i = 0#usize := Std.UScalar.eq_of_val_eq (by simpa using h_i)
  -- Bridge 1 gives the spec-equality half of the post.
  have h_bridge :=
    Composition.keccakf1600_equiv_hacspec s h_i'
  -- Extract the underlying Result equation `keccak.keccakf1600 s = .ok r0`.
  obtain ⟨r0, h_ok⟩ := triple_noThrow_exists_ok_local h_bridge
  -- Bridge 1's post evaluated at `r0`: spec-equality half.
  have h_spec : keccak_f.keccak_f (Foundation.lift s) = .ok (Foundation.lift r0) :=
    triple_noThrow_elim_local h_bridge h_ok
  -- Body-derived fact: `r0.i = 0#usize` ⇒ `r0.i.val = 0`.
  have h_r0_i : r0.i = 0#usize := keccakf1600_i_zero_of_ok h_ok
  have h_r0_val : r0.i.val = 0 := by
    rw [h_r0_i]; rfl
  -- Repackage as a Triple with the conjoined post.
  exact triple_of_ok_local h_ok ⟨h_spec, h_r0_val⟩

/-! Seal: from here on, no proof in `Sponge/` may unfold either side of
    Bridge 1. Importing files inherit `local irreducible` for these
    declarations, and each downstream file in `Sponge/` re-issues the
    attribute defensively.

    Note: `keccak_f.keccak_f` is marked `@[reducible]` in the spec
    extraction; demoting it to `[irreducible]` requires
    `allowUnsafeReducibility`. -/
set_option allowUnsafeReducibility true in
attribute [local irreducible] keccak.keccakf1600 keccak_f.keccak_f

end libcrux_iot_sha3.Sponge
