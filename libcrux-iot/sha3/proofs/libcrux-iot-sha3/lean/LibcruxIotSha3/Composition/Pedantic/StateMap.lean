import HacspecSha3Pedantic
import LibcruxIotSha3.Composition.Pedantic.Parameters
import LibcruxIotSha3.LaneModel
/-!
# The state correspondence between the two SHA-3 hacspecs

`hacspec_sha3` keeps the Keccak state as 25 `u64` lanes, `state[5*y + x]` holding
the lane `A[x, y]` (FIPS 202, Sec. 3.1.2); `hacspec_sha3_pedantic` keeps it as the
FIPS state array itself, `A.a[x][y][z] : Bool`.  With `w = 64` the two are the
same data, related by "bit `z` of the lane is `A[x, y, z]`" -- which is exactly
the lane convention of Sec. 3.1.2, `S[w(5y + x) + z] = A[x, y, z]`, read
little-endian within the lane.

This module makes that relation a pair of functions, `ofLanes` / `toLanes`, and
proves they are mutually inverse.  Everything above it in `Composition/Pedantic/`
is phrased as "`f_pedantic (ofLanes s) = ofLanes (f_hacspec s)`", so the two
directions are both needed: `ofLanes` to push a `hacspec_sha3` state into the
pedantic world, `toLanes` to come back at the end.

The maps are total and definitional -- no `RustM`, no loops -- so they can be
unfolded freely; the extracted `from_bits` / `to_bits` (which do the same job
against a flat bit string at the sponge boundary) are related to them separately.
-/

open Aeneas Aeneas.Std
open LibcruxIotSha3.LaneModel

namespace LibcruxIotSha3.Composition.Pedantic

/-- The pedantic state array at the Keccak-f[1600] lane width, `w = 64`. -/
abbrev SA : Type := hacspec_sha3_pedantic.state_array.StateArray 64#usize

/-! ### Reading a state array

`A[x][y][z]`, with out-of-range indices reading `false`.  Indices stay `Nat`
here (rather than `Fin`): the extracted definitions index with `Usize` values
whose bounds are proof obligations discharged inside `RustM`, and matching that
shape keeps the step-mapping lemmas free of index coercions. -/
def bitAt (A : SA) (x y z : Nat) : Bool := A.a.val[x]!.val[y]!.val[z]!

/-! ### The two directions -/

/-- The state array whose bits are given by `f` (a "`ofFn` for state arrays").
    Every characterisation of an extracted step mapping below has the shape
    `step A = ok (mkSA <FIPS formula in bitAt A>)`, so this is the one place
    where a state array is built. -/
def mkSA (f : Nat → Nat → Nat → Bool) : SA :=
  { a := ⟨(List.ofFn fun x : Fin 5 =>
            (⟨(List.ofFn fun y : Fin 5 =>
                (⟨List.ofFn fun z : Fin 64 => f x.val y.val z.val, by simp⟩ :
                  Array Bool 64#usize)), by simp⟩ :
              Array (Array Bool 64#usize) 5#usize)), by simp⟩ }

/-- The state array of a 25-lane state (FIPS 202, Sec. 3.1.2). -/
def ofLanes (s : Lanes) : SA := mkSA (laneBit s)

/-- The 25-lane state of a state array (the inverse of `ofLanes`). -/
def toLanes (A : SA) : Lanes :=
  ⟨List.ofFn fun i : Fin 25 =>
     (⟨BitVec.ofFn fun z : Fin 64 => bitAt A (i.val % 5) (i.val / 5) z.val⟩ : Std.U64), by simp⟩

/-! ### Projection and extensionality

`mkSA` is projected by `bitAt` (in range), and two state arrays with the same
bits are equal.  Both are proved by `getElem!` rewriting rather than `simp`:
unfolding the three nested `List.ofFn`s of `mkSA` produces a literal
5 x 5 x 64 list, which is unusable downstream. -/

@[simp]
theorem bitAt_mkSA (f : Nat → Nat → Nat → Bool) {x y z : Nat}
    (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    bitAt (mkSA f) x y z = f x y z := by
  simp only [bitAt, mkSA, List.getElem!_eq_getElem?_getD, List.length_ofFn,
    List.getElem?_eq_getElem, hx, hy, hz, List.getElem_ofFn, Option.getD_some]

@[simp]
theorem bitAt_ofLanes (s : Lanes) {x y z : Nat} (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    bitAt (ofLanes s) x y z = laneBit s x y z :=
  bitAt_mkSA _ hx hy hz

/-- Extensionality for the Aeneas fixed-size arrays the state array is built
    from, in terms of the `[i]!` accessor `bitAt` uses. -/
private theorem array_ext_getElem! {α : Type} [Inhabited α] {n : Std.Usize}
    (a b : Array α n) (h : ∀ i, i < n.val → a.val[i]! = b.val[i]!) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < n.val := by rw [a.property] at h1; exact h1
  have hab := h i hi
  rwa [getElem!_pos a.val i (by omega), getElem!_pos b.val i (by omega)] at hab

theorem ext {A B : SA} (h : ∀ x y z, x < 5 → y < 5 → z < 64 → bitAt A x y z = bitAt B x y z) :
    A = B := by
  have h5 : (5#usize).val = 5 := by simp
  have h64 : (64#usize).val = 64 := by simp
  obtain ⟨a⟩ := A; obtain ⟨b⟩ := B
  congr 1
  refine array_ext_getElem! _ _ (fun x hx => array_ext_getElem! _ _ (fun y hy =>
    array_ext_getElem! _ _ (fun z hz => ?_)))
  exact h x y z (by omega) (by omega) (by omega)

/-! ### The maps are mutually inverse -/

theorem toLanes_ofLanes (s : Lanes) : toLanes (ofLanes s) = s := by
  have hlen : s.val.length = 25 := by simp
  apply Subtype.ext
  apply List.ext_getElem (by simp [toLanes, hlen])
  intro i h1 h2
  have hi : i < 25 := by rw [hlen] at h2; exact h2
  apply (Std.U64.eq_equiv_bv_eq _ _).mpr
  apply BitVec.eq_of_getElem_eq
  intro z hz
  simp only [toLanes, List.getElem_ofFn, BitVec.getElem_ofFn]
  rw [bitAt_ofLanes s (Nat.mod_lt _ (by omega)) (by omega) hz]
  unfold laneBit
  have h5 : 5 * (i / 5) + i % 5 = i := by omega
  rw [h5, getElem!_pos s.val i (by omega), BitVec.getLsbD_eq_getElem hz]

theorem ofLanes_toLanes (A : SA) : ofLanes (toLanes A) = A := by
  refine ext (fun x y z hx hy hz => ?_)
  rw [bitAt_ofLanes _ hx hy hz]
  unfold laneBit toLanes
  have hidx : 5 * y + x < 25 := by omega
  rw [getElem!_pos _ _ (by simp [hidx]), BitVec.getLsbD_eq_getElem hz]
  simp only [List.getElem_ofFn]
  simp
  congr 2 <;> omega

/-- `mkSA` is surjective onto state arrays: rebuilding a state array from its own
    bits gives it back.  Loop invariants below are stated with `mkSA`, and this is
    how they are started from an arbitrary initial state array. -/
@[simp]
theorem mkSA_bitAt (A : SA) : mkSA (bitAt A) = A :=
  ext (fun _ _ _ hx hy hz => bitAt_mkSA _ hx hy hz)

/-- Two state arrays built from functions agreeing in range are equal. -/
theorem mkSA_congr {f g : Nat → Nat → Nat → Bool}
    (h : ∀ x y z, x < 5 → y < 5 → z < 64 → f x y z = g x y z) : mkSA f = mkSA g :=
  ext (fun x y z hx hy hz => by
    rw [bitAt_mkSA _ hx hy hz, bitAt_mkSA _ hx hy hz]; exact h x y z hx hy hz)

-- Pinned by `#guard_msgs`: the build fails if a result comes to depend on any
-- axiom beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Composition.Pedantic.ofLanes_toLanes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ofLanes_toLanes

/--
info: 'LibcruxIotSha3.Composition.Pedantic.toLanes_ofLanes' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toLanes_ofLanes

end LibcruxIotSha3.Composition.Pedantic
