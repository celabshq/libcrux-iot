import LibcruxIotSha3.Composition.Pedantic.LoopEq
/-!
# Writing one bit of a state array

Every FIPS 202 step mapping that builds a fresh output state does it the same
way: `out.a[x][y][z] = <formula>` inside a `for x / for y / for z` nest.  The
extraction reaches that cell through two `Array.index_mut_usize` calls and one
`Array.update`, and composing the two write-backs with the update is `setBit`.

`bitAt_setBit` is the only fact the loop proofs need about it, and it is what
makes the invariants in `Chi`, `Pi`, ... readable: an invariant says which cells
have been written so far, and each iteration moves one cell across that line.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-! ### Writing a single bit

The extracted loop body reaches `out.a[x][y][z]` through two
`Array.index_mut_usize` calls and one `Array.update`; composing the two
write-backs with the update is exactly `setBit`. -/

/-- `A` with `A[x, y, z]` replaced by `b`. -/
def setBit (A : SA) (x y z : Std.Usize) (b : Bool) : SA :=
  { a := A.a.set x ((A.a.val[x.val]!).set y ((A.a.val[x.val]!.val[y.val]!).set z b)) }

theorem bitAt_setBit (A : SA) (x y z : Std.Usize) (b : Bool) (x' y' z' : Nat)
    (hx : x.val < 5) (hy : y.val < 5) (hz : z.val < 64)
    (hx' : x' < 5) (hy' : y' < 5) (hz' : z' < 64) :
    bitAt (setBit A x y z b) x' y' z'
      = if x' = x.val ∧ y' = y.val ∧ z' = z.val then b else bitAt A x' y' z' := by
  have hlen5 : A.a.val.length = 5 := by simp
  have hlen5' : (A.a.val[x.val]!).val.length = 5 := by simp
  have hlen64 : (A.a.val[x.val]!.val[y.val]!).val.length = 64 := by simp
  by_cases hxx : x' = x.val <;> by_cases hyy : y' = y.val <;> by_cases hzz : z' = z.val <;>
    simp_all [bitAt, setBit]


/-- Pointwise equality up to the length is equality, for Aeneas' fixed-size
    arrays, in terms of the `[i]!` accessor the readers use. -/
theorem array_ext {α : Type} [Inhabited α] {n : Std.Usize} {u v : Std.Array α n}
    (h : ∀ i < n.val, u.val[i]! = v.val[i]!) : u = v := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [u.property, v.property])
  intro i hi hi'
  have hin : i < n.val := by rw [← u.property]; exact hi
  have e1 : u.val[i]! = u.val[i] := getElem!_pos u.val i hi
  have e2 : v.val[i]! = v.val[i] := getElem!_pos v.val i hi'
  rw [← e1, ← e2]
  exact h i hin

/-! ## The `5 × w` scratch planes

θ builds two of them, FIPS 202's `C` and `D` (Algorithm 1, steps 1 and 2).  They
are the same story as the state array one dimension down, so they get the same
four pieces: a reader, a builder, extensionality, and a one-bit write. -/

/-- FIPS 202's `C` / `D`: one bit per column and slice. -/
abbrev CArr : Type := Std.Array (Std.Array Bool 64#usize) 5#usize

/-- `C[x, z]`, out-of-range indices reading `false`. -/
def cAt (c : CArr) (x z : Nat) : Bool := c.val[x]!.val[z]!

/-- The plane whose bits are given by `f`. -/
def mkC (f : Nat → Nat → Bool) : CArr :=
  ⟨(List.ofFn fun x : Fin 5 =>
      (⟨List.ofFn fun z : Fin 64 => f x.val z.val, by simp⟩ : Std.Array Bool 64#usize)), by simp⟩

@[simp]
theorem cAt_mkC (f : Nat → Nat → Bool) {x z : Nat} (hx : x < 5) (hz : z < 64) :
    cAt (mkC f) x z = f x z := by
  simp only [cAt, mkC, List.getElem!_eq_getElem?_getD, List.length_ofFn,
    List.getElem?_eq_getElem, hx, hz, List.getElem_ofFn, Option.getD_some]

theorem cext {c d : CArr} (h : ∀ x z, x < 5 → z < 64 → cAt c x z = cAt d x z) : c = d := by
  refine array_ext (fun x hx => ?_)
  refine array_ext (fun z hz => ?_)
  exact h x z (by simpa using hx) (by simpa using hz)

/-- `c` with `c[x, z]` replaced by `b`. -/
def setCBit (c : CArr) (x z : Std.Usize) (b : Bool) : CArr :=
  c.set x ((c.val[x.val]!).set z b)

theorem cAt_setCBit (c : CArr) (x z : Std.Usize) (b : Bool) (x' z' : Nat)
    (hx : x.val < 5) (hz : z.val < 64) (hx' : x' < 5) (hz' : z' < 64) :
    cAt (setCBit c x z b) x' z'
      = if x' = x.val ∧ z' = z.val then b else cAt c x' z' := by
  have hlen5 : c.val.length = 5 := by simp
  have hlen64 : (c.val[x.val]!).val.length = 64 := by simp
  by_cases hxx : x' = x.val <;> by_cases hzz : z' = z.val <;>
    simp_all [cAt, setCBit]

end LibcruxIotSha3.Composition.Pedantic
