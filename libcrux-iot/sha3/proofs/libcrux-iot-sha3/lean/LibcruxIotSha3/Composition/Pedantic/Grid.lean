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

end LibcruxIotSha3.Composition.Pedantic
