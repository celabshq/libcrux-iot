import LibcruxIotSha3.Composition.Pedantic.BitsOps
import LibcruxIotSha3.SpongeModel
/-!
# Bytes and bits (FIPS 202, App. B.1)

`h2b` and `b2h` convert between a byte string and a bit string, least
significant bit of each byte first (Algorithms 10 and 11).

Both are primitives of the transcript's opaque `BitStr` now, so this file is
the three-line bridge from their hand-written models to the lists the lane
model uses, rather than the loop induction it used to be. The models in
`HacspecSha3Pedantic/Assumptions/FunsExternal.lean` are written in exactly the
shapes below, so each bridge is `rfl`.

`h2b_full_eq` is the one that matters downstream, and note what it no longer
asks for: the old version needed `8 * h.val.length ≤ Usize.max`, because the
transcript formed the message's bit count in a machine word. It does not any
more.

`h2b` at an explicit `n` (Algorithm 10 in general, rather than at its maximum)
has no bridge here. The old one existed only to prove `h2b_full_eq` through the
conversion loop; with `from_bytes` a primitive there is nothing left to prove,
and nothing in the tree consumed it.
-/

open CoreModels Aeneas
open LibcruxIotSha3.SpongeModel
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Composition.Pedantic

/-- The eight bits of a byte, least significant first. -/
def byteBits (x : Std.U8) : List Bool := (List.range 8).map (fun j => x.bv.getLsbD j)

theorem byteBits_len (x : Std.U8) : (byteBits x).length = 8 := by simp [byteBits]

/-- A byte string as a bit string (FIPS 202, Algorithm 10). -/
def h2bList (h : List Std.U8) : List Bool := h.flatMap byteBits

theorem h2bList_len (h : List Std.U8) : (h2bList h).length = 8 * h.length := by
  simp only [h2bList, List.length_flatMap]
  rw [show h.map (fun x => (byteBits x).length) = h.map (fun _ => 8) from by
    apply List.map_congr_left
    intro x _
    exact byteBits_len x]
  simp [Nat.mul_comm]

theorem range_map_getElem' {α : Type} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun i => l[i]!) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getElem!_pos l i (by simpa using h1)]

/-- A bit string as a byte string: zero-pad to a multiple of eight, then take
    the bits eight at a time. -/
def b2hList (s : List Bool) : List Std.U8 :=
  let t := s ++ List.replicate ((8 - s.length % 8) % 8) false
  (List.range (t.length / 8)).map (fun i => byteOf (fun j => t[8 * i + j]!))

/-! ### The bridges to the transcript's models -/

/-- FIPS 202, Algorithm 10 on a whole byte string.

    No hypothesis: `BitStr::from_bytes` is a primitive precisely so that
    `8 * h.len()` is never formed. -/
theorem h2b_full_eq (h : Slice Std.U8) :
    hacspec_sha3_pedantic.bits.h2b_full h = ok (h2bList h.val) := by
  unfold hacspec_sha3_pedantic.bits.h2b_full hacspec_sha3_pedantic.bits.BitStr.from_bytes
  rfl

/-- FIPS 202, Algorithm 11. -/
theorem b2h_eq (s : hacspec_sha3_pedantic.bits.BitStr)
    (hb : (b2hList s).length ≤ Std.Usize.max) :
    hacspec_sha3_pedantic.bits.b2h s = ok ⟨b2hList s, hb⟩ := by
  unfold hacspec_sha3_pedantic.bits.b2h hacspec_sha3_pedantic.bits.BitStr.to_bytes
  refine dif_pos hb

end LibcruxIotSha3.Composition.Pedantic
