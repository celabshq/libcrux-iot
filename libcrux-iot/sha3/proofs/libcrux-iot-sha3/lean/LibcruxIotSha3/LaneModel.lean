import Aeneas
import LibcruxIotSha3.Tables
/-!
# `Keccak-f[1600]` on 25 lanes

The lane model: the Keccak state as twenty-five `u64` lanes, `A[x, y]` at index
`5y + x` (FIPS 202, Sec. 3.1.2), and the five step mappings on it.  These are
ordinary total Lean functions -- no `RustM`, no loops -- so they can be unfolded
freely, which is what makes them usable as the common midpoint of the two proof
halves:

  * `Foundation/` and `Sponge/` show the **implementation** computes them
    (the state is a packed bit-interleaved `KeccakState`, so the work there is
    in the interleaving, not in the step mappings themselves);
  * `Composition/Pedantic/` shows they are the **specification**, by reading
    each lane bit by bit and matching FIPS 202's Algorithms 1-5 as transcribed
    in `hacspec_sha3_pedantic`.

Nothing here is trusted: every definition below is justified by the bit-level
theorems in `Composition/Pedantic/Lanes.lean` (`theta_bit`, `rho_bit`, ...),
which pin them to the transcript.
-/

open Aeneas Aeneas.Std

namespace LibcruxIotSha3.LaneModel

/-- The Keccak state as 25 lanes, `A[x, y]` at index `5*y + x`. -/
abbrev Lanes : Type := Std.Array Std.U64 25#usize

/-- Bit `z` of the lane `A[x, y]`, i.e. FIPS 202's `A[x, y, z]`. -/
def laneBit (s : Lanes) (x y z : Nat) : Bool := (s.val[5 * y + x]!).bv.getLsbD z

/-! ### Building a lane array -/

/-- The array whose element `i` is `g i`. -/
def mkArr {T : Type} (N : Std.Usize) (g : Nat → T) : Std.Array T N :=
  ⟨(List.range N.val).map g, by simp⟩

theorem mkArr_get {T : Type} [Inhabited T] (N : Std.Usize) (g : Nat → T) {i : Nat}
    (hi : i < N.val) : (mkArr N g).val[i]! = g i := by
  show ((List.range N.val).map g)[i]! = g i
  rw [getElem!_pos _ i (by simp; omega)]
  simp

theorem laneBit_mkArr (g : Nat → Std.U64) {x y z : Nat} (hx : x < 5) (hy : y < 5) :
    laneBit (mkArr 25#usize g) x y z = (g (5 * y + x)).bv.getLsbD z := by
  rw [laneBit, mkArr_get 25#usize g (by simp; omega)]

/-! ### Bit-level arithmetic on lanes -/

theorem u64_xor_bit (a b : Std.U64) (z : Nat) :
    (a ^^^ b).bv.getLsbD z = (a.bv.getLsbD z ^^ b.bv.getLsbD z) := by
  show (a.bv ^^^ b.bv).getLsbD z = _
  simp

theorem u64_and_bit (a b : Std.U64) (z : Nat) :
    (a &&& b).bv.getLsbD z = (a.bv.getLsbD z && b.bv.getLsbD z) := by
  show (a.bv &&& b.bv).getLsbD z = _
  simp

theorem u64_not_bit (a : Std.U64) (z : Nat) (hz : z < 64) :
    (~~~ a).bv.getLsbD z = !a.bv.getLsbD z := by
  show (~~~ a.bv).getLsbD z = _
  simp [hz]

/-! ### The five step mappings -/

/-- θ's `C[x]` (FIPS 202, Algorithm 1 step 1). -/
def cLane (s : Lanes) (x : Nat) : Std.U64 :=
  (((s.val[5 * 0 + x]! ^^^ s.val[5 * 1 + x]!) ^^^ s.val[5 * 2 + x]!) ^^^ s.val[5 * 3 + x]!)
    ^^^ s.val[5 * 4 + x]!

/-- θ's `D[x]` (step 2). -/
def dLane (c : Std.Array Std.U64 5#usize) (x : Nat) : Std.U64 :=
  c.val[(x + 4) % 5]! ^^^ Std.UScalar.rotate_left c.val[(x + 1) % 5]! 1#u32

/-- θ on lanes (step 3). -/
def thetaLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t => s.val[t]! ^^^ (mkArr 5#usize (dLane (mkArr 5#usize (cLane s)))).val[t % 5]!)

/-- ρ on lanes: rotate each lane by its tabulated offset. -/
def rhoLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t =>
    Std.UScalar.rotate_left s.val[t]! libcrux_iot_sha3.rhoOffsets.val[t]!)

/-- π on lanes: lane `(x, y)` takes the old lane `((x + 3y) mod 5, x)`. -/
def piLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t => s.val[5 * (t % 5) + ((t % 5 + 3 * (t / 5)) % 5)]!)

/-- χ on lanes (FIPS 202, Algorithm 4). -/
def chiLanes (s : Lanes) : Lanes :=
  mkArr 25#usize (fun t =>
    s.val[5 * (t / 5) + t % 5]! ^^^
      ((~~~ s.val[5 * (t / 5) + (t % 5 + 1) % 5]!) &&&
        s.val[5 * (t / 5) + (t % 5 + 2) % 5]!))

/-- ι on lanes: XOR round constant `r` into lane `(0, 0)`. -/
def iotaLanes (s : Lanes) (r : Nat) : Lanes :=
  s.set 0#usize (s.val[0]! ^^^ libcrux_iot_sha3.roundConstants.val[r]!)

/-! ### One round, and the 24-round permutation -/

/-- Round `r` of `Keccak-f[1600]` on lanes. -/
def roundLanes (s : Lanes) (r : Nat) : Lanes :=
  iotaLanes (chiLanes (piLanes (rhoLanes (thetaLanes s)))) r

/-- Rounds `0 … n-1`, in order.  Mirrors the transcript's `roundsFrom` (which
    does the same at the bit level), so the two induct in step. -/
def roundsUpTo (s : Lanes) : Nat → Lanes
  | 0 => s
  | n + 1 => roundLanes (roundsUpTo s n) n

/-- `Keccak-f[1600]`: all twenty-four rounds. -/
def keccakFLanes (s : Lanes) : Lanes := roundsUpTo s 24

/-! ### The lane state as a flat bit string -/

/-- Bit `p` of the state read as a flat 1600-bit string: FIPS 202's
    `S[w(5y + x) + z] = A[x, y, z]` solved for `(x, y, z)`. -/
def laneBitAt (s : Lanes) (p : Nat) : Bool :=
  laneBit s ((p / 64) % 5) (p / 320) (p % 64)

/-- The 1600 bits of a 25-lane state, in the FIPS order `S[64(5y + x) + z]`. -/
def lanesToBits (s : Lanes) : List Bool :=
  (List.range 1600).map (laneBitAt s)

@[simp]
theorem lanesToBits_len (s : Lanes) : (lanesToBits s).length = 1600 := by
  simp [lanesToBits]

end LibcruxIotSha3.LaneModel
