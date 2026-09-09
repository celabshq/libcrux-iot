/-
  Bit-interleaved → standard `u64` lifting + the algebraic identities
  used to fold lifted-lane towers in the θ / ρ ∘ π ∘ χ proofs.

  The implementation stores each 64-bit Keccak lane as two 32-bit halves
  in bit-interleaved form:
    z0 holds even-indexed bits, z1 holds odd-indexed bits.

  These definitions reconstruct the standard 64-bit lane and lift the
  full 25-lane state to the spec's `Array Std.U64 25#usize`.

  The impl stores `A[x, y]` at `st[5*x + y]`. The spec stores `A[x, y]`
  at `state[5*y + x]` (FIPS 202 §3.1.2). The bridge therefore transposes
  flat indices via `transpose_perm`, which `lift` and `lift_perm` bake
  in so callers see the canonical "identity" relationship between impl
  storage and the spec view.

  `spread_to_even` and `lift_lane_bv` are marked `@[local irreducible]`
  *in downstream files* (e.g. `ThetaLift.lean`) after this module's
  per-bit algebraic lemmas are in scope; without that
  guard, every later simp pass unfolds them into a six-step parallel
  bit-deposit sequence × 25 lanes, blowing up term sizes by orders of
  magnitude.

  ## Catalog (algebraic lemmas, second half of file)

  - **Rotation table** (`rot_N` for the 25 ρ offsets used by Keccak):
    converts a 64-bit rotation of a lifted lane to two 32-bit rotations
    on the interleaved halves. Even `N` rotates both halves by `N/2`
    without swapping; odd `N` swaps the halves and adjusts.
  - **Bitwise distributivity** (`lift_xor`/`lift_and`/`lift_not`):
    XOR/AND/NOT commute with lifting.
  - **Step-specific composites** (`lift_chi`/`lift_xor5`/`lift_td`/
    `lift_rot1`): the exact patterns that show up in the post-mvcgen
    goals for θ and ρ∘π∘χ.
-/
import LibcruxIotSha3.Extraction.Funs

open Aeneas Aeneas.Std Std.Do

namespace libcrux_iot_sha3.Foundation

/-- The interleaved lane representation has a canonical default
    (both halves zero) — needed for the `_!` accessors used below. -/
instance : Inhabited libcrux_iot_sha3.lane.Lane2U32 :=
  ⟨⟨[0#u32, 0#u32], by decide⟩⟩

/-- Spread 32 bits into the even bit positions of a 64-bit word.
    Bit `i` of the input lands at bit `2*i` of the output. -/
def spread_to_even (x : BitVec 32) : BitVec 64 :=
  let x : BitVec 64 := x.zeroExtend 64
  let x := (x ||| (x <<< 16)) &&& 0x0000ffff0000ffff#64
  let x := (x ||| (x <<<  8)) &&& 0x00ff00ff00ff00ff#64
  let x := (x ||| (x <<<  4)) &&& 0x0f0f0f0f0f0f0f0f#64
  let x := (x ||| (x <<<  2)) &&& 0x3333333333333333#64
  let x := (x ||| (x <<<  1)) &&& 0x5555555555555555#64
  x

/-- Reconstruct a 64-bit lane from interleaved halves: bit `2k` from `z0`,
    bit `2k+1` from `z1`. -/
def lift_lane_bv (z0 z1 : BitVec 32) : BitVec 64 :=
  spread_to_even z0 ||| (spread_to_even z1 <<< 1)

/-- Lift one interleaved `Lane2U32` to a standard `Std.U64`. -/
def lift_lane (l : libcrux_iot_sha3.lane.Lane2U32) : Std.U64 :=
  ⟨lift_lane_bv (l.val[0]!).bv (l.val[1]!).bv⟩


/-! ## Per-bit characterisation of the interleaved lift

`spread_to_even` deposits bit `j` of its 32-bit input at bit `2j`, and
`lift_lane_bv z0 z1` therefore holds `z0` on the even bits and `z1` on the odd
bits. Both facts are proved once, bit by bit (the 64 bit positions are
enumerated and each is a closed Boolean identity for `simp`), and every
algebraic lemma about `lift_lane_bv` below is derived from them with the core
`BitVec.getLsbD_*` lemmas. Nothing here uses `bv_decide`, so the whole
development rests on Lean's three standard axioms only. -/

/-- The 64 bit positions of a `BitVec 64`, for case enumeration. -/
theorem nat_lt_64_cases (i : Nat) (h : i < 64) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21 ∨ i = 22 ∨ i = 23 ∨ i = 24 ∨ i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 ∨ i = 33 ∨ i = 34 ∨ i = 35 ∨ i = 36 ∨ i = 37 ∨ i = 38 ∨ i = 39 ∨ i = 40 ∨ i = 41 ∨ i = 42 ∨ i = 43 ∨ i = 44 ∨ i = 45 ∨ i = 46 ∨ i = 47 ∨ i = 48 ∨ i = 49 ∨ i = 50 ∨ i = 51 ∨ i = 52 ∨ i = 53 ∨ i = 54 ∨ i = 55 ∨ i = 56 ∨ i = 57 ∨ i = 58 ∨ i = 59 ∨ i = 60 ∨ i = 61 ∨ i = 62 ∨ i = 63 := by omega

set_option maxHeartbeats 1000000 in
theorem spread_to_even_getLsbD (x : BitVec 32) (i : Nat) (hi : i < 64) :
    (spread_to_even x).getLsbD i = (decide (i % 2 = 0) && x.getLsbD (i / 2)) := by
  unfold spread_to_even
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.zeroExtend,
    BitVec.getLsbD_setWidth]
  rcases nat_lt_64_cases i hi with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp (config := {decide := true})

theorem lift_lane_bv_getLsbD (z0 z1 : BitVec 32) (i : Nat) (hi : i < 64) :
    (lift_lane_bv z0 z1).getLsbD i
      = if i % 2 = 0 then z0.getLsbD (i / 2) else z1.getLsbD (i / 2) := by
  unfold lift_lane_bv
  rw [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, spread_to_even_getLsbD z0 i hi]
  by_cases he : i % 2 = 0
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0; simp
    · rw [spread_to_even_getLsbD z1 (i - 1) (by omega)]
      have h1 : ¬ (i - 1) % 2 = 0 := by omega
      simp [he, h1]
  · rw [spread_to_even_getLsbD z1 (i - 1) (by omega)]
    have h1 : (i - 1) % 2 = 0 := by omega
    have h2 : (i - 1) / 2 = i / 2 := by omega
    have h3 : ¬ i = 0 := by omega
    simp [he, h1, h2, hi, h3]

/-- Rotation by an even amount `2k` rotates each half by `k`. -/
theorem rot_even (z0 z1 : BitVec 32) (k : Nat) (hk : k < 32) :
    (lift_lane_bv z0 z1).rotateLeft (2 * k) = lift_lane_bv (z0.rotateLeft k) (z1.rotateLeft k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h2k : 2 * k % 64 = 2 * k := Nat.mod_eq_of_lt (by omega)
  have hk32 : k % 32 = k := Nat.mod_eq_of_lt hk
  rw [BitVec.getLsbD_rotateLeft, h2k, lift_lane_bv_getLsbD _ _ i hi]
  simp only [BitVec.getLsbD_rotateLeft, hk32, Bool.cond_eq_ite]
  have hi2 : i / 2 < 32 := by omega
  by_cases hlt : i < 2 * k
  · rw [if_pos (decide_eq_true hlt), lift_lane_bv_getLsbD _ _ _ (by omega)]
    have hp : (64 - 2 * k + i) % 2 = i % 2 := by omega
    have hd : (64 - 2 * k + i) / 2 = 32 - k + i / 2 := by omega
    have hl : i / 2 < k := by omega
    rw [hp, hd]; simp [hl]
  · rw [if_neg (by simp [hlt]), lift_lane_bv_getLsbD _ _ _ (by omega)]
    have hp : (i - 2 * k) % 2 = i % 2 := by omega
    have hd : (i - 2 * k) / 2 = i / 2 - k := by omega
    have hl : ¬ i / 2 < k := by omega
    rw [hp, hd]; simp [hl, hi, hi2]

/-- Rotation by an odd amount `2k+1` swaps the halves: the odd half moves to
    the even positions rotated by `k+1`, the even half to the odd positions
    rotated by `k`. -/
theorem rot_odd (z0 z1 : BitVec 32) (k : Nat) (hk : k < 31) :
    (lift_lane_bv z0 z1).rotateLeft (2 * k + 1)
      = lift_lane_bv (z1.rotateLeft (k + 1)) (z0.rotateLeft k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have h2k : (2 * k + 1) % 64 = 2 * k + 1 := Nat.mod_eq_of_lt (by omega)
  have hk32 : k % 32 = k := Nat.mod_eq_of_lt (by omega)
  have hk32' : (k + 1) % 32 = k + 1 := Nat.mod_eq_of_lt (by omega)
  rw [BitVec.getLsbD_rotateLeft, h2k, lift_lane_bv_getLsbD _ _ i hi]
  simp only [BitVec.getLsbD_rotateLeft, hk32, hk32', Bool.cond_eq_ite]
  have hi2 : i / 2 < 32 := by omega
  by_cases hlt : i < 2 * k + 1
  · rw [if_pos (decide_eq_true hlt), lift_lane_bv_getLsbD _ _ _ (by omega)]
    by_cases he : i % 2 = 0
    · have hd : (64 - (2 * k + 1) + i) / 2 = 32 - (k + 1) + i / 2 := by omega
      have hl : i / 2 < k + 1 := by omega
      rw [hd]; simp [he, hl]; intro h; omega
    · have hd : (64 - (2 * k + 1) + i) / 2 = 32 - k + i / 2 := by omega
      have hl : i / 2 < k := by omega
      rw [hd]; simp [he, hl]; intro h; omega
  · rw [if_neg (by simp [hlt]), lift_lane_bv_getLsbD _ _ _ (by omega)]
    by_cases he : i % 2 = 0
    · have hp : ¬ (i - (2 * k + 1)) % 2 = 0 := by omega
      have hd : (i - (2 * k + 1)) / 2 = i / 2 - (k + 1) := by omega
      have hl : ¬ i / 2 < k + 1 := by omega
      rw [hd]; simp [hp, he, hl, hi, hi2]
    · have hp : (i - (2 * k + 1)) % 2 = 0 := by omega
      have hd : (i - (2 * k + 1)) / 2 = i / 2 - k := by omega
      have hl : ¬ i / 2 < k := by omega
      rw [hd]; simp [hp, he, hl, hi, hi2]

/-- Spec-index ↔ impl-index transpose: `transpose_perm (5*y + x) = 5*x + y`.

    The impl stores `A[x, y]` at impl index `5*x + y`; the spec stores it at
    spec index `5*y + x`. So spec position `i = 5*y + x` corresponds to impl
    position `5*x + y = transpose_perm i`. Involution: `transpose_perm ∘
    transpose_perm = id`. -/
def transpose_perm (i : Fin 25) : Fin 25 :=
  ⟨5 * (i.val % 5) + i.val / 5, by omega⟩

/-- Lift the full 25-lane Keccak state from interleaved to standard form,
    routing through the spec↔impl transpose:
    `(lift s).val[i]! = lift_lane (s.st.val[transpose_perm i]!)`. -/
def lift (s : libcrux_iot_sha3.state.KeccakState) : Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 => lift_lane (s.st.val[(transpose_perm i).val]!)),
    by simp⟩

/-! ## 32-bit rotation abbreviation used in the interleaved implementation -/

abbrev rot32 (x : Std.U32) (n : Nat) : Std.U32 :=
  ⟨x.bv.rotateLeft n⟩

/-! ## The permutation that the impl applies implicitly through addressing.

    The implementation performs π as a *storage relabeling*: each round
    reads from different physical positions, so after one round the
    canonical `st[5*x + y] ↔ A[x, y]` mapping no longer holds. The
    cycle has order 4 — every 4 rounds the lane layout re-aligns with
    the spec.
-/

/-- The lane permutation induced by one round of the implementation.
    Maps a spec cell index to the impl lane that now holds it:
    `impl_perm(5*x + z) = 5*x + ((2*z + x) mod 5)`. -/
def impl_perm (i : Fin 25) : Fin 25 :=
  let x := i.val / 5
  let z := i.val % 5
  ⟨5 * x + (2 * z + x) % 5, by omega⟩

/-- The impl permutation has order 4: after 4 rounds, layout re-aligns
    with the spec's `[u64; 25]` ordering. Closed by `decide` over the 25
    indices. -/
theorem impl_perm_pow4_eq_id :
    ∀ i : Fin 25, impl_perm (impl_perm (impl_perm (impl_perm i))) = i := by
  decide

/-- Per-impl-lane half-swap flag for the round-0 storage layout.
    `impl_swap L = true` iff impl lane `L` stores its U64 with halves
    physically reversed (i.e., `val[0]` holds spec `z1` and `val[1]` holds
    spec `z0`). Formula: `parity (rho_table[L/5][L%5])` — the
    bit-interleaved impl pre-aligns each lane's polarity to match the
    rho rotation that the NEXT round will apply to that physical
    position, avoiding explicit half-swaps during chi. -/
def impl_swap (i : Fin 25) : Bool :=
  match i.val with
  | 2 | 3 | 5 | 8 | 12 | 13 | 14 | 16 | 17 | 18 | 20 | 22 => true
  | _ => false

/-- Time-varying polarity layout. After round `k`, the impl-side lane at
    impl-pos `L` stores its halves swapped (relative to canonical) iff
    `impl_swap_k k L = true`. Cycle of length 4 — `impl_swap_k 4 =
    impl_swap_k 0 = (fun _ => false)`.

    Per-round identities

    `spec_round_step (lift_perm s.toAeneas (impl_perm^[k]) (impl_swap_k k)) s.i`
    `  = .ok (lift_perm (bit_round{k} s).toAeneas (impl_perm^[k+1]) (impl_swap_k (k+1)))`

    hold **unconditionally** (no `BalancedAt`-style precondition) for this
    cycle. The four `bit_round{k}` ops absorb the polarity changes into
    the impl's actual half-storage; the `impl_swap_k k` function tracks
    which impl-positions are swapped at round `k` so the canonical lift
    recovers the spec U64.

    The 4-round cycle starts and ends with `swZero` (no swap), so the
    canonical `lift s = lift_perm s id (fun _ => false)` view threads
    cleanly through the 24-round chain. -/
@[irreducible] def impl_swap_k (k : Nat) (L : Fin 25) : Bool :=
  match k % 4 with
  | 0 => false
  | 1 => impl_swap L
  | 2 => decide (L.val ∉ ([0, 9, 13, 17, 21] : List Nat))
  | _ => decide (L.val ∈ ([1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24] : List Nat))

theorem impl_swap_k_zero (L : Fin 25) : impl_swap_k 0 L = false := by
  unfold impl_swap_k; rfl

theorem impl_swap_k_four (L : Fin 25) : impl_swap_k 4 L = impl_swap_k 0 L := by
  unfold impl_swap_k; rfl

theorem impl_swap_k_one (L : Fin 25) : impl_swap_k 1 L = impl_swap L := by
  unfold impl_swap_k; rfl

/-- `impl_swap_k 2 L = decide (L.val ∉ [0, 9, 13, 17, 21])`. Shared
    across `PrcLiftRound2` + downstream round-2 spec files. -/
theorem impl_swap_k_two (L : Fin 25) :
    impl_swap_k 2 L =
      decide (L.val ∉ ([0, 9, 13, 17, 21] : List Nat)) := by
  unfold impl_swap_k; rfl

/-- `impl_swap_k 3 L = decide (L.val ∈ [1,4,6,7,10,11,13,15,17,19,23,24])`.
    Shared across `PrcLiftRound3` + downstream round-3 spec files. -/
theorem impl_swap_k_three (L : Fin 25) :
    impl_swap_k 3 L =
      decide (L.val ∈ ([1, 4, 6, 7, 10, 11, 13, 15, 17, 19, 23, 24] : List Nat)) := by
  unfold impl_swap_k; rfl

/-- Lift a single lane to U64, optionally swapping halves. -/
def lift_lane_maybe_swap (l : libcrux_iot_sha3.lane.Lane2U32) (sw : Bool) :
    Std.U64 :=
  if sw then ⟨lift_lane_bv (l.val[1]!).bv (l.val[0]!).bv⟩
  else lift_lane l

/-- Lift a permuted state: composes `p` after the spec↔impl transpose, then
    reads the impl state at the resulting impl index (optionally swapping
    halves per `sw`). `p` is a permutation of impl indices. -/
def lift_perm (s : libcrux_iot_sha3.state.KeccakState) (p : Fin 25 → Fin 25)
    (sw : Fin 25 → Bool) :
    Array Std.U64 25#usize :=
  ⟨List.ofFn (fun i : Fin 25 =>
      lift_lane_maybe_swap (s.st.val[(p (transpose_perm i)).val]!)
                           (sw (p (transpose_perm i)))),
    by simp⟩

/-- `lift_perm s id (fun _ => false) = lift s`. Both bake in the transpose. -/
theorem lift_perm_id (s : libcrux_iot_sha3.state.KeccakState) :
    lift_perm s id (fun _ => false) = lift s := by
  unfold lift_perm lift lift_lane_maybe_swap
  rfl

/-! ## Generic `lift_perm` / `lift_lane_maybe_swap` helpers

These four lemmas appear textually-identical across all three
`ThetaLiftRound{1,2,3}` files; hoisted here so each round file
just references the shared copy. -/

/-- `lift_perm` lane indexing: read the k-th lane of a permuted state.
    Note: the permutation `p` is composed with
    `transpose_perm`. -/
theorem lift_perm_getElem (s : libcrux_iot_sha3.state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    (lift_perm s p sw).val[k.val]! =
      lift_lane_maybe_swap (s.st.val[(p (transpose_perm k)).val]!)
                           (sw (p (transpose_perm k))) := by
  unfold lift_perm
  change (List.ofFn _)[k.val]! = _
  rw [getElem!_pos _ k.val (by simp), List.getElem_ofFn]

/-- BV variant of `lift_perm_getElem`. -/
theorem lift_perm_getElem_bv_aux (s : libcrux_iot_sha3.state.KeccakState)
    (p : Fin 25 → Fin 25) (sw : Fin 25 → Bool) (k : Fin 25) :
    ((↑(lift_perm s p sw) : List Std.U64)[(k.val : Nat)]!).bv =
      (lift_lane_maybe_swap (s.st.val[(p (transpose_perm k)).val]!)
                            (sw (p (transpose_perm k)))).bv := by
  show ((lift_perm s p sw).val[k.val]!).bv = _
  rw [lift_perm_getElem]

/-- `lift_lane_maybe_swap` on the `true` branch. -/
theorem lift_lane_maybe_swap_true_bv (l : libcrux_iot_sha3.lane.Lane2U32) :
    (lift_lane_maybe_swap l true).bv =
      lift_lane_bv (l.val[1]!).bv (l.val[0]!).bv := by
  unfold lift_lane_maybe_swap; rfl

/-- `lift_lane_maybe_swap` on the `false` branch. -/
theorem lift_lane_maybe_swap_false_bv (l : libcrux_iot_sha3.lane.Lane2U32) :
    (lift_lane_maybe_swap l false).bv =
      lift_lane_bv (l.val[0]!).bv (l.val[1]!).bv := by
  unfold lift_lane_maybe_swap lift_lane; rfl

/-! ## Algebraic lemmas about `lift_lane_bv`

Every lemma below is a pure BitVec identity, derived from the per-bit
characterisation `lift_lane_bv_getLsbD` above (the rotation lemmas are the
instances `rot_even`/`rot_odd` of the two generic rotation facts). -/

/-! ### Rotation lifting: even offsets

For even `N`, a 64-bit rotation of a lifted lane equals lifting each
32-bit half rotated by `N/2`. -/

theorem rot_0 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 0 = lift_lane_bv (z0.rotateLeft 0) (z1.rotateLeft 0) := by
  exact rot_even z0 z1 0 (by omega)
theorem rot_2 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 2 = lift_lane_bv (z0.rotateLeft 1) (z1.rotateLeft 1) := by
  exact rot_even z0 z1 1 (by omega)
theorem rot_6 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 6 = lift_lane_bv (z0.rotateLeft 3) (z1.rotateLeft 3) := by
  exact rot_even z0 z1 3 (by omega)
theorem rot_8 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 8 = lift_lane_bv (z0.rotateLeft 4) (z1.rotateLeft 4) := by
  exact rot_even z0 z1 4 (by omega)
theorem rot_10 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 10 = lift_lane_bv (z0.rotateLeft 5) (z1.rotateLeft 5) := by
  exact rot_even z0 z1 5 (by omega)
theorem rot_14 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 14 = lift_lane_bv (z0.rotateLeft 7) (z1.rotateLeft 7) := by
  exact rot_even z0 z1 7 (by omega)
theorem rot_18 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 18 = lift_lane_bv (z0.rotateLeft 9) (z1.rotateLeft 9) := by
  exact rot_even z0 z1 9 (by omega)
theorem rot_20 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 20 = lift_lane_bv (z0.rotateLeft 10) (z1.rotateLeft 10) := by
  exact rot_even z0 z1 10 (by omega)
theorem rot_28 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 28 = lift_lane_bv (z0.rotateLeft 14) (z1.rotateLeft 14) := by
  exact rot_even z0 z1 14 (by omega)
theorem rot_36 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 36 = lift_lane_bv (z0.rotateLeft 18) (z1.rotateLeft 18) := by
  exact rot_even z0 z1 18 (by omega)
theorem rot_44 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 44 = lift_lane_bv (z0.rotateLeft 22) (z1.rotateLeft 22) := by
  exact rot_even z0 z1 22 (by omega)
theorem rot_56 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 56 = lift_lane_bv (z0.rotateLeft 28) (z1.rotateLeft 28) := by
  exact rot_even z0 z1 28 (by omega)
theorem rot_62 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 62 = lift_lane_bv (z0.rotateLeft 31) (z1.rotateLeft 31) := by
  exact rot_even z0 z1 31 (by omega)

/-! ### Rotation lifting: odd offsets

For odd `N`, the halves swap. `z0` is taken from `z1.rotateLeft ((N+1)/2)`
and `z1` is taken from `z0.rotateLeft (N/2)`. -/

theorem rot_1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) (z0.rotateLeft 0) := by
  exact rot_odd z0 z1 0 (by omega)
theorem rot_3 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 3 = lift_lane_bv (z1.rotateLeft 2) (z0.rotateLeft 1) := by
  exact rot_odd z0 z1 1 (by omega)
theorem rot_15 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 15 = lift_lane_bv (z1.rotateLeft 8) (z0.rotateLeft 7) := by
  exact rot_odd z0 z1 7 (by omega)
theorem rot_21 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 21 = lift_lane_bv (z1.rotateLeft 11) (z0.rotateLeft 10) := by
  exact rot_odd z0 z1 10 (by omega)
theorem rot_25 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 25 = lift_lane_bv (z1.rotateLeft 13) (z0.rotateLeft 12) := by
  exact rot_odd z0 z1 12 (by omega)
theorem rot_27 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 27 = lift_lane_bv (z1.rotateLeft 14) (z0.rotateLeft 13) := by
  exact rot_odd z0 z1 13 (by omega)
theorem rot_39 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 39 = lift_lane_bv (z1.rotateLeft 20) (z0.rotateLeft 19) := by
  exact rot_odd z0 z1 19 (by omega)
theorem rot_41 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 41 = lift_lane_bv (z1.rotateLeft 21) (z0.rotateLeft 20) := by
  exact rot_odd z0 z1 20 (by omega)
theorem rot_43 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 43 = lift_lane_bv (z1.rotateLeft 22) (z0.rotateLeft 21) := by
  exact rot_odd z0 z1 21 (by omega)
theorem rot_45 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 45 = lift_lane_bv (z1.rotateLeft 23) (z0.rotateLeft 22) := by
  exact rot_odd z0 z1 22 (by omega)
theorem rot_55 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 55 = lift_lane_bv (z1.rotateLeft 28) (z0.rotateLeft 27) := by
  exact rot_odd z0 z1 27 (by omega)
theorem rot_61 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 61 = lift_lane_bv (z1.rotateLeft 31) (z0.rotateLeft 30) := by
  exact rot_odd z0 z1 30 (by omega)

/-! ### Bitwise distributivity over lifting -/

@[agrind =, grind =]
theorem lift_xor (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0) (a1 ^^^ b1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_xor, lift_lane_bv_getLsbD _ _ i hi, lift_lane_bv_getLsbD _ _ i hi,
    lift_lane_bv_getLsbD _ _ i hi]
  split <;> simp [BitVec.getLsbD_xor]

@[agrind =, grind =]
theorem lift_and (a0 a1 b0 b1 : BitVec 32) :
    lift_lane_bv (a0 &&& b0) (a1 &&& b1) = lift_lane_bv a0 a1 &&& lift_lane_bv b0 b1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  rw [BitVec.getLsbD_and, lift_lane_bv_getLsbD _ _ i hi, lift_lane_bv_getLsbD _ _ i hi,
    lift_lane_bv_getLsbD _ _ i hi]
  split <;> simp [BitVec.getLsbD_and]

@[agrind =, grind =]
theorem lift_not (a0 a1 : BitVec 32) :
    lift_lane_bv (~~~a0) (~~~a1) = ~~~(lift_lane_bv a0 a1) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi2 : i / 2 < 32 := by omega
  rw [BitVec.getLsbD_not, lift_lane_bv_getLsbD _ _ i hi, lift_lane_bv_getLsbD _ _ i hi]
  split <;> simp [hi, hi2]

/-! ### Step-specific composites -/

/-- χ step lifting: `a ⊕ (¬b ∧ c)` distributes through interleaved
    representation. -/
theorem lift_chi (bx0_z0 bx0_z1 bx1_z0 bx1_z1 bx2_z0 bx2_z1 : BitVec 32) :
    lift_lane_bv (bx0_z0 ^^^ ((~~~bx1_z0) &&& bx2_z0))
                 (bx0_z1 ^^^ ((~~~bx1_z1) &&& bx2_z1)) =
    lift_lane_bv bx0_z0 bx0_z1 ^^^
      ((~~~(lift_lane_bv bx1_z0 bx1_z1)) &&& lift_lane_bv bx2_z0 bx2_z1) := by
  simp only [lift_xor, lift_not, lift_and]

/-- θ-apply lifting: XOR with a `d`-value distributes through lifting. -/
theorem lift_theta_apply (a0 a1 d0 d1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ d0) (a1 ^^^ d1) = lift_lane_bv a0 a1 ^^^ lift_lane_bv d0 d1 := by
  simp only [lift_xor]

/-- Single odd-1 rotation: halves swap with adjusted sub-rotations.
    `rotateLeft(lift(z0,z1), 1) = lift(rot(z1,1), z0)` (the `k = 0` instance of
    `rot_odd`, with `rotateLeft 0` removed). -/
@[agrind =, grind =]
theorem lift_rot1 (z0 z1 : BitVec 32) :
    (lift_lane_bv z0 z1).rotateLeft 1 = lift_lane_bv (z1.rotateLeft 1) z0 := by
  have h := rot_odd z0 z1 0 (by omega)
  have h0 : z0.rotateLeft 0 = z0 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
  simpa [h0] using h

/-- θ-d structure: the interleaved θ-d computation lifts correctly.
    `lift(cL ⊕ rot(cR,1), cL' ⊕ cR') = lift(cL,cL') ⊕ rotateLeft(lift(cR,cR'),1)`. -/
@[agrind =, grind =]
theorem lift_td (cL0 cL1 cR0 cR1 : BitVec 32) :
    lift_lane_bv (cL0 ^^^ cR1.rotateLeft 1) (cL1 ^^^ cR0) =
    lift_lane_bv cL0 cL1 ^^^ (lift_lane_bv cR0 cR1).rotateLeft 1 := by
  rw [lift_xor, lift_rot1]

/-- XOR of 5 lanes distributes through interleaved lifting. Used for the
    C-row computation in θ. -/
@[agrind =, grind =]
theorem lift_xor5 (a0 a1 b0 b1 c0 c1 d0 d1 e0 e1 : BitVec 32) :
    lift_lane_bv (a0 ^^^ b0 ^^^ c0 ^^^ d0 ^^^ e0)
                 (a1 ^^^ b1 ^^^ c1 ^^^ d1 ^^^ e1) =
    lift_lane_bv a0 a1 ^^^ lift_lane_bv b0 b1 ^^^ lift_lane_bv c0 c1 ^^^
      lift_lane_bv d0 d1 ^^^ lift_lane_bv e0 e1 := by
  simp only [lift_xor]

/-- `BitVec.rotateLeft 1` distributes over XOR (BV-32 version). Needed to
    flatten `(a ^^^ b).rotateLeft 1` into `a.rotateLeft 1 ^^^ b.rotateLeft 1`
    so that `ac_rfl` can solve XOR-AC equalities involving rotated
    column-XOR chains. Shared across `ThetaLiftRound{1,2,3}`. -/
theorem rotateLeft1_xor_bv32 (a b : BitVec 32) :
    (a ^^^ b).rotateLeft 1 = a.rotateLeft 1 ^^^ b.rotateLeft 1 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateLeft, BitVec.getLsbD_xor, Bool.cond_eq_ite]
  split <;> (by_cases h32 : i < 32 <;> simp [h32])

/-! ## `Usize`-bv constant normalisation -/

/-- Normalisation bridge: `↑(BitVec.ofNat numBits k)#uscalar = k` when k is
    in bounds. The shape is what `hax_mvcgen` leaves behind when applying
    `createi_pure_spec`'s `hpure` over `inst.FnMutInst.call_mut c ⟨BitVec.ofNat _ k⟩`. -/
theorem usize_bv_ofNat_val (k : Nat) (h : k < 2^Std.UScalarTy.Usize.numBits) :
    Std.UScalar.val (Std.UScalar.mk (BitVec.ofNat Std.UScalarTy.Usize.numBits k)) = k := by
  show (BitVec.ofNat _ k).toNat = k
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- From a Triple with trivial pre, success post, and value-equality post,
    derive the underlying `RustM` equation `x = .ok v`. Useful to close
    `keccak_f.X state = .ok (X_applied state)` after `hax_mvcgen` has
    produced the corresponding Triple. -/
theorem result_eq_of_triple {α : Type} {x : Std.RustM α} {v : α}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ r = v ⌝ ⦄) : x = .ok v := by
  match hx : x, h with
  | .ok v', h =>
      have hv' : v' = v := by simpa [Triple, WP.wp, PredTrans.apply] using h
      rw [hv']
  | .fail e, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])
  | .div, h => exact absurd h (by simp [Triple, WP.wp, PredTrans.apply])

end libcrux_iot_sha3.Foundation
