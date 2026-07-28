/-
  Pure-Lean intermediate spec for the Keccak `keccakf1600` impl.

  Mirrors the Aeneas-extracted `keccak.keccakf1600_*` sub-functions
  line-by-line, but as plain `BitVec 32` arithmetic on the pure-Lean
  `KState` record (no `Result` monad, no `Aeneas.Std.UScalar`, no
  `Lane2U32` wrappers).

  This is the impl side of the algebraic equivalence's domain — the
  structural-equivalence equivalence (`StructuralEquiv.lean`) proves
  `keccakf1600_round*_*` ≡ the corresponding `bit_*` definition here
  via `hax_mvcgen`.
-/
import LibcruxIotSha3.BitSpec.State
import LibcruxIotSha3.Extraction.Funs

namespace libcrux_iot_sha3.BitSpec

open Aeneas Aeneas.Std libcrux_iot_sha3

/-! ## Pure-Lean primitive helpers on `KState`

    Each mirrors an Aeneas method on `state.KeccakState`. -/

/-- Read lane at index `(5*j + i)`, half `zeta`. Mirrors
    `state.KeccakState.get_with_zeta`. Returns 0 on out-of-range. -/
@[inline] def KState.getWithZeta (s : KState) (i j zeta : Nat) : BitVec 32 :=
  let idx := 5 * j + i
  let lane := s.st.toList[idx]?.getD Lane.zero
  if zeta = 0 then lane.z0 else lane.z1

/-- Read `s.d[col]!.val[zeta]!`. Mirrors the impl's d-cell read pattern. -/
@[inline] def KState.getDCell (s : KState) (col zeta : Nat) : BitVec 32 :=
  let lane := s.d.toList[col]?.getD Lane.zero
  if zeta = 0 then lane.z0 else lane.z1

/-- Write `v` into lane at index `(5*j + i)`, half `zeta`. Mirrors
    `state.KeccakState.set_with_zeta`. No-op if `(5*j + i) ≥ 25`. -/
@[inline] def KState.setWithZeta (s : KState) (i j zeta : Nat) (v : BitVec 32) : KState :=
  let idx := 5 * j + i
  if h : idx < 25 then
    let old := s.st[idx]
    let newLane : Lane := if zeta = 0 then { old with z0 := v } else { old with z1 := v }
    { s with st := s.st.set idx newLane h }
  else s

/-! ## `bit_pi_rho_chi_y0_zeta0` — rosetta-stone sub-fn

    Pure-Lean mirror of
    `keccak.keccakf1600_round0_pi_rho_chi_y0_zeta0` (Funs.lean:3417).

    Lane reads: (i=0,j=0,ζ=0)→idx0/h0, (1,1,0)→idx6/h0, (2,2,1)→idx12/h1,
                (3,3,1)→idx18/h1, (4,4,0)→idx24/h0.
    D-cell reads: d[0][0], d[1][0], d[2][1], d[3][1], d[4][0].
    Rotation amounts: 0, 22, 22, 11, 7.
    Iota: RC_INTERLEAVED_0[s.i] XORed into ax0 only.
    Writes (same lanes/halves as reads):
      lane 0/h0 := bx0 ⊕ (¬bx1 ∧ bx2) ⊕ RC_INTERLEAVED_0[s.i]
      lane 6/h0 := bx1 ⊕ (¬bx2 ∧ bx3)
      lane 12/h1 := bx2 ⊕ (¬bx3 ∧ bx4)
      lane 18/h1 := bx3 ⊕ (¬bx4 ∧ bx0)
      lane 24/h0 := bx4 ⊕ (¬bx0 ∧ bx1)
    No `s.i` increment (only `_y0_zeta1` increments `s.i`). -/
def bit_pi_rho_chi_y0_zeta0 (_BR : Std.Usize) (s : KState) : KState :=
  let a0 := s.st[0].z0
  let d0 := s.d[0].z0
  let a1 := s.st[6].z0
  let d1 := s.d[1].z0
  let a2 := s.st[12].z1
  let d2 := s.d[2].z1
  let a3 := s.st[18].z1
  let d3 := s.d[3].z1
  let a4 := s.st[24].z0
  let d4 := s.d[4].z0
  let bx0 := (a0 ^^^ d0).rotateLeft 0
  let bx1 := (a1 ^^^ d1).rotateLeft 22
  let bx2 := (a2 ^^^ d2).rotateLeft 22
  let bx3 := (a3 ^^^ d3).rotateLeft 11
  let bx4 := (a4 ^^^ d4).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_0.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨ax0, s.st[0].z1⟩
  let new6  : Lane := ⟨ax1, s.st[6].z1⟩
  let new12 : Lane := ⟨s.st[12].z0, ax2⟩
  let new18 : Lane := ⟨s.st[18].z0, ax3⟩
  let new24 : Lane := ⟨ax4, s.st[24].z1⟩
  let st' := s.st.set 0 new0 |>.set 6 new6 |>.set 12 new12 |>.set 18 new18 |>.set 24 new24
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y0_zeta1` — RC_INTERLEAVED_1, INCREMENTS `s.i` -/
def bit_pi_rho_chi_y0_zeta1 (_BR : Std.Usize) (s : KState) : KState :=
  let a0 := s.st[0].z1
  let d0 := s.d[0].z1
  let a1 := s.st[6].z1
  let d1 := s.d[1].z1
  let a2 := s.st[12].z0
  let d2 := s.d[2].z0
  let a3 := s.st[18].z0
  let d3 := s.d[3].z0
  let a4 := s.st[24].z1
  let d4 := s.d[4].z1
  let bx0 := (a0 ^^^ d0).rotateLeft 0
  let bx1 := (a1 ^^^ d1).rotateLeft 22
  let bx2 := (a2 ^^^ d2).rotateLeft 21
  let bx3 := (a3 ^^^ d3).rotateLeft 10
  let bx4 := (a4 ^^^ d4).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_1.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨s.st[0].z0, ax0⟩
  let new6  : Lane := ⟨s.st[6].z0, ax1⟩
  let new12 : Lane := ⟨ax2, s.st[12].z1⟩
  let new18 : Lane := ⟨ax3, s.st[18].z1⟩
  let new24 : Lane := ⟨s.st[24].z0, ax4⟩
  let st' := s.st.set 0 new0 |>.set 6 new6 |>.set 12 new12 |>.set 18 new18 |>.set 24 new24
  { s with st := st', i := ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ }

/-! ## `bit_pi_rho_chi_y1_zeta0` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y1_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[15].z0 ^^^ s.d[3].z0).rotateLeft 14
  let bx1 := (s.st[21].z0 ^^^ s.d[4].z0).rotateLeft 10
  let bx2 := (s.st[2].z1  ^^^ s.d[0].z1).rotateLeft 2
  let bx3 := (s.st[8].z1  ^^^ s.d[1].z1).rotateLeft 23
  let bx4 := (s.st[14].z1 ^^^ s.d[2].z1).rotateLeft 31
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨s.st[2].z0,  ax0⟩
  let new8  : Lane := ⟨s.st[8].z0,  ax1⟩
  let new14 : Lane := ⟨s.st[14].z0, ax2⟩
  let new15 : Lane := ⟨ax3, s.st[15].z1⟩
  let new21 : Lane := ⟨ax4, s.st[21].z1⟩
  let st' := s.st.set 2 new2 |>.set 8 new8 |>.set 14 new14 |>.set 15 new15 |>.set 21 new21
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y1_zeta1` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y1_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[15].z1 ^^^ s.d[3].z1).rotateLeft 14
  let bx1 := (s.st[21].z1 ^^^ s.d[4].z1).rotateLeft 10
  let bx2 := (s.st[2].z0  ^^^ s.d[0].z0).rotateLeft 1
  let bx3 := (s.st[8].z0  ^^^ s.d[1].z0).rotateLeft 22
  let bx4 := (s.st[14].z0 ^^^ s.d[2].z0).rotateLeft 30
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨ax0, s.st[2].z1⟩
  let new8  : Lane := ⟨ax1, s.st[8].z1⟩
  let new14 : Lane := ⟨ax2, s.st[14].z1⟩
  let new15 : Lane := ⟨s.st[15].z0, ax3⟩
  let new21 : Lane := ⟨s.st[21].z0, ax4⟩
  let st' := s.st.set 2 new2 |>.set 8 new8 |>.set 14 new14 |>.set 15 new15 |>.set 21 new21
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y2_zeta0` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y2_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[5].z1  ^^^ s.d[1].z1).rotateLeft 1
  let bx1 := (s.st[11].z0 ^^^ s.d[2].z0).rotateLeft 3
  let bx2 := (s.st[17].z1 ^^^ s.d[3].z1).rotateLeft 13
  let bx3 := (s.st[23].z0 ^^^ s.d[4].z0).rotateLeft 4
  let bx4 := (s.st[4].z0  ^^^ s.d[0].z0).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨ax0, s.st[4].z1⟩
  let new5  : Lane := ⟨s.st[5].z0,  ax1⟩
  let new11 : Lane := ⟨ax2, s.st[11].z1⟩
  let new17 : Lane := ⟨s.st[17].z0, ax3⟩
  let new23 : Lane := ⟨ax4, s.st[23].z1⟩
  let st' := s.st.set 4 new4 |>.set 5 new5 |>.set 11 new11 |>.set 17 new17 |>.set 23 new23
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y2_zeta1` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y2_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[5].z0  ^^^ s.d[1].z0).rotateLeft 0
  let bx1 := (s.st[11].z1 ^^^ s.d[2].z1).rotateLeft 3
  let bx2 := (s.st[17].z0 ^^^ s.d[3].z0).rotateLeft 12
  let bx3 := (s.st[23].z1 ^^^ s.d[4].z1).rotateLeft 4
  let bx4 := (s.st[4].z1  ^^^ s.d[0].z1).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨s.st[4].z0,  ax0⟩
  let new5  : Lane := ⟨ax1, s.st[5].z1⟩
  let new11 : Lane := ⟨s.st[11].z0, ax2⟩
  let new17 : Lane := ⟨ax3, s.st[17].z1⟩
  let new23 : Lane := ⟨s.st[23].z0, ax4⟩
  let st' := s.st.set 4 new4 |>.set 5 new5 |>.set 11 new11 |>.set 17 new17 |>.set 23 new23
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y3_zeta0` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y3_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[20].z1 ^^^ s.d[4].z1).rotateLeft 14
  let bx1 := (s.st[1].z0  ^^^ s.d[0].z0).rotateLeft 18
  let bx2 := (s.st[7].z0  ^^^ s.d[1].z0).rotateLeft 5
  let bx3 := (s.st[13].z1 ^^^ s.d[2].z1).rotateLeft 8
  let bx4 := (s.st[19].z0 ^^^ s.d[3].z0).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨ax0, s.st[1].z1⟩
  let new7  : Lane := ⟨ax1, s.st[7].z1⟩
  let new13 : Lane := ⟨s.st[13].z0, ax2⟩
  let new19 : Lane := ⟨ax3, s.st[19].z1⟩
  let new20 : Lane := ⟨s.st[20].z0, ax4⟩
  let st' := s.st.set 1 new1 |>.set 7 new7 |>.set 13 new13 |>.set 19 new19 |>.set 20 new20
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y3_zeta1` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y3_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[20].z0 ^^^ s.d[4].z0).rotateLeft 13
  let bx1 := (s.st[1].z1  ^^^ s.d[0].z1).rotateLeft 18
  let bx2 := (s.st[7].z1  ^^^ s.d[1].z1).rotateLeft 5
  let bx3 := (s.st[13].z0 ^^^ s.d[2].z0).rotateLeft 7
  let bx4 := (s.st[19].z1 ^^^ s.d[3].z1).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨s.st[1].z0,  ax0⟩
  let new7  : Lane := ⟨s.st[7].z0,  ax1⟩
  let new13 : Lane := ⟨ax2, s.st[13].z1⟩
  let new19 : Lane := ⟨s.st[19].z0, ax3⟩
  let new20 : Lane := ⟨ax4, s.st[20].z1⟩
  let st' := s.st.set 1 new1 |>.set 7 new7 |>.set 13 new13 |>.set 19 new19 |>.set 20 new20
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y4_zeta0` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y4_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[10].z0 ^^^ s.d[2].z0).rotateLeft 31
  let bx1 := (s.st[16].z1 ^^^ s.d[3].z1).rotateLeft 28
  let bx2 := (s.st[22].z1 ^^^ s.d[4].z1).rotateLeft 20
  let bx3 := (s.st[3].z1  ^^^ s.d[0].z1).rotateLeft 21
  let bx4 := (s.st[9].z0  ^^^ s.d[1].z0).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨s.st[3].z0,  ax0⟩
  let new9  : Lane := ⟨ax1, s.st[9].z1⟩
  let new10 : Lane := ⟨ax2, s.st[10].z1⟩
  let new16 : Lane := ⟨s.st[16].z0, ax3⟩
  let new22 : Lane := ⟨s.st[22].z0, ax4⟩
  let st' := s.st.set 3 new3 |>.set 9 new9 |>.set 10 new10 |>.set 16 new16 |>.set 22 new22
  { s with st := st' }

/-! ## `bit_pi_rho_chi_y4_zeta1` — no RC, no `s.i` increment -/
def bit_pi_rho_chi_y4_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[10].z1 ^^^ s.d[2].z1).rotateLeft 31
  let bx1 := (s.st[16].z0 ^^^ s.d[3].z0).rotateLeft 27
  let bx2 := (s.st[22].z0 ^^^ s.d[4].z0).rotateLeft 19
  let bx3 := (s.st[3].z0  ^^^ s.d[0].z0).rotateLeft 20
  let bx4 := (s.st[9].z1  ^^^ s.d[1].z1).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨ax0, s.st[3].z1⟩
  let new9  : Lane := ⟨s.st[9].z0,  ax1⟩
  let new10 : Lane := ⟨s.st[10].z0, ax2⟩
  let new16 : Lane := ⟨ax3, s.st[16].z1⟩
  let new22 : Lane := ⟨ax4, s.st[22].z1⟩
  let st' := s.st.set 3 new3 |>.set 9 new9 |>.set 10 new10 |>.set 16 new16 |>.set 22 new22
  { s with st := st' }

/-! ## θ-stage c-cell sub-fns

    Each `bit_theta_c_x{X}_z{Z}` overwrites the `z{Z}` half of the column
    XOR cell `s.c[X]` with the XOR of the `z{Z}` halves of the five
    lanes in column `X`: `s.st[5*X + 0..4].z{Z}`.

    The `s.st`, `s.i`, `s.d` fields are preserved. -/
def bit_theta_c_x0_z0 (s : KState) : KState :=
  let v := s.st[0].z0 ^^^ s.st[1].z0 ^^^ s.st[2].z0 ^^^ s.st[3].z0 ^^^ s.st[4].z0
  { s with c := s.c.set 0 { s.c[0] with z0 := v } }

def bit_theta_c_x0_z1 (s : KState) : KState :=
  let v := s.st[0].z1 ^^^ s.st[1].z1 ^^^ s.st[2].z1 ^^^ s.st[3].z1 ^^^ s.st[4].z1
  { s with c := s.c.set 0 { s.c[0] with z1 := v } }

def bit_theta_c_x1_z0 (s : KState) : KState :=
  let v := s.st[5].z0 ^^^ s.st[6].z0 ^^^ s.st[7].z0 ^^^ s.st[8].z0 ^^^ s.st[9].z0
  { s with c := s.c.set 1 { s.c[1] with z0 := v } }

def bit_theta_c_x1_z1 (s : KState) : KState :=
  let v := s.st[5].z1 ^^^ s.st[6].z1 ^^^ s.st[7].z1 ^^^ s.st[8].z1 ^^^ s.st[9].z1
  { s with c := s.c.set 1 { s.c[1] with z1 := v } }

def bit_theta_c_x2_z0 (s : KState) : KState :=
  let v := s.st[10].z0 ^^^ s.st[11].z0 ^^^ s.st[12].z0 ^^^ s.st[13].z0 ^^^ s.st[14].z0
  { s with c := s.c.set 2 { s.c[2] with z0 := v } }

def bit_theta_c_x2_z1 (s : KState) : KState :=
  let v := s.st[10].z1 ^^^ s.st[11].z1 ^^^ s.st[12].z1 ^^^ s.st[13].z1 ^^^ s.st[14].z1
  { s with c := s.c.set 2 { s.c[2] with z1 := v } }

def bit_theta_c_x3_z0 (s : KState) : KState :=
  let v := s.st[15].z0 ^^^ s.st[16].z0 ^^^ s.st[17].z0 ^^^ s.st[18].z0 ^^^ s.st[19].z0
  { s with c := s.c.set 3 { s.c[3] with z0 := v } }

def bit_theta_c_x3_z1 (s : KState) : KState :=
  let v := s.st[15].z1 ^^^ s.st[16].z1 ^^^ s.st[17].z1 ^^^ s.st[18].z1 ^^^ s.st[19].z1
  { s with c := s.c.set 3 { s.c[3] with z1 := v } }

def bit_theta_c_x4_z0 (s : KState) : KState :=
  let v := s.st[20].z0 ^^^ s.st[21].z0 ^^^ s.st[22].z0 ^^^ s.st[23].z0 ^^^ s.st[24].z0
  { s with c := s.c.set 4 { s.c[4] with z0 := v } }

def bit_theta_c_x4_z1 (s : KState) : KState :=
  let v := s.st[20].z1 ^^^ s.st[21].z1 ^^^ s.st[22].z1 ^^^ s.st[23].z1 ^^^ s.st[24].z1
  { s with c := s.c.set 4 { s.c[4] with z1 := v } }

/-! ## θ-stage d-cell sub-fn

    Overwrites all five `s.d` cells with the XOR-rotate-1 pattern from
    `s.c`. Preserves `s.st`, `s.i`, `s.c`. -/
def bit_theta_d (s : KState) : KState :=
  let nd0 : Lane := ⟨s.c[4].z0 ^^^ (s.c[1].z1).rotateLeft 1, s.c[4].z1 ^^^ s.c[1].z0⟩
  let nd1 : Lane := ⟨s.c[0].z0 ^^^ (s.c[2].z1).rotateLeft 1, s.c[0].z1 ^^^ s.c[2].z0⟩
  let nd2 : Lane := ⟨s.c[1].z0 ^^^ (s.c[3].z1).rotateLeft 1, s.c[1].z1 ^^^ s.c[3].z0⟩
  let nd3 : Lane := ⟨s.c[2].z0 ^^^ (s.c[4].z1).rotateLeft 1, s.c[2].z1 ^^^ s.c[4].z0⟩
  let nd4 : Lane := ⟨s.c[3].z0 ^^^ (s.c[0].z1).rotateLeft 1, s.c[3].z1 ^^^ s.c[0].z0⟩
  let d' := s.d.set 0 nd0 |>.set 1 nd1 |>.set 2 nd2 |>.set 3 nd3 |>.set 4 nd4
  { s with d := d' }

/-! ## θ-step composition (round 0)

    Mirror of `keccak.keccakf1600_round0_theta` in `Funs.lean`: a
    deterministic let-chain through the 10 c-cell sub-fns followed by
    the d-cell write. -/
def bit_keccakf1600_round0_theta (s : KState) : KState :=
  let s1  := bit_theta_c_x0_z0 s
  let s2  := bit_theta_c_x0_z1 s1
  let s3  := bit_theta_c_x1_z0 s2
  let s4  := bit_theta_c_x1_z1 s3
  let s5  := bit_theta_c_x2_z0 s4
  let s6  := bit_theta_c_x2_z1 s5
  let s7  := bit_theta_c_x3_z0 s6
  let s8  := bit_theta_c_x3_z1 s7
  let s9  := bit_theta_c_x4_z0 s8
  let s10 := bit_theta_c_x4_z1 s9
  bit_theta_d s10

/-! ## PrcLift compositions (round 0)

    Mirrors of `keccak.keccakf1600_round0_pi_rho_chi_{1,2}` in
    `Funs.lean`. `_1` carries the round-constant parameter `BR` (only
    the `y0` sub-fns consume it; `y1` sub-fns ignore). -/
def bit_keccakf1600_round0_pi_rho_chi_1 (BR : Std.Usize) (s : KState) : KState :=
  let s1 := bit_pi_rho_chi_y0_zeta0 BR s
  let s2 := bit_pi_rho_chi_y0_zeta1 BR s1
  let s3 := bit_pi_rho_chi_y1_zeta0 s2
  bit_pi_rho_chi_y1_zeta1 s3

def bit_keccakf1600_round0_pi_rho_chi_2 (s : KState) : KState :=
  let s1 := bit_pi_rho_chi_y2_zeta0 s
  let s2 := bit_pi_rho_chi_y2_zeta1 s1
  let s3 := bit_pi_rho_chi_y3_zeta0 s2
  let s4 := bit_pi_rho_chi_y3_zeta1 s3
  let s5 := bit_pi_rho_chi_y4_zeta0 s4
  bit_pi_rho_chi_y4_zeta1 s5

/-! # Round 1

Round 1 reads from `impl_perm`-permuted lane positions: each `theta_c`
sub-fn reads lane half `(impl_swap i ? 1 : 0)` for the `z0` write
(symmetric for `z1`); each `pi_rho_chi` sub-fn visits the impl_perm-image
of the round-0 diagonal. Lane addressing transcribed line-by-line from
`keccak.keccakf1600_round1_*` in `Extraction/Funs.lean:2077-2900`. -/

/-! ## θ-stage c-cell sub-fns (round 1)

Like round-0's `bit_theta_c_*` but with the round-1 zeta-pattern: lanes
swapped by `impl_swap` read their other half. The result still lands in
`s.c[X].z{Z}`. -/

def bit_round1_theta_c_x0_z0 (s : KState) : KState :=
  let v := s.st[0].z0 ^^^ s.st[1].z0 ^^^ s.st[2].z1 ^^^ s.st[3].z1 ^^^ s.st[4].z0
  { s with c := s.c.set 0 { s.c[0] with z0 := v } }

def bit_round1_theta_c_x0_z1 (s : KState) : KState :=
  let v := s.st[0].z1 ^^^ s.st[1].z1 ^^^ s.st[2].z0 ^^^ s.st[3].z0 ^^^ s.st[4].z1
  { s with c := s.c.set 0 { s.c[0] with z1 := v } }

def bit_round1_theta_c_x1_z0 (s : KState) : KState :=
  let v := s.st[5].z1 ^^^ s.st[6].z0 ^^^ s.st[7].z0 ^^^ s.st[8].z1 ^^^ s.st[9].z0
  { s with c := s.c.set 1 { s.c[1] with z0 := v } }

def bit_round1_theta_c_x1_z1 (s : KState) : KState :=
  let v := s.st[5].z0 ^^^ s.st[6].z1 ^^^ s.st[7].z1 ^^^ s.st[8].z0 ^^^ s.st[9].z1
  { s with c := s.c.set 1 { s.c[1] with z1 := v } }

def bit_round1_theta_c_x2_z0 (s : KState) : KState :=
  let v := s.st[10].z0 ^^^ s.st[11].z0 ^^^ s.st[12].z1 ^^^ s.st[13].z1 ^^^ s.st[14].z1
  { s with c := s.c.set 2 { s.c[2] with z0 := v } }

def bit_round1_theta_c_x2_z1 (s : KState) : KState :=
  let v := s.st[10].z1 ^^^ s.st[11].z1 ^^^ s.st[12].z0 ^^^ s.st[13].z0 ^^^ s.st[14].z0
  { s with c := s.c.set 2 { s.c[2] with z1 := v } }

def bit_round1_theta_c_x3_z0 (s : KState) : KState :=
  let v := s.st[15].z0 ^^^ s.st[16].z1 ^^^ s.st[17].z1 ^^^ s.st[18].z1 ^^^ s.st[19].z0
  { s with c := s.c.set 3 { s.c[3] with z0 := v } }

def bit_round1_theta_c_x3_z1 (s : KState) : KState :=
  let v := s.st[15].z1 ^^^ s.st[16].z0 ^^^ s.st[17].z0 ^^^ s.st[18].z0 ^^^ s.st[19].z1
  { s with c := s.c.set 3 { s.c[3] with z1 := v } }

def bit_round1_theta_c_x4_z0 (s : KState) : KState :=
  let v := s.st[20].z1 ^^^ s.st[21].z0 ^^^ s.st[22].z1 ^^^ s.st[23].z0 ^^^ s.st[24].z0
  { s with c := s.c.set 4 { s.c[4] with z0 := v } }

def bit_round1_theta_c_x4_z1 (s : KState) : KState :=
  let v := s.st[20].z0 ^^^ s.st[21].z1 ^^^ s.st[22].z0 ^^^ s.st[23].z1 ^^^ s.st[24].z1
  { s with c := s.c.set 4 { s.c[4] with z1 := v } }

/-! ## θ-stage d-cell sub-fn (round 1)

Same shape as `bit_theta_d`: `d[i].z0 = c[i-1 mod 5].z0 ^ rot1(c[i+1 mod 5].z1)`,
`d[i].z1 = c[i-1 mod 5].z1 ^ c[i+1 mod 5].z0`. Round-1's theta_d body
in Aeneas does the writes in a different order but the dependence pattern
on c[*].z0/z1 is identical to round-0's. -/

def bit_round1_theta_d (s : KState) : KState :=
  let nd0 : Lane := ⟨s.c[4].z0 ^^^ (s.c[1].z1).rotateLeft 1, s.c[4].z1 ^^^ s.c[1].z0⟩
  let nd1 : Lane := ⟨s.c[0].z0 ^^^ (s.c[2].z1).rotateLeft 1, s.c[0].z1 ^^^ s.c[2].z0⟩
  let nd2 : Lane := ⟨s.c[1].z0 ^^^ (s.c[3].z1).rotateLeft 1, s.c[1].z1 ^^^ s.c[3].z0⟩
  let nd3 : Lane := ⟨s.c[2].z0 ^^^ (s.c[4].z1).rotateLeft 1, s.c[2].z1 ^^^ s.c[4].z0⟩
  let nd4 : Lane := ⟨s.c[3].z0 ^^^ (s.c[0].z1).rotateLeft 1, s.c[3].z1 ^^^ s.c[0].z0⟩
  let d' := s.d.set 0 nd0 |>.set 1 nd1 |>.set 2 nd2 |>.set 3 nd3 |>.set 4 nd4
  { s with d := d' }

/-! ## PrcLift sub-fns (round 1)

Each visits 5 lanes (impl_perm-image of round-0's per-y diagonal). Half
(`z0`/`z1`) and rotation amounts transcribed line-by-line from the
Aeneas extraction. -/

/-- `keccak.keccakf1600_round1_pi_rho_chi_y0_zeta0` (Funs.lean:2592).
    Visits lanes 0/8/11/19/22 at halves 0/1/1/1/1. RC_INTERLEAVED_0 XORed
    into ax0 only; no `s.i` increment. -/
def bit_round1_pi_rho_chi_y0_zeta0 (_BR : Std.Usize) (s : KState) : KState :=
  let a0 := s.st[0].z0
  let d0 := s.d[0].z0
  let a1 := s.st[8].z1
  let d1 := s.d[1].z0
  let a2 := s.st[11].z1
  let d2 := s.d[2].z1
  let a3 := s.st[19].z1
  let d3 := s.d[3].z1
  let a4 := s.st[22].z1
  let d4 := s.d[4].z0
  let bx0 := (a0 ^^^ d0).rotateLeft 0
  let bx1 := (a1 ^^^ d1).rotateLeft 22
  let bx2 := (a2 ^^^ d2).rotateLeft 22
  let bx3 := (a3 ^^^ d3).rotateLeft 11
  let bx4 := (a4 ^^^ d4).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_0.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨ax0, s.st[0].z1⟩
  let new8  : Lane := ⟨s.st[8].z0, ax1⟩
  let new11 : Lane := ⟨s.st[11].z0, ax2⟩
  let new19 : Lane := ⟨s.st[19].z0, ax3⟩
  let new22 : Lane := ⟨s.st[22].z0, ax4⟩
  let st' := s.st.set 0 new0 |>.set 8 new8 |>.set 11 new11 |>.set 19 new19 |>.set 22 new22
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y0_zeta1` (Funs.lean:2530). Visits
    lanes 0/8/11/19/22 at halves 1/0/0/0/0. RC_INTERLEAVED_1 XORed into
    ax0; INCREMENTS `s.i`. -/
def bit_round1_pi_rho_chi_y0_zeta1 (_BR : Std.Usize) (s : KState) : KState :=
  let a0 := s.st[0].z1
  let d0 := s.d[0].z1
  let a1 := s.st[8].z0
  let d1 := s.d[1].z1
  let a2 := s.st[11].z0
  let d2 := s.d[2].z0
  let a3 := s.st[19].z0
  let d3 := s.d[3].z0
  let a4 := s.st[22].z0
  let d4 := s.d[4].z1
  let bx0 := (a0 ^^^ d0).rotateLeft 0
  let bx1 := (a1 ^^^ d1).rotateLeft 22
  let bx2 := (a2 ^^^ d2).rotateLeft 21
  let bx3 := (a3 ^^^ d3).rotateLeft 10
  let bx4 := (a4 ^^^ d4).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_1.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨s.st[0].z0, ax0⟩
  let new8  : Lane := ⟨ax1, s.st[8].z1⟩
  let new11 : Lane := ⟨ax2, s.st[11].z1⟩
  let new19 : Lane := ⟨ax3, s.st[19].z1⟩
  let new22 : Lane := ⟨ax4, s.st[22].z1⟩
  let st' := s.st.set 0 new0 |>.set 8 new8 |>.set 11 new11 |>.set 19 new19 |>.set 22 new22
  { s with st := st', i := ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y1_zeta0` (Funs.lean:2475). Visits
    lanes 4/7/10/18/21 at halves 1/1/1/1/0. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y1_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[18].z1 ^^^ s.d[3].z0).rotateLeft 14
  let bx1 := (s.st[21].z0 ^^^ s.d[4].z0).rotateLeft 10
  let bx2 := (s.st[4].z1  ^^^ s.d[0].z1).rotateLeft 2
  let bx3 := (s.st[7].z1  ^^^ s.d[1].z1).rotateLeft 23
  let bx4 := (s.st[10].z1 ^^^ s.d[2].z1).rotateLeft 31
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨s.st[4].z0, ax0⟩
  let new7  : Lane := ⟨s.st[7].z0, ax1⟩
  let new10 : Lane := ⟨s.st[10].z0, ax2⟩
  let new18 : Lane := ⟨s.st[18].z0, ax3⟩
  let new21 : Lane := ⟨ax4, s.st[21].z1⟩
  let st' := s.st.set 4 new4 |>.set 7 new7 |>.set 10 new10 |>.set 18 new18 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y1_zeta1` (Funs.lean:2420). Visits
    lanes 4/7/10/18/21 at halves 0/0/0/0/1. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y1_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[18].z0 ^^^ s.d[3].z1).rotateLeft 14
  let bx1 := (s.st[21].z1 ^^^ s.d[4].z1).rotateLeft 10
  let bx2 := (s.st[4].z0  ^^^ s.d[0].z0).rotateLeft 1
  let bx3 := (s.st[7].z0  ^^^ s.d[1].z0).rotateLeft 22
  let bx4 := (s.st[10].z0 ^^^ s.d[2].z0).rotateLeft 30
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨ax0, s.st[4].z1⟩
  let new7  : Lane := ⟨ax1, s.st[7].z1⟩
  let new10 : Lane := ⟨ax2, s.st[10].z1⟩
  let new18 : Lane := ⟨ax3, s.st[18].z1⟩
  let new21 : Lane := ⟨s.st[21].z0, ax4⟩
  let st' := s.st.set 4 new4 |>.set 7 new7 |>.set 10 new10 |>.set 18 new18 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y2_zeta0` (Funs.lean:2354). Visits
    lanes 3/6/14/17/20 at halves 1/1/1/0/1. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y2_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[6].z1  ^^^ s.d[1].z1).rotateLeft 1
  let bx1 := (s.st[14].z1 ^^^ s.d[2].z0).rotateLeft 3
  let bx2 := (s.st[17].z0 ^^^ s.d[3].z1).rotateLeft 13
  let bx3 := (s.st[20].z1 ^^^ s.d[4].z0).rotateLeft 4
  let bx4 := (s.st[3].z1  ^^^ s.d[0].z0).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨s.st[3].z0,  ax0⟩
  let new6  : Lane := ⟨s.st[6].z0,  ax1⟩
  let new14 : Lane := ⟨s.st[14].z0, ax2⟩
  let new17 : Lane := ⟨ax3, s.st[17].z1⟩
  let new20 : Lane := ⟨s.st[20].z0, ax4⟩
  let st' := s.st.set 3 new3 |>.set 6 new6 |>.set 14 new14 |>.set 17 new17 |>.set 20 new20
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y2_zeta1` (Funs.lean:2299). Visits
    lanes 3/6/14/17/20 at halves 0/0/0/1/0. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y2_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[6].z0  ^^^ s.d[1].z0).rotateLeft 0
  let bx1 := (s.st[14].z0 ^^^ s.d[2].z1).rotateLeft 3
  let bx2 := (s.st[17].z1 ^^^ s.d[3].z0).rotateLeft 12
  let bx3 := (s.st[20].z0 ^^^ s.d[4].z1).rotateLeft 4
  let bx4 := (s.st[3].z0  ^^^ s.d[0].z1).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨ax0, s.st[3].z1⟩
  let new6  : Lane := ⟨ax1, s.st[6].z1⟩
  let new14 : Lane := ⟨ax2, s.st[14].z1⟩
  let new17 : Lane := ⟨s.st[17].z0, ax3⟩
  let new20 : Lane := ⟨ax4, s.st[20].z1⟩
  let st' := s.st.set 3 new3 |>.set 6 new6 |>.set 14 new14 |>.set 17 new17 |>.set 20 new20
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y3_zeta0` (Funs.lean:2244). Visits
    lanes 2/5/13/16/24 at halves 1/1/0/1/1. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y3_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[24].z1 ^^^ s.d[4].z1).rotateLeft 14
  let bx1 := (s.st[2].z1  ^^^ s.d[0].z0).rotateLeft 18
  let bx2 := (s.st[5].z1  ^^^ s.d[1].z0).rotateLeft 5
  let bx3 := (s.st[13].z0 ^^^ s.d[2].z1).rotateLeft 8
  let bx4 := (s.st[16].z1 ^^^ s.d[3].z0).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨s.st[2].z0,  ax0⟩
  let new5  : Lane := ⟨s.st[5].z0,  ax1⟩
  let new13 : Lane := ⟨ax2, s.st[13].z1⟩
  let new16 : Lane := ⟨s.st[16].z0, ax3⟩
  let new24 : Lane := ⟨s.st[24].z0, ax4⟩
  let st' := s.st.set 2 new2 |>.set 5 new5 |>.set 13 new13 |>.set 16 new16 |>.set 24 new24
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y3_zeta1` (Funs.lean:2189). Visits
    lanes 2/5/13/16/24 at halves 0/0/1/0/0. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y3_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[24].z0 ^^^ s.d[4].z0).rotateLeft 13
  let bx1 := (s.st[2].z0  ^^^ s.d[0].z1).rotateLeft 18
  let bx2 := (s.st[5].z0  ^^^ s.d[1].z1).rotateLeft 5
  let bx3 := (s.st[13].z1 ^^^ s.d[2].z0).rotateLeft 7
  let bx4 := (s.st[16].z0 ^^^ s.d[3].z1).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨ax0, s.st[2].z1⟩
  let new5  : Lane := ⟨ax1, s.st[5].z1⟩
  let new13 : Lane := ⟨s.st[13].z0, ax2⟩
  let new16 : Lane := ⟨ax3, s.st[16].z1⟩
  let new24 : Lane := ⟨ax4, s.st[24].z1⟩
  let st' := s.st.set 2 new2 |>.set 5 new5 |>.set 13 new13 |>.set 16 new16 |>.set 24 new24
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y4_zeta0` (Funs.lean:2134). Visits
    lanes 1/9/12/15/23 at halves 1/0/1/1/1. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y4_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[12].z1 ^^^ s.d[2].z0).rotateLeft 31
  let bx1 := (s.st[15].z1 ^^^ s.d[3].z1).rotateLeft 28
  let bx2 := (s.st[23].z1 ^^^ s.d[4].z1).rotateLeft 20
  let bx3 := (s.st[1].z1  ^^^ s.d[0].z1).rotateLeft 21
  let bx4 := (s.st[9].z0  ^^^ s.d[1].z0).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨s.st[1].z0,  ax0⟩
  let new9  : Lane := ⟨ax1, s.st[9].z1⟩
  let new12 : Lane := ⟨s.st[12].z0, ax2⟩
  let new15 : Lane := ⟨s.st[15].z0, ax3⟩
  let new23 : Lane := ⟨s.st[23].z0, ax4⟩
  let st' := s.st.set 1 new1 |>.set 9 new9 |>.set 12 new12 |>.set 15 new15 |>.set 23 new23
  { s with st := st' }

/-- `keccak.keccakf1600_round1_pi_rho_chi_y4_zeta1` (Funs.lean:2079). Visits
    lanes 1/9/12/15/23 at halves 0/1/0/0/0. No RC, no `s.i` increment. -/
def bit_round1_pi_rho_chi_y4_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[12].z0 ^^^ s.d[2].z1).rotateLeft 31
  let bx1 := (s.st[15].z0 ^^^ s.d[3].z0).rotateLeft 27
  let bx2 := (s.st[23].z0 ^^^ s.d[4].z0).rotateLeft 19
  let bx3 := (s.st[1].z0  ^^^ s.d[0].z0).rotateLeft 20
  let bx4 := (s.st[9].z1  ^^^ s.d[1].z1).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨ax0, s.st[1].z1⟩
  let new9  : Lane := ⟨s.st[9].z0, ax1⟩
  let new12 : Lane := ⟨ax2, s.st[12].z1⟩
  let new15 : Lane := ⟨ax3, s.st[15].z1⟩
  let new23 : Lane := ⟨ax4, s.st[23].z1⟩
  let st' := s.st.set 1 new1 |>.set 9 new9 |>.set 12 new12 |>.set 15 new15 |>.set 23 new23
  { s with st := st' }

/-! ## Compositions (round 1) -/

def bit_keccakf1600_round1_theta (s : KState) : KState :=
  let s1  := bit_round1_theta_c_x0_z0 s
  let s2  := bit_round1_theta_c_x0_z1 s1
  let s3  := bit_round1_theta_c_x1_z0 s2
  let s4  := bit_round1_theta_c_x1_z1 s3
  let s5  := bit_round1_theta_c_x2_z0 s4
  let s6  := bit_round1_theta_c_x2_z1 s5
  let s7  := bit_round1_theta_c_x3_z0 s6
  let s8  := bit_round1_theta_c_x3_z1 s7
  let s9  := bit_round1_theta_c_x4_z0 s8
  let s10 := bit_round1_theta_c_x4_z1 s9
  bit_round1_theta_d s10

def bit_keccakf1600_round1_pi_rho_chi_1 (BR : Std.Usize) (s : KState) : KState :=
  let s1 := bit_round1_pi_rho_chi_y0_zeta0 BR s
  let s2 := bit_round1_pi_rho_chi_y0_zeta1 BR s1
  let s3 := bit_round1_pi_rho_chi_y1_zeta0 s2
  bit_round1_pi_rho_chi_y1_zeta1 s3

def bit_keccakf1600_round1_pi_rho_chi_2 (s : KState) : KState :=
  let s1 := bit_round1_pi_rho_chi_y2_zeta0 s
  let s2 := bit_round1_pi_rho_chi_y2_zeta1 s1
  let s3 := bit_round1_pi_rho_chi_y3_zeta0 s2
  let s4 := bit_round1_pi_rho_chi_y3_zeta1 s3
  let s5 := bit_round1_pi_rho_chi_y4_zeta0 s4
  bit_round1_pi_rho_chi_y4_zeta1 s5

/-! ## θ-stage c-cell sub-fns (round 2)

Round-2 zeta-pattern derives from `impl_perm` applied twice to round-0's
column-read pattern. The per-lane `z0`/`z1` choice (transcribed from
`keccakf1600_round2_theta_c_x{X}_z{Z}` in `Extraction/Funs.lean`) is
recorded below — see `StructuralEquiv.lean` for the equivalence proofs. -/

def bit_round2_theta_c_x0_z0 (s : KState) : KState :=
  let v := s.st[0].z0 ^^^ s.st[1].z1 ^^^ s.st[2].z1 ^^^ s.st[3].z1 ^^^ s.st[4].z1
  { s with c := s.c.set 0 { s.c[0] with z0 := v } }

def bit_round2_theta_c_x0_z1 (s : KState) : KState :=
  let v := s.st[0].z1 ^^^ s.st[1].z0 ^^^ s.st[2].z0 ^^^ s.st[3].z0 ^^^ s.st[4].z0
  { s with c := s.c.set 0 { s.c[0] with z1 := v } }

def bit_round2_theta_c_x1_z0 (s : KState) : KState :=
  let v := s.st[5].z1 ^^^ s.st[6].z1 ^^^ s.st[7].z1 ^^^ s.st[8].z1 ^^^ s.st[9].z0
  { s with c := s.c.set 1 { s.c[1] with z0 := v } }

def bit_round2_theta_c_x1_z1 (s : KState) : KState :=
  let v := s.st[5].z0 ^^^ s.st[6].z0 ^^^ s.st[7].z0 ^^^ s.st[8].z0 ^^^ s.st[9].z1
  { s with c := s.c.set 1 { s.c[1] with z1 := v } }

def bit_round2_theta_c_x2_z0 (s : KState) : KState :=
  let v := s.st[10].z1 ^^^ s.st[11].z1 ^^^ s.st[12].z1 ^^^ s.st[13].z0 ^^^ s.st[14].z1
  { s with c := s.c.set 2 { s.c[2] with z0 := v } }

def bit_round2_theta_c_x2_z1 (s : KState) : KState :=
  let v := s.st[10].z0 ^^^ s.st[11].z0 ^^^ s.st[12].z0 ^^^ s.st[13].z1 ^^^ s.st[14].z0
  { s with c := s.c.set 2 { s.c[2] with z1 := v } }

def bit_round2_theta_c_x3_z0 (s : KState) : KState :=
  let v := s.st[15].z1 ^^^ s.st[16].z1 ^^^ s.st[17].z0 ^^^ s.st[18].z1 ^^^ s.st[19].z1
  { s with c := s.c.set 3 { s.c[3] with z0 := v } }

def bit_round2_theta_c_x3_z1 (s : KState) : KState :=
  let v := s.st[15].z0 ^^^ s.st[16].z0 ^^^ s.st[17].z1 ^^^ s.st[18].z0 ^^^ s.st[19].z0
  { s with c := s.c.set 3 { s.c[3] with z1 := v } }

def bit_round2_theta_c_x4_z0 (s : KState) : KState :=
  let v := s.st[20].z1 ^^^ s.st[21].z0 ^^^ s.st[22].z1 ^^^ s.st[23].z1 ^^^ s.st[24].z1
  { s with c := s.c.set 4 { s.c[4] with z0 := v } }

def bit_round2_theta_c_x4_z1 (s : KState) : KState :=
  let v := s.st[20].z0 ^^^ s.st[21].z1 ^^^ s.st[22].z0 ^^^ s.st[23].z0 ^^^ s.st[24].z0
  { s with c := s.c.set 4 { s.c[4] with z1 := v } }

/-! ## θ-stage d-cell sub-fn (round 2)

Identical formula to round 0/1's `theta_d` (same XOR-rotate-1 pattern on
`s.c`). Only the function name changes. -/

def bit_round2_theta_d (s : KState) : KState :=
  let nd0 : Lane := ⟨s.c[4].z0 ^^^ (s.c[1].z1).rotateLeft 1, s.c[4].z1 ^^^ s.c[1].z0⟩
  let nd1 : Lane := ⟨s.c[0].z0 ^^^ (s.c[2].z1).rotateLeft 1, s.c[0].z1 ^^^ s.c[2].z0⟩
  let nd2 : Lane := ⟨s.c[1].z0 ^^^ (s.c[3].z1).rotateLeft 1, s.c[1].z1 ^^^ s.c[3].z0⟩
  let nd3 : Lane := ⟨s.c[2].z0 ^^^ (s.c[4].z1).rotateLeft 1, s.c[2].z1 ^^^ s.c[4].z0⟩
  let nd4 : Lane := ⟨s.c[3].z0 ^^^ (s.c[0].z1).rotateLeft 1, s.c[3].z1 ^^^ s.c[0].z0⟩
  let d' := s.d.set 0 nd0 |>.set 1 nd1 |>.set 2 nd2 |>.set 3 nd3 |>.set 4 nd4
  { s with d := d' }

/-! ## PrcLift sub-fns (round 2)

Each visits 5 lanes (impl_perm²-image of round-0's per-y diagonal). Lane
sets:
- y0: {0, 7, 14, 16, 23}
- y1: {3, 5, 12, 19, 21}
- y2: {1, 8, 10, 17, 24}
- y3: {4, 6, 13, 15, 22}
- y4: {2, 9, 11, 18, 20}

The bx-numbering below matches the Aeneas extraction verbatim (Aeneas
permutes bx-indices so the chi-chain `bx_k → ax_k` lines up with its
emitted write order). -/

/-- `keccak.keccakf1600_round2_pi_rho_chi_y0_zeta0`. Visits lanes
    0/7/14/16/23 at halves 0/1/0/0/1. RC_INTERLEAVED_0 XORed into ax0
    only; no `s.i` increment. -/
def bit_round2_pi_rho_chi_y0_zeta0 (_BR : Std.Usize) (s : KState) : KState :=
  let bx0 := (s.st[0].z0  ^^^ s.d[0].z0).rotateLeft 0
  let bx1 := (s.st[7].z1  ^^^ s.d[1].z0).rotateLeft 22
  let bx2 := (s.st[14].z0 ^^^ s.d[2].z1).rotateLeft 22
  let bx3 := (s.st[16].z0 ^^^ s.d[3].z1).rotateLeft 11
  let bx4 := (s.st[23].z1 ^^^ s.d[4].z0).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_0.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨ax0, s.st[0].z1⟩
  let new7  : Lane := ⟨s.st[7].z0, ax1⟩
  let new14 : Lane := ⟨ax2, s.st[14].z1⟩
  let new16 : Lane := ⟨ax3, s.st[16].z1⟩
  let new23 : Lane := ⟨s.st[23].z0, ax4⟩
  let st' := s.st.set 0 new0 |>.set 7 new7 |>.set 14 new14 |>.set 16 new16 |>.set 23 new23
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y0_zeta1`. Visits lanes
    0/7/14/16/23 at halves 1/0/1/1/0. RC_INTERLEAVED_1 XORed into ax0;
    INCREMENTS `s.i`. -/
def bit_round2_pi_rho_chi_y0_zeta1 (_BR : Std.Usize) (s : KState) : KState :=
  let bx0 := (s.st[0].z1  ^^^ s.d[0].z1).rotateLeft 0
  let bx1 := (s.st[7].z0  ^^^ s.d[1].z1).rotateLeft 22
  let bx2 := (s.st[14].z1 ^^^ s.d[2].z0).rotateLeft 21
  let bx3 := (s.st[16].z1 ^^^ s.d[3].z0).rotateLeft 10
  let bx4 := (s.st[23].z0 ^^^ s.d[4].z1).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_1.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨s.st[0].z0, ax0⟩
  let new7  : Lane := ⟨ax1, s.st[7].z1⟩
  let new14 : Lane := ⟨s.st[14].z0, ax2⟩
  let new16 : Lane := ⟨s.st[16].z0, ax3⟩
  let new23 : Lane := ⟨ax4, s.st[23].z1⟩
  let st' := s.st.set 0 new0 |>.set 7 new7 |>.set 14 new14 |>.set 16 new16 |>.set 23 new23
  { s with st := st', i := ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y1_zeta0`. Visits lanes
    3/5/12/19/21 at halves 0/0/0/1/0. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y1_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[19].z1 ^^^ s.d[3].z0).rotateLeft 14
  let bx1 := (s.st[21].z0 ^^^ s.d[4].z0).rotateLeft 10
  let bx2 := (s.st[3].z0  ^^^ s.d[0].z1).rotateLeft 2
  let bx3 := (s.st[5].z0  ^^^ s.d[1].z1).rotateLeft 23
  let bx4 := (s.st[12].z0 ^^^ s.d[2].z1).rotateLeft 31
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨ax0, s.st[3].z1⟩
  let new5  : Lane := ⟨ax1, s.st[5].z1⟩
  let new12 : Lane := ⟨ax2, s.st[12].z1⟩
  let new19 : Lane := ⟨s.st[19].z0, ax3⟩
  let new21 : Lane := ⟨ax4, s.st[21].z1⟩
  let st' := s.st.set 3 new3 |>.set 5 new5 |>.set 12 new12 |>.set 19 new19 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y1_zeta1`. Visits lanes
    3/5/12/19/21 at halves 1/1/1/0/1. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y1_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[19].z0 ^^^ s.d[3].z1).rotateLeft 14
  let bx1 := (s.st[21].z1 ^^^ s.d[4].z1).rotateLeft 10
  let bx2 := (s.st[3].z1  ^^^ s.d[0].z0).rotateLeft 1
  let bx3 := (s.st[5].z1  ^^^ s.d[1].z0).rotateLeft 22
  let bx4 := (s.st[12].z1 ^^^ s.d[2].z0).rotateLeft 30
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨s.st[3].z0, ax0⟩
  let new5  : Lane := ⟨s.st[5].z0, ax1⟩
  let new12 : Lane := ⟨s.st[12].z0, ax2⟩
  let new19 : Lane := ⟨ax3, s.st[19].z1⟩
  let new21 : Lane := ⟨s.st[21].z0, ax4⟩
  let st' := s.st.set 3 new3 |>.set 5 new5 |>.set 12 new12 |>.set 19 new19 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y2_zeta0`. Visits lanes
    1/8/10/17/24 at halves 1/0/1/1/1. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y2_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[8].z0  ^^^ s.d[1].z1).rotateLeft 1
  let bx1 := (s.st[10].z1 ^^^ s.d[2].z0).rotateLeft 3
  let bx2 := (s.st[17].z1 ^^^ s.d[3].z1).rotateLeft 13
  let bx3 := (s.st[24].z1 ^^^ s.d[4].z0).rotateLeft 4
  let bx4 := (s.st[1].z1  ^^^ s.d[0].z0).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨s.st[1].z0,  ax0⟩
  let new8  : Lane := ⟨ax1, s.st[8].z1⟩
  let new10 : Lane := ⟨s.st[10].z0, ax2⟩
  let new17 : Lane := ⟨s.st[17].z0, ax3⟩
  let new24 : Lane := ⟨s.st[24].z0, ax4⟩
  let st' := s.st.set 1 new1 |>.set 8 new8 |>.set 10 new10 |>.set 17 new17 |>.set 24 new24
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y2_zeta1`. Visits lanes
    1/8/10/17/24 at halves 0/1/0/0/0. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y2_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[8].z1  ^^^ s.d[1].z0).rotateLeft 0
  let bx1 := (s.st[10].z0 ^^^ s.d[2].z1).rotateLeft 3
  let bx2 := (s.st[17].z0 ^^^ s.d[3].z0).rotateLeft 12
  let bx3 := (s.st[24].z0 ^^^ s.d[4].z1).rotateLeft 4
  let bx4 := (s.st[1].z0  ^^^ s.d[0].z1).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨ax0, s.st[1].z1⟩
  let new8  : Lane := ⟨s.st[8].z0, ax1⟩
  let new10 : Lane := ⟨ax2, s.st[10].z1⟩
  let new17 : Lane := ⟨ax3, s.st[17].z1⟩
  let new24 : Lane := ⟨ax4, s.st[24].z1⟩
  let st' := s.st.set 1 new1 |>.set 8 new8 |>.set 10 new10 |>.set 17 new17 |>.set 24 new24
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y3_zeta0`. Visits lanes
    4/6/13/15/22 at halves 1/1/1/1/0. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y3_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[22].z0 ^^^ s.d[4].z1).rotateLeft 14
  let bx1 := (s.st[4].z1  ^^^ s.d[0].z0).rotateLeft 18
  let bx2 := (s.st[6].z1  ^^^ s.d[1].z0).rotateLeft 5
  let bx3 := (s.st[13].z1 ^^^ s.d[2].z1).rotateLeft 8
  let bx4 := (s.st[15].z1 ^^^ s.d[3].z0).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨s.st[4].z0,  ax0⟩
  let new6  : Lane := ⟨s.st[6].z0,  ax1⟩
  let new13 : Lane := ⟨s.st[13].z0, ax2⟩
  let new15 : Lane := ⟨s.st[15].z0, ax3⟩
  let new22 : Lane := ⟨ax4, s.st[22].z1⟩
  let st' := s.st.set 4 new4 |>.set 6 new6 |>.set 13 new13 |>.set 15 new15 |>.set 22 new22
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y3_zeta1`. Visits lanes
    4/6/13/15/22 at halves 0/0/0/0/1. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y3_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[22].z1 ^^^ s.d[4].z0).rotateLeft 13
  let bx1 := (s.st[4].z0  ^^^ s.d[0].z1).rotateLeft 18
  let bx2 := (s.st[6].z0  ^^^ s.d[1].z1).rotateLeft 5
  let bx3 := (s.st[13].z0 ^^^ s.d[2].z0).rotateLeft 7
  let bx4 := (s.st[15].z0 ^^^ s.d[3].z1).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨ax0, s.st[4].z1⟩
  let new6  : Lane := ⟨ax1, s.st[6].z1⟩
  let new13 : Lane := ⟨ax2, s.st[13].z1⟩
  let new15 : Lane := ⟨ax3, s.st[15].z1⟩
  let new22 : Lane := ⟨s.st[22].z0, ax4⟩
  let st' := s.st.set 4 new4 |>.set 6 new6 |>.set 13 new13 |>.set 15 new15 |>.set 22 new22
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y4_zeta0`. Visits lanes
    2/9/11/18/20 at halves 0/0/1/0/0. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y4_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[11].z1 ^^^ s.d[2].z0).rotateLeft 31
  let bx1 := (s.st[18].z0 ^^^ s.d[3].z1).rotateLeft 28
  let bx2 := (s.st[20].z0 ^^^ s.d[4].z1).rotateLeft 20
  let bx3 := (s.st[2].z0  ^^^ s.d[0].z1).rotateLeft 21
  let bx4 := (s.st[9].z0  ^^^ s.d[1].z0).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨ax0, s.st[2].z1⟩
  let new9  : Lane := ⟨ax1, s.st[9].z1⟩
  let new11 : Lane := ⟨s.st[11].z0, ax2⟩
  let new18 : Lane := ⟨ax3, s.st[18].z1⟩
  let new20 : Lane := ⟨ax4, s.st[20].z1⟩
  let st' := s.st.set 2 new2 |>.set 9 new9 |>.set 11 new11 |>.set 18 new18 |>.set 20 new20
  { s with st := st' }

/-- `keccak.keccakf1600_round2_pi_rho_chi_y4_zeta1`. Visits lanes
    2/9/11/18/20 at halves 1/1/0/1/1. No RC, no `s.i` increment. -/
def bit_round2_pi_rho_chi_y4_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[11].z0 ^^^ s.d[2].z1).rotateLeft 31
  let bx1 := (s.st[18].z1 ^^^ s.d[3].z0).rotateLeft 27
  let bx2 := (s.st[20].z1 ^^^ s.d[4].z0).rotateLeft 19
  let bx3 := (s.st[2].z1  ^^^ s.d[0].z0).rotateLeft 20
  let bx4 := (s.st[9].z1  ^^^ s.d[1].z1).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨s.st[2].z0, ax0⟩
  let new9  : Lane := ⟨s.st[9].z0, ax1⟩
  let new11 : Lane := ⟨ax2, s.st[11].z1⟩
  let new18 : Lane := ⟨s.st[18].z0, ax3⟩
  let new20 : Lane := ⟨s.st[20].z0, ax4⟩
  let st' := s.st.set 2 new2 |>.set 9 new9 |>.set 11 new11 |>.set 18 new18 |>.set 20 new20
  { s with st := st' }

/-! ## Compositions (round 2) -/

def bit_keccakf1600_round2_theta (s : KState) : KState :=
  let s1  := bit_round2_theta_c_x0_z0 s
  let s2  := bit_round2_theta_c_x0_z1 s1
  let s3  := bit_round2_theta_c_x1_z0 s2
  let s4  := bit_round2_theta_c_x1_z1 s3
  let s5  := bit_round2_theta_c_x2_z0 s4
  let s6  := bit_round2_theta_c_x2_z1 s5
  let s7  := bit_round2_theta_c_x3_z0 s6
  let s8  := bit_round2_theta_c_x3_z1 s7
  let s9  := bit_round2_theta_c_x4_z0 s8
  let s10 := bit_round2_theta_c_x4_z1 s9
  bit_round2_theta_d s10

def bit_keccakf1600_round2_pi_rho_chi_1 (BR : Std.Usize) (s : KState) : KState :=
  let s1 := bit_round2_pi_rho_chi_y0_zeta0 BR s
  let s2 := bit_round2_pi_rho_chi_y0_zeta1 BR s1
  let s3 := bit_round2_pi_rho_chi_y1_zeta0 s2
  bit_round2_pi_rho_chi_y1_zeta1 s3

def bit_keccakf1600_round2_pi_rho_chi_2 (s : KState) : KState :=
  let s1 := bit_round2_pi_rho_chi_y2_zeta0 s
  let s2 := bit_round2_pi_rho_chi_y2_zeta1 s1
  let s3 := bit_round2_pi_rho_chi_y3_zeta0 s2
  let s4 := bit_round2_pi_rho_chi_y3_zeta1 s3
  let s5 := bit_round2_pi_rho_chi_y4_zeta0 s4
  bit_round2_pi_rho_chi_y4_zeta1 s5

/-! ## θ-stage c-cell sub-fns (round 3)

Round-3 zeta-pattern derives from `impl_perm` applied three times to
round-0's column-read pattern. The per-lane `z0`/`z1` choice
(transcribed from `keccakf1600_round3_theta_c_x{X}_z{Z}` in
`Extraction/Funs.lean`) is recorded below — see `StructuralEquiv.lean`
for the equivalence proofs. -/

def bit_round3_theta_c_x0_z0 (s : KState) : KState :=
  let v := s.st[0].z0 ^^^ s.st[1].z1 ^^^ s.st[2].z0 ^^^ s.st[3].z0 ^^^ s.st[4].z1
  { s with c := s.c.set 0 { s.c[0] with z0 := v } }

def bit_round3_theta_c_x0_z1 (s : KState) : KState :=
  let v := s.st[0].z1 ^^^ s.st[1].z0 ^^^ s.st[2].z1 ^^^ s.st[3].z1 ^^^ s.st[4].z0
  { s with c := s.c.set 0 { s.c[0] with z1 := v } }

def bit_round3_theta_c_x1_z0 (s : KState) : KState :=
  let v := s.st[5].z0 ^^^ s.st[6].z1 ^^^ s.st[7].z1 ^^^ s.st[8].z0 ^^^ s.st[9].z0
  { s with c := s.c.set 1 { s.c[1] with z0 := v } }

def bit_round3_theta_c_x1_z1 (s : KState) : KState :=
  let v := s.st[5].z1 ^^^ s.st[6].z0 ^^^ s.st[7].z0 ^^^ s.st[8].z1 ^^^ s.st[9].z1
  { s with c := s.c.set 1 { s.c[1] with z1 := v } }

def bit_round3_theta_c_x2_z0 (s : KState) : KState :=
  let v := s.st[10].z1 ^^^ s.st[11].z1 ^^^ s.st[12].z0 ^^^ s.st[13].z1 ^^^ s.st[14].z0
  { s with c := s.c.set 2 { s.c[2] with z0 := v } }

def bit_round3_theta_c_x2_z1 (s : KState) : KState :=
  let v := s.st[10].z0 ^^^ s.st[11].z0 ^^^ s.st[12].z1 ^^^ s.st[13].z0 ^^^ s.st[14].z1
  { s with c := s.c.set 2 { s.c[2] with z1 := v } }

def bit_round3_theta_c_x3_z0 (s : KState) : KState :=
  let v := s.st[15].z1 ^^^ s.st[16].z0 ^^^ s.st[17].z1 ^^^ s.st[18].z0 ^^^ s.st[19].z1
  { s with c := s.c.set 3 { s.c[3] with z0 := v } }

def bit_round3_theta_c_x3_z1 (s : KState) : KState :=
  let v := s.st[15].z0 ^^^ s.st[16].z1 ^^^ s.st[17].z0 ^^^ s.st[18].z1 ^^^ s.st[19].z0
  { s with c := s.c.set 3 { s.c[3] with z1 := v } }

def bit_round3_theta_c_x4_z0 (s : KState) : KState :=
  let v := s.st[20].z0 ^^^ s.st[21].z0 ^^^ s.st[22].z0 ^^^ s.st[23].z1 ^^^ s.st[24].z1
  { s with c := s.c.set 4 { s.c[4] with z0 := v } }

def bit_round3_theta_c_x4_z1 (s : KState) : KState :=
  let v := s.st[20].z1 ^^^ s.st[21].z1 ^^^ s.st[22].z1 ^^^ s.st[23].z0 ^^^ s.st[24].z0
  { s with c := s.c.set 4 { s.c[4] with z1 := v } }

/-! ## θ-stage d-cell sub-fn (round 3)

Identical formula to round 0/1/2's `theta_d`. -/

def bit_round3_theta_d (s : KState) : KState :=
  let nd0 : Lane := ⟨s.c[4].z0 ^^^ (s.c[1].z1).rotateLeft 1, s.c[4].z1 ^^^ s.c[1].z0⟩
  let nd1 : Lane := ⟨s.c[0].z0 ^^^ (s.c[2].z1).rotateLeft 1, s.c[0].z1 ^^^ s.c[2].z0⟩
  let nd2 : Lane := ⟨s.c[1].z0 ^^^ (s.c[3].z1).rotateLeft 1, s.c[1].z1 ^^^ s.c[3].z0⟩
  let nd3 : Lane := ⟨s.c[2].z0 ^^^ (s.c[4].z1).rotateLeft 1, s.c[2].z1 ^^^ s.c[4].z0⟩
  let nd4 : Lane := ⟨s.c[3].z0 ^^^ (s.c[0].z1).rotateLeft 1, s.c[3].z1 ^^^ s.c[0].z0⟩
  let d' := s.d.set 0 nd0 |>.set 1 nd1 |>.set 2 nd2 |>.set 3 nd3 |>.set 4 nd4
  { s with d := d' }

/-! ## PrcLift sub-fns (round 3)

Each visits 5 lanes (impl_perm³-image of round-0's per-y diagonal —
which here happens to coincide with column-aligned reads
`s.st[5*j + X]`). Lane sets:
- y0: {0, 5, 10, 15, 20}
- y1: {1, 6, 11, 16, 21}
- y2: {2, 7, 12, 17, 22}
- y3: {3, 8, 13, 18, 23}
- y4: {4, 9, 14, 19, 24}

The bx-numbering below matches the Aeneas extraction verbatim. -/

/-- `keccak.keccakf1600_round3_pi_rho_chi_y0_zeta0`. Visits lanes
    0/5/10/15/20 at halves 0/0/0/0/0. RC_INTERLEAVED_0 XORed into ax0
    only; no `s.i` increment. -/
def bit_round3_pi_rho_chi_y0_zeta0 (_BR : Std.Usize) (s : KState) : KState :=
  let bx0 := (s.st[0].z0  ^^^ s.d[0].z0).rotateLeft 0
  let bx1 := (s.st[5].z0  ^^^ s.d[1].z0).rotateLeft 22
  let bx2 := (s.st[10].z0 ^^^ s.d[2].z1).rotateLeft 22
  let bx3 := (s.st[15].z0 ^^^ s.d[3].z1).rotateLeft 11
  let bx4 := (s.st[20].z0 ^^^ s.d[4].z0).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_0.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨ax0, s.st[0].z1⟩
  let new5  : Lane := ⟨ax1, s.st[5].z1⟩
  let new10 : Lane := ⟨ax2, s.st[10].z1⟩
  let new15 : Lane := ⟨ax3, s.st[15].z1⟩
  let new20 : Lane := ⟨ax4, s.st[20].z1⟩
  let st' := s.st.set 0 new0 |>.set 5 new5 |>.set 10 new10 |>.set 15 new15 |>.set 20 new20
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y0_zeta1`. Visits lanes
    0/5/10/15/20 at halves 1/1/1/1/1. RC_INTERLEAVED_1 XORed into ax0;
    INCREMENTS `s.i`. -/
def bit_round3_pi_rho_chi_y0_zeta1 (_BR : Std.Usize) (s : KState) : KState :=
  let bx0 := (s.st[0].z1  ^^^ s.d[0].z1).rotateLeft 0
  let bx1 := (s.st[5].z1  ^^^ s.d[1].z1).rotateLeft 22
  let bx2 := (s.st[10].z1 ^^^ s.d[2].z0).rotateLeft 21
  let bx3 := (s.st[15].z1 ^^^ s.d[3].z0).rotateLeft 10
  let bx4 := (s.st[20].z1 ^^^ s.d[4].z1).rotateLeft 7
  let rc  := (keccak.RC_INTERLEAVED_1.val[s.i.val]!).bv
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2) ^^^ rc
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new0  : Lane := ⟨s.st[0].z0,  ax0⟩
  let new5  : Lane := ⟨s.st[5].z0,  ax1⟩
  let new10 : Lane := ⟨s.st[10].z0, ax2⟩
  let new15 : Lane := ⟨s.st[15].z0, ax3⟩
  let new20 : Lane := ⟨s.st[20].z0, ax4⟩
  let st' := s.st.set 0 new0 |>.set 5 new5 |>.set 10 new10 |>.set 15 new15 |>.set 20 new20
  { s with st := st', i := ⟨s.i.bv + (1 : BitVec System.Platform.numBits)⟩ }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y1_zeta0`. Visits lanes
    1/6/11/16/21 at halves 0/0/0/0/0. No RC, no `s.i` increment.
    Aeneas bx ordering: bx0←a3, bx1←a4, bx2←a0, bx3←a1, bx4←a2. -/
def bit_round3_pi_rho_chi_y1_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[16].z0 ^^^ s.d[3].z0).rotateLeft 14
  let bx1 := (s.st[21].z0 ^^^ s.d[4].z0).rotateLeft 10
  let bx2 := (s.st[1].z0  ^^^ s.d[0].z1).rotateLeft 2
  let bx3 := (s.st[6].z0  ^^^ s.d[1].z1).rotateLeft 23
  let bx4 := (s.st[11].z0 ^^^ s.d[2].z1).rotateLeft 31
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨ax0, s.st[1].z1⟩
  let new6  : Lane := ⟨ax1, s.st[6].z1⟩
  let new11 : Lane := ⟨ax2, s.st[11].z1⟩
  let new16 : Lane := ⟨ax3, s.st[16].z1⟩
  let new21 : Lane := ⟨ax4, s.st[21].z1⟩
  let st' := s.st.set 1 new1 |>.set 6 new6 |>.set 11 new11 |>.set 16 new16 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y1_zeta1`. Visits lanes
    1/6/11/16/21 at halves 1/1/1/1/1. No RC, no `s.i` increment. -/
def bit_round3_pi_rho_chi_y1_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[16].z1 ^^^ s.d[3].z1).rotateLeft 14
  let bx1 := (s.st[21].z1 ^^^ s.d[4].z1).rotateLeft 10
  let bx2 := (s.st[1].z1  ^^^ s.d[0].z0).rotateLeft 1
  let bx3 := (s.st[6].z1  ^^^ s.d[1].z0).rotateLeft 22
  let bx4 := (s.st[11].z1 ^^^ s.d[2].z0).rotateLeft 30
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new1  : Lane := ⟨s.st[1].z0,  ax0⟩
  let new6  : Lane := ⟨s.st[6].z0,  ax1⟩
  let new11 : Lane := ⟨s.st[11].z0, ax2⟩
  let new16 : Lane := ⟨s.st[16].z0, ax3⟩
  let new21 : Lane := ⟨s.st[21].z0, ax4⟩
  let st' := s.st.set 1 new1 |>.set 6 new6 |>.set 11 new11 |>.set 16 new16 |>.set 21 new21
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y2_zeta0`. Visits lanes
    2/7/12/17/22 at halves 0/0/0/0/0. No RC, no `s.i` increment.
    Aeneas bx ordering: bx0←a1, bx1←a2, bx2←a3, bx3←a4, bx4←a0. -/
def bit_round3_pi_rho_chi_y2_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[7].z0  ^^^ s.d[1].z1).rotateLeft 1
  let bx1 := (s.st[12].z0 ^^^ s.d[2].z0).rotateLeft 3
  let bx2 := (s.st[17].z0 ^^^ s.d[3].z1).rotateLeft 13
  let bx3 := (s.st[22].z0 ^^^ s.d[4].z0).rotateLeft 4
  let bx4 := (s.st[2].z0  ^^^ s.d[0].z0).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨ax0, s.st[2].z1⟩
  let new7  : Lane := ⟨ax1, s.st[7].z1⟩
  let new12 : Lane := ⟨ax2, s.st[12].z1⟩
  let new17 : Lane := ⟨ax3, s.st[17].z1⟩
  let new22 : Lane := ⟨ax4, s.st[22].z1⟩
  let st' := s.st.set 2 new2 |>.set 7 new7 |>.set 12 new12 |>.set 17 new17 |>.set 22 new22
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y2_zeta1`. Visits lanes
    2/7/12/17/22 at halves 1/1/1/1/1. No RC, no `s.i` increment. -/
def bit_round3_pi_rho_chi_y2_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[7].z1  ^^^ s.d[1].z0).rotateLeft 0
  let bx1 := (s.st[12].z1 ^^^ s.d[2].z1).rotateLeft 3
  let bx2 := (s.st[17].z1 ^^^ s.d[3].z0).rotateLeft 12
  let bx3 := (s.st[22].z1 ^^^ s.d[4].z1).rotateLeft 4
  let bx4 := (s.st[2].z1  ^^^ s.d[0].z1).rotateLeft 9
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new2  : Lane := ⟨s.st[2].z0,  ax0⟩
  let new7  : Lane := ⟨s.st[7].z0,  ax1⟩
  let new12 : Lane := ⟨s.st[12].z0, ax2⟩
  let new17 : Lane := ⟨s.st[17].z0, ax3⟩
  let new22 : Lane := ⟨s.st[22].z0, ax4⟩
  let st' := s.st.set 2 new2 |>.set 7 new7 |>.set 12 new12 |>.set 17 new17 |>.set 22 new22
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y3_zeta0`. Visits lanes
    3/8/13/18/23 at halves 0/0/0/0/0. No RC, no `s.i` increment.
    Aeneas bx ordering: bx0←a4, bx1←a0, bx2←a1, bx3←a2, bx4←a3. -/
def bit_round3_pi_rho_chi_y3_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[23].z0 ^^^ s.d[4].z1).rotateLeft 14
  let bx1 := (s.st[3].z0  ^^^ s.d[0].z0).rotateLeft 18
  let bx2 := (s.st[8].z0  ^^^ s.d[1].z0).rotateLeft 5
  let bx3 := (s.st[13].z0 ^^^ s.d[2].z1).rotateLeft 8
  let bx4 := (s.st[18].z0 ^^^ s.d[3].z0).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨ax0, s.st[3].z1⟩
  let new8  : Lane := ⟨ax1, s.st[8].z1⟩
  let new13 : Lane := ⟨ax2, s.st[13].z1⟩
  let new18 : Lane := ⟨ax3, s.st[18].z1⟩
  let new23 : Lane := ⟨ax4, s.st[23].z1⟩
  let st' := s.st.set 3 new3 |>.set 8 new8 |>.set 13 new13 |>.set 18 new18 |>.set 23 new23
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y3_zeta1`. Visits lanes
    3/8/13/18/23 at halves 1/1/1/1/1. No RC, no `s.i` increment. -/
def bit_round3_pi_rho_chi_y3_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[23].z1 ^^^ s.d[4].z0).rotateLeft 13
  let bx1 := (s.st[3].z1  ^^^ s.d[0].z1).rotateLeft 18
  let bx2 := (s.st[8].z1  ^^^ s.d[1].z1).rotateLeft 5
  let bx3 := (s.st[13].z1 ^^^ s.d[2].z0).rotateLeft 7
  let bx4 := (s.st[18].z1 ^^^ s.d[3].z1).rotateLeft 28
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new3  : Lane := ⟨s.st[3].z0,  ax0⟩
  let new8  : Lane := ⟨s.st[8].z0,  ax1⟩
  let new13 : Lane := ⟨s.st[13].z0, ax2⟩
  let new18 : Lane := ⟨s.st[18].z0, ax3⟩
  let new23 : Lane := ⟨s.st[23].z0, ax4⟩
  let st' := s.st.set 3 new3 |>.set 8 new8 |>.set 13 new13 |>.set 18 new18 |>.set 23 new23
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y4_zeta0`. Visits lanes
    4/9/14/19/24 at halves 0/0/0/0/0. No RC, no `s.i` increment.
    Aeneas bx ordering: bx0←a2, bx1←a3, bx2←a4, bx3←a0, bx4←a1. -/
def bit_round3_pi_rho_chi_y4_zeta0 (s : KState) : KState :=
  let bx0 := (s.st[14].z0 ^^^ s.d[2].z0).rotateLeft 31
  let bx1 := (s.st[19].z0 ^^^ s.d[3].z1).rotateLeft 28
  let bx2 := (s.st[24].z0 ^^^ s.d[4].z1).rotateLeft 20
  let bx3 := (s.st[4].z0  ^^^ s.d[0].z1).rotateLeft 21
  let bx4 := (s.st[9].z0  ^^^ s.d[1].z0).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨ax0, s.st[4].z1⟩
  let new9  : Lane := ⟨ax1, s.st[9].z1⟩
  let new14 : Lane := ⟨ax2, s.st[14].z1⟩
  let new19 : Lane := ⟨ax3, s.st[19].z1⟩
  let new24 : Lane := ⟨ax4, s.st[24].z1⟩
  let st' := s.st.set 4 new4 |>.set 9 new9 |>.set 14 new14 |>.set 19 new19 |>.set 24 new24
  { s with st := st' }

/-- `keccak.keccakf1600_round3_pi_rho_chi_y4_zeta1`. Visits lanes
    4/9/14/19/24 at halves 1/1/1/1/1. No RC, no `s.i` increment. -/
def bit_round3_pi_rho_chi_y4_zeta1 (s : KState) : KState :=
  let bx0 := (s.st[14].z1 ^^^ s.d[2].z1).rotateLeft 31
  let bx1 := (s.st[19].z1 ^^^ s.d[3].z0).rotateLeft 27
  let bx2 := (s.st[24].z1 ^^^ s.d[4].z0).rotateLeft 19
  let bx3 := (s.st[4].z1  ^^^ s.d[0].z0).rotateLeft 20
  let bx4 := (s.st[9].z1  ^^^ s.d[1].z1).rotateLeft 1
  let ax0 := bx0 ^^^ ((~~~ bx1) &&& bx2)
  let ax1 := bx1 ^^^ ((~~~ bx2) &&& bx3)
  let ax2 := bx2 ^^^ ((~~~ bx3) &&& bx4)
  let ax3 := bx3 ^^^ ((~~~ bx4) &&& bx0)
  let ax4 := bx4 ^^^ ((~~~ bx0) &&& bx1)
  let new4  : Lane := ⟨s.st[4].z0,  ax0⟩
  let new9  : Lane := ⟨s.st[9].z0,  ax1⟩
  let new14 : Lane := ⟨s.st[14].z0, ax2⟩
  let new19 : Lane := ⟨s.st[19].z0, ax3⟩
  let new24 : Lane := ⟨s.st[24].z0, ax4⟩
  let st' := s.st.set 4 new4 |>.set 9 new9 |>.set 14 new14 |>.set 19 new19 |>.set 24 new24
  { s with st := st' }

/-! ## Compositions (round 3) -/

def bit_keccakf1600_round3_theta (s : KState) : KState :=
  let s1  := bit_round3_theta_c_x0_z0 s
  let s2  := bit_round3_theta_c_x0_z1 s1
  let s3  := bit_round3_theta_c_x1_z0 s2
  let s4  := bit_round3_theta_c_x1_z1 s3
  let s5  := bit_round3_theta_c_x2_z0 s4
  let s6  := bit_round3_theta_c_x2_z1 s5
  let s7  := bit_round3_theta_c_x3_z0 s6
  let s8  := bit_round3_theta_c_x3_z1 s7
  let s9  := bit_round3_theta_c_x4_z0 s8
  let s10 := bit_round3_theta_c_x4_z1 s9
  bit_round3_theta_d s10

def bit_keccakf1600_round3_pi_rho_chi_1 (BR : Std.Usize) (s : KState) : KState :=
  let s1 := bit_round3_pi_rho_chi_y0_zeta0 BR s
  let s2 := bit_round3_pi_rho_chi_y0_zeta1 BR s1
  let s3 := bit_round3_pi_rho_chi_y1_zeta0 s2
  bit_round3_pi_rho_chi_y1_zeta1 s3

def bit_keccakf1600_round3_pi_rho_chi_2 (s : KState) : KState :=
  let s1 := bit_round3_pi_rho_chi_y2_zeta0 s
  let s2 := bit_round3_pi_rho_chi_y2_zeta1 s1
  let s3 := bit_round3_pi_rho_chi_y3_zeta0 s2
  let s4 := bit_round3_pi_rho_chi_y3_zeta1 s3
  let s5 := bit_round3_pi_rho_chi_y4_zeta0 s4
  bit_round3_pi_rho_chi_y4_zeta1 s5

/-! ## 4-round bundle (the structural-equivalence mid-level composition)

    Mirrors the structure of `keccak.keccakf1600_4rounds`: 12 sub-piece
    calls chained `round0_theta → round0_pi_rho_chi_1 → _2 → round1_…
    → … → round3_pi_rho_chi_2`. `BR` is the `BASE_ROUND` parameter
    (always `0#usize` at the top-level loop call site). -/
def bit_keccakf1600_4rounds (BR : Std.Usize) (s : KState) : KState :=
  let s1  := bit_keccakf1600_round0_theta s
  let s2  := bit_keccakf1600_round0_pi_rho_chi_1 BR s1
  let s3  := bit_keccakf1600_round0_pi_rho_chi_2 s2
  let s4  := bit_keccakf1600_round1_theta s3
  let s5  := bit_keccakf1600_round1_pi_rho_chi_1 BR s4
  let s6  := bit_keccakf1600_round1_pi_rho_chi_2 s5
  let s7  := bit_keccakf1600_round2_theta s6
  let s8  := bit_keccakf1600_round2_pi_rho_chi_1 BR s7
  let s9  := bit_keccakf1600_round2_pi_rho_chi_2 s8
  let s10 := bit_keccakf1600_round3_theta s9
  let s11 := bit_keccakf1600_round3_pi_rho_chi_1 BR s10
  bit_keccakf1600_round3_pi_rho_chi_2 s11

/-! ## Top-level spec: 6 × 4-round bundle, then reset `i` to 0.

    `Nat.iterate f 6` is `f∘f∘f∘f∘f∘f`. Each `bit_keccakf1600_4rounds 0`
    bumps `s.i` by 4 (one increment in each round's `pi_rho_chi_1`), so
    after 6 iterations `s.i.val = 24`. The final `with i := 0` reset
    mirrors `ok { s1 with i := 0#usize }` in
    `keccak.keccakf1600`. -/
def bit_keccak_spec (s : KState) : KState :=
  let s' := Nat.iterate (bit_keccakf1600_4rounds 0#usize) 6 s
  { s' with i := 0#usize }

end libcrux_iot_sha3.BitSpec
