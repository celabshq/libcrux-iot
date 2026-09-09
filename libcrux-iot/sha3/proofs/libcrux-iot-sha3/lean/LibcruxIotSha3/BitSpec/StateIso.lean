/-
  Structural isomorphism between the pure-Lean `BitSpec.KState` and the
  Aeneas-extracted `libcrux_iot_sha3.state.KeccakState`.

  Provides the conversion functions `KState.toAeneas` and
  `KState.fromAeneas` plus the per-Lane round-trip theorems.
-/
import LibcruxIotSha3.BitSpec.State
import LibcruxIotSha3.Extraction.Funs

namespace libcrux_iot_sha3.BitSpec

open Aeneas Aeneas.Std libcrux_iot_sha3

/-! ## Lane ↔ Lane2U32 -/

/-- Wrap a `BitVec 32` as a `Std.U32`. -/
@[inline]
private def u32OfBV (b : BitVec 32) : Std.U32 :=
  Std.UScalar.mk (ty := Std.UScalarTy.U32) b

/-- A pure-Lean `Lane` (two `BitVec 32` halves) as an Aeneas `Lane2U32`
    (a length-2 list with proof). -/
def Lane.toAeneas (l : Lane) : lane.Lane2U32 :=
  ⟨[u32OfBV l.z0, u32OfBV l.z1], by
    simp only [List.length_cons, List.length_nil, Nat.add_one]
    rfl⟩

/-- The reverse: read the two halves as `BitVec 32` from the underlying
    list, defaulting to `0` on out-of-range (which never happens for a
    well-formed `Lane2U32`). -/
def Lane.fromAeneas (l : lane.Lane2U32) : Lane :=
  { z0 := (l.val[0]?.getD (u32OfBV 0)).bv
    z1 := (l.val[1]?.getD (u32OfBV 0)).bv }

theorem Lane.fromAeneas_toAeneas (l : Lane) :
    Lane.fromAeneas (Lane.toAeneas l) = l := by
  cases l; rfl

theorem Lane.toAeneas_fromAeneas (l : lane.Lane2U32) :
    Lane.toAeneas (Lane.fromAeneas l) = l := by
  obtain ⟨vals, hlen⟩ := l
  have hlen' : vals.length = 2 := by
    have h2 : ((2#usize : Std.Usize).val) = 2 := by
      simp [Std.UScalar.ofNatCore_val_eq]
    rw [h2] at hlen; exact hlen
  match vals, hlen' with
  | [a, b], _ =>
    cases a; cases b; rfl

/-! ## Vector Lane n ↔ Aeneas.Std.Array Lane2U32 n#usize -/

private theorem listLenAeneas25 (v : Vector Lane 25) :
    (v.toList.map Lane.toAeneas).length = (25#usize).val := by
  rw [List.length_map, Vector.length_toList]; rfl

private theorem listLenAeneas5 (v : Vector Lane 5) :
    (v.toList.map Lane.toAeneas).length = (5#usize).val := by
  rw [List.length_map, Vector.length_toList]; rfl

def stateArray25ToAeneas (v : Vector Lane 25) :
    Aeneas.Std.Array lane.Lane2U32 25#usize :=
  ⟨v.toList.map Lane.toAeneas, listLenAeneas25 v⟩

def stateArray25FromAeneas (a : Aeneas.Std.Array lane.Lane2U32 25#usize) :
    Vector Lane 25 :=
  ⟨(a.val.map Lane.fromAeneas).toArray, by
    rw [List.size_toArray, List.length_map]
    have : a.val.length = (25#usize : Std.Usize).val := a.property
    have h25 : ((25#usize : Std.Usize).val) = 25 := by
      simp [Std.UScalar.ofNatCore_val_eq]
    omega⟩

def stateArray5ToAeneas (v : Vector Lane 5) :
    Aeneas.Std.Array lane.Lane2U32 5#usize :=
  ⟨v.toList.map Lane.toAeneas, listLenAeneas5 v⟩

def stateArray5FromAeneas (a : Aeneas.Std.Array lane.Lane2U32 5#usize) :
    Vector Lane 5 :=
  ⟨(a.val.map Lane.fromAeneas).toArray, by
    rw [List.size_toArray, List.length_map]
    have : a.val.length = (5#usize : Std.Usize).val := a.property
    have h5 : ((5#usize : Std.Usize).val) = 5 := by
      simp [Std.UScalar.ofNatCore_val_eq]
    omega⟩

/-! ## Per-half `Lane.fromAeneas` bridge for `Std.Array.set` -/

theorem Lane.fromAeneas_set_zeta0 (l : lane.Lane2U32) (v : Std.U32) :
    Lane.fromAeneas (Std.Array.set l 0#usize v) = { (Lane.fromAeneas l) with z0 := v.bv } := by
  obtain ⟨vals, hlen⟩ := l
  have h2 : vals.length = 2 := by
    have : ((2#usize : Std.Usize).val) = 2 := by simp [Std.UScalar.ofNatCore_val_eq]
    rw [this] at hlen; exact hlen
  match vals, h2 with
  | [_, _], _ => rfl

theorem Lane.fromAeneas_set_zeta1 (l : lane.Lane2U32) (v : Std.U32) :
    Lane.fromAeneas (Std.Array.set l 1#usize v) = { (Lane.fromAeneas l) with z1 := v.bv } := by
  obtain ⟨vals, hlen⟩ := l
  have h2 : vals.length = 2 := by
    have : ((2#usize : Std.Usize).val) = 2 := by simp [Std.UScalar.ofNatCore_val_eq]
    rw [this] at hlen; exact hlen
  match vals, h2 with
  | [_, _], _ => rfl

/-! ## `stateArray25FromAeneas` distributes over `List.set` -/

theorem stateArray25FromAeneas_set_val
    (a : Aeneas.Std.Array lane.Lane2U32 25#usize) (k : Nat) (hk : k < 25) (v : lane.Lane2U32)
    (hlen : (a.val.set k v).length = (25#usize : Std.Usize).val) :
    stateArray25FromAeneas ⟨a.val.set k v, hlen⟩
    = (stateArray25FromAeneas a).set k (Lane.fromAeneas v) (by simp [hk]) := by
  have hk' : k < (List.map Lane.fromAeneas a.val).toArray.size := by
    simp [List.length_map, a.property, Std.UScalar.ofNatCore_val_eq, hk]
  apply Vector.toArray_inj.mp
  show ((a.val.set k v).map Lane.fromAeneas).toArray
       = (a.val.map Lane.fromAeneas).toArray.set k (Lane.fromAeneas v) hk'
  rw [List.map_set]
  rfl

theorem stateArray5FromAeneas_eq_of_val_eq (a b : Aeneas.Std.Array lane.Lane2U32 5#usize) :
    a = b → stateArray5FromAeneas a = stateArray5FromAeneas b := fun h => h ▸ rfl

/-! ## KState ↔ state.KeccakState -/

/-- The pure-Lean `KState` as an Aeneas `state.KeccakState`. -/
def KState.toAeneas (s : KState) : state.KeccakState :=
  { st := stateArray25ToAeneas s.st
    c  := stateArray5ToAeneas s.c
    d  := stateArray5ToAeneas s.d
    i  := s.i }

/-- An Aeneas `state.KeccakState` as a pure-Lean `KState`. -/
def KState.fromAeneas (s : state.KeccakState) : KState :=
  { st := stateArray25FromAeneas s.st
    c  := stateArray5FromAeneas s.c
    d  := stateArray5FromAeneas s.d
    i  := s.i }

end libcrux_iot_sha3.BitSpec
