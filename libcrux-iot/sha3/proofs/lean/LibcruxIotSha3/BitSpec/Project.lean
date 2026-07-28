/-
  Projection simp-lemma bridge between `Lane.fromAeneas l .zζ` and
  `l.val[ζ]!.bv` for `ζ ∈ {0, 1}`. After applying these as `simp`, the
  per-lane equalities reduce to pure `BitVec 32` equations closable by
  `bv_decide`.
-/
import LibcruxIotSha3.BitSpec.StateIso
import LibcruxIotSha3.Foundation.Lift

namespace libcrux_iot_sha3.BitSpec

open Aeneas Aeneas.Std libcrux_iot_sha3

/-- A `Lane2U32` always has two elements; destructure to expose them. -/
private theorem Lane2U32.shape (l : lane.Lane2U32) :
    ∃ a b, l.val = [a, b] := by
  obtain ⟨vs, hlen⟩ := l
  have hu2 : ((2#usize : Std.Usize).val) = 2 := by simp [Std.UScalar.ofNatCore_val_eq]
  have h2 : vs.length = 2 := by rw [hu2] at hlen; exact hlen
  match vs, h2 with
  | [a, b], _ => exact ⟨a, b, rfl⟩

@[simp]
theorem Lane.fromAeneas_z0 (l : lane.Lane2U32) :
    (Lane.fromAeneas l).z0 = l.val[0]!.bv := by
  obtain ⟨a, b, hl⟩ := Lane2U32.shape l
  simp [Lane.fromAeneas, hl]

@[simp]
theorem Lane.fromAeneas_z1 (l : lane.Lane2U32) :
    (Lane.fromAeneas l).z1 = l.val[1]!.bv := by
  obtain ⟨a, b, hl⟩ := Lane2U32.shape l
  simp [Lane.fromAeneas, hl]

/-- `Lane.fromAeneas` written as a literal `Lane.mk`, with the two halves
    expressed via `[k]!` rather than `[k]?.getD _`. Used by `bit_theta_d_eq`
    to bridge the raw projection form (exposed after `Lane.mk.injEq` on the
    LHS) back to FC-style `r.d.val[i]!.val[j]!` cells. -/
theorem Lane.fromAeneas_mk (l : lane.Lane2U32) :
    Lane.fromAeneas l = ⟨l.val[0]!.bv, l.val[1]!.bv⟩ := by
  obtain ⟨a, b, hl⟩ := Lane2U32.shape l
  simp [Lane.fromAeneas, hl]

/-! ## `stateArray*FromAeneas` indexed reads — bridge to underlying `.val[k]` -/

@[simp]
theorem stateArray25FromAeneas_getElem
    (a : Std.Array lane.Lane2U32 25#usize) (k : Nat) (hk : k < 25) :
    (stateArray25FromAeneas a)[k] = Lane.fromAeneas (a.val[k]'(by
      have h25u : ((25#usize : Std.Usize).val) = 25 := by
        simp [Std.UScalar.ofNatCore_val_eq]
      have := a.property; omega)) := by
  show ((a.val.map Lane.fromAeneas).toArray)[k]'_ = _
  simp [List.getElem_map]

@[simp]
theorem stateArray5FromAeneas_getElem
    (a : Std.Array lane.Lane2U32 5#usize) (k : Nat) (hk : k < 5) :
    (stateArray5FromAeneas a)[k] = Lane.fromAeneas (a.val[k]'(by
      have h5u : ((5#usize : Std.Usize).val) = 5 := by
        simp [Std.UScalar.ofNatCore_val_eq]
      have := a.property; omega)) := by
  show ((a.val.map Lane.fromAeneas).toArray)[k]'_ = _
  simp [List.getElem_map]

/-- Variant of `stateArray5FromAeneas_getElem` reading the underlying list
    via `[k]!` rather than the bounded `[k]'_`. Used by `bit_theta_d_eq`
    (and the round-1..3 d-cell analogues) so the FC's per-cell hypotheses
    `r.d.val[i]!.val[j]! = …` plug in directly without a `[i]'_` ↔ `[i]!`
    bridge step. -/
theorem stateArray5FromAeneas_getElem!
    (a : Std.Array lane.Lane2U32 5#usize) (k : Nat) (hk : k < 5) :
    (stateArray5FromAeneas a)[k] = Lane.fromAeneas a.val[k]! := by
  have hp : k < a.val.length := by
    have h5u : ((5#usize : Std.Usize).val) = 5 := by
      simp [Std.UScalar.ofNatCore_val_eq]
    have := a.property; omega
  rw [stateArray5FromAeneas_getElem _ k hk, getElem!_pos a.val k hp]

end libcrux_iot_sha3.BitSpec
