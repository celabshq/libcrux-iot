/-
  # `Matrix/ComputeRingElementV/Hacspec.lean` — L7.3 `D′` tail bridge.

  The hacspec↔pure equational bridge for the *add-message-error* tail of the
  `compute_ring_element_v` decomposition. The hacspec `compute_ring_element_v`
  tail unfolds to
    `let a ← add_polynomials inner_product_inv error_2;
     add_polynomials a message`,
  where the L7.3 bridge supplies `inner_product_inv = scaleZ 512 result2`.

  This file proves the *outer* `add_polynomials … message` step on top of the
  already-proven *inner* bridge `ComputeVectorU.add_polynomials_scaleZ_eq`
  (the `add_polynomials (scaleZ 512 b) e = add_error_reduce_pure b e` lemma):

    add_polynomials (add_error_reduce_pure result2 e2) msg
      = add_message_error_reduce_pure e2 msg result2.

  Per-lane both sides reduce, in `ZMod 3329`, to `512·result2 + e2 + msg`.
  The proof mirrors `add_polynomials_scaleZ_eq` exactly:
  `matrix_add_polynomials_eq_ok` reduction, `eq_of_zmod_lane_canon''`
  3-part split, per-lane `add_pure` associativity/commutativity closed by
  `ring`.

  Local copies of the `private` lane-access / canonicity helpers from
  `ComputeVectorU` are re-derived here (the originals are `private`).
-/
import LibcruxIotMlKem.Spec.Lift
import LibcruxIotMlKem.Vector.Portable.Arithmetic.PerElement
import LibcruxIotMlKem.Vector.Portable.Arithmetic.Element
import LibcruxIotMlKem.Vector.Portable.Ntt
import LibcruxIotMlKem.Ntt
import LibcruxIotMlKem.InvertNtt
import LibcruxIotMlKem.Polynomial.NttDrivers
import LibcruxIotMlKem.Polynomial.PolyOps
import LibcruxIotMlKem.Polynomial.PolyOpsFcBarrett
import LibcruxIotMlKem.Polynomial.PolyOpsFc
import LibcruxIotMlKem.Polynomial.NttMultiply
import LibcruxIotMlKem.Matrix.Common
import LibcruxIotMlKem.Matrix.ComputeAsPlusE
import LibcruxIotMlKem.Matrix.ComputeMessage.Hacspec
import LibcruxIotMlKem.Matrix.ComputeVectorU.Hacspec

set_option mvcgen.warning false
set_option linter.unusedVariables false

namespace libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Hacspec
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec libcrux_iot_ml_kem.Matrix.ComputeVectorU.Hacspec
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt
open libcrux_iot_ml_kem.Spec.Pure (Canonical)
section AddMessageErrorScaleZ

/-! ### Local lane-access / canonicity helpers (copies of the `private`
    originals in `ComputeVectorU`). -/

/-- Generic `Std.Array.make … (range m).map f` lane access (local copy). -/
private theorem mkN_map_lane'' {α : Type} [Inhabited α] {n : Std.Usize} {m : Nat}
    (f : Nat → α) (k : Nat) (hk : k < m)
    (hlen : ((List.range m).map f).length = n.val) :
    (Std.Array.make n ((List.range m).map f) hlen).val[k]! = f k := by
  show ((List.range m).map f)[k]! = f k
  have h_len : ((List.range m).map f).length = m := by simp
  rw [getElem!_pos _ k (by rw [h_len]; exact hk)]
  simp

/-- `chunk_at` lane access (local copy). -/
private theorem chunk_at_lane''
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_at p k).val[ℓ]! = p.val[16 * k + ℓ]! := by
  unfold Spec.chunk_at
  show ((List.range 16).map (fun j => p.val[16 * k + j]!))[ℓ]! = p.val[16 * k + ℓ]!
  have h_len : ((List.range 16).map (fun j => p.val[16 * k + j]!)).length = 16 := by simp
  rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
  rw [List.getElem_map, List.getElem_range]

/-- Lane access for a 16-chunk flatten shape (local copy). -/
private theorem flatten_chunk_map_lane''
    (H : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (j : Nat) (hj : j < 256)
    (h : ((List.range 16).map H).length = (16#usize).val) :
    (Spec.flatten_chunks (Std.Array.make 16#usize ((List.range 16).map H) h)).val[j]!
      = (H (j / 16)).val[j % 16]! := by
  have hk : j / 16 < 16 := by omega
  unfold Spec.flatten_chunks
  rw [mkN_map_lane'' _ j hj]
  rw [mkN_map_lane'' H (j / 16) hk]

/-- Canonical round-trip (local copy). -/
private theorem canon_feOfZMod'' (z : ZMod 3329) : Canonical (feOfZMod z) := by
  unfold Canonical feOfZMod hacspec_ml_kem.parameters.FIELD_MODULUS
  show (BitVec.ofNat 16 z.val).toNat < _
  rw [BitVec.toNat_ofNat]
  have hz : z.val < 3329 := ZMod.val_lt z
  have : z.val % 2 ^ 16 = z.val := Nat.mod_eq_of_lt (by omega)
  simp only [this]; simpa using hz

/-- Canonical round-trip (local copy). -/
private theorem feOfZMod_zmodOfFE_of_canon''
    (fe : hacspec_ml_kem.parameters.FieldElement) (h : Canonical fe) :
    feOfZMod (zmodOfFE fe) = fe := by
  have h' : fe.val.val < 3329 := by
    unfold Canonical hacspec_ml_kem.parameters.FIELD_MODULUS at h; simpa using h
  unfold feOfZMod zmodOfFE
  have hzval : ((fe.val.val : ZMod 3329)).val = fe.val.val := ZMod.val_natCast_of_lt h'
  rw [hzval]
  have hfeval : fe.val.val < 2 ^ 16 := by
    have h_p : (3329 : Nat) ≤ 2 ^ 16 := by decide
    omega
  have hfebv : BitVec.ofNat 16 fe.val.val = fe.val.bv := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    show fe.val.val % 2 ^ 16 = fe.val.bv.toNat
    rw [Nat.mod_eq_of_lt hfeval]; rfl
  show ({ val := ⟨BitVec.ofNat 16 fe.val.val⟩ } :
          hacspec_ml_kem.parameters.FieldElement) = fe
  rw [hfebv]

/-- Two canonical 256-arrays with equal `zmodOfFE` lanes are equal (local copy). -/
private theorem eq_of_zmod_lane_canon''
    (u v : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hcu : ∀ j : Nat, j < 256 → Canonical (u.val[j]!))
    (hcv : ∀ j : Nat, j < 256 → Canonical (v.val[j]!))
    (hz : ∀ j : Nat, j < 256 → zmodOfFE (u.val[j]!) = zmodOfFE (v.val[j]!)) :
    u = v := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [Aeneas.Std.Array.length_eq u, Aeneas.Std.Array.length_eq v]
  · intro j hj1 _hj2
    have hj : j < 256 := by rw [Aeneas.Std.Array.length_eq u] at hj1; simpa using hj1
    have heq : u.val[j]! = v.val[j]! := by
      rw [← feOfZMod_zmodOfFE_of_canon'' (u.val[j]!) (hcu j hj),
          ← feOfZMod_zmodOfFE_of_canon'' (v.val[j]!) (hcv j hj), hz j hj]
    have huj : u.val[j]! = u.val[j] :=
      getElem!_pos u.val j (by rw [Aeneas.Std.Array.length_eq u]; exact hj)
    have hvj : v.val[j]! = v.val[j] :=
      getElem!_pos v.val j (by rw [Aeneas.Std.Array.length_eq v]; exact hj)
    rw [← huj, ← hvj]; exact heq

/-- Per-lane characterization of `Spec.add_error_reduce_pure` (local copy of
    `ComputeVectorU.zmodOfFE_add_error_reduce_pure_lane`): for `j < 256` and
    canonical `b[j]`,
    `zmodOfFE ((add_error_reduce_pure b e)[j]) = 512·zmodOfFE (b[j]) + zmodOfFE (e[j])`. -/
private theorem zmodOfFE_add_error_reduce_pure_lane''
    (b e : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256)
    (hb : libcrux_iot_ml_kem.Spec.Pure.Canonical (b.val[j]!)) :
    zmodOfFE ((Spec.add_error_reduce_pure b e).val[j]!)
      = 512 * zmodOfFE (b.val[j]!) + zmodOfFE (e.val[j]!) := by
  have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hjeq : 16 * (j / 16) + j % 16 = j := by omega
  unfold Spec.add_error_reduce_pure
  rw [flatten_chunk_map_lane'' (fun k => Spec.chunk_add_error_reduce_pure
        (Spec.chunk_at b k) (Spec.chunk_at e k)) j hj (by simp)]
  unfold Spec.chunk_add_error_reduce_pure
  rw [mkN_map_lane'' _ (j % 16) hℓ]
  rw [chunk_at_lane'' b (j / 16) (j % 16) hℓ, chunk_at_lane'' e (j / 16) (j % 16) hℓ]
  rw [hjeq]
  rw [zmodOfFE_add_pure]
  rw [zmodOfFE_mul_pure]
  rw [zmodOfFE_lift_fe_mont]
  have h1441 : (((1441#i16 : Std.I16).val : ZMod 3329)) = 1441 := by decide
  rw [h1441]
  have h512 : (1441 : ZMod 3329) * 169 = 512 := glue_1441_169
  rw [show (zmodOfFE (b.val[j]!) * (1441 * 169) : ZMod 3329)
        = 512 * zmodOfFE (b.val[j]!) by rw [h512]; ring]

/-! ### `D′` — the `add_polynomials ∘ add_polynomials ∘ scaleZ` tail bridge. -/

set_option maxHeartbeats 1000000 in
/-- **L7.3 `D′` tail bridge.** The hacspec `compute_ring_element_v` tail
    `add_polynomials (add_polynomials (scaleZ 512 result2) e2) msg`
    equals `Spec.add_message_error_reduce_pure e2 msg result2` for canonical
    `result2`. The inner add reuses `add_polynomials_scaleZ_eq`; the outer add
    mirrors its body (createi reduction + lane split + per-lane `ring`). -/
theorem add_message_error_scaleZ_eq
    (result2 e2 msg : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (h_r2_canon : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical (result2.val[j]!)) :
    (do let a ← hacspec_ml_kem.matrix.add_polynomials (scaleZ 512 result2) e2
        hacspec_ml_kem.matrix.add_polynomials a msg)
      = .ok (Spec.add_message_error_reduce_pure e2 msg result2) := by
  -- Inner add: reuse the proven bridge.
  rw [add_polynomials_scaleZ_eq result2 e2 h_r2_canon]
  simp only [Aeneas.Std.bind_tc_ok]
  -- Outer add: reduce via createi.
  rw [Stage4MatrixAddFC.matrix_add_polynomials_eq_ok (Spec.add_error_reduce_pure result2 e2) msg]
  set L : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    ⟨(List.range 256).map (fun k =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          ((Spec.add_error_reduce_pure result2 e2).val[k]!) (msg.val[k]!)),
     by simp [List.length_map, List.length_range]⟩ with hL_def
  have hL_lane : ∀ j : Nat, j < 256 →
      L.val[j]! = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                    ((Spec.add_error_reduce_pure result2 e2).val[j]!) (msg.val[j]!) := by
    intro j hj
    show ((List.range 256).map (fun k =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
              ((Spec.add_error_reduce_pure result2 e2).val[k]!) (msg.val[k]!)))[j]! = _
    rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
    rw [List.getElem_map, List.getElem_range]
  apply congrArg Result.ok
  apply eq_of_zmod_lane_canon''
  · -- L lanes canonical
    intro j hj
    rw [hL_lane j hj]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
  · -- add_message_error_reduce_pure lanes canonical
    intro j hj
    have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
    unfold Spec.add_message_error_reduce_pure
    rw [flatten_chunk_map_lane'' (fun k => Spec.chunk_add_message_error_reduce_pure
          (Spec.chunk_at e2 k) (Spec.chunk_at msg k) (Spec.chunk_at result2 k)) j hj (by simp)]
    unfold Spec.chunk_add_message_error_reduce_pure
    rw [mkN_map_lane'' _ (j % 16) hℓ]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
  · -- per-lane zmodOfFE equality
    intro j hj
    have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
    have hjeq : 16 * (j / 16) + j % 16 = j := by omega
    rw [hL_lane j hj]
    rw [zmodOfFE_add_pure]
    rw [zmodOfFE_add_error_reduce_pure_lane'' result2 e2 j hj (h_r2_canon j hj)]
    -- RHS: unfold add_message_error_reduce_pure lane.
    unfold Spec.add_message_error_reduce_pure
    rw [flatten_chunk_map_lane'' (fun k => Spec.chunk_add_message_error_reduce_pure
          (Spec.chunk_at e2 k) (Spec.chunk_at msg k) (Spec.chunk_at result2 k)) j hj (by simp)]
    unfold Spec.chunk_add_message_error_reduce_pure
    rw [mkN_map_lane'' _ (j % 16) hℓ]
    rw [chunk_at_lane'' e2 (j / 16) (j % 16) hℓ, chunk_at_lane'' msg (j / 16) (j % 16) hℓ,
        chunk_at_lane'' result2 (j / 16) (j % 16) hℓ]
    rw [hjeq]
    rw [zmodOfFE_add_pure, zmodOfFE_mul_pure, zmodOfFE_add_pure, zmodOfFE_lift_fe_mont]
    have h1441 : (((1441#i16 : Std.I16).val : ZMod 3329)) = 1441 := by decide
    rw [h1441]
    have h512 : (1441 : ZMod 3329) * 169 = 512 := glue_1441_169
    rw [show (zmodOfFE (result2.val[j]!) * (1441 * 169) : ZMod 3329)
          = 512 * zmodOfFE (result2.val[j]!) by rw [h512]; ring]
    ring

end AddMessageErrorScaleZ

end libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Hacspec