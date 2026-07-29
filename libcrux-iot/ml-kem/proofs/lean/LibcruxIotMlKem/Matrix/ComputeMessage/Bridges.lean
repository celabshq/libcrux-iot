/-
  # `Matrix/ComputeMessage/Bridges.lean` — L7.4 bridge foundation.

  ZMod-domain bridge lemmas for the L7.4 `compute_message` decomposition.
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
import LibcruxIotMlKem.Matrix.Common

namespace libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges
open libcrux_iot_ml_kem.Matrix.Common
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-! ## `zmodOfFE` distribution helpers (public re-derivations).

    FCTargets' `L2_8c.zmodOfFE_{mul,add}_pure` and `Common.lean`'s
    `Impl.zmodOfFE_mul_pure` are `private`. We re-expose them publicly. The
    `*_val_eq` lemmas re-derive the impl's `% 3329` value equation; `mul`/`add`
    are unconditional, `sub` requires canonical inputs. -/

/-- Local copy of `Spec.Pure.uscalar_rem_ok_U32` (private there). -/
private theorem uscalar_rem_ok_U32 (z m : Std.U32) (hm : m.val ≠ 0) :
    ∃ w : Std.U32, (z % m : Result Std.U32) = .ok w ∧ w.val = z.val % m.val := by
  have heq : (z % m : Result Std.U32) = Std.UScalar.rem z m := rfl
  unfold Std.UScalar.rem at heq
  simp [hm] at heq
  refine ⟨_, heq, ?_⟩
  show (BitVec.umod z.bv m.bv).toNat = z.val % m.val
  unfold BitVec.umod
  simp only [BitVec.toNat_ofNatLT]
  rfl

private theorem mul_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b).val.val
      = (a.val.val * b.val.val) % 3329 := by
  have hmul :
      hacspec_ml_kem.parameters.FieldElement.mul a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.mul at hmul
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hmul
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.mul_equiv x y
  have heqmul : (x * y : Result Std.U32) = Std.UScalar.mul x y := rfl
  cases hxy : (x * y : Result Std.U32) with
  | ok z =>
    rw [hxy] at hmul
    rw [heqmul] at hxy; rw [hxy] at hae; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hmul
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hmul; simp only [Aeneas.Std.bind_tc_ok] at hmul
    unfold hacspec_ml_kem.parameters.FieldElement.new at hmul
    simp at hmul
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hmul]
    show (Std.UScalar.cast .U16 w).val = (a.val.val * b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail _ =>
    rw [heqmul] at hxy; rw [hxy] at hae
    simp only [Std.UScalar.max, Aeneas.Std.UScalarTy.numBits] at hae
    rw [hxval, hyval] at hae
    have : a.val.val * b.val.val < 2^32 := by
      have h1 : a.val.val * b.val.val ≤ (2^16 - 1) * (2^16 - 1) := by
        apply Nat.mul_le_mul <;> omega
      have heq : (2^16 - 1) * (2^16 - 1) = 2^32 - 2*2^16 + 1 := by decide
      omega
    omega
  | div => rw [heqmul] at hxy; rw [hxy] at hae; exact hae.elim

/-- `zmodOfFE` distributes over `mul_pure` (public). -/
theorem zmodOfFE_mul_pure
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure a b)
      = zmodOfFE a * zmodOfFE b := by
  unfold zmodOfFE
  rw [mul_pure_val_eq, ZMod.natCast_mod]; push_cast; rfl

private theorem add_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b).val.val
      = (a.val.val + b.val.val) % 3329 := by
  have hadd :
      hacspec_ml_kem.parameters.FieldElement.add a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_eq_ok a b
  unfold hacspec_ml_kem.parameters.FieldElement.add at hadd
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hadd
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hae := Std.UScalar.add_equiv x y
  cases hxy : (x + y) with
  | ok z =>
    rw [hxy] at hae hadd; simp at hae
    obtain ⟨_, hzval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hadd
    have hmod_val :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329 := by
      unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
    have hmod_ne :
        (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val ≠ 0 := by
      rw [hmod_val]; decide
    set m : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
    obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 z m hmod_ne
    rw [hw_eq] at hadd; simp only [Aeneas.Std.bind_tc_ok] at hadd
    unfold hacspec_ml_kem.parameters.FieldElement.new at hadd
    simp at hadd
    have hwbnd : w.val < 3329 := by
      rw [hwval, hmod_val]; exact Nat.mod_lt _ (by decide)
    have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
      apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
      simp [Aeneas.Std.UScalarTy.numBits]; omega
    rw [← hadd]
    show (Std.UScalar.cast .U16 w).val = (a.val.val + b.val.val) % 3329
    rw [hwcast, hwval, hmod_val, hzval, hxval, hyval]
  | fail e =>
    rw [hxy] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hyval] at hae; omega
  | div => rw [hxy] at hae; exact hae.elim

/-- `zmodOfFE` distributes over `add_pure` (public). -/
theorem zmodOfFE_add_pure
    (a b : hacspec_ml_kem.parameters.FieldElement) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b)
      = zmodOfFE a + zmodOfFE b := by
  unfold zmodOfFE
  rw [add_pure_val_eq, ZMod.natCast_mod]; push_cast; rfl

private theorem sub_pure_val_eq
    (a b : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.Spec.Pure.Canonical a)
    (hb : libcrux_iot_ml_kem.Spec.Pure.Canonical b) :
    (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a b).val.val
      = (a.val.val + 3329 - b.val.val) % 3329 := by
  have hsub :
      hacspec_ml_kem.parameters.FieldElement.sub a b
        = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a b) :=
    libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_eq_ok a b ha hb
  have ha' : a.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at ha
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at ha; simpa using ha
  have hb' : b.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hb
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at hb; simpa using hb
  unfold hacspec_ml_kem.parameters.FieldElement.sub at hsub
  simp only [Aeneas.Std.lift, Aeneas.Std.bind_tc_ok] at hsub
  have hA := a.val.hBounds; have hB := b.val.hBounds
  simp [Aeneas.Std.UScalarTy.numBits] at hA hB
  set x : Std.U32 := Std.UScalar.cast .U32 a.val
  set y : Std.U32 := Std.UScalar.cast .U32 b.val
  set q : Std.U32 := Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS
  have hxval : x.val = a.val.val := Std.U16.cast_U32_val_eq a.val
  have hyval : y.val = b.val.val := Std.U16.cast_U32_val_eq b.val
  have hqval : q.val = 3329 := by
    show (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS).val = 3329
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS; simp
  have hae := Std.UScalar.add_equiv x q
  cases hxq : (x + q : Result Std.U32) with
  | ok s =>
    rw [hxq] at hae hsub; simp at hae
    obtain ⟨_, hsval, _⟩ := hae
    simp only [Aeneas.Std.bind_tc_ok] at hsub
    have hae2 := Std.UScalar.sub_equiv s y
    cases hsy : (s - y : Result Std.U32) with
    | ok u =>
      rw [hsy] at hae2 hsub; simp at hae2
      obtain ⟨_hyle, hsuy, _⟩ := hae2
      simp only [Aeneas.Std.bind_tc_ok] at hsub
      have hq_ne : q.val ≠ 0 := by rw [hqval]; decide
      obtain ⟨w, hw_eq, hwval⟩ := uscalar_rem_ok_U32 u q hq_ne
      rw [hw_eq] at hsub; simp only [Aeneas.Std.bind_tc_ok] at hsub
      unfold hacspec_ml_kem.parameters.FieldElement.new at hsub
      simp at hsub
      have hwbnd : w.val < 3329 := by
        rw [hwval, hqval]; exact Nat.mod_lt _ (by decide)
      have hwcast : (Std.UScalar.cast .U16 w).val = w.val := by
        apply Std.UScalar.cast_val_mod_pow_of_inBounds_eq
        simp [Aeneas.Std.UScalarTy.numBits]; omega
      rw [← hsub]
      show (Std.UScalar.cast .U16 w).val = (a.val.val + 3329 - b.val.val) % 3329
      rw [hwcast, hwval, hqval]
      have hu_eq : u.val = a.val.val + 3329 - b.val.val := by
        have h1 : s.val = u.val + y.val := hsuy
        rw [hsval, hxval, hqval, hyval] at h1
        omega
      rw [hu_eq]
    | fail e =>
      rw [hsy] at hae2; simp at hae2
      rw [hsval, hxval, hqval, hyval] at hae2
      omega
    | div => rw [hsy] at hae2; exact hae2.elim
  | fail e =>
    rw [hxq] at hae; simp [Std.UScalar.inBounds] at hae
    rw [hxval, hqval] at hae
    omega
  | div => rw [hxq] at hae; exact hae.elim

/-- `zmodOfFE` distributes over `sub_pure` (public; requires canonical inputs,
    which all `*_pure` outputs and `lift_fe`/`lift_fe_mont`/`feOfZMod`-built
    lanes satisfy). -/
theorem zmodOfFE_sub_pure
    (a b : hacspec_ml_kem.parameters.FieldElement)
    (ha : libcrux_iot_ml_kem.Spec.Pure.Canonical a)
    (hb : libcrux_iot_ml_kem.Spec.Pure.Canonical b) :
    zmodOfFE (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure a b)
      = zmodOfFE a - zmodOfFE b := by
  have hb' : b.val.val < 3329 := by
    unfold libcrux_iot_ml_kem.Spec.Pure.Canonical at hb
    unfold hacspec_ml_kem.parameters.FIELD_MODULUS at hb; simpa using hb
  unfold zmodOfFE
  rw [sub_pure_val_eq a b ha hb, ZMod.natCast_mod]
  -- (a + 3329 - b : ℕ) cast to ZMod 3329 = a - b, using b < 3329 so the
  -- Nat subtraction does not truncate.
  have hcast : ((a.val.val + 3329 - b.val.val : ℕ) : ZMod 3329)
      = (a.val.val : ZMod 3329) - (b.val.val : ZMod 3329) := by
    have hle : b.val.val ≤ a.val.val + 3329 := by omega
    rw [Nat.cast_sub hle]
    push_cast
    ring
  rw [hcast]

/-! ## `scaleZ` — per-lane `ZMod 3329` scale on FE-arrays. -/

/-- Per-lane scale of a 256-FE array by a `ZMod 3329` constant `c`:
    lane `j` becomes `feOfZMod (c * zmodOfFE p[j])`. -/
noncomputable def scaleZ (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
  Std.Array.make 256#usize
    ((List.range 256).map (fun j => feOfZMod (c * zmodOfFE (p.val[j]!))))
    (by simp only [List.length_map, List.length_range]; rfl)

/-- Lane-access law for `scaleZ`: for `j < 256`,
    `zmodOfFE ((scaleZ c p)[j]) = c * zmodOfFE (p[j])`. -/
theorem scaleZ_lane (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) :
    zmodOfFE ((scaleZ c p).val[j]!) = c * zmodOfFE (p.val[j]!) := by
  unfold scaleZ
  show zmodOfFE (((List.range 256).map
        (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))))[j]!)
      = c * zmodOfFE (p.val[j]!)
  have h_len : ((List.range 256).map
      (fun k => feOfZMod (c * zmodOfFE (p.val[k]!)))).length = 256 := by simp
  rw [getElem!_pos _ j (by rw [h_len]; exact hj)]
  rw [List.getElem_map, List.getElem_range]
  exact zmodOfFE_feOfZMod _

/-- Composition law: `scaleZ a (scaleZ b p) = scaleZ (a * b) p`. -/
theorem scaleZ_compose (a b : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    scaleZ a (scaleZ b p) = scaleZ (a * b) p := by
  unfold scaleZ
  apply Subtype.ext
  show (List.range 256).map
        (fun j => feOfZMod (a * zmodOfFE ((Std.Array.make 256#usize
          ((List.range 256).map (fun k => feOfZMod (b * zmodOfFE (p.val[k]!))))
          (by simp only [List.length_map, List.length_range]; rfl)).val[j]!)))
      = (List.range 256).map (fun j => feOfZMod (a * b * zmodOfFE (p.val[j]!)))
  apply List.ext_getElem
  · simp
  · intro j hj1 _hj2
    have hj : j < 256 := by simpa using hj1
    simp only [List.getElem_map, List.getElem_range]
    -- inner lane access
    have h_len : ((List.range 256).map
        (fun k => feOfZMod (b * zmodOfFE (p.val[k]!)))).length = 256 := by simp
    have hinner : ((Std.Array.make 256#usize
          ((List.range 256).map (fun k => feOfZMod (b * zmodOfFE (p.val[k]!))))
          (by simp only [List.length_map, List.length_range]; rfl)).val[j]!)
        = feOfZMod (b * zmodOfFE (p.val[j]!)) := by
      show ((List.range 256).map (fun k => feOfZMod (b * zmodOfFE (p.val[k]!))))[j]!
            = feOfZMod (b * zmodOfFE (p.val[j]!))
      rw [getElem!_pos _ j (by rw [h_len]; exact hj)]
      rw [List.getElem_map, List.getElem_range]
    rw [hinner, zmodOfFE_feOfZMod]
    congr 1
    ring

/-! ## Glue arithmetic (all `decide` in `ZMod 3329`). -/

theorem glue_3303_2285 : (3303 * 2285 : ZMod 3329) = 512 := by decide
theorem glue_1441_169  : (1441 * 169  : ZMod 3329) = 512 := by decide
theorem glue_169_2285  : (169 * 2285  : ZMod 3329) = 1   := by decide

/-! ## Chunk / flatten lane-access helpers.

    NB: a *statement type* containing a nested-array index `(xs : List (Std.Array
    FE 16#usize))[j]!` fails to elaborate (the `private` FCTargets chunk-`Inhabited`
    instance's `by simp` over-solves when forced during type elaboration). We work
    around this by stating the generic lemma `mkN_map_lane` with an *abstract* element
    type `α` (so no concrete nested type appears in the statement) and only applying
    it in *tactic mode* (where the nested index is fine). -/

/-- Generic lane access for a `(List.range m).map f`-backed `Std.Array n`:
    for `k < m`, `(make n ((range m).map f) hlen).val[k]! = f k`. -/
private theorem mkN_map_lane {α : Type} [Inhabited α] {n : Std.Usize} {m : Nat}
    (f : Nat → α) (k : Nat) (hk : k < m)
    (hlen : ((List.range m).map f).length = n.val) :
    (Std.Array.make n ((List.range m).map f) hlen).val[k]! = f k := by
  show ((List.range m).map f)[k]! = f k
  have h_len : ((List.range m).map f).length = m := by simp
  rw [getElem!_pos _ k (by rw [h_len]; exact hk)]
  simp

/-- Lane access for `Spec.chunk_at` (flat statement, elaborates fine): for `ℓ < 16`,
    `(chunk_at p k)[ℓ] = p[16*k + ℓ]`. -/
private theorem chunk_at_lane
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_at p k).val[ℓ]! = p.val[16 * k + ℓ]! := by
  unfold Spec.chunk_at
  exact mkN_map_lane _ ℓ hℓ _

/-- Lane access for a 16-chunk `Std.Array.make` of a mapped `List.range 16`
    (`f`/`h` inferred from the goal; matches the call sites in the D proof). -/
private theorem mk16_chunk_lane {α : Type} [Inhabited α]
    (f : Nat → α) (k : Nat) (hk : k < 16)
    {h : ((List.range 16).map f).length = (16#usize).val} :
    (Std.Array.make 16#usize ((List.range 16).map f) h).val[k]! = f k :=
  mkN_map_lane f k hk h

/-- `zmodOfFE (lift_fe_mont x) = x.val · 169` (public; re-derives the
    `private` copies in FCTargets/Common). -/
theorem zmodOfFE_lift_fe_mont (x : Std.I16) :
    zmodOfFE (lift_fe_mont x) = (x.val : ZMod 3329) * 169 := by
  unfold lift_fe_mont
  rw [zmodOfFE_feOfZMod]; rfl

/-! ## D / subtract bridge (factor 512 = 1441·169). -/

/-- Per-lane characterization of `Spec.subtract_reduce_pure`: for `j < 256`
    and canonical `a[j]` (the actual `self`-poly lanes are always canonical),
    `zmodOfFE ((subtract_reduce_pure a b)[j]) = zmodOfFE (a[j]) - 512 * zmodOfFE (b[j])`.
    The impl's fused Montgomery `·1441` correction equals `·512` in `ZMod 3329`
    since `1441 · 169 ≡ 512` (`glue_1441_169`). -/
theorem zmodOfFE_subtract_reduce_pure_lane
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256)
    (ha : libcrux_iot_ml_kem.Spec.Pure.Canonical (a.val[j]!)) :
    zmodOfFE ((Spec.subtract_reduce_pure a b).val[j]!)
      = zmodOfFE (a.val[j]!) - 512 * zmodOfFE (b.val[j]!) := by
  have hk : j / 16 < 16 := by omega
  have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
  have hjeq : 16 * (j / 16) + j % 16 = j := by omega
  unfold Spec.subtract_reduce_pure
  -- Reduce `(flatten_chunks …).val[j]!` to the nested chunk lookup directly via the
  -- generic `mkN_map_lane` (stating a standalone `flatten_chunks_lane` lemma fails:
  -- a nested `[!]` index in a *theorem statement type* re-runs the `16#usize`
  -- `(by decide)` proof and over-solves — see file header note).
  unfold Spec.flatten_chunks
  rw [mkN_map_lane _ j hj]
  rw [mk16_chunk_lane _ (j / 16) hk]
  -- now: chunk_subtract_reduce_pure (chunk_at a k) (chunk_at b k) [j%16]
  unfold Spec.chunk_subtract_reduce_pure
  rw [mk16_chunk_lane _ (j % 16) hℓ]
  -- lane = sub_pure (chunk_at a k)[ℓ] (mul_pure (chunk_at b k)[ℓ] (lift_fe_mont 1441))
  rw [chunk_at_lane a (j / 16) (j % 16) hℓ, chunk_at_lane b (j / 16) (j % 16) hℓ]
  rw [hjeq]
  -- Need canonicity of the two sub_pure args.
  have hcb : libcrux_iot_ml_kem.Spec.Pure.Canonical
      (libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
        (b.val[j]!) (lift_fe_mont (1441#i16))) :=
    libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
  rw [zmodOfFE_sub_pure _ _ ha hcb]
  rw [zmodOfFE_mul_pure]
  -- zmodOfFE (lift_fe_mont 1441) = 1441 * 169 = 512
  rw [zmodOfFE_lift_fe_mont]
  have h1441 : (((1441#i16 : Std.I16).val : ZMod 3329)) = 1441 := by decide
  rw [h1441]
  have h512 : (1441 : ZMod 3329) * 169 = 512 := glue_1441_169
  rw [show (zmodOfFE (b.val[j]!) * (1441 * 169) : ZMod 3329)
        = 512 * zmodOfFE (b.val[j]!) by rw [h512]; ring]

end libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges