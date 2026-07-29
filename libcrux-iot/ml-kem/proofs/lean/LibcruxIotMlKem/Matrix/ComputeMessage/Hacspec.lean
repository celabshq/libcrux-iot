/-
  # `Matrix/ComputeMessage/Hacspec.lean` — L7.4 pure/spec bridges.

  Pure-side and pure↔hacspec equational bridges for the direct
  `compute_message` decomposition:

  * **B** — `invert_ntt_montgomery_pure` is `scaleZ`-equivariant (pure
    scalar-linearity; the constant passes through all 7 inverse layers).
  * **C** — `hacspec ntt_inverse p = scaleZ 3303 (invert_ntt_montgomery_pure p)`
    (`3303 = 512·169`, the fixed Montgomery factor between the hacspec inverse
    NTT and the Mont-domain pure inverse).
  * **D (hacspec side)** — `sub_polynomials a (scaleZ 512 b)
    = subtract_reduce_pure a b` for canonical `a` (the `·512` cancels the
    surplus `R` the invert path carries; `Bridges.zmodOfFE_subtract_reduce_pure_lane`
    supplies the per-lane characterization, `1441·169 ≡ 512`).
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
import LibcruxIotMlKem.Matrix.ComputeMessage.Bridges

namespace libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec
open libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeMessage.Bridges
open CoreModels Aeneas Aeneas.Std Std.Do
open libcrux_iot_ml_kem.Spec
open libcrux_iot_ml_kem.InvertNtt libcrux_iot_ml_kem.Matrix.Common libcrux_iot_ml_kem.Matrix.ComputeAsPlusE libcrux_iot_ml_kem.Ntt libcrux_iot_ml_kem.Polynomial.NttMultiply libcrux_iot_ml_kem.Polynomial.PolyOpsFc libcrux_iot_ml_kem.Polynomial.PolyOpsFcBarrett libcrux_iot_ml_kem.Spec.Lift libcrux_iot_ml_kem.Vector.Portable.Arithmetic.Element libcrux_iot_ml_kem.Vector.Portable.Arithmetic.PerElement libcrux_iot_ml_kem.Vector.Portable.Ntt

/-! ## B — `invert_ntt_montgomery_pure` is `scaleZ`-equivariant.

    The 7-layer inverse NTT is `ZMod`-linear: each Gentleman–Sande butterfly
    is `add_pure` / `sub_pure` / `mul_pure`-by-constant on the lanes, all of
    which are linear in the lane value. Scaling the input by `c` scales every
    output lane by `c`. Both sides are canonical (`Canonical_{add,sub,mul}_pure`),
    so the equality holds strictly (not merely per-lane in `ZMod`).

    Proof strategy (per-layer equivariance, compose 7×):
    * Per-chunk butterflies: `zmodOfFE (butterfly (scaled inputs)) =
      c * zmodOfFE (butterfly (inputs))` via `zmodOfFE_{add,sub,mul}_pure` +
      ring; `scaleZ_lane` to expose the `c *` on the input side.
    * Each `Spec.invert_ntt_layer_*_pure` preserves the "lane `j` is `c`-scaled"
      relation (chunk_at / flatten_chunks lane bookkeeping).
    * `Spec.invert_ntt_montgomery_pure` = compose of the 7 layers; the relation
      threads through. Finish via canonical determination (two canonical FEs
      with equal `zmodOfFE` are equal).

    **Canonical precondition (required).** `Spec.Pure.FieldElement.sub_pure` is
    only the linear `a − b` when the subtrahend is canonical (< 3329); on a
    non-canonical subtrahend the underlying U32 subtraction underflows and
    `sub_pure` saturates to `defaultFE` (residue 0). The layer-1 inverse
    butterfly subtracts a *raw input lane*, so equivariance is FALSE for
    non-canonical `p` (counterexample: `p[0] = 60000` vs its canonical residue
    `78` give different layer-1 outputs). `hp` rules this out; it is discharged
    at every L7.4 call site because the inputs are `lift_poly` / `scaleZ`
    outputs (canonical by construction). Canonicity is preserved across the
    layers by `Canonical_{add,sub,mul}_pure`. -/
section InvertScaleZ

open libcrux_iot_ml_kem.Spec.Pure (Canonical)
/-- 256-lane "every lane canonical" predicate. -/
private def CanonArr (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) : Prop :=
  ∀ j : Nat, j < 256 → Canonical (p.val[j]!)

/-- 256-lane "`q` is the per-lane `c`-scale of `p` in `ZMod 3329`" predicate. -/
private def ScaledArr (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) : Prop :=
  ∀ j : Nat, j < 256 → zmodOfFE (q.val[j]!) = c * zmodOfFE (p.val[j]!)

/-- 16-lane "every lane canonical" predicate. -/
private def CanonChunk (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) : Prop :=
  ∀ ℓ : Nat, ℓ < 16 → Canonical (a.val[ℓ]!)

/-- 16-lane "`q` is the per-lane `c`-scale of `p`" predicate. -/
private def ScaledChunk (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) : Prop :=
  ∀ ℓ : Nat, ℓ < 16 → zmodOfFE (q.val[ℓ]!) = c * zmodOfFE (p.val[ℓ]!)

/-- `chunk_at` lane access (public re-derivation of the `private` Bridges copy). -/
private theorem chunk_at_lane'
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_at p k).val[ℓ]! = p.val[16 * k + ℓ]! := by
  unfold Spec.chunk_at
  show ((List.range 16).map (fun j => p.val[16 * k + j]!))[ℓ]! = p.val[16 * k + ℓ]!
  have h_len : ((List.range 16).map (fun j => p.val[16 * k + j]!)).length = 16 := by simp
  rw [getElem!_pos _ ℓ (by rw [h_len]; exact hℓ)]
  rw [List.getElem_map, List.getElem_range]

/-- Generic `Std.Array.make … (range m).map f` lane access (local copy). -/
private theorem mkN_map_lane' {α : Type} [Inhabited α] {n : Std.Usize} {m : Nat}
    (f : Nat → α) (k : Nat) (hk : k < m)
    (hlen : ((List.range m).map f).length = n.val) :
    (Std.Array.make n ((List.range m).map f) hlen).val[k]! = f k := by
  show ((List.range m).map f)[k]! = f k
  have h_len : ((List.range m).map f).length = m := by simp
  rw [getElem!_pos _ k (by rw [h_len]; exact hk)]
  simp

/-- Canonical round-trip (local copy of the `private` FCTargets lemma). -/
private theorem feOfZMod_zmodOfFE_of_canon
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

/-! ### Chunk-level equivariance of `chunk_inv_ntt_step_pure`. -/

/-- Lane formula for one inverse-NTT chunk step: only lanes `i`/`j` change. -/
private theorem chunk_inv_ntt_step_lane
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16) (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_ntt_step_pure a zeta i j).val[ℓ]!
      = if ℓ = j.val then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[j.val]!) (a.val[i.val]!)) zeta
        else if ℓ = i.val then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (a.val[j.val]!) (a.val[i.val]!)
        else a.val[ℓ]! := by
  unfold Spec.chunk_inv_ntt_step_pure
  simp only []  -- expose the let-bindings
  rw [← Aeneas.Std.Array.getElem!_Nat_eq]
  have hlen : a.length = 16 := Aeneas.Std.Array.length_eq a
  by_cases hℓj : ℓ = j.val
  · rw [if_pos hℓj]
    subst hℓj
    have hbnd : j.val < (a.set i (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
        (a.val[j.val]!) (a.val[i.val]!))).length := by
      rw [Aeneas.Std.Array.set_length]; rw [hlen]; exact hj
    rw [Aeneas.Std.Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, hbnd⟩]
  · rw [if_neg hℓj,
        Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ (fun h => hℓj h.symm)]
    by_cases hℓi : ℓ = i.val
    · rw [if_pos hℓi]
      subst hℓi
      rw [Aeneas.Std.Array.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by rw [hlen]; exact hi⟩]
    · rw [if_neg hℓi,
          Aeneas.Std.Array.getElem!_Nat_set_ne _ _ _ _ (fun h => hℓi h.symm),
          Aeneas.Std.Array.getElem!_Nat_eq]

/-- `chunk_inv_ntt_step_pure` preserves `CanonChunk`. -/
private theorem chunk_inv_ntt_step_canon
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16) (ha : CanonChunk a) :
    CanonChunk (Spec.chunk_inv_ntt_step_pure a zeta i j) := by
  intro ℓ hℓ
  rw [chunk_inv_ntt_step_lane a zeta i j hi hj ℓ hℓ]
  by_cases hℓj : ℓ = j.val
  · simp only [if_pos hℓj]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
  · simp only [if_neg hℓj]
    by_cases hℓi : ℓ = i.val
    · simp only [if_pos hℓi]
      exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
    · simp only [if_neg hℓi]; exact ha ℓ hℓ

/-- `chunk_inv_ntt_step_pure` preserves `ScaledChunk` (given canonical inputs on
    both sides, so the `sub_pure` lanes are genuinely linear). -/
private theorem chunk_inv_ntt_step_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (zeta : hacspec_ml_kem.parameters.FieldElement) (i j : Std.Usize)
    (hi : i.val < 16) (hj : j.val < 16)
    (hq : CanonChunk q) (hpc : CanonChunk p)
    (hs : ScaledChunk c q p) :
    ScaledChunk c (Spec.chunk_inv_ntt_step_pure q zeta i j)
      (Spec.chunk_inv_ntt_step_pure p zeta i j) := by
  intro ℓ hℓ
  rw [chunk_inv_ntt_step_lane q zeta i j hi hj ℓ hℓ,
      chunk_inv_ntt_step_lane p zeta i j hi hj ℓ hℓ]
  by_cases hℓj : ℓ = j.val
  · simp only [if_pos hℓj]
    rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure,
        zmodOfFE_sub_pure _ _ (hq j.val hj) (hq i.val hi),
        zmodOfFE_sub_pure _ _ (hpc j.val hj) (hpc i.val hi),
        hs j.val hj, hs i.val hi]
    ring
  · simp only [if_neg hℓj]
    by_cases hℓi : ℓ = i.val
    · simp only [if_pos hℓi]
      rw [zmodOfFE_add_pure, zmodOfFE_add_pure, hs j.val hj, hs i.val hi]
      ring
    · simp only [if_neg hℓi]; exact hs ℓ hℓ

/-! ### Layer-step (chunk) equivariance for layers 1/2/3. -/

/-- `chunk_inv_ntt_layer_1_step_pure` preserves `CanonChunk`. -/
private theorem chunk_inv_ntt_layer_1_step_canon
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) (ha : CanonChunk a) :
    CanonChunk (Spec.chunk_inv_ntt_layer_1_step_pure a z0 z1 z2 z3) := by
  unfold Spec.chunk_inv_ntt_layer_1_step_pure
  exact chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide) ha)))))))

/-- `chunk_inv_ntt_layer_2_step_pure` preserves `CanonChunk`. -/
private theorem chunk_inv_ntt_layer_2_step_canon
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) (ha : CanonChunk a) :
    CanonChunk (Spec.chunk_inv_ntt_layer_2_step_pure a z0 z1) := by
  unfold Spec.chunk_inv_ntt_layer_2_step_pure
  exact chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide) ha)))))))

/-- `chunk_inv_ntt_layer_3_step_pure` preserves `CanonChunk`. -/
private theorem chunk_inv_ntt_layer_3_step_canon
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) (ha : CanonChunk a) :
    CanonChunk (Spec.chunk_inv_ntt_layer_3_step_pure a z) := by
  unfold Spec.chunk_inv_ntt_layer_3_step_pure
  exact chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide)
    (chunk_inv_ntt_step_canon _ _ _ _ (by decide) (by decide) ha)))))))

/-- `chunk_inv_ntt_layer_1_step_pure` preserves `ScaledChunk`. -/
private theorem chunk_inv_ntt_layer_1_step_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement)
    (hq : CanonChunk q) (hpc : CanonChunk p) (hs : ScaledChunk c q p) :
    ScaledChunk c (Spec.chunk_inv_ntt_layer_1_step_pure q z0 z1 z2 z3)
      (Spec.chunk_inv_ntt_layer_1_step_pure p z0 z1 z2 z3) := by
  unfold Spec.chunk_inv_ntt_layer_1_step_pure
  -- thread canon + scaled through the 8 steps
  have c1q := chunk_inv_ntt_step_canon q z0 0#usize 2#usize (by decide) (by decide) hq
  have c1p := chunk_inv_ntt_step_canon p z0 0#usize 2#usize (by decide) (by decide) hpc
  have s1 := chunk_inv_ntt_step_scaled c q p z0 0#usize 2#usize (by decide) (by decide) hq hpc hs
  have c2q := chunk_inv_ntt_step_canon _ z0 1#usize 3#usize (by decide) (by decide) c1q
  have c2p := chunk_inv_ntt_step_canon _ z0 1#usize 3#usize (by decide) (by decide) c1p
  have s2 := chunk_inv_ntt_step_scaled c _ _ z0 1#usize 3#usize (by decide) (by decide) c1q c1p s1
  have c3q := chunk_inv_ntt_step_canon _ z1 4#usize 6#usize (by decide) (by decide) c2q
  have c3p := chunk_inv_ntt_step_canon _ z1 4#usize 6#usize (by decide) (by decide) c2p
  have s3 := chunk_inv_ntt_step_scaled c _ _ z1 4#usize 6#usize (by decide) (by decide) c2q c2p s2
  have c4q := chunk_inv_ntt_step_canon _ z1 5#usize 7#usize (by decide) (by decide) c3q
  have c4p := chunk_inv_ntt_step_canon _ z1 5#usize 7#usize (by decide) (by decide) c3p
  have s4 := chunk_inv_ntt_step_scaled c _ _ z1 5#usize 7#usize (by decide) (by decide) c3q c3p s3
  have c5q := chunk_inv_ntt_step_canon _ z2 8#usize 10#usize (by decide) (by decide) c4q
  have c5p := chunk_inv_ntt_step_canon _ z2 8#usize 10#usize (by decide) (by decide) c4p
  have s5 := chunk_inv_ntt_step_scaled c _ _ z2 8#usize 10#usize (by decide) (by decide) c4q c4p s4
  have c6q := chunk_inv_ntt_step_canon _ z2 9#usize 11#usize (by decide) (by decide) c5q
  have c6p := chunk_inv_ntt_step_canon _ z2 9#usize 11#usize (by decide) (by decide) c5p
  have s6 := chunk_inv_ntt_step_scaled c _ _ z2 9#usize 11#usize (by decide) (by decide) c5q c5p s5
  have c7q := chunk_inv_ntt_step_canon _ z3 12#usize 14#usize (by decide) (by decide) c6q
  have c7p := chunk_inv_ntt_step_canon _ z3 12#usize 14#usize (by decide) (by decide) c6p
  have s7 := chunk_inv_ntt_step_scaled c _ _ z3 12#usize 14#usize (by decide) (by decide) c6q c6p s6
  exact chunk_inv_ntt_step_scaled c _ _ z3 13#usize 15#usize (by decide) (by decide) c7q c7p s7

/-- `chunk_inv_ntt_layer_2_step_pure` preserves `ScaledChunk`. -/
private theorem chunk_inv_ntt_layer_2_step_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement)
    (hq : CanonChunk q) (hpc : CanonChunk p) (hs : ScaledChunk c q p) :
    ScaledChunk c (Spec.chunk_inv_ntt_layer_2_step_pure q z0 z1)
      (Spec.chunk_inv_ntt_layer_2_step_pure p z0 z1) := by
  unfold Spec.chunk_inv_ntt_layer_2_step_pure
  have c1q := chunk_inv_ntt_step_canon q z0 0#usize 4#usize (by decide) (by decide) hq
  have c1p := chunk_inv_ntt_step_canon p z0 0#usize 4#usize (by decide) (by decide) hpc
  have s1 := chunk_inv_ntt_step_scaled c q p z0 0#usize 4#usize (by decide) (by decide) hq hpc hs
  have c2q := chunk_inv_ntt_step_canon _ z0 1#usize 5#usize (by decide) (by decide) c1q
  have c2p := chunk_inv_ntt_step_canon _ z0 1#usize 5#usize (by decide) (by decide) c1p
  have s2 := chunk_inv_ntt_step_scaled c _ _ z0 1#usize 5#usize (by decide) (by decide) c1q c1p s1
  have c3q := chunk_inv_ntt_step_canon _ z0 2#usize 6#usize (by decide) (by decide) c2q
  have c3p := chunk_inv_ntt_step_canon _ z0 2#usize 6#usize (by decide) (by decide) c2p
  have s3 := chunk_inv_ntt_step_scaled c _ _ z0 2#usize 6#usize (by decide) (by decide) c2q c2p s2
  have c4q := chunk_inv_ntt_step_canon _ z0 3#usize 7#usize (by decide) (by decide) c3q
  have c4p := chunk_inv_ntt_step_canon _ z0 3#usize 7#usize (by decide) (by decide) c3p
  have s4 := chunk_inv_ntt_step_scaled c _ _ z0 3#usize 7#usize (by decide) (by decide) c3q c3p s3
  have c5q := chunk_inv_ntt_step_canon _ z1 8#usize 12#usize (by decide) (by decide) c4q
  have c5p := chunk_inv_ntt_step_canon _ z1 8#usize 12#usize (by decide) (by decide) c4p
  have s5 := chunk_inv_ntt_step_scaled c _ _ z1 8#usize 12#usize (by decide) (by decide) c4q c4p s4
  have c6q := chunk_inv_ntt_step_canon _ z1 9#usize 13#usize (by decide) (by decide) c5q
  have c6p := chunk_inv_ntt_step_canon _ z1 9#usize 13#usize (by decide) (by decide) c5p
  have s6 := chunk_inv_ntt_step_scaled c _ _ z1 9#usize 13#usize (by decide) (by decide) c5q c5p s5
  have c7q := chunk_inv_ntt_step_canon _ z1 10#usize 14#usize (by decide) (by decide) c6q
  have c7p := chunk_inv_ntt_step_canon _ z1 10#usize 14#usize (by decide) (by decide) c6p
  have s7 := chunk_inv_ntt_step_scaled c _ _ z1 10#usize 14#usize (by decide) (by decide) c6q c6p s6
  exact chunk_inv_ntt_step_scaled c _ _ z1 11#usize 15#usize (by decide) (by decide) c7q c7p s7

/-- `chunk_inv_ntt_layer_3_step_pure` preserves `ScaledChunk`. -/
private theorem chunk_inv_ntt_layer_3_step_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement)
    (hq : CanonChunk q) (hpc : CanonChunk p) (hs : ScaledChunk c q p) :
    ScaledChunk c (Spec.chunk_inv_ntt_layer_3_step_pure q z)
      (Spec.chunk_inv_ntt_layer_3_step_pure p z) := by
  unfold Spec.chunk_inv_ntt_layer_3_step_pure
  have c1q := chunk_inv_ntt_step_canon q z 0#usize 8#usize (by decide) (by decide) hq
  have c1p := chunk_inv_ntt_step_canon p z 0#usize 8#usize (by decide) (by decide) hpc
  have s1 := chunk_inv_ntt_step_scaled c q p z 0#usize 8#usize (by decide) (by decide) hq hpc hs
  have c2q := chunk_inv_ntt_step_canon _ z 1#usize 9#usize (by decide) (by decide) c1q
  have c2p := chunk_inv_ntt_step_canon _ z 1#usize 9#usize (by decide) (by decide) c1p
  have s2 := chunk_inv_ntt_step_scaled c _ _ z 1#usize 9#usize (by decide) (by decide) c1q c1p s1
  have c3q := chunk_inv_ntt_step_canon _ z 2#usize 10#usize (by decide) (by decide) c2q
  have c3p := chunk_inv_ntt_step_canon _ z 2#usize 10#usize (by decide) (by decide) c2p
  have s3 := chunk_inv_ntt_step_scaled c _ _ z 2#usize 10#usize (by decide) (by decide) c2q c2p s2
  have c4q := chunk_inv_ntt_step_canon _ z 3#usize 11#usize (by decide) (by decide) c3q
  have c4p := chunk_inv_ntt_step_canon _ z 3#usize 11#usize (by decide) (by decide) c3p
  have s4 := chunk_inv_ntt_step_scaled c _ _ z 3#usize 11#usize (by decide) (by decide) c3q c3p s3
  have c5q := chunk_inv_ntt_step_canon _ z 4#usize 12#usize (by decide) (by decide) c4q
  have c5p := chunk_inv_ntt_step_canon _ z 4#usize 12#usize (by decide) (by decide) c4p
  have s5 := chunk_inv_ntt_step_scaled c _ _ z 4#usize 12#usize (by decide) (by decide) c4q c4p s4
  have c6q := chunk_inv_ntt_step_canon _ z 5#usize 13#usize (by decide) (by decide) c5q
  have c6p := chunk_inv_ntt_step_canon _ z 5#usize 13#usize (by decide) (by decide) c5p
  have s6 := chunk_inv_ntt_step_scaled c _ _ z 5#usize 13#usize (by decide) (by decide) c5q c5p s5
  have c7q := chunk_inv_ntt_step_canon _ z 6#usize 14#usize (by decide) (by decide) c6q
  have c7p := chunk_inv_ntt_step_canon _ z 6#usize 14#usize (by decide) (by decide) c6p
  have s7 := chunk_inv_ntt_step_scaled c _ _ z 6#usize 14#usize (by decide) (by decide) c6q c6p s6
  exact chunk_inv_ntt_step_scaled c _ _ z 7#usize 15#usize (by decide) (by decide) c7q c7p s7

/-! ### Lift chunk preservation to the 256-array layers 1/2/3. -/

/-- Lane access for a 16-chunk flatten shape: lane `j` of
    `flatten_chunks (make 16 ((range 16).map H))` is `(H (j/16)).val[j%16]!`. -/
private theorem flatten_chunk_map_lane
    (H : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (j : Nat) (hj : j < 256)
    (h : ((List.range 16).map H).length = (16#usize).val) :
    (Spec.flatten_chunks (Std.Array.make 16#usize ((List.range 16).map H) h)).val[j]!
      = (H (j / 16)).val[j % 16]! := by
  have hk : j / 16 < 16 := by omega
  unfold Spec.flatten_chunks
  rw [mkN_map_lane' _ j hj]
  rw [mkN_map_lane' H (j / 16) hk]

/-- A `chunk_step`-mapped layer preserves `CanonArr`, given the chunk step
    preserves `CanonChunk` (with zetas possibly depending on chunk index `k`). -/
private theorem layer_canon_of_chunk_canon
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (G : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize →
         Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (hp : CanonArr p)
    (hG : ∀ (k : Nat) (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize),
            CanonChunk a → CanonChunk (G k a))
    (h : ((List.range 16).map (fun k => G k (Spec.chunk_at p k))).length = (16#usize).val) :
    CanonArr (Spec.flatten_chunks (Std.Array.make 16#usize
        ((List.range 16).map (fun k => G k (Spec.chunk_at p k))) h)) := by
  intro j hj
  rw [flatten_chunk_map_lane (fun k => G k (Spec.chunk_at p k)) j hj h]
  apply hG (j / 16) _ _ (j % 16) (Nat.mod_lt _ (by decide))
  intro ℓ hℓ
  rw [chunk_at_lane' p (j / 16) ℓ hℓ]
  apply hp
  have hk : j / 16 < 16 := by omega
  omega

/-- `chunk_at` of a `CanonArr` is `CanonChunk`. -/
private theorem canonChunk_chunk_at
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hp : CanonArr p) (k : Nat) (hk : k < 16) : CanonChunk (Spec.chunk_at p k) := by
  intro ℓ hℓ
  rw [chunk_at_lane' p k ℓ hℓ]
  exact hp _ (by omega)

/-- `chunk_at` is scale-compatible: `ScaledArr c q p → ScaledChunk c (chunk_at q k) (chunk_at p k)`. -/
private theorem scaledChunk_chunk_at (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hs : ScaledArr c q p) (k : Nat) (hk : k < 16) :
    ScaledChunk c (Spec.chunk_at q k) (Spec.chunk_at p k) := by
  intro ℓ hℓ
  rw [chunk_at_lane' q k ℓ hℓ, chunk_at_lane' p k ℓ hℓ]
  exact hs _ (by omega)

/-- A `chunk_step`-mapped layer preserves `ScaledArr`, given the chunk step
    preserves `ScaledChunk` (using canonicity of both `chunk_at` sides). -/
private theorem layer_scaled_of_chunk_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (G : Nat → Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize →
         Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p)
    (hG : ∀ (k : Nat) (qc pc : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize),
            CanonChunk qc → CanonChunk pc → ScaledChunk c qc pc → ScaledChunk c (G k qc) (G k pc))
    (hlq : ((List.range 16).map (fun k => G k (Spec.chunk_at q k))).length = (16#usize).val)
    (hlp : ((List.range 16).map (fun k => G k (Spec.chunk_at p k))).length = (16#usize).val) :
    ScaledArr c
      (Spec.flatten_chunks (Std.Array.make 16#usize
        ((List.range 16).map (fun k => G k (Spec.chunk_at q k))) hlq))
      (Spec.flatten_chunks (Std.Array.make 16#usize
        ((List.range 16).map (fun k => G k (Spec.chunk_at p k))) hlp)) := by
  intro j hj
  rw [flatten_chunk_map_lane (fun k => G k (Spec.chunk_at q k)) j hj hlq,
      flatten_chunk_map_lane (fun k => G k (Spec.chunk_at p k)) j hj hlp]
  have hk : j / 16 < 16 := by omega
  exact hG (j / 16) _ _
    (canonChunk_chunk_at q hq (j / 16) hk) (canonChunk_chunk_at p hpc (j / 16) hk)
    (scaledChunk_chunk_at c q p hs (j / 16) hk) (j % 16) (Nat.mod_lt _ (by decide))

/-! ### Array-level layers 1/2/3: canon + scaled preservation. -/

private theorem invert_ntt_layer_1_canon
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hp : CanonArr p) :
    CanonArr (Spec.invert_ntt_layer_1_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_1_pure
  exact layer_canon_of_chunk_canon p
    (fun k a => Spec.chunk_inv_ntt_layer_1_step_pure a
      (Spec.zeta_at (zeta_i.val - 4 * k - 1)) (Spec.zeta_at (zeta_i.val - 4 * k - 2))
      (Spec.zeta_at (zeta_i.val - 4 * k - 3)) (Spec.zeta_at (zeta_i.val - 4 * k - 4)))
    hp (fun k a ha => chunk_inv_ntt_layer_1_step_canon a _ _ _ _ ha) _

private theorem invert_ntt_layer_2_canon
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hp : CanonArr p) :
    CanonArr (Spec.invert_ntt_layer_2_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_2_pure
  exact layer_canon_of_chunk_canon p
    (fun k a => Spec.chunk_inv_ntt_layer_2_step_pure a
      (Spec.zeta_at (zeta_i.val - 2 * k - 1)) (Spec.zeta_at (zeta_i.val - 2 * k - 2)))
    hp (fun k a ha => chunk_inv_ntt_layer_2_step_canon a _ _ ha) _

private theorem invert_ntt_layer_3_canon
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hp : CanonArr p) :
    CanonArr (Spec.invert_ntt_layer_3_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_3_pure
  exact layer_canon_of_chunk_canon p
    (fun k a => Spec.chunk_inv_ntt_layer_3_step_pure a (Spec.zeta_at (zeta_i.val - k - 1)))
    hp (fun k a ha => chunk_inv_ntt_layer_3_step_canon a _ ha) _

private theorem invert_ntt_layer_1_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p) :
    ScaledArr c (Spec.invert_ntt_layer_1_pure q zeta_i) (Spec.invert_ntt_layer_1_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_1_pure
  exact layer_scaled_of_chunk_scaled c q p
    (fun k a => Spec.chunk_inv_ntt_layer_1_step_pure a
      (Spec.zeta_at (zeta_i.val - 4 * k - 1)) (Spec.zeta_at (zeta_i.val - 4 * k - 2))
      (Spec.zeta_at (zeta_i.val - 4 * k - 3)) (Spec.zeta_at (zeta_i.val - 4 * k - 4)))
    hq hpc hs (fun k qc pc hqc hpc' hsc =>
      chunk_inv_ntt_layer_1_step_scaled c qc pc _ _ _ _ hqc hpc' hsc) _ _

private theorem invert_ntt_layer_2_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p) :
    ScaledArr c (Spec.invert_ntt_layer_2_pure q zeta_i) (Spec.invert_ntt_layer_2_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_2_pure
  exact layer_scaled_of_chunk_scaled c q p
    (fun k a => Spec.chunk_inv_ntt_layer_2_step_pure a
      (Spec.zeta_at (zeta_i.val - 2 * k - 1)) (Spec.zeta_at (zeta_i.val - 2 * k - 2)))
    hq hpc hs (fun k qc pc hqc hpc' hsc =>
      chunk_inv_ntt_layer_2_step_scaled c qc pc _ _ hqc hpc' hsc) _ _

private theorem invert_ntt_layer_3_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i : Std.Usize) (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p) :
    ScaledArr c (Spec.invert_ntt_layer_3_pure q zeta_i) (Spec.invert_ntt_layer_3_pure p zeta_i) := by
  unfold Spec.invert_ntt_layer_3_pure
  exact layer_scaled_of_chunk_scaled c q p
    (fun k a => Spec.chunk_inv_ntt_layer_3_step_pure a (Spec.zeta_at (zeta_i.val - k - 1)))
    hq hpc hs (fun k qc pc hqc hpc' hsc =>
      chunk_inv_ntt_layer_3_step_scaled c qc pc _ hqc hpc' hsc) _ _

/-! ### Cross-chunk butterflies (layers 4-7). -/

/-- Lane formula for `chunk_inv_pair_butterfly_a_pure`. -/
private theorem chunk_inv_pair_butterfly_a_lane
    (ca cb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_pair_butterfly_a_pure ca cb).val[ℓ]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (ca.val[ℓ]!) (cb.val[ℓ]!) := by
  unfold Spec.chunk_inv_pair_butterfly_a_pure
  exact mkN_map_lane' _ ℓ hℓ _

/-- Lane formula for `chunk_inv_pair_butterfly_b_pure`. -/
private theorem chunk_inv_pair_butterfly_b_lane
    (ca cb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_pair_butterfly_b_pure ca cb z).val[ℓ]!
      = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
            (cb.val[ℓ]!) (ca.val[ℓ]!)) z := by
  unfold Spec.chunk_inv_pair_butterfly_b_pure
  exact mkN_map_lane' _ ℓ hℓ _

private theorem chunk_inv_pair_butterfly_a_canon
    (ca cb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) :
    CanonChunk (Spec.chunk_inv_pair_butterfly_a_pure ca cb) := by
  intro ℓ hℓ
  rw [chunk_inv_pair_butterfly_a_lane ca cb ℓ hℓ]
  exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _

private theorem chunk_inv_pair_butterfly_b_canon
    (ca cb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) :
    CanonChunk (Spec.chunk_inv_pair_butterfly_b_pure ca cb z) := by
  intro ℓ hℓ
  rw [chunk_inv_pair_butterfly_b_lane ca cb z ℓ hℓ]
  exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _

private theorem chunk_inv_pair_butterfly_a_scaled (c : ZMod 3329)
    (qa qb pa pb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (hsa : ScaledChunk c qa pa) (hsb : ScaledChunk c qb pb) :
    ScaledChunk c (Spec.chunk_inv_pair_butterfly_a_pure qa qb)
      (Spec.chunk_inv_pair_butterfly_a_pure pa pb) := by
  intro ℓ hℓ
  rw [chunk_inv_pair_butterfly_a_lane qa qb ℓ hℓ,
      chunk_inv_pair_butterfly_a_lane pa pb ℓ hℓ,
      zmodOfFE_add_pure, zmodOfFE_add_pure, hsa ℓ hℓ, hsb ℓ hℓ]
  ring

private theorem chunk_inv_pair_butterfly_b_scaled (c : ZMod 3329)
    (qa qb pa pb : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement)
    (hqa : CanonChunk qa) (hqb : CanonChunk qb) (hpa : CanonChunk pa) (hpb : CanonChunk pb)
    (hsa : ScaledChunk c qa pa) (hsb : ScaledChunk c qb pb) :
    ScaledChunk c (Spec.chunk_inv_pair_butterfly_b_pure qa qb z)
      (Spec.chunk_inv_pair_butterfly_b_pure pa pb z) := by
  intro ℓ hℓ
  rw [chunk_inv_pair_butterfly_b_lane qa qb z ℓ hℓ,
      chunk_inv_pair_butterfly_b_lane pa pb z ℓ hℓ,
      zmodOfFE_mul_pure, zmodOfFE_mul_pure,
      zmodOfFE_sub_pure _ _ (hqb ℓ hℓ) (hqa ℓ hℓ),
      zmodOfFE_sub_pure _ _ (hpb ℓ hℓ) (hpa ℓ hℓ),
      hsa ℓ hℓ, hsb ℓ hℓ]
  ring

/-! ### Array-level layer 4+ preservation. -/

/-- `chunks0` lane access: `(make 16 (map (chunk_at p))).val[k]! = chunk_at p k`. -/
private theorem chunks0_lane
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (k : Nat) (hk : k < 16)
    (h : ((List.range 16).map (Spec.chunk_at p)).length = (16#usize).val) :
    (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) h).val[k]!
      = Spec.chunk_at p k :=
  mkN_map_lane' (Spec.chunk_at p) k hk h

/-- `chunk_inv_at_layer_4_plus_pure` preserves `CanonChunk` per output chunk. -/
private theorem chunk_inv_at_layer_4_plus_canon
    (chunks : Std.Array (Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize) 16#usize)
    (layer : Std.Usize) (zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement) (cc : Nat) :
    CanonChunk (Spec.chunk_inv_at_layer_4_plus_pure chunks layer zeta_fn cc) := by
  unfold Spec.chunk_inv_at_layer_4_plus_pure
  by_cases h : cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16
  · simp only [h, if_true]
    exact chunk_inv_pair_butterfly_a_canon _ _
  · simp only [h, if_false]
    exact chunk_inv_pair_butterfly_b_canon _ _ _

/-- Body equation for one output chunk of layer 4+ (avoids any nested chunk
    `[!]` in a statement type by phrasing over the `chunks0 = make 16 (map chunk_at)`
    array built from a 256-array `p`). Reduces `chunks0.val[k]!` to `chunk_at p k`.
    Requires `cc < 16` and, in the a-branch, `cc + step < 16` (always true by
    construction; passed in as `hub`). -/
private theorem chunk_inv_at_layer_4_plus_chunks0_eq
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (layer : Std.Usize) (zeta_fn : Nat → hacspec_ml_kem.parameters.FieldElement) (cc : Nat)
    (hcc : cc < 16)
    (hub : cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16 →
            cc + (1 <<< layer.val) / 16 < 16)
    (h : ((List.range 16).map (Spec.chunk_at p)).length = (16#usize).val) :
    Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) h) layer zeta_fn cc
      = if cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16 then
          Spec.chunk_inv_pair_butterfly_a_pure (Spec.chunk_at p cc)
            (Spec.chunk_at p (cc + (1 <<< layer.val) / 16))
        else
          Spec.chunk_inv_pair_butterfly_b_pure (Spec.chunk_at p (cc - (1 <<< layer.val) / 16))
            (Spec.chunk_at p cc) (zeta_fn (cc / (2 * ((1 <<< layer.val) / 16)))) := by
  unfold Spec.chunk_inv_at_layer_4_plus_pure
  by_cases hb : cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16
  · rw [if_pos hb, if_pos hb]
    have hub' : cc + (1 <<< layer.val) / 16 < 16 := hub hb
    rw [chunks0_lane p cc hcc h, chunks0_lane p (cc + (1 <<< layer.val) / 16) hub' h]
  · rw [if_neg hb, if_neg hb]
    have hsub : cc - (1 <<< layer.val) / 16 < 16 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcc
    rw [chunks0_lane p cc hcc h, chunks0_lane p (cc - (1 <<< layer.val) / 16) hsub h]

/-- For `cc < 16`, `2*step ∣ 16`, and `cc % (2*step) < step`, we have
    `cc + step < 16` (the partner chunk stays in range). -/
private theorem layer4_partner_lt
    (cc step : Nat) (hcc : cc < 16) (_hstep : 0 < step) (hdvd : (2 * step) ∣ 16)
    (hoff : cc % (2 * step) < step) : cc + step < 16 := by
  obtain ⟨t, ht⟩ := hdvd
  set Q := cc / (2 * step) with hQ
  set r := cc % (2 * step) with hr
  have ht16 : (2 * step) * t = 16 := ht.symm
  have hblock : Q < t := by
    apply Nat.div_lt_of_lt_mul; rw [ht16]; exact hcc
  have hdm : cc = (2 * step) * Q + r := (Nat.div_add_mod cc (2 * step)).symm
  calc cc + step < (2 * step) * Q + 2 * step := by omega
    _ = (2 * step) * (Q + 1) := by ring
    _ ≤ (2 * step) * t := by apply Nat.mul_le_mul_left; omega
    _ = 16 := ht16

/-- `invert_ntt_layer_4_plus_pure` preserves `CanonArr`. -/
private theorem invert_ntt_layer_4_plus_canon
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i layer : Std.Usize) (_hp : CanonArr p) :
    CanonArr (Spec.invert_ntt_layer_4_plus_pure p zeta_i layer) := by
  intro j hj
  unfold Spec.invert_ntt_layer_4_plus_pure
  rw [flatten_chunk_map_lane (fun cc => Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) (by simp))
        layer (fun group => Spec.zeta_at (zeta_i.val - 1 - group)) cc) j hj (by simp)]
  apply chunk_inv_at_layer_4_plus_canon _ _ _ _ (j % 16) (Nat.mod_lt _ (by decide))

/-- Scaled-preservation of one output chunk of layer 4+, phrased over 256-arrays
    `q p` and chunk index `cc` (uses `chunk_inv_at_layer_4_plus_chunks0_eq`). -/
private theorem chunk_inv_at_layer_4_plus_scaled_chunks0 (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (layer : Std.Usize) (zfn : Nat → hacspec_ml_kem.parameters.FieldElement) (cc : Nat)
    (hcc : cc < 16)
    (hub : cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16 →
            cc + (1 <<< layer.val) / 16 < 16)
    (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p)
    (hqlen : ((List.range 16).map (Spec.chunk_at q)).length = (16#usize).val)
    (hplen : ((List.range 16).map (Spec.chunk_at p)).length = (16#usize).val) :
    ScaledChunk c
      (Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at q)) hqlen) layer zfn cc)
      (Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) hplen) layer zfn cc) := by
  rw [chunk_inv_at_layer_4_plus_chunks0_eq q layer zfn cc hcc hub hqlen,
      chunk_inv_at_layer_4_plus_chunks0_eq p layer zfn cc hcc hub hplen]
  by_cases hbr : cc % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16
  · rw [if_pos hbr, if_pos hbr]
    have hub' := hub hbr
    exact chunk_inv_pair_butterfly_a_scaled c _ _ _ _
      (scaledChunk_chunk_at c q p hs cc hcc)
      (scaledChunk_chunk_at c q p hs _ hub')
  · rw [if_neg hbr, if_neg hbr]
    have hsub : cc - (1 <<< layer.val) / 16 < 16 := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hcc
    exact chunk_inv_pair_butterfly_b_scaled c _ _ _ _ _
      (canonChunk_chunk_at q hq _ hsub) (canonChunk_chunk_at q hq cc hcc)
      (canonChunk_chunk_at p hpc _ hsub) (canonChunk_chunk_at p hpc cc hcc)
      (scaledChunk_chunk_at c q p hs _ hsub)
      (scaledChunk_chunk_at c q p hs cc hcc)

/-- `invert_ntt_layer_4_plus_pure` preserves `ScaledArr`, given the step
    `(1<<<layer)/16` is positive and `2*step ∣ 16` (true for layers 4-7). -/
private theorem invert_ntt_layer_4_plus_scaled (c : ZMod 3329)
    (q p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i layer : Std.Usize)
    (hstep : 0 < (1 <<< layer.val) / 16) (hdvd : (2 * ((1 <<< layer.val) / 16)) ∣ 16)
    (hq : CanonArr q) (hpc : CanonArr p) (hs : ScaledArr c q p) :
    ScaledArr c (Spec.invert_ntt_layer_4_plus_pure q zeta_i layer)
      (Spec.invert_ntt_layer_4_plus_pure p zeta_i layer) := by
  intro j hj
  unfold Spec.invert_ntt_layer_4_plus_pure
  rw [flatten_chunk_map_lane (fun cc => Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at q)) (by simp)) layer
        (fun group => Spec.zeta_at (zeta_i.val - 1 - group)) cc) j hj (by simp),
      flatten_chunk_map_lane (fun cc => Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at p)) (by simp)) layer
        (fun group => Spec.zeta_at (zeta_i.val - 1 - group)) cc) j hj (by simp)]
  have hcc : j / 16 < 16 := by omega
  have hub : (j / 16) % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16 →
      (j / 16) + (1 <<< layer.val) / 16 < 16 :=
    fun hoff => layer4_partner_lt (j / 16) _ hcc hstep hdvd hoff
  exact chunk_inv_at_layer_4_plus_scaled_chunks0 c q p layer _ (j / 16) hcc hub hq hpc hs _ _
    (j % 16) (Nat.mod_lt _ (by decide))

/-! ### Final assembly. -/

/-- `feOfZMod z` is canonical. -/
private theorem canon_feOfZMod (z : ZMod 3329) : Canonical (feOfZMod z) := by
  unfold Canonical feOfZMod hacspec_ml_kem.parameters.FIELD_MODULUS
  show (BitVec.ofNat 16 z.val).toNat < _
  rw [BitVec.toNat_ofNat]
  have hz : z.val < 3329 := ZMod.val_lt z
  have : z.val % 2 ^ 16 = z.val := Nat.mod_eq_of_lt (by omega)
  simp only [this]; simpa using hz

/-- `scaleZ c p` is canonical (every lane is `feOfZMod _`). -/
private theorem canonArr_scaleZ (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    CanonArr (scaleZ c p) := by
  intro j hj
  unfold scaleZ
  rw [mkN_map_lane' (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))) j hj _]
  exact canon_feOfZMod _

/-- `scaleZ c p` is the per-lane `c`-scale of `p`. -/
private theorem scaledArr_scaleZ (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    ScaledArr c (scaleZ c p) p := fun j hj => scaleZ_lane c p j hj

/-- Two canonical 256-arrays that are both the per-lane `c`-scale of the same `p`
    are equal. -/
private theorem eq_of_scaledArr_canon (c : ZMod 3329)
    (a b p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hca : CanonArr a) (hcb : CanonArr b)
    (hsa : ScaledArr c a p) (hsb : ScaledArr c b p) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [Aeneas.Std.Array.length_eq a, Aeneas.Std.Array.length_eq b]
  · intro j hj1 _hj2
    have hj : j < 256 := by rw [Aeneas.Std.Array.length_eq a] at hj1; simpa using hj1
    have hca' := hca j hj
    have hcb' := hcb j hj
    have hzeq : zmodOfFE (a.val[j]!) = zmodOfFE (b.val[j]!) := by
      rw [hsa j hj, hsb j hj]
    have ha := feOfZMod_zmodOfFE_of_canon (a.val[j]!) hca'
    have hb := feOfZMod_zmodOfFE_of_canon (b.val[j]!) hcb'
    have : a.val[j]! = b.val[j]! := by rw [← ha, ← hb, hzeq]
    have haj : a.val[j]! = a.val[j] := getElem!_pos a.val j (by rw [Aeneas.Std.Array.length_eq a]; exact hj)
    have hbj : b.val[j]! = b.val[j] := getElem!_pos b.val j (by rw [Aeneas.Std.Array.length_eq b]; exact hj)
    rw [← haj, ← hbj]; exact this

theorem invert_ntt_montgomery_pure_scaleZ (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hp : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical (p.val[j]!)) :
    Spec.invert_ntt_montgomery_pure (scaleZ c p)
      = scaleZ c (Spec.invert_ntt_montgomery_pure p) := by
  -- divisibility / positivity facts for layers 4-7 (step = 2^layer/16)
  have hl4 : (0 < (1 <<< (4#usize).val) / 16) ∧ ((2 * ((1 <<< (4#usize).val) / 16)) ∣ 16) := by
    constructor <;> decide
  have hl5 : (0 < (1 <<< (5#usize).val) / 16) ∧ ((2 * ((1 <<< (5#usize).val) / 16)) ∣ 16) := by
    constructor <;> decide
  have hl6 : (0 < (1 <<< (6#usize).val) / 16) ∧ ((2 * ((1 <<< (6#usize).val) / 16)) ∣ 16) := by
    constructor <;> decide
  have hl7 : (0 < (1 <<< (7#usize).val) / 16) ∧ ((2 * ((1 <<< (7#usize).val) / 16)) ∣ 16) := by
    constructor <;> decide
  -- canonicity of the scaleZ side input
  have hpq : CanonArr (scaleZ c p) := canonArr_scaleZ c p
  have hpp : CanonArr p := hp
  have hs0 : ScaledArr c (scaleZ c p) p := scaledArr_scaleZ c p
  -- Unfold the 7-layer composition on both sides simultaneously.
  unfold Spec.invert_ntt_montgomery_pure
  -- q-side intermediates (scaled input), p-side intermediates (plain input).
  -- Thread canon + scaled through layers 1,2,3,4,5,6,7.
  have c1q := invert_ntt_layer_1_canon (scaleZ c p) 128#usize hpq
  have c1p := invert_ntt_layer_1_canon p 128#usize hpp
  have s1 := invert_ntt_layer_1_scaled c (scaleZ c p) p 128#usize hpq hpp hs0
  have c2q := invert_ntt_layer_2_canon _ 64#usize c1q
  have c2p := invert_ntt_layer_2_canon _ 64#usize c1p
  have s2 := invert_ntt_layer_2_scaled c _ _ 64#usize c1q c1p s1
  have c3q := invert_ntt_layer_3_canon _ 32#usize c2q
  have c3p := invert_ntt_layer_3_canon _ 32#usize c2p
  have s3 := invert_ntt_layer_3_scaled c _ _ 32#usize c2q c2p s2
  have c4q := invert_ntt_layer_4_plus_canon _ 16#usize 4#usize c3q
  have c4p := invert_ntt_layer_4_plus_canon _ 16#usize 4#usize c3p
  have s4 := invert_ntt_layer_4_plus_scaled c _ _ 16#usize 4#usize hl4.1 hl4.2 c3q c3p s3
  have c5q := invert_ntt_layer_4_plus_canon _ 8#usize 5#usize c4q
  have c5p := invert_ntt_layer_4_plus_canon _ 8#usize 5#usize c4p
  have s5 := invert_ntt_layer_4_plus_scaled c _ _ 8#usize 5#usize hl5.1 hl5.2 c4q c4p s4
  have c6q := invert_ntt_layer_4_plus_canon _ 4#usize 6#usize c5q
  have c6p := invert_ntt_layer_4_plus_canon _ 4#usize 6#usize c5p
  have s6 := invert_ntt_layer_4_plus_scaled c _ _ 4#usize 6#usize hl6.1 hl6.2 c5q c5p s5
  have c7q := invert_ntt_layer_4_plus_canon _ 2#usize 7#usize c6q
  have c7p := invert_ntt_layer_4_plus_canon _ 2#usize 7#usize c6p
  have s7 := invert_ntt_layer_4_plus_scaled c _ _ 2#usize 7#usize hl7.1 hl7.2 c6q c6p s6
  -- The RHS `scaleZ c (invert p)` is also `c`-scaled vs `invert p`, and canonical.
  exact eq_of_scaledArr_canon c _ _ _ c7q (canonArr_scaleZ c _) s7 (scaledArr_scaleZ c _)

end InvertScaleZ

/-! ## C — hacspec `ntt_inverse` ≡ `scaleZ 3303 ∘ invert_ntt_montgomery_pure`.

    `3303 = INVERSE_OF_128 = 512·169`. Decomposed into:

    * **C1** — `ntt_inverse p = scaleZ 3303 (ntt_inverse_butterflies p)`: the
      `reduce_polynomial` createi wrapper multiplying every lane by
      `INVERSE_OF_128 = 3303`.
    * **C2** — `ntt_inverse_butterflies p = .ok (invert_ntt_montgomery_pure p)`:
      the hacspec 7-layer plain-field Gentleman–Sande inverse equals the
      Mont-domain pure 7-layer inverse (the Montgomery `R`-factors net to 1).

    Canonical precondition (same mechanism as `invert_ntt_montgomery_pure_scaleZ`:
    `sub_pure` saturates on non-canonical lanes). Discharged at the L7.4 call
    site: C is applied at `p = multiply_vectors …`, whose lanes are
    `add_pure`/`mul_pure` results (canonical). -/
section InvertReduceC1

open libcrux_iot_ml_kem.Spec.Pure (Canonical)
/-- The `INVERSE_OF_128 = FieldElement.new 3303` FE has `zmodOfFE = 3303`. -/
private theorem zmodOfFE_inverse_of_128 :
    zmodOfFE (⟨3303#u16⟩ : hacspec_ml_kem.parameters.FieldElement) = (3303 : ZMod 3329) := by
  unfold zmodOfFE
  show ((3303#u16 : Std.U16).val : ZMod 3329) = 3303
  norm_num

set_option maxHeartbeats 1000000 in
/-- `reduce_polynomial a` reduces to the per-lane `mul_pure a[k] 3303` array. -/
private theorem reduce_polynomial_eq_ok
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) :
    hacspec_ml_kem.invert_ntt.reduce_polynomial a
      = .ok ⟨(List.range 256).map (fun k =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (a.val[k]!) ⟨3303#u16⟩),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun k => libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (a.val[k]!) ⟨3303#u16⟩ with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.invert_ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            a ⟨BitVec.ofNat _ k⟩
        = .ok (f k, a) := by
    intro k hk
    have hk' : k < 256 := hk
    show hacspec_ml_kem.invert_ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        a ⟨BitVec.ofNat _ k⟩ = .ok (f k, a)
    unfold hacspec_ml_kem.invert_ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold hacspec_ml_kem.invert_ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have ha_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < a.length := by
      rw [hk_us]; show k < a.val.length
      rw [a.property]; exact hk
    have h_a_idx :
        Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (a.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a
                  (⟨BitVec.ofNat _ k⟩ : Std.Usize) ha_len
      rw [hk_us] at this; exact this
    have h_inv : hacspec_ml_kem.invert_ntt.INVERSE_OF_128
        = .ok (⟨3303#u16⟩ : hacspec_ml_kem.parameters.FieldElement) := by
      unfold hacspec_ml_kem.invert_ntt.INVERSE_OF_128
        hacspec_ml_kem.parameters.FieldElement.new
      rfl
    have h_mul :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_eq_ok
        (a.val[k]!) (⟨3303#u16⟩ : hacspec_ml_kem.parameters.FieldElement)
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
        let fe1 ← hacspec_ml_kem.invert_ntt.INVERSE_OF_128
        hacspec_ml_kem.parameters.FieldElement.mul fe fe1)
      Result.ok (fe, a)) = Result.ok (f k, a)
    rw [h_a_idx]; simp only [bind_tc_ok]
    rw [h_inv]; simp only [bind_tc_ok]
    rw [h_mul]; simp only [bind_tc_ok, hf_def]
  unfold hacspec_ml_kem.invert_ntt.reduce_polynomial
  exact libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq 256#usize
    hacspec_ml_kem.invert_ntt.reduce_polynomial.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
    a f hpure

/-- **C1.** Given the butterflies output `q`, `ntt_inverse p = scaleZ 3303 q`
    (the `reduce_polynomial` wrapper multiplies every lane by
    `INVERSE_OF_128 = 3303`). Requires `q` canonical (so `scaleZ 3303 q` matches
    the `mul_pure`-reduced lanes; the reduced lanes are canonical by `mul_pure`). -/
private theorem ntt_inverse_reduce_eq
    (p q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (_hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!))
    (hbut : hacspec_ml_kem.invert_ntt.ntt_inverse_butterflies p = .ok q) :
    hacspec_ml_kem.invert_ntt.ntt_inverse p = .ok (scaleZ 3303 q) := by
  unfold hacspec_ml_kem.invert_ntt.ntt_inverse
  rw [hbut]; simp only [bind_tc_ok]
  rw [reduce_polynomial_eq_ok q]
  congr 1
  set L : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    ⟨(List.range 256).map (fun k =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (q.val[k]!) ⟨3303#u16⟩),
     by simp [List.length_map, List.length_range]⟩ with hL_def
  have hL_lane : ∀ j : Nat, j < 256 →
      L.val[j]! = libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                    (q.val[j]!) ⟨3303#u16⟩ := by
    intro j hj
    show ((List.range 256).map (fun k =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
              (q.val[k]!) ⟨3303#u16⟩))[j]! = _
    rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
    rw [List.getElem_map, List.getElem_range]
  -- Both `L` and `scaleZ 3303 q` are the per-lane `3303`-scale of `q`; finish via
  -- `eq_of_scaledArr_canon` (both canonical, both `ScaledArr 3303 · q`).
  refine eq_of_scaledArr_canon 3303 L (scaleZ 3303 q) q ?_ (canonArr_scaleZ 3303 q) ?_
    (scaledArr_scaleZ 3303 q)
  · -- L lanes canonical
    intro j hj
    rw [hL_lane j hj]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _
  · -- L is `ScaledArr 3303 L q`
    intro j hj
    rw [hL_lane j hj, zmodOfFE_mul_pure, zmodOfFE_inverse_of_128]
    ring

end InvertReduceC1

/-! ## C2 — hacspec `ntt_inverse_butterflies` ≡ `Spec.invert_ntt_montgomery_pure`
    (factor 1).

    Closed by `ntt_inverse_butterflies_eq_invert_pure`: per-layer flat↔chunk
    match (`ntt_inverse_layer` createi reduction + flat-lane
    `i ↔ chunk (i/16, i%16)` correspondence + the cross-chunk layers 4-7), then
    composing 7 layers; lemma C (`ntt_inverse_eq_scaleZ_invert_pure`) is C1 ∘ C2.

    `zetas_bridge_zmod` below is the gating arithmetic shared by every layer:
    the hacspec plain-domain zeta table `ntt.ZETAS[i]` matches the Mont-domain
    `Spec.zeta_at i` in `ZMod 3329` (`ZETAS[i] ≡ ZETAS_TIMES_MONTGOMERY_R[i]·R⁻¹`,
    `R⁻¹ = 169`); proven by `interval_cases … <;> rfl` after unfolding both
    tables. -/
section InvertButterfliesC2

open libcrux_iot_ml_kem.Spec.Pure (Canonical)
/-- The hacspec `ntt.ZETAS` table, unwrapped from `Result`. `ntt.ZETAS` is a
    pure `do`-chain of `FieldElement.new` (all `.ok`), so this is `.ok`-total;
    the fallback branch is unreachable. -/
private noncomputable def zetasArr :
    Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize :=
  match hacspec_ml_kem.ntt.ZETAS with
  | .ok a => a
  | _ => Std.Array.make 128#usize (List.replicate 128 ⟨0#u16⟩) (by simp)

set_option maxRecDepth 20000 in
private theorem ntt_zetas_eq_ok : hacspec_ml_kem.ntt.ZETAS = .ok zetasArr := by
  unfold zetasArr
  unfold hacspec_ml_kem.ntt.ZETAS
  rfl

set_option maxRecDepth 20000 in
/-- **C2 gating arithmetic.** Per-entry equality (in `ZMod 3329`) of the hacspec
    plain-domain zeta table and the Mont-domain `Spec.zeta_at`. Proven over all
    128 entries by case split + `rfl` (each entry: `ZETAS[i] = ZTMR[i]·169 mod q`). -/
private theorem zetas_bridge_zmod (i : Nat) (hi : i < 128) :
    zmodOfFE (zetasArr.val[i]!) = zmodOfFE (Spec.zeta_at i) := by
  unfold zetasArr Spec.zeta_at lift_fe_mont
  rw [zmodOfFE_feOfZMod]
  unfold zmodOfFE i16_to_spec_fe_mont
  unfold hacspec_ml_kem.ntt.ZETAS
  unfold hacspec_ml_kem.parameters.FieldElement.new
  simp only [bind_tc_ok]
  unfold libcrux_iot_ml_kem.polynomial.ZETAS_TIMES_MONTGOMERY_R
  interval_cases i <;> rfl

/-! ### C2 : flat per-lane reduction of `ntt_inverse_layer_n`.

    The monadic usize arithmetic in the hacspec body is discharged via
    `*_ok'` helpers (Aeneas `*_spec` Triples → `.ok`-exists), and the
    `inv_butterfly` is reduced to its `add_pure`/`mul_pure`-of-`sub_pure`
    pure projection (`inv_butterfly_eq`). The per-lane closure value
    (`layer_n_at_eq`) feeds `from_fn_pure_eq` to give the full layer's
    explicit per-lane array (`ntt_inverse_layer_n_eq_ok`). -/

private theorem umul_ok' (a b : Std.Usize) (h : a.val * b.val ≤ Std.Usize.max) :
    ∃ c : Std.Usize, (a * b : Result Std.Usize) = .ok c ∧ c.val = a.val * b.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.mul_spec h)
  exact ⟨v, hv, by simpa using hpv⟩

private theorem uadd_ok' (a b : Std.Usize) (h : a.val + b.val ≤ Std.Usize.max) :
    ∃ c : Std.Usize, (a + b : Result Std.Usize) = .ok c ∧ c.val = a.val + b.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.add_spec h)
  exact ⟨v, hv, by simpa using hpv⟩

private theorem usub_ok' (a b : Std.Usize) (h : b.val ≤ a.val) :
    ∃ c : Std.Usize, (a - b : Result Std.Usize) = .ok c ∧ c.val = a.val - b.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.sub_spec h)
  refine ⟨v, hv, ?_⟩
  have := hpv.1; simpa using this

private theorem udiv_ok' (a b : Std.Usize) (h : b.val ≠ 0) :
    ∃ c : Std.Usize, (a / b : Result Std.Usize) = .ok c ∧ c.val = a.val / b.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.div_spec a h)
  exact ⟨v, hv, by simpa using hpv⟩

private theorem umod_ok' (a b : Std.Usize) (h : b.val ≠ 0) :
    ∃ c : Std.Usize, (a % b : Result Std.Usize) = .ok c ∧ c.val = a.val % b.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.rem_spec a h)
  exact ⟨v, hv, by simpa using hpv⟩

/-- `inv_butterfly z a b` pure projection: `(add a b, mul z (sub b a))`
    (requires `a`, `b` canonical for the `sub`). -/
private theorem inv_butterfly_eq (z a b : hacspec_ml_kem.parameters.FieldElement)
    (ha : Canonical a) (hb : Canonical b) :
    hacspec_ml_kem.invert_ntt.inv_butterfly z a b
    = .ok (libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure a b,
           libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure z
             (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure b a)) := by
  unfold hacspec_ml_kem.invert_ntt.inv_butterfly
  rw [libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_eq_ok a b]
  simp only [bind_tc_ok]
  rw [libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_eq_ok b a hb ha]
  simp only [bind_tc_ok]
  rw [libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_eq_ok z _]
  simp only [bind_tc_ok]

set_option maxRecDepth 8000 in
/-- Per-lane value of `ntt_inverse_layer_n_at p len s i`: the flat
    Gentleman–Sande butterfly. `group = i/(2·len)`, `idx = i%(2·len)`;
    a-side (`idx < len`) = `add p[i] p[i+len]`, b-side =
    `mul s[group] (sub p[i] p[i−len])`. -/
private theorem layer_n_at_eq
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (len : Std.Usize) (s : Slice hacspec_ml_kem.parameters.FieldElement)
    (i : Std.Usize)
    (hlen : 0 < len.val) (h2len : 2 * len.val ≤ Std.Usize.max)
    (hi : i.val < 256) (hil : i.val + len.val ≤ Std.Usize.max)
    (hcanon : ∀ j : Nat, j < 256 → Canonical (p.val[j]!))
    (hsg : i.val / (2 * len.val) < s.val.length)
    (hapart : i.val % (2*len.val) < len.val → i.val + len.val < 256)
    (hbpart : ¬ (i.val % (2*len.val) < len.val) → len.val ≤ i.val) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n_at p len s i
      = .ok (if i.val % (2*len.val) < len.val then
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (p.val[i.val]!) (p.val[i.val + len.val]!)
            else
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (s.val[i.val / (2*len.val)]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (p.val[i.val]!) (p.val[i.val - len.val]!))) := by
  unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n_at
  obtain ⟨i1, hi1, hi1v⟩ := umul_ok' 2#usize len (by simpa using h2len)
  rw [hi1]; simp only [bind_tc_ok]
  have hi1ne : i1.val ≠ 0 := by rw [hi1v]; simp; omega
  obtain ⟨grp, hgrp, hgrpv⟩ := udiv_ok' i i1 hi1ne
  rw [hgrp]; simp only [bind_tc_ok]
  obtain ⟨idx, hidx, hidxv⟩ := umod_ok' i i1 hi1ne
  rw [hidx]; simp only [bind_tc_ok]
  have hidxlen : (idx.val < len.val) = (i.val % (2*len.val) < len.val) := by
    rw [hidxv, hi1v]; simp
  have hdec : (idx < len) = (idx.val < len.val) := by
    simp [Std.UScalar.lt_equiv]
  by_cases hbr : idx.val < len.val
  · rw [if_pos (by rw [hdec]; exact hbr : idx < len)]
    have hbr' : i.val % (2*len.val) < len.val := by rw [← hidxlen]; exact hbr
    rw [if_pos hbr']
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq s grp (by rw [hgrpv, hi1v]; exact hsg)]
    simp only [bind_tc_ok]
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq p i
        (by show i.val < p.val.length; rw [p.property]; exact hi)]
    simp only [bind_tc_ok]
    obtain ⟨i2, hi2, hi2v⟩ := uadd_ok' i len (by simpa using hil)
    rw [hi2]; simp only [bind_tc_ok]
    have hi2lt : i2.val < 256 := by rw [hi2v]; exact hapart hbr'
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq p i2
        (by show i2.val < p.val.length; rw [p.property]; exact hi2lt)]
    simp only [bind_tc_ok]
    rw [inv_butterfly_eq _ _ _ (hcanon i.val hi) (hcanon i2.val hi2lt)]
    simp only [bind_tc_ok, hi2v]
    rfl
  · rw [if_neg (by rw [hdec]; exact hbr : ¬ (idx < len))]
    have hbr' : ¬ (i.val % (2*len.val) < len.val) := by rw [← hidxlen]; exact hbr
    rw [if_neg hbr']
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.slice_index_usize_ok_eq s grp (by rw [hgrpv, hi1v]; exact hsg)]
    simp only [bind_tc_ok]
    obtain ⟨i2, hi2, hi2v⟩ := usub_ok' i len (hbpart hbr')
    rw [hi2]; simp only [bind_tc_ok]
    have hi2lt : i2.val < 256 := by rw [hi2v]; omega
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq p i2
        (by show i2.val < p.val.length; rw [p.property]; exact hi2lt)]
    simp only [bind_tc_ok]
    rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq p i
        (by show i.val < p.val.length; rw [p.property]; exact hi)]
    simp only [bind_tc_ok]
    rw [inv_butterfly_eq _ _ _ (hcanon i2.val hi2lt) (hcanon i.val hi)]
    simp only [bind_tc_ok, hgrpv, hi1v, hi2v]
    norm_num

set_option maxHeartbeats 1000000 in
/-- Full per-layer reduction of `ntt_inverse_layer_n p len s` to an explicit
    per-lane array (createi → `createi_pure_eq` over `layer_n_at_eq`). The
    `hslen`/`hpart` hypotheses package the slice-bound + partner-in-range facts
    for all 256 lanes (discharged per concrete layer downstream). -/
private theorem ntt_inverse_layer_n_eq_ok
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (len : Std.Usize) (s : Slice hacspec_ml_kem.parameters.FieldElement)
    (hlen : 0 < len.val) (h2len : 2 * len.val ≤ Std.Usize.max)
    (hlen256 : len.val ≤ 128)
    (hcanon : ∀ j : Nat, j < 256 → Canonical (p.val[j]!))
    (hslen : ∀ i : Nat, i < 256 → i / (2 * len.val) < s.val.length)
    (hpart : ∀ i : Nat, i < 256 → (i % (2*len.val) < len.val → i + len.val < 256)
                                ∧ (¬ (i % (2*len.val) < len.val) → len.val ≤ i)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n p len s
      = .ok ⟨(List.range 256).map (fun i =>
              if i % (2*len.val) < len.val then
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (p.val[i]!) (p.val[i + len.val]!)
              else
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (s.val[i / (2*len.val)]!)
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                    (p.val[i]!) (p.val[i - len.val]!))),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun i =>
      if i % (2*len.val) < len.val then
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
          (p.val[i]!) (p.val[i + len.val]!)
      else
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
          (s.val[i / (2*len.val)]!)
          (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
            (p.val[i]!) (p.val[i - len.val]!)) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        256#usize : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            (p, len, s) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (p, len, s)) := by
    intro k hk
    have hk' : k < 256 := hk
    show hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        (p, len, s) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (p, len, s))
    unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      rw [Std.UScalarTy.Usize_numBits_eq]
      have hbits : 2^16 ≤ 2^System.Platform.numBits :=
        Nat.pow_le_pow_right (by decide) (by
          cases System.Platform.numBits_eq with
          | inl h => rw [h]; decide
          | inr h => rw [h]; decide)
      omega
    have hmaxb : (384:Nat) ≤ Std.Usize.max := by scalar_tac
    have hilk : k + len.val ≤ Std.Usize.max := by omega
    show (do
        let fe ← hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n_at p len s ⟨BitVec.ofNat _ k⟩
        Result.ok (fe, (p, len, s))) = _
    have hlat := layer_n_at_eq p len s ⟨BitVec.ofNat _ k⟩ hlen h2len (by rw [hk_us]; exact hk')
          (by rw [hk_us]; exact hilk) hcanon
          (by rw [hk_us]; exact hslen k hk') (by rw [hk_us]; exact (hpart k hk').1)
          (by rw [hk_us]; exact (hpart k hk').2)
    rw [hlat]
    simp only [bind_tc_ok, hk_us, hf_def]
    rfl
  unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n
  exact libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq 256#usize
    (hacspec_ml_kem.invert_ntt.ntt_inverse_layer_n.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement 256#usize)
    (p, len, s) f hpure

/-! ### C2 : `ntt_inverse_layer` (zetas createi + range-slice) reduction.

    `ntt_inverse_layer p layer` builds `zetas = createi 128 (closure) groups`
    (per-index `g`, `ntt_inverse_layer_zeta groups g`), slices `s = zetas[0:groups]`,
    and feeds `s` to `ntt_inverse_layer_n p len s`. We reduce the whole thing to an
    explicit flat per-lane array using the global `zetasArr` table:
    b-side lane `i` reads `zetasArr[2·groups − 1 − i/(2·len)]`. -/

/-- `BitVec.ofNat _ k` round-trips through `Usize.val` when `k < 256` (local copy). -/
private theorem usize_ofNat_val_eq_self_of_lt_256' (k : Nat) (h : k < 256) :
    (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
  show (BitVec.ofNat System.Platform.numBits k).toNat = k
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have h_max : k ≤ Std.Usize.max := by scalar_tac
  have h_max_def : Std.Usize.max + 1 = 2 ^ System.Platform.numBits := by scalar_tac
  omega

set_option maxRecDepth 8000 in
/-- The `zetas` createi inside `ntt_inverse_layer` reduces to an explicit array:
    lane `g` is `ntt_inverse_layer_zeta groups ⟨g⟩` (i.e. `zetasArr[2·groups−1−g]`
    when `g < groups`). Requires `groups ≤ 64` (true for layers 1-7, `len ≥ 2`). -/
private theorem ntt_inverse_layer_zetas_eq_ok (groups : Std.Usize)
    (hgroups : groups.val ≤ 64) :
    (hacspec_ml_kem.parameters.createi 128#usize
      hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
      groups)
      = .ok ⟨(List.range 128).map (fun g =>
              if g < groups.val then zetasArr.val[2 * groups.val - 1 - g]!
              else (⟨0#u16⟩ : hacspec_ml_kem.parameters.FieldElement)),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun g => if g < groups.val then zetasArr.val[2 * groups.val - 1 - g]!
             else (⟨0#u16⟩ : hacspec_ml_kem.parameters.FieldElement) with hf_def
  have hpure : ∀ g : Nat, g < (128#usize : Std.Usize).val →
      (hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            groups ⟨BitVec.ofNat _ g⟩
        = .ok (f g, groups) := by
    intro g hg
    have hg' : g < 128 := hg
    show hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        groups ⟨BitVec.ofNat _ g⟩ = .ok (f g, groups)
    unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hg_us : (⟨BitVec.ofNat _ g⟩ : Std.Usize).val = g :=
      usize_ofNat_val_eq_self_of_lt_256' g (by omega)
    show (do
        let fe ← hacspec_ml_kem.invert_ntt.ntt_inverse_layer_zeta groups ⟨BitVec.ofNat _ g⟩
        Result.ok (fe, groups)) = _
    unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer_zeta
    by_cases hbr : (⟨BitVec.ofNat _ g⟩ : Std.Usize) < groups
    · have hbr' : g < groups.val := by
        have := (Std.UScalar.lt_equiv (⟨BitVec.ofNat _ g⟩ : Std.Usize) groups).mp hbr
        rw [hg_us] at this; exact this
      rw [if_pos hbr]
      rw [ntt_zetas_eq_ok]; simp only [bind_tc_ok]
      have h2us : (2#usize : Std.Usize).val = 2 := by scalar_tac
      have h1us : (1#usize : Std.Usize).val = 1 := by scalar_tac
      obtain ⟨i1, hi1, hi1v⟩ := umul_ok' 2#usize groups (by
        show (2#usize : Std.Usize).val * groups.val ≤ Std.Usize.max
        have hm : (128:Nat) ≤ Std.Usize.max := by scalar_tac
        rw [h2us]; omega)
      rw [hi1]; simp only [bind_tc_ok]
      obtain ⟨i2, hi2, hi2v⟩ := usub_ok' i1 1#usize (by
        show (1#usize : Std.Usize).val ≤ i1.val; rw [hi1v, h1us, h2us]; omega)
      rw [hi2]; simp only [bind_tc_ok]
      obtain ⟨i3, hi3, hi3v⟩ := usub_ok' i2 ⟨BitVec.ofNat _ g⟩ (by
        show (⟨BitVec.ofNat _ g⟩ : Std.Usize).val ≤ i2.val
        rw [hi2v, hi1v, h1us, h2us, hg_us]; omega)
      rw [hi3]; simp only [bind_tc_ok]
      have h128us : (128#usize : Std.Usize).val = 128 := by scalar_tac
      have hi3lt : i3.val < zetasArr.val.length := by
        rw [zetasArr.property, h128us, hi3v, hi2v, hi1v, h1us, h2us, hg_us]; omega
      rw [libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq zetasArr i3 hi3lt]
      simp only [bind_tc_ok, hf_def, if_pos hbr', hi3v, hi2v, hi1v, h1us, h2us, hg_us]
    · have hbr' : ¬ (g < groups.val) := by
        intro hc
        exact hbr ((Std.UScalar.lt_equiv (⟨BitVec.ofNat _ g⟩ : Std.Usize) groups).mpr (by
          rw [hg_us]; exact hc))
      rw [if_neg hbr]
      show (do
          let fe ← hacspec_ml_kem.parameters.FieldElement.new 0#u16
          Result.ok (fe, groups)) = _
      unfold hacspec_ml_kem.parameters.FieldElement.new
      simp only [bind_tc_ok, hf_def, if_neg hbr']
  have h_from_fn :=
    libcrux_iot_ml_kem.Util.CreateI.from_fn_pure_eq
      (T := hacspec_ml_kem.parameters.FieldElement)
      (F := hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure)
      (N := 128#usize)
      (inst := hacspec_ml_kem.invert_ntt.ntt_inverse_layer.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement)
      (c := groups)
      (f := f)
      hpure
  unfold hacspec_ml_kem.parameters.createi
  show core.array.from_fn 128#usize _ groups = _
  exact h_from_fn

/-- The hacspec slice-by-range extraction `zetas[0..groups]` reduces to
    `List.slice 0 groups zetas.val` (local copy of `slice_zetas_succeeds`). -/
private theorem slice_zetas0_succeeds
    (zs : Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize)
    (groups : Std.Usize) (hgroups : groups.val ≤ 128) :
    core.Array.Insts.CoreOpsIndexIndex.index
      (core.Slice.Insts.CoreOpsIndexIndex
      (core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      hacspec_ml_kem.parameters.FieldElement)) zs
      { start := 0#usize, «end» := groups }
    = .ok (⟨List.slice 0 groups.val zs.val, by
            unfold List.slice
            have h : zs.val.length = 128 := zs.property
            simp only [List.drop_zero, List.length_take, h]
            scalar_tac⟩ :
           Aeneas.Std.Slice hacspec_ml_kem.parameters.FieldElement) := by
  unfold core.Array.Insts.CoreOpsIndexIndex.index
         core.slice.index.Slice.index
         core.Slice.Insts.CoreOpsIndexIndex
         core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
  show core.slice.index.SliceIndexRangeUsizeSlice.index
      (core.cmRangeUsizeToAeneas _) zs.to_slice = _
  unfold core.slice.index.SliceIndexRangeUsizeSlice.index
         core.cmRangeUsizeToAeneas
  have h_alen : zs.val.length = 128 := zs.property
  have h_cond : (0#usize : Std.Usize) ≤ groups ∧
      groups.val ≤ zs.to_slice.val.length := by
    refine ⟨by scalar_tac, by
      show groups.val ≤ zs.val.length; omega⟩
  rw [if_pos h_cond]
  rfl

/-- `List.slice 0 b l [k]! = l[k]!` when `b ≤ l.length` and `k < b`
    (local specialization of `slice_getElem_at`). -/
private theorem slice0_getElem_at {α} [Inhabited α]
    (l : List α) (b : Nat) (_h_le_b : b ≤ l.length) (k : Nat) (hk : k < b) :
    (List.slice 0 b l)[k]! = l[k]! := by
  unfold List.slice
  rw [List.drop_zero, Nat.sub_zero]
  have h_take_idx : (l.take b)[k]? = l[k]? := by
    rw [List.getElem?_take, if_pos hk]
  rw [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD, h_take_idx]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1000000 in
/-- **Full reduction of `ntt_inverse_layer p layer`** to an explicit flat per-lane
    array. b-side lane `i` reads `zetasArr[2·groups − 1 − i/(2·len)]` (plain domain),
    a-side `add p[i] p[i+len]`. Parametrized by the resolved `len`/`groups` values. -/
private theorem ntt_inverse_layer_eq_ok
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (layer len groups : Std.Usize)
    (hlen_def : (1#usize <<< layer : Result Std.Usize) = .ok len)
    (hgroups_def : (128#usize / len : Result Std.Usize) = .ok groups)
    (hlenpos : 0 < len.val) (hlen2 : 2 ≤ len.val) (hlen128 : len.val ≤ 128)
    (hgroups : groups.val = 128 / len.val)
    (hpart_slice : ∀ i : Nat, i < 256 → i / (2 * len.val) < groups.val)
    (hpart : ∀ i : Nat, i < 256 → (i % (2*len.val) < len.val → i + len.val < 256)
                                ∧ (¬ (i % (2*len.val) < len.val) → len.val ≤ i))
    (hcanon : ∀ j : Nat, j < 256 → Canonical (p.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer p layer
      = .ok ⟨(List.range 256).map (fun i =>
              if i % (2*len.val) < len.val then
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                  (p.val[i]!) (p.val[i + len.val]!)
              else
                libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                  (zetasArr.val[2 * groups.val - 1 - i / (2*len.val)]!)
                  (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                    (p.val[i]!) (p.val[i - len.val]!))),
             by simp [List.length_map, List.length_range]⟩ := by
  unfold hacspec_ml_kem.invert_ntt.ntt_inverse_layer
  rw [hlen_def]; simp only [bind_tc_ok]
  rw [hgroups_def]; simp only [bind_tc_ok]
  have hgroups64 : groups.val ≤ 64 := by
    rw [hgroups]
    calc 128 / len.val ≤ 128 / 2 := Nat.div_le_div_left hlen2 (by omega)
      _ = 64 := by norm_num
  rw [ntt_inverse_layer_zetas_eq_ok groups hgroups64]; simp only [bind_tc_ok]
  set zs : Std.Array hacspec_ml_kem.parameters.FieldElement 128#usize :=
    ⟨(List.range 128).map (fun g =>
        if g < groups.val then zetasArr.val[2 * groups.val - 1 - g]!
        else (⟨0#u16⟩ : hacspec_ml_kem.parameters.FieldElement)),
     by simp [List.length_map, List.length_range]⟩ with hzs_def
  rw [slice_zetas0_succeeds zs groups (by omega)]; simp only [bind_tc_ok]
  set s : Slice hacspec_ml_kem.parameters.FieldElement :=
    ⟨List.slice 0 groups.val zs.val, by
      unfold List.slice
      have h : zs.val.length = 128 := zs.property
      simp only [List.drop_zero, List.length_take, h]; scalar_tac⟩ with hs_def
  have hslen_eq : s.val.length = groups.val := by
    show (List.slice 0 groups.val zs.val).length = groups.val
    unfold List.slice
    have h : zs.val.length = 128 := zs.property
    simp only [List.drop_zero, List.length_take, h]; omega
  have h2lenmax : 2 * len.val ≤ Std.Usize.max := by
    have : (256:Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  -- s lane access: for g < groups, s[g]! = zs[g]! = zetasArr[2groups-1-g]
  have hslane : ∀ g : Nat, g < groups.val →
      s.val[g]! = zetasArr.val[2 * groups.val - 1 - g]! := by
    intro g hg
    show (List.slice 0 groups.val zs.val)[g]! = _
    rw [slice0_getElem_at zs.val groups.val (by
          rw [zs.property]; have : (128#usize : Std.Usize).val = 128 := by scalar_tac
          omega) g hg]
    show ((List.range 128).map (fun g =>
            if g < groups.val then zetasArr.val[2 * groups.val - 1 - g]!
            else (⟨0#u16⟩ : hacspec_ml_kem.parameters.FieldElement)))[g]! = _
    rw [getElem!_pos _ g (by simp [List.length_map, List.length_range]; omega)]
    rw [List.getElem_map, List.getElem_range, if_pos hg]
  rw [ntt_inverse_layer_n_eq_ok p len s hlenpos h2lenmax hlen128 hcanon
      (fun i hi => by rw [hslen_eq]; exact hpart_slice i hi) hpart]
  -- the flat array from the layer_n reduction uses `s[i/(2len)]!`; rewrite to zetasArr.
  congr 1
  apply Subtype.ext
  simp only []
  apply List.map_congr_left
  intro i hi
  have hi256 : i < 256 := by rw [List.mem_range] at hi; exact hi
  by_cases hbr : i % (2*len.val) < len.val
  · rw [if_pos hbr, if_pos hbr]
  · rw [if_neg hbr, if_neg hbr]
    rw [hslane (i / (2*len.val)) (hpart_slice i hi256)]

/-! ### C2 : per-layer flat↔chunk match.

    For each layer N we prove `ntt_inverse_layer q N = .ok (Spec.invert_ntt_layer_..._pure
    q zeta_i)` for canonical `q`, by reducing the LHS to the flat array
    (`ntt_inverse_layer_eq_ok`) and the RHS lane to the same flat butterfly (in
    `ZMod 3329`), then concluding via canonical determination (`eq_of_zmod_lane_canon'`).
    The per-lane match uses commutativity of `add`/`mul` in `ZMod` and
    `zetas_bridge_zmod` (zeta-index correspondence). -/

/-- Local copy of `eq_of_zmod_lane_canon` (the SubPolyScaleZ one is defined later). -/
private theorem eq_of_zmod_lane_canon'
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
      rw [← feOfZMod_zmodOfFE_of_canon (u.val[j]!) (hcu j hj),
          ← feOfZMod_zmodOfFE_of_canon (v.val[j]!) (hcv j hj), hz j hj]
    have huj : u.val[j]! = u.val[j] :=
      getElem!_pos u.val j (by rw [Aeneas.Std.Array.length_eq u]; exact hj)
    have hvj : v.val[j]! = v.val[j] :=
      getElem!_pos v.val j (by rw [Aeneas.Std.Array.length_eq v]; exact hj)
    rw [← huj, ← hvj]; exact heq

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- Lane `ℓ` of `chunk_inv_ntt_layer_1_step_pure a z0 z1 z2 z3`: each lane is
    written by exactly one of the 8 disjoint butterfly steps; pairs
    `(0,2)(1,3)(4,6)(5,7)(8,10)(9,11)(12,14)(13,15)` with zetas `z0 z0 z1 z1 z2 z2 z3 z3`. -/
private theorem chunk_inv_ntt_layer_1_step_lane
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 z2 z3 : hacspec_ml_kem.parameters.FieldElement) (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_ntt_layer_1_step_pure a z0 z1 z2 z3).val[ℓ]!
      = if ℓ % 4 < 2 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (a.val[ℓ + 2]!) (a.val[ℓ]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[ℓ]!) (a.val[ℓ - 2]!))
            (if ℓ / 4 = 0 then z0 else if ℓ / 4 = 1 then z1 else if ℓ / 4 = 2 then z2 else z3) := by
  unfold Spec.chunk_inv_ntt_layer_1_step_pure Spec.chunk_inv_ntt_step_pure
  -- each lane is written once (disjoint pairs); resolve nested `.set` getElem.
  interval_cases ℓ <;>
    simp only [Aeneas.Std.Array.set_val_eq] <;> norm_num

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- Lane `ℓ` of `chunk_inv_ntt_layer_2_step_pure a z0 z1`: pairs
    `(0,4)(1,5)(2,6)(3,7)(8,12)(9,13)(10,14)(11,15)` with zetas `z0×4, z1×4`. -/
private theorem chunk_inv_ntt_layer_2_step_lane
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z0 z1 : hacspec_ml_kem.parameters.FieldElement) (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_ntt_layer_2_step_pure a z0 z1).val[ℓ]!
      = if ℓ % 8 < 4 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (a.val[ℓ + 4]!) (a.val[ℓ]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[ℓ]!) (a.val[ℓ - 4]!))
            (if ℓ / 8 = 0 then z0 else z1) := by
  unfold Spec.chunk_inv_ntt_layer_2_step_pure Spec.chunk_inv_ntt_step_pure
  interval_cases ℓ <;>
    simp only [Aeneas.Std.Array.set_val_eq] <;> norm_num

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2000000 in
/-- Lane `ℓ` of `chunk_inv_ntt_layer_3_step_pure a z`: pairs
    `(0,8)(1,9)…(7,15)` with single zeta `z`. -/
private theorem chunk_inv_ntt_layer_3_step_lane
    (a : Std.Array hacspec_ml_kem.parameters.FieldElement 16#usize)
    (z : hacspec_ml_kem.parameters.FieldElement) (ℓ : Nat) (hℓ : ℓ < 16) :
    (Spec.chunk_inv_ntt_layer_3_step_pure a z).val[ℓ]!
      = if ℓ < 8 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (a.val[ℓ + 8]!) (a.val[ℓ]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[ℓ]!) (a.val[ℓ - 8]!)) z := by
  unfold Spec.chunk_inv_ntt_layer_3_step_pure Spec.chunk_inv_ntt_step_pure
  interval_cases ℓ <;>
    simp only [Aeneas.Std.Array.set_val_eq] <;> norm_num

/-! ### C2 (cont.): per-layer match `ntt_inverse_layer ≡ spec layer`. -/

/-- `(1#usize <<< n)` succeeds with value `2^n.val` (for `n.val < numBits`). -/
private theorem shl_one_ok (n : Std.Usize) (hn : n.val < UScalarTy.Usize.numBits) :
    ∃ len : Std.Usize, (1#usize <<< n : Result Std.Usize) = .ok len ∧ len.val = 2 ^ n.val := by
  have h_one_shl_pow : ((1#usize : Std.Usize).val <<< n.val) < 2 ^ System.Platform.numBits := by
    have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
    rw [h_one_eq, Nat.shiftLeft_eq, Nat.one_mul]
    have hnb : n.val < System.Platform.numBits := by
      rwa [Std.UScalarTy.Usize_numBits_eq] at hn
    rcases System.Platform.numBits_eq with h32 | h64
    · rw [h32]; rw [h32] at hnb; exact Nat.pow_lt_pow_right (by decide) hnb
    · rw [h64]; rw [h64] at hnb; exact Nat.pow_lt_pow_right (by decide) hnb
  have hT := Aeneas.Std.UScalar.ShiftLeft_spec (1#usize : Std.Usize) n
    (Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize) hn rfl
  obtain ⟨z, h_eq, h_v_mod, _h_bv⟩ := Std.WP.spec_imp_exists hT
  refine ⟨z, h_eq, ?_⟩
  have h_one_eq : (1#usize : Std.Usize).val = 1 := rfl
  have h_size_eq : (Aeneas.Std.UScalar.size Aeneas.Std.UScalarTy.Usize) = 2 ^ System.Platform.numBits := by
    rw [Aeneas.Std.UScalar.size]; rw [Std.UScalarTy.Usize_numBits_eq]
  rw [h_v_mod, h_one_eq, h_size_eq, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt]
  rw [h_one_eq, Nat.shiftLeft_eq, Nat.one_mul] at h_one_shl_pow
  exact h_one_shl_pow

private theorem numbits_ge (n : Nat) (hn : n ≤ 7) : n < UScalarTy.Usize.numBits := by
  rw [Std.UScalarTy.Usize_numBits_eq]
  rcases System.Platform.numBits_eq with h | h <;> (rw [h]; omega)

/-- `128#usize / len` succeeds with value `128 / len.val` (for `len.val ≠ 0`). -/
private theorem div128_ok (len : Std.Usize) (hlen : len.val ≠ 0) :
    ∃ g : Std.Usize, (128#usize / len : Result Std.Usize) = .ok g ∧ g.val = 128 / len.val := by
  obtain ⟨v, hv, hpv⟩ := Aeneas.Std.WP.spec_imp_exists (Std.Usize.div_spec 128#usize hlen)
  exact ⟨v, hv, by simpa using hpv⟩

/-- Spec layer-1 lane in flat form: `(invert_ntt_layer_1_pure q 128).val[i]!` for `i<256`. -/
private theorem spec_inv_layer_1_lane
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (i : Nat) (hi : i < 256) :
    (Spec.invert_ntt_layer_1_pure q 128#usize).val[i]!
      = if i % 4 < 2 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (q.val[i + 2]!) (q.val[i]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (q.val[i]!) (q.val[i - 2]!))
            (Spec.zeta_at (128 - 4 * (i / 16) - (i % 16) / 4 - 1)) := by
  unfold Spec.invert_ntt_layer_1_pure
  simp only [show (128#usize : Std.Usize).val = 128 from by rfl]
  rw [flatten_chunk_map_lane (fun k => Spec.chunk_inv_ntt_layer_1_step_pure (Spec.chunk_at q k)
        (Spec.zeta_at (128 - 4 * k - 1)) (Spec.zeta_at (128 - 4 * k - 2))
        (Spec.zeta_at (128 - 4 * k - 3)) (Spec.zeta_at (128 - 4 * k - 4))) i hi (by simp)]
  rw [chunk_inv_ntt_layer_1_step_lane _ _ _ _ _ (i % 16) (Nat.mod_lt _ (by decide))]
  have hk : i / 16 < 16 := by omega
  have hmod4 : (i % 16) % 4 = i % 4 := by omega
  have him : i % 16 < 16 := by omega
  by_cases hbr : i % 4 < 2
  · rw [if_pos (by rw [hmod4]; exact hbr)]
    have ha2 : (i % 16) + 2 < 16 := by
      have : (i % 16) % 4 < 2 := by rw [hmod4]; exact hbr
      omega
    rw [if_pos hbr]
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) + 2) ha2]
    congr 2 <;> omega
  · rw [if_neg (by rw [hmod4]; exact hbr), if_neg hbr]
    have hsub : 2 ≤ i % 16 := by omega
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) - 2) (by omega)]
    have hidx1 : 16 * (i / 16) + (i % 16) = i := by omega
    have hidx2 : 16 * (i / 16) + ((i % 16) - 2) = i - 2 := by omega
    rw [hidx1, hidx2]
    -- zeta selector: (i%16)/4 picks z_{(i%16)/4} = zeta_at (128 - 4k - ((i%16)/4) - 1)
    have hzsel : (if (i % 16) / 4 = 0 then Spec.zeta_at (128 - 4 * (i / 16) - 1)
        else if (i % 16) / 4 = 1 then Spec.zeta_at (128 - 4 * (i / 16) - 2)
        else if (i % 16) / 4 = 2 then Spec.zeta_at (128 - 4 * (i / 16) - 3)
        else Spec.zeta_at (128 - 4 * (i / 16) - 4))
        = Spec.zeta_at (128 - 4 * (i / 16) - (i % 16) / 4 - 1) := by
      have hq : (i % 16) / 4 < 4 := by omega
      interval_cases h : ((i % 16) / 4) <;> simp <;> congr 1
    rw [hzsel]

/-- The explicit flat layer array (from `ntt_inverse_layer_eq_ok`) has canonical lanes. -/
private theorem flat_layer_canon
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (len groups : Std.Usize)
    (j : Nat) (hj : j < 256) :
    Canonical ((⟨(List.range 256).map (fun i =>
            if i % (2*len.val) < len.val then
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (q.val[i]!) (q.val[i + len.val]!)
            else
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (zetasArr.val[2 * groups.val - 1 - i / (2*len.val)]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (q.val[i]!) (q.val[i - len.val]!))),
           by simp [List.length_map, List.length_range]⟩ :
          Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize).val[j]!) := by
  show Canonical (((List.range 256).map (fun i =>
            if i % (2*len.val) < len.val then
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
                (q.val[i]!) (q.val[i + len.val]!)
            else
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
                (zetasArr.val[2 * groups.val - 1 - i / (2*len.val)]!)
                (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                  (q.val[i]!) (q.val[i - len.val]!))))[j]!)
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
  rw [List.getElem_map, List.getElem_range]
  by_cases hbr : j % (2*len.val) < len.val
  · rw [if_pos hbr]; exact libcrux_iot_ml_kem.Spec.Pure.Canonical_add_pure _ _
  · rw [if_neg hbr]; exact libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _

set_option maxHeartbeats 1000000 in
/-- **Layer-1 match:** `ntt_inverse_layer q 1 = .ok (invert_ntt_layer_1_pure q 128)`. -/
private theorem ntt_inverse_layer_1_match
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer q 1#usize
      = .ok (Spec.invert_ntt_layer_1_pure q 128#usize) := by
  obtain ⟨len, hlen_def, hlenv⟩ := shl_one_ok 1#usize (numbits_ge 1 (by omega))
  have hlenv2 : len.val = 2 := by rw [hlenv]; decide
  obtain ⟨groups, hgroups_def, hgroupsv⟩ := div128_ok len (by omega)
  have hgroupsv2 : groups.val = 64 := by rw [hgroupsv, hlenv2]
  rw [ntt_inverse_layer_eq_ok q 1#usize len groups hlen_def hgroups_def
      (by omega) (by omega) (by omega) (by rw [hgroupsv, hlenv2])
      (fun i hi => by rw [hlenv2, hgroupsv2]; omega)
      (fun i hi => ⟨fun hc => by rw [hlenv2] at *; omega, fun hc => by rw [hlenv2] at *; omega⟩) hq]
  congr 1
  refine eq_of_zmod_lane_canon' _ _ (flat_layer_canon q len groups)
    (invert_ntt_layer_1_canon q 128#usize hq) ?_
  intro j hj
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj]),
      List.getElem_map, List.getElem_range]
  rw [spec_inv_layer_1_lane q j hj]
  rw [hlenv2, hgroupsv2]
  by_cases hbr : j % 4 < 2
  · rw [show (2 * 2) = 4 from by norm_num, if_pos hbr, if_pos hbr]
    rw [zmodOfFE_add_pure, zmodOfFE_add_pure]; ring
  · rw [show (2 * 2) = 4 from by norm_num, if_neg hbr, if_neg hbr]
    have hsub : 2 ≤ j := by omega
    rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure]
    have hzidx : 2 * 64 - 1 - j / 4 = 128 - 4 * (j / 16) - (j % 16) / 4 - 1 := by omega
    rw [hzidx, ← zetas_bridge_zmod (128 - 4 * (j / 16) - (j % 16) / 4 - 1) (by omega)]
    ring

/-- Spec layer-2 lane in flat form. -/
private theorem spec_inv_layer_2_lane
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (i : Nat) (hi : i < 256) :
    (Spec.invert_ntt_layer_2_pure q 64#usize).val[i]!
      = if i % 8 < 4 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (q.val[i + 4]!) (q.val[i]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (q.val[i]!) (q.val[i - 4]!))
            (Spec.zeta_at (64 - 2 * (i / 16) - (i % 16) / 8 - 1)) := by
  unfold Spec.invert_ntt_layer_2_pure
  simp only [show (64#usize : Std.Usize).val = 64 from by rfl]
  rw [flatten_chunk_map_lane (fun k => Spec.chunk_inv_ntt_layer_2_step_pure (Spec.chunk_at q k)
        (Spec.zeta_at (64 - 2 * k - 1)) (Spec.zeta_at (64 - 2 * k - 2))) i hi (by simp)]
  rw [chunk_inv_ntt_layer_2_step_lane _ _ _ (i % 16) (Nat.mod_lt _ (by decide))]
  have hk : i / 16 < 16 := by omega
  have him : i % 16 < 16 := by omega
  have hmod8 : (i % 16) % 8 = i % 8 := by omega
  by_cases hbr : i % 8 < 4
  · rw [if_pos (by rw [hmod8]; exact hbr)]
    have ha : (i % 16) + 4 < 16 := by
      have : (i % 16) % 8 < 4 := by rw [hmod8]; exact hbr
      omega
    rw [if_pos hbr]
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) + 4) ha]
    congr 2 <;> omega
  · rw [if_neg (by rw [hmod8]; exact hbr), if_neg hbr]
    have hsub : 4 ≤ i % 16 := by
      have : ¬ ((i % 16) % 8 < 4) := by rw [hmod8]; exact hbr
      omega
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) - 4) (by omega)]
    have hidx1 : 16 * (i / 16) + (i % 16) = i := by omega
    have hidx2 : 16 * (i / 16) + ((i % 16) - 4) = i - 4 := by omega
    rw [hidx1, hidx2]
    have hzsel : (if (i % 16) / 8 = 0 then Spec.zeta_at (64 - 2 * (i / 16) - 1)
        else Spec.zeta_at (64 - 2 * (i / 16) - 2))
        = Spec.zeta_at (64 - 2 * (i / 16) - (i % 16) / 8 - 1) := by
      have hq : (i % 16) / 8 < 2 := by omega
      interval_cases h : ((i % 16) / 8) <;> simp ; congr 1
    rw [hzsel]

set_option maxHeartbeats 1000000 in
/-- **Layer-2 match.** -/
private theorem ntt_inverse_layer_2_match
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer q 2#usize
      = .ok (Spec.invert_ntt_layer_2_pure q 64#usize) := by
  obtain ⟨len, hlen_def, hlenv⟩ := shl_one_ok 2#usize (numbits_ge 2 (by omega))
  have hlenv2 : len.val = 4 := by rw [hlenv]; decide
  obtain ⟨groups, hgroups_def, hgroupsv⟩ := div128_ok len (by omega)
  have hgroupsv2 : groups.val = 32 := by rw [hgroupsv, hlenv2]
  rw [ntt_inverse_layer_eq_ok q 2#usize len groups hlen_def hgroups_def
      (by omega) (by omega) (by omega) (by rw [hgroupsv, hlenv2])
      (fun i hi => by rw [hlenv2, hgroupsv2]; omega)
      (fun i hi => ⟨fun hc => by rw [hlenv2] at *; omega, fun hc => by rw [hlenv2] at *; omega⟩) hq]
  congr 1
  refine eq_of_zmod_lane_canon' _ _ (flat_layer_canon q len groups)
    (invert_ntt_layer_2_canon q 64#usize hq) ?_
  intro j hj
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj]),
      List.getElem_map, List.getElem_range]
  rw [spec_inv_layer_2_lane q j hj]
  rw [hlenv2, hgroupsv2]
  by_cases hbr : j % 8 < 4
  · rw [show (2 * 4) = 8 from by norm_num, if_pos hbr, if_pos hbr]
    rw [zmodOfFE_add_pure, zmodOfFE_add_pure]; ring
  · rw [show (2 * 4) = 8 from by norm_num, if_neg hbr, if_neg hbr]
    have hsub : 4 ≤ j := by omega
    rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure]
    have hzidx : 2 * 32 - 1 - j / 8 = 64 - 2 * (j / 16) - (j % 16) / 8 - 1 := by omega
    rw [hzidx, ← zetas_bridge_zmod (64 - 2 * (j / 16) - (j % 16) / 8 - 1) (by omega)]
    ring

/-- Spec layer-3 lane in flat form. -/
private theorem spec_inv_layer_3_lane
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize) (i : Nat) (hi : i < 256) :
    (Spec.invert_ntt_layer_3_pure q 32#usize).val[i]!
      = if i % 16 < 8 then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (q.val[i + 8]!) (q.val[i]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (q.val[i]!) (q.val[i - 8]!))
            (Spec.zeta_at (32 - (i / 16) - 1)) := by
  unfold Spec.invert_ntt_layer_3_pure
  simp only [show (32#usize : Std.Usize).val = 32 from by rfl]
  rw [flatten_chunk_map_lane (fun k => Spec.chunk_inv_ntt_layer_3_step_pure (Spec.chunk_at q k)
        (Spec.zeta_at (32 - k - 1))) i hi (by simp)]
  rw [chunk_inv_ntt_layer_3_step_lane _ _ (i % 16) (Nat.mod_lt _ (by decide))]
  have hk : i / 16 < 16 := by omega
  have him : i % 16 < 16 := by omega
  by_cases hbr : i % 16 < 8
  · rw [if_pos hbr, if_pos hbr]
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) + 8) (by omega)]
    congr 2 <;> omega
  · rw [if_neg hbr, if_neg hbr]
    rw [chunk_at_lane' q (i / 16) (i % 16) (by omega),
        chunk_at_lane' q (i / 16) ((i % 16) - 8) (by omega)]
    have hidx1 : 16 * (i / 16) + (i % 16) = i := by omega
    have hidx2 : 16 * (i / 16) + ((i % 16) - 8) = i - 8 := by omega
    rw [hidx1, hidx2]

set_option maxHeartbeats 1000000 in
/-- **Layer-3 match.** -/
private theorem ntt_inverse_layer_3_match
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer q 3#usize
      = .ok (Spec.invert_ntt_layer_3_pure q 32#usize) := by
  obtain ⟨len, hlen_def, hlenv⟩ := shl_one_ok 3#usize (numbits_ge 3 (by omega))
  have hlenv2 : len.val = 8 := by rw [hlenv]; decide
  obtain ⟨groups, hgroups_def, hgroupsv⟩ := div128_ok len (by omega)
  have hgroupsv2 : groups.val = 16 := by rw [hgroupsv, hlenv2]
  rw [ntt_inverse_layer_eq_ok q 3#usize len groups hlen_def hgroups_def
      (by omega) (by omega) (by omega) (by rw [hgroupsv, hlenv2])
      (fun i hi => by rw [hlenv2, hgroupsv2]; omega)
      (fun i hi => ⟨fun hc => by rw [hlenv2] at *; omega, fun hc => by rw [hlenv2] at *; omega⟩) hq]
  congr 1
  refine eq_of_zmod_lane_canon' _ _ (flat_layer_canon q len groups)
    (invert_ntt_layer_3_canon q 32#usize hq) ?_
  intro j hj
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj]),
      List.getElem_map, List.getElem_range]
  rw [spec_inv_layer_3_lane q j hj]
  rw [hlenv2, hgroupsv2]
  by_cases hbr : j % 16 < 8
  · rw [show (2 * 8) = 16 from by norm_num, if_pos hbr, if_pos hbr]
    rw [zmodOfFE_add_pure, zmodOfFE_add_pure]; ring
  · rw [show (2 * 8) = 16 from by norm_num, if_neg hbr, if_neg hbr]
    have hsub : 8 ≤ j := by omega
    rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure]
    have hzidx : 2 * 16 - 1 - j / 16 = 32 - (j / 16) - 1 := by omega
    rw [hzidx, ← zetas_bridge_zmod (32 - (j / 16) - 1) (by omega)]
    ring

/-- Mod-chunk identity: `i % (2·(16·step)) = 16·((i/16) % (2·step)) + i%16`. -/
private theorem mod_chunk_eq (i step : Nat) (hstep : 0 < step) :
    i % (2 * (16 * step)) = 16 * ((i / 16) % (2 * step)) + i % 16 := by
  have h1 : i = 16 * (i / 16) + i % 16 := (Nat.div_add_mod i 16).symm
  have key : (16 * (i / 16)) % (16 * (2 * step)) = 16 * ((i / 16) % (2 * step)) :=
    Nat.mul_mod_mul_left 16 (i / 16) (2 * step)
  have h16 : i % 16 < 16 := Nat.mod_lt _ (by decide)
  have hxlt : (i / 16) % (2 * step) + 1 ≤ 2 * step := Nat.mod_lt _ (by omega)
  have hml : 16 * ((i / 16) % (2 * step) + 1) ≤ 16 * (2 * step) :=
    Nat.mul_le_mul (Nat.le_refl 16) hxlt
  have hbound : 16 * ((i / 16) % (2 * step)) + i % 16 < 16 * (2 * step) := by
    rw [Nat.mul_add] at hml; omega
  have hstep_eq : 2 * (16 * step) = 16 * (2 * step) := by ring
  have h16' : i % 16 < 16 * (2 * step) := by
    have hge : 16 * 1 ≤ 16 * (2 * step) := Nat.mul_le_mul (Nat.le_refl 16) (by omega)
    omega
  rw [hstep_eq]
  conv_lhs => rw [h1]
  rw [Nat.add_mod, key, Nat.mod_eq_of_lt h16', Nat.mod_eq_of_lt hbound]

/-- Spec layer-4+ lane in flat form, parametrized by `layer`/`zeta_i`, with `step`
    the chunk step `(1<<<layer)/16` and `len = 16·step`. -/
private theorem spec_inv_layer_4_plus_lane
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i layer : Std.Usize) (step len : Nat)
    (hstep : step = (1 <<< layer.val) / 16) (hlen : len = 16 * step)
    (hstep_pos : 0 < step) (hdvd : (2 * step) ∣ 16)
    (i : Nat) (hi : i < 256) :
    (Spec.invert_ntt_layer_4_plus_pure q zeta_i layer).val[i]!
      = if i % (2 * len) < len then
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.add_pure
            (q.val[i]!) (q.val[i + len]!)
        else
          libcrux_iot_ml_kem.Spec.Pure.FieldElement.mul_pure
            (libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (q.val[i]!) (q.val[i - len]!))
            (Spec.zeta_at (zeta_i.val - 1 - (i / 16) / (2 * step))) := by
  unfold Spec.invert_ntt_layer_4_plus_pure
  rw [flatten_chunk_map_lane (fun c => Spec.chunk_inv_at_layer_4_plus_pure
        (Std.Array.make 16#usize ((List.range 16).map (Spec.chunk_at q)) (by simp))
        layer (fun group => Spec.zeta_at (zeta_i.val - 1 - group)) c) i hi (by simp)]
  have hc : i / 16 < 16 := by omega
  have hℓ : i % 16 < 16 := Nat.mod_lt _ (by decide)
  have hstep16 : (1 <<< layer.val) / 16 = step := hstep.symm
  -- partner-in-range for the a-branch
  have hub : (i / 16) % (2 * ((1 <<< layer.val) / 16)) < (1 <<< layer.val) / 16 →
      (i / 16) + (1 <<< layer.val) / 16 < 16 := by
    rw [hstep16]; exact fun hoff => layer4_partner_lt (i / 16) step hc hstep_pos hdvd hoff
  rw [chunk_inv_at_layer_4_plus_chunks0_eq q layer
      (fun group => Spec.zeta_at (zeta_i.val - 1 - group)) (i / 16) hc hub (by simp)]
  rw [hstep16]
  -- relate flat a/b decision to chunk a/b decision via mod_chunk_eq
  have hmce : i % (2 * len) = 16 * ((i / 16) % (2 * step)) + i % 16 := by
    rw [hlen]; exact mod_chunk_eq i step hstep_pos
  have hdecf : (i % (2 * len) < len) ↔ ((i / 16) % (2 * step) < step) := by
    rw [hmce, hlen]
    constructor
    · intro h; by_contra hco; push Not at hco
      have : 16 * step ≤ 16 * ((i / 16) % (2 * step)) := Nat.mul_le_mul (Nat.le_refl 16) hco
      omega
    · intro h
      have : 16 * ((i / 16) % (2 * step) + 1) ≤ 16 * step := Nat.mul_le_mul (Nat.le_refl 16) (by omega)
      rw [Nat.mul_add] at this; have h16 : i % 16 < 16 := Nat.mod_lt _ (by decide); omega
  by_cases hbr : (i / 16) % (2 * step) < step
  · rw [if_pos hbr, if_pos (hdecf.mpr hbr)]
    have hub' : (i / 16) + step < 16 := layer4_partner_lt (i / 16) step hc hstep_pos hdvd hbr
    rw [chunk_inv_pair_butterfly_a_lane _ _ (i % 16) hℓ]
    rw [chunk_at_lane' q (i / 16) (i % 16) hℓ,
        chunk_at_lane' q ((i / 16) + step) (i % 16) hℓ]
    have e1 : 16 * (i / 16) + (i % 16) = i := by omega
    have e2 : 16 * ((i / 16) + step) + (i % 16) = i + len := by
      rw [hlen, Nat.mul_add]; omega
    rw [e1, e2]
  · rw [if_neg hbr, if_neg (fun hc2 => hbr (hdecf.mp hc2))]
    rw [chunk_inv_pair_butterfly_b_lane _ _ _ (i % 16) hℓ]
    rw [chunk_at_lane' q (i / 16) (i % 16) hℓ,
        chunk_at_lane' q ((i / 16) - step) (i % 16) hℓ]
    have e1 : 16 * (i / 16) + (i % 16) = i := by omega
    have hstep_le : step ≤ i / 16 := by
      have hr : (i / 16) % (2 * step) ≤ i / 16 := Nat.mod_le _ _
      omega
    have e2 : 16 * ((i / 16) - step) + (i % 16) = i - len := by
      rw [hlen, Nat.mul_sub]; omega
    rw [e1, e2]

set_option maxHeartbeats 1000000 in
/-- **Layer-4+ match** for a concrete `layer`/`zeta_i`, `step`/`len`. -/
private theorem ntt_inverse_layer_4_plus_match
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (zeta_i layer : Std.Usize) (lenu groups : Std.Usize) (step : Nat)
    (hlen_def : (1#usize <<< layer : Result Std.Usize) = .ok lenu)
    (hgroups_def : (128#usize / lenu : Result Std.Usize) = .ok groups)
    (hstep : step = (1 <<< layer.val) / 16) (hlenv : lenu.val = 16 * step)
    (hstep_pos : 0 < step) (hdvd : (2 * step) ∣ 16)
    (hlen2 : 2 ≤ lenu.val) (hlen128 : lenu.val ≤ 128)
    (hgroupsv : groups.val = 128 / lenu.val) (hlg : lenu.val * groups.val = 128)
    (hzeta : ∀ i : Nat, i < 256 → 2 * groups.val - 1 - i / (2 * lenu.val)
        = zeta_i.val - 1 - (i / 16) / (2 * step))
    (hzeta_lt : ∀ i : Nat, i < 256 → ¬ (i % (2 * lenu.val) < lenu.val) →
        zeta_i.val - 1 - (i / 16) / (2 * step) < 128)
    (hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer q layer
      = .ok (Spec.invert_ntt_layer_4_plus_pure q zeta_i layer) := by
  have h256 : 2 * lenu.val * groups.val = 256 := by rw [show 2 * lenu.val * groups.val = 2 * (lenu.val * groups.val) from by ring, hlg]
  rw [ntt_inverse_layer_eq_ok q layer lenu groups hlen_def hgroups_def
      (by omega) (by omega) hlen128 hgroupsv
      (fun i hi => Nat.div_lt_of_lt_mul (by omega))
      (fun i hi => ⟨fun hc => by
          -- a-side: i % (2*len) < len ⇒ i + len < 256
          have hdm : i = 2 * lenu.val * (i / (2 * lenu.val)) + i % (2 * lenu.val) :=
            (Nat.div_add_mod i (2 * lenu.val)).symm
          have hblk : i / (2 * lenu.val) < groups.val := Nat.div_lt_of_lt_mul (by omega)
          have hbk1 : i / (2 * lenu.val) + 1 ≤ groups.val := by omega
          have hmul : 2 * lenu.val * (i / (2 * lenu.val) + 1) ≤ 2 * lenu.val * groups.val :=
            Nat.mul_le_mul (Nat.le_refl _) hbk1
          rw [Nat.mul_add] at hmul; omega,
        fun hc => by
          have hle : i % (2 * lenu.val) ≤ i := Nat.mod_le _ _
          omega⟩) hq]
  congr 1
  refine eq_of_zmod_lane_canon' _ _ (flat_layer_canon q lenu groups)
    (invert_ntt_layer_4_plus_canon q zeta_i layer hq) ?_
  intro j hj
  rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj]),
      List.getElem_map, List.getElem_range]
  rw [spec_inv_layer_4_plus_lane q zeta_i layer step lenu.val hstep hlenv hstep_pos hdvd j hj]
  by_cases hbr : j % (2 * lenu.val) < lenu.val
  · rw [if_pos hbr, if_pos hbr]
  · rw [if_neg hbr, if_neg hbr]
    rw [zmodOfFE_mul_pure, zmodOfFE_mul_pure]
    rw [hzeta j hj, ← zetas_bridge_zmod (zeta_i.val - 1 - (j / 16) / (2 * step)) (hzeta_lt j hj hbr)]
    ring

/-- Concrete cross-chunk-layer match, instantiating `ntt_inverse_layer_4_plus_match`
    for a layer `N ∈ {4,5,6,7}` (given as `layer : Std.Usize` with `4 ≤ N ≤ 7`).
    The Spec zeta-index `zeta_i = 128 / 2^N` and `step = 2^N / 16`. -/
private theorem ntt_inverse_layer_4plus_match'
    (q : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (layer zeta_i : Std.Usize) (N : Nat)
    (hN_def : layer.val = N) (hN_lo : 4 ≤ N) (hN_hi : N ≤ 7)
    (hzi : zeta_i.val = 256 / 2 ^ N)
    (hq : ∀ j : Nat, j < 256 → Canonical (q.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_layer q layer
      = .ok (Spec.invert_ntt_layer_4_plus_pure q zeta_i layer) := by
  obtain ⟨lenu, hlen_def, hlenv⟩ := shl_one_ok layer (by rw [hN_def]; exact numbits_ge N (by omega))
  have hlenval : lenu.val = 2 ^ N := by rw [hlenv, hN_def]
  obtain ⟨groups, hgroups_def, hgroupsv⟩ := div128_ok lenu (by rw [hlenval]; positivity)
  set step : Nat := 2 ^ N / 16 with hstep_def
  have hstep_pos : 0 < step := by
    rw [hstep_def]; have : 16 ≤ 2 ^ N := by calc 16 = 2 ^ 4 := by norm_num
                                                  _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) hN_lo
    omega
  have h16dvd : (16 : Nat) ∣ 2 ^ N := by
    calc (16 : Nat) = 2 ^ 4 := by norm_num
      _ ∣ 2 ^ N := pow_dvd_pow 2 hN_lo
  have hlenv16 : lenu.val = 16 * step := by
    rw [hlenval, hstep_def]; exact (Nat.mul_div_cancel' h16dvd).symm
  have hstep_eq : step = (1 <<< layer.val) / 16 := by
    rw [hstep_def, hN_def, Nat.shiftLeft_eq, Nat.one_mul]
  have hdvd : (2 * step) ∣ 16 := by
    rw [hstep_def]; interval_cases N <;> decide
  have hlen2 : 2 ≤ lenu.val := by rw [hlenval]; calc 2 = 2 ^ 1 := by norm_num
                                                       _ ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  have hlen128 : lenu.val ≤ 128 := by
    rw [hlenval]; calc 2 ^ N ≤ 2 ^ 7 := Nat.pow_le_pow_right (by omega) hN_hi
      _ = 128 := by norm_num
  have hgroupsv' : groups.val = 128 / lenu.val := by rw [hgroupsv, hlenval]
  have hlg : lenu.val * groups.val = 128 := by
    rw [hgroupsv', hlenval]; rw [Nat.mul_div_cancel']
    calc (2 : Nat) ^ N ∣ 2 ^ 7 := pow_dvd_pow 2 hN_hi
      _ = 128 := by norm_num
  have h2lenmax : 2 * lenu.val ≤ Std.Usize.max := by
    have : 2 * lenu.val ≤ 256 := by omega
    have h256 : (256 : Nat) ≤ Std.Usize.max := by scalar_tac
    omega
  -- `zeta_i = 2 * groups` and `2 * lenu = 32 * step`
  have hzi_eq : zeta_i.val = 2 * groups.val := by
    rw [hzi, hgroupsv', hlenval]
    have h128dvd : (2 : Nat) ^ N ∣ 128 := by
      calc (2 : Nat) ^ N ∣ 2 ^ 7 := pow_dvd_pow 2 hN_hi
        _ = 128 := by norm_num
    -- `256 / 2^N = 2 * (128 / 2^N)` since `2^N ∣ 128`
    rw [show (256 : Nat) = 2 * 128 from by norm_num, Nat.mul_div_assoc 2 h128dvd]
  have h2len32 : 2 * lenu.val = 32 * step := by rw [hlenv16]; ring
  rw [ntt_inverse_layer_4_plus_match q zeta_i layer lenu groups step
      hlen_def hgroups_def hstep_eq hlenv16 hstep_pos hdvd hlen2 hlen128 hgroupsv' hlg
      (fun i hi => by
        rw [hzi_eq, h2len32]
        have hnest : (i / 16) / (2 * step) = i / (32 * step) := by
          rw [Nat.div_div_eq_div_mul]; ring_nf
        rw [hnest])
      (fun i hi hbr => by
        -- `zeta_i - 1 - (i/16)/(2*step) ≤ zeta_i - 1 < 128` since `zeta_i ≤ 128`
        have h2g : 2 * groups.val ≤ lenu.val * groups.val :=
          Nat.mul_le_mul_right _ hlen2
        have hgle : 2 * groups.val ≤ 128 := by rw [hlg] at h2g; exact h2g
        have hzle : zeta_i.val ≤ 128 := hzi_eq ▸ hgle
        calc zeta_i.val - 1 - (i / 16) / (2 * step)
            ≤ zeta_i.val - 1 := Nat.sub_le _ _
          _ ≤ 128 - 1 := Nat.sub_le_sub_right hzle 1
          _ < 128 := by omega)
      hq]

/-- **C2.** The hacspec `ntt_inverse_butterflies` (7-layer `let`-chain) matches the
    Spec `invert_ntt_montgomery_pure` (the same 7 layers with zeta-thread
    `128 → 64 → 32 → 16 → 8 → 4 → 2`), for canonical input. Each layer match is the
    corresponding `_match` lemma; canonicity threads via the `_canon` lemmas. -/
private theorem ntt_inverse_butterflies_eq_invert_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hp : ∀ j : Nat, j < 256 → Canonical (p.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse_butterflies p
      = .ok (Spec.invert_ntt_montgomery_pure p) := by
  unfold hacspec_ml_kem.invert_ntt.ntt_inverse_butterflies Spec.invert_ntt_montgomery_pure
  -- Layer 1
  rw [ntt_inverse_layer_1_match p hp]; simp only [bind_tc_ok]
  have hc1 : CanonArr (Spec.invert_ntt_layer_1_pure p 128#usize) :=
    invert_ntt_layer_1_canon p 128#usize hp
  -- Layer 2
  rw [ntt_inverse_layer_2_match _ hc1]; simp only [bind_tc_ok]
  have hc2 : CanonArr (Spec.invert_ntt_layer_2_pure (Spec.invert_ntt_layer_1_pure p 128#usize) 64#usize) :=
    invert_ntt_layer_2_canon _ 64#usize hc1
  -- Layer 3
  rw [ntt_inverse_layer_3_match _ hc2]; simp only [bind_tc_ok]
  have hc3 : CanonArr (Spec.invert_ntt_layer_3_pure _ 32#usize) :=
    invert_ntt_layer_3_canon _ 32#usize hc2
  -- Layer 4 (cross-chunk; zeta_i = 16, step = 1)
  rw [ntt_inverse_layer_4plus_match' _ 4#usize 16#usize 4 rfl (by omega) (by omega) (by decide) hc3]
  simp only [bind_tc_ok]
  have hc4 : CanonArr (Spec.invert_ntt_layer_4_plus_pure _ 16#usize 4#usize) :=
    invert_ntt_layer_4_plus_canon _ 16#usize 4#usize hc3
  -- Layer 5 (zeta_i = 8, step = 2)
  rw [ntt_inverse_layer_4plus_match' _ 5#usize 8#usize 5 rfl (by omega) (by omega) (by decide) hc4]
  simp only [bind_tc_ok]
  have hc5 : CanonArr (Spec.invert_ntt_layer_4_plus_pure _ 8#usize 5#usize) :=
    invert_ntt_layer_4_plus_canon _ 8#usize 5#usize hc4
  -- Layer 6 (zeta_i = 4, step = 4)
  rw [ntt_inverse_layer_4plus_match' _ 6#usize 4#usize 6 rfl (by omega) (by omega) (by decide) hc5]
  simp only [bind_tc_ok]
  have hc6 : CanonArr (Spec.invert_ntt_layer_4_plus_pure _ 4#usize 6#usize) :=
    invert_ntt_layer_4_plus_canon _ 4#usize 6#usize hc5
  -- Layer 7 (zeta_i = 2, step = 8)
  rw [ntt_inverse_layer_4plus_match' _ 7#usize 2#usize 7 rfl (by omega) (by omega) (by decide) hc6]

end InvertButterfliesC2

theorem ntt_inverse_eq_scaleZ_invert_pure
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (hp : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical (p.val[j]!)) :
    hacspec_ml_kem.invert_ntt.ntt_inverse p
      = .ok (scaleZ 3303 (Spec.invert_ntt_montgomery_pure p)) := by
  have hcanon : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical
        ((Spec.invert_ntt_montgomery_pure p).val[j]!) := by
    unfold Spec.invert_ntt_montgomery_pure
    exact invert_ntt_layer_4_plus_canon _ 2#usize 7#usize
      (invert_ntt_layer_4_plus_canon _ 4#usize 6#usize
        (invert_ntt_layer_4_plus_canon _ 8#usize 5#usize
          (invert_ntt_layer_4_plus_canon _ 16#usize 4#usize
            (invert_ntt_layer_3_canon _ 32#usize
              (invert_ntt_layer_2_canon _ 64#usize
                (invert_ntt_layer_1_canon p 128#usize hp))))))
  exact ntt_inverse_reduce_eq p _ hcanon (ntt_inverse_butterflies_eq_invert_pure p hp)

/-! ## D (hacspec side) — `sub_polynomials a (scaleZ 512 b) ≡ subtract_reduce_pure a b`.

    `Bridges.zmodOfFE_subtract_reduce_pure_lane` gives, for canonical `a[j]`,
    `zmodOfFE (subtract_reduce_pure a b)[j] = zmodOfFE a[j] - 512 * zmodOfFE b[j]`.
    `sub_polynomials a c` is per-lane `sub_pure a[j] c[j]`; with `c = scaleZ 512 b`,
    `zmodOfFE c[j] = 512 * zmodOfFE b[j]` (`scaleZ_lane`), so both sides have the
    same canonical lanes. -/
section SubPolyScaleZ

open libcrux_iot_ml_kem.Spec.Pure (Canonical)
/-- `feOfZMod z` is canonical (local copy; the `InvertScaleZ` one is `private`). -/
private theorem canon_feOfZMod' (z : ZMod 3329) : Canonical (feOfZMod z) := by
  unfold Canonical feOfZMod hacspec_ml_kem.parameters.FIELD_MODULUS
  show (BitVec.ofNat 16 z.val).toNat < _
  rw [BitVec.toNat_ofNat]
  have hz : z.val < 3329 := ZMod.val_lt z
  have : z.val % 2 ^ 16 = z.val := Nat.mod_eq_of_lt (by omega)
  simp only [this]; simpa using hz

/-- `scaleZ c p` is canonical per lane. -/
private theorem canonArr_scaleZ' (c : ZMod 3329)
    (p : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (j : Nat) (hj : j < 256) : Canonical ((scaleZ c p).val[j]!) := by
  unfold scaleZ
  rw [mkN_map_lane' (fun k => feOfZMod (c * zmodOfFE (p.val[k]!))) j hj _]
  exact canon_feOfZMod' _

/-- Canonical round-trip (local copy). -/
private theorem feOfZMod_zmodOfFE_of_canon'
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

/-- Two canonical 256-arrays with equal `zmodOfFE` lanes are equal. -/
private theorem eq_of_zmod_lane_canon
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
      rw [← feOfZMod_zmodOfFE_of_canon' (u.val[j]!) (hcu j hj),
          ← feOfZMod_zmodOfFE_of_canon' (v.val[j]!) (hcv j hj), hz j hj]
    have huj : u.val[j]! = u.val[j] :=
      getElem!_pos u.val j (by rw [Aeneas.Std.Array.length_eq u]; exact hj)
    have hvj : v.val[j]! = v.val[j] :=
      getElem!_pos v.val j (by rw [Aeneas.Std.Array.length_eq v]; exact hj)
    rw [← huj, ← hvj]; exact heq

-- The 8-bind monadic do-block in the `sub_polynomials` closure needs a deeper
-- elaboration recursion limit than the default (512). Mirrors the createi/from_fn
-- proof family in `FCTargets.lean` (e.g. `set_option maxRecDepth 4000 in` at the
-- ntt closure proofs); the `add_polynomials` template stays under 512 only because
-- its closure body is one bind shorter.
-- `createi_pure_eq` over a 2-tuple closure state `(a, c)` still needs a deeper
-- recursion limit for the `parameters.createi`→`from_fn` defeq (sanctioned
-- createi exception); the single-state `reduce_polynomial_eq_ok` does not.
set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
/-- `sub_polynomials a c` reduces to the per-lane `sub_pure` array, given `a` and
    `c` canonical (the closure body is byte-identical to `FieldElement.sub`, so
    `sub_eq_ok` applies). Mirrors `matrix_add_polynomials_eq_ok` (FCTargets). -/
private theorem sub_polynomials_eq_ok
    (a c : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ k : Nat, k < 256 → Canonical (a.val[k]!))
    (hc : ∀ k : Nat, k < 256 → Canonical (c.val[k]!)) :
    hacspec_ml_kem.matrix.sub_polynomials a c
      = .ok ⟨(List.range 256).map (fun k =>
              libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                (a.val[k]!) (c.val[k]!)),
             by simp [List.length_map, List.length_range]⟩ := by
  set f : Nat → hacspec_ml_kem.parameters.FieldElement :=
    fun k => libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[k]!) (c.val[k]!) with hf_def
  have hpure : ∀ k : Nat, k < (256#usize : Std.Usize).val →
      (hacspec_ml_kem.matrix.sub_polynomials.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
        : CoreModels.core.ops.function.Fn _ _ _).FnMutInst.call_mut
            (a, c) ⟨BitVec.ofNat _ k⟩
        = .ok (f k, (a, c)) := by
    intro k hk
    have hk' : k < 256 := hk
    show hacspec_ml_kem.matrix.sub_polynomials.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
        (a, c) ⟨BitVec.ofNat _ k⟩ = .ok (f k, (a, c))
    unfold hacspec_ml_kem.matrix.sub_polynomials.closure.Insts.CoreOpsFunctionFnMutTupleUsizeFieldElement.call_mut
    unfold hacspec_ml_kem.matrix.sub_polynomials.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement.call
    have hk_us : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val = k := by
      show (BitVec.ofNat _ k).toNat = k
      apply Nat.mod_eq_of_lt
      have : k < 2^System.Platform.numBits := by
        have hbits : 2^16 ≤ 2^System.Platform.numBits :=
          Nat.pow_le_pow_right (by decide) (by
            cases System.Platform.numBits_eq with
            | inl h => rw [h]; decide
            | inr h => rw [h]; decide)
        omega
      exact this
    have ha_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < a.length := by
      rw [hk_us]; show k < a.val.length
      rw [a.property]; exact hk
    have hc_len : (⟨BitVec.ofNat _ k⟩ : Std.Usize).val < c.length := by
      rw [hk_us]; show k < c.val.length
      rw [c.property]; exact hk
    have h_a_idx :
        Std.Array.index_usize a (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (a.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq a
                  (⟨BitVec.ofNat _ k⟩ : Std.Usize) ha_len
      rw [hk_us] at this; exact this
    have h_c_idx :
        Std.Array.index_usize c (⟨BitVec.ofNat _ k⟩ : Std.Usize)
          = .ok (c.val[k]!) := by
      have := libcrux_iot_ml_kem.Vector.Portable.Arithmetic.LoopHelper.array_index_usize_ok_eq c
                  (⟨BitVec.ofNat _ k⟩ : Std.Usize) hc_len
      rw [hk_us] at this; exact this
    have h_sub :=
      libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_eq_ok
        (a.val[k]!) (c.val[k]!) (ha k hk') (hc k hk')
    change (do
      let fe ← (do
        let fe ← Std.Array.index_usize a ⟨BitVec.ofNat _ k⟩
        let i ← lift (Std.UScalar.cast .U32 fe.val)
        let i1 ← lift (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS)
        let i2 ← i + i1
        let fe1 ← Std.Array.index_usize c ⟨BitVec.ofNat _ k⟩
        let i3 ← lift (Std.UScalar.cast .U32 fe1.val)
        let i4 ← i2 - i3
        let i5 ← lift (Std.UScalar.cast .U32 hacspec_ml_kem.parameters.FIELD_MODULUS)
        let i6 ← i4 % i5
        let i7 ← lift (Std.UScalar.cast .U16 i6)
        hacspec_ml_kem.parameters.FieldElement.new i7)
      Result.ok (fe, a, c)) = Result.ok (f k, a, c)
    rw [h_a_idx]; simp only [bind_tc_ok]
    rw [h_c_idx]; simp only [bind_tc_ok]
    unfold hacspec_ml_kem.parameters.FieldElement.sub at h_sub
    rw [h_sub]
    simp only [bind_tc_ok, hf_def]
  unfold hacspec_ml_kem.matrix.sub_polynomials
  exact libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq 256#usize
    hacspec_ml_kem.matrix.sub_polynomials.closure.Insts.CoreOpsFunctionFnTupleUsizeFieldElement
    (a, c) f hpure

set_option maxHeartbeats 1000000 in
theorem sub_polynomials_scaleZ_eq
    (a b : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize)
    (ha : ∀ j : Nat, j < 256 →
      libcrux_iot_ml_kem.Spec.Pure.Canonical (a.val[j]!)) :
    hacspec_ml_kem.matrix.sub_polynomials a (scaleZ 512 b)
      = .ok (Spec.subtract_reduce_pure a b) := by
  have hc : ∀ k : Nat, k < 256 → Canonical ((scaleZ 512 b).val[k]!) :=
    fun k hk => canonArr_scaleZ' 512 b k hk
  rw [sub_polynomials_eq_ok a (scaleZ 512 b) ha hc]
  -- The reduced LHS array (set L); show it equals `subtract_reduce_pure a b`.
  set L : Std.Array hacspec_ml_kem.parameters.FieldElement 256#usize :=
    ⟨(List.range 256).map (fun k =>
        libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
          (a.val[k]!) ((scaleZ 512 b).val[k]!)),
     by simp [List.length_map, List.length_range]⟩ with hL_def
  have hL_lane : ∀ j : Nat, j < 256 →
      L.val[j]! = libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
                    (a.val[j]!) ((scaleZ 512 b).val[j]!) := by
    intro j hj
    show ((List.range 256).map (fun k =>
            libcrux_iot_ml_kem.Spec.Pure.FieldElement.sub_pure
              (a.val[k]!) ((scaleZ 512 b).val[k]!)))[j]! = _
    rw [getElem!_pos _ j (by simp [List.length_map, List.length_range, hj])]
    rw [List.getElem_map, List.getElem_range]
  congr 1
  apply eq_of_zmod_lane_canon
  · -- L lanes canonical
    intro j hj
    rw [hL_lane j hj]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_sub_pure _ _ (ha j hj) (hc j hj)
  · -- subtract_reduce_pure lanes canonical
    intro j hj
    have hℓ : j % 16 < 16 := Nat.mod_lt _ (by decide)
    have hjeq : 16 * (j / 16) + j % 16 = j := by omega
    unfold Spec.subtract_reduce_pure
    rw [flatten_chunk_map_lane (fun k => Spec.chunk_subtract_reduce_pure
          (Spec.chunk_at a k) (Spec.chunk_at b k)) j hj (by simp)]
    unfold Spec.chunk_subtract_reduce_pure
    rw [mkN_map_lane' _ (j % 16) hℓ]
    rw [chunk_at_lane' a (j / 16) (j % 16) hℓ, hjeq]
    exact libcrux_iot_ml_kem.Spec.Pure.Canonical_sub_pure _ _ (ha j hj)
      (libcrux_iot_ml_kem.Spec.Pure.Canonical_mul_pure _ _)
  · -- per-lane zmodOfFE equality
    intro j hj
    rw [hL_lane j hj]
    rw [zmodOfFE_sub_pure _ _ (ha j hj) (hc j hj)]
    rw [scaleZ_lane 512 b j hj]
    rw [zmodOfFE_subtract_reduce_pure_lane a b j hj (ha j hj)]

end SubPolyScaleZ

end libcrux_iot_ml_kem.Matrix.ComputeMessage.Hacspec