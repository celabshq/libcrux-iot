/-
  # `Spec/StateIso.lean` — M.3 impl ↔ MontPoly round-trip lemmas.

  Companion to `Spec.lean` (M.1) and `Spec/Commute.lean` (M.2).
  This file ships the **Decision Point I.6** injectivity pair plus an
  `lift_id` round-trip showing `to_spec_poly_plain (canonicalUnlift m) = m`
  for any `m : MontPoly`.

  ## Theorems landed (this file)

  - `to_spec_poly_mont_injective_canonical` — under the bound
    `|.val| < 1665` per lane, `to_spec_poly_mont` injective on Ints.
  - `to_spec_poly_mont_extended` — the functorial direction:
    per-lane equality of `i16_to_spec_fe_mont` ⇔ `to_spec_poly_mont`
    equality (the `←` direction; the `→` direction is M.1's
    `lemma_to_spec_poly_mont_eq_of_coeffs`).
  - `canonicalUnlift` + `to_spec_poly_plain_canonicalUnlift` — option (a)
    of the arch plan: nonneg `Fin 3329` representative carried through
    `Std.I16.ofIntCore`, then back through the plain lift gives `id`.
  - `to_spec_poly_mont_of_zero` — the zero-PolynomialRingElement lifts
    to the all-zeros `MontPoly`.

  ## Decision Point I.6 — bound choice (arch plan §D.1)

  Canonical injectivity uses `|lane.val| < 1665`. Each `ZMod 3329`
  element has a unique Int representative in `(-1664, 1664]` once we
  restrict to that bound — `i16_to_spec_fe_mont` is then a bijection
  with the integer lane value (after stripping the `· 169` factor).

  The cancellation step needs `169 · 2285 ≡ 1 (mod 3329)` (the inverse
  of `R⁻¹ = 169` is `R = 2285` in `ZMod 3329`; this is exactly
  `mont_R_inv_q` from `Util/NumericKeystones` after the `2^16 ↦ 2285`
  conversion in B.3). We pull it as `mul_169_2285_eq_one` below.

  ## Discipline

  - No `@[scoped grind]` — these are one-shot lemmas for downstream
    explicit use, not a grind set.
  - No `sorry`, no `admit`.
  Mathlib is imported here for `ZMod 3329` injectivity arguments
  (cancel `169` via the explicit inverse).
-/
import LibcruxIotMlKem.Spec
import LibcruxIotMlKem.Spec.NumericKeystones
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace libcrux_iot_ml_kem.Spec.StateIso
open CoreModels Aeneas Aeneas.Std
open libcrux_iot_ml_kem.Spec

/-! ### Local `Inhabited` instances (mirror of `Spec.lean`). -/

local instance instInhabitedPortableVector_stateIso :
    Inhabited libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  ⟨{ elements := Std.Array.make 16#usize (List.replicate 16 (0#i16 : Std.I16))
        (by simp) }⟩

local instance instInhabitedPolynomialRingElement_stateIso
    {Vector : Type} [Inhabited Vector] :
    Inhabited (libcrux_iot_ml_kem.polynomial.PolynomialRingElement Vector) :=
  ⟨{ coefficients := Std.Array.make 16#usize (List.replicate 16 default) (by simp) }⟩

/-! ## §D.1 Inverse keystone — `169 · 2285 ≡ 1 (mod 3329)`. -/

/-- The Mont-factor inverse identity: `(169 : ZMod 3329) * 2285 = 1`.
    Used to cancel the `· 169` factor in `i16_to_spec_fe_mont` when
    proving canonical injectivity. -/
theorem mul_169_2285_eq_one : (169 : ZMod 3329) * 2285 = 1 := by decide

/-- `169` is nonzero in `ZMod 3329`. -/
theorem ne_zero_169 : (169 : ZMod 3329) ≠ 0 := by decide

/-- Cancellation lemma: if `a * 169 = b * 169` in `ZMod 3329`, then
    `a = b`. -/
theorem mul_169_cancel {a b : ZMod 3329} (h : a * 169 = b * 169) : a = b := by
  -- Multiply both sides on the right by 2285, then use the inverse identity.
  have := congrArg (· * 2285) h
  simp only [mul_assoc, mul_169_2285_eq_one, mul_one] at this
  exact this

/-! ## §D.1 — extended (functorial) equivalence. -/

/-- **Extended functorial equivalence.** `to_spec_poly_mont` equality
    is equivalent to lane-by-lane equality of `i16_to_spec_fe_mont`
    (i.e. of `(.val : ZMod 3329) * 169`). The `→` direction is the
    point — `lemma_to_spec_poly_mont_eq_of_coeffs` from M.1 already
    gives the `←` direction, and this is its converse. -/
theorem to_spec_poly_mont_extended
    (re re' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_eq : to_spec_poly_mont re = to_spec_poly_mont re') :
    ∀ i j : Fin 16,
      i16_to_spec_fe_mont
        ((re.coefficients.val[i.val]!).elements.val[j.val]!)
      = i16_to_spec_fe_mont
          ((re'.coefficients.val[i.val]!).elements.val[j.val]!) := by
  intro i j
  -- Apply M.1's unfold lemma at index 16*i + j on both sides.
  have h_at := congrArg (fun v : MontPoly => v[16 * i.val + j.val]'(by
      have hi : i.val < 16 := i.isLt
      have hj : j.val < 16 := j.isLt
      omega)) h_eq
  simp only at h_at
  rw [lemma_to_spec_poly_mont_unfold, lemma_to_spec_poly_mont_unfold] at h_at
  exact h_at

/-! ## §D.1 — canonical injectivity. -/

/-- **Canonical-bounded injectivity.** If both polys have all lanes
    with `|.val|` bounded by `< 1665`, then `to_spec_poly_mont`
    equality lifts to lane-by-lane `Int`-equality.

    Proof shape:
    1. Drop to per-lane `i16_to_spec_fe_mont` equality via
       `to_spec_poly_mont_extended`.
    2. Cancel `· 169` via `mul_169_cancel`.
    3. Use the `< 1665` bound to lift `ZMod 3329` equality to
       `Int`-equality (each ZMod 3329 has a unique canonical
       representative in `(-1664, 1664]`). -/
theorem to_spec_poly_mont_injective_canonical
    (re re' : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
                libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_re  : ∀ i j : Fin 16,
              (re.coefficients.val[i.val]!.elements.val[j.val]!).val.natAbs < 1665)
    (h_re' : ∀ i j : Fin 16,
              (re'.coefficients.val[i.val]!.elements.val[j.val]!).val.natAbs < 1665)
    (h_eq  : to_spec_poly_mont re = to_spec_poly_mont re') :
    ∀ i j : Fin 16,
      (re.coefficients.val[i.val]!.elements.val[j.val]!).val =
      (re'.coefficients.val[i.val]!.elements.val[j.val]!).val := by
  intro i j
  -- Step 1: per-lane Mont-lift equality.
  have h_lane := to_spec_poly_mont_extended re re' h_eq i j
  -- Step 2: unfold + cancel `· 169`.
  rw [i16_to_spec_fe_mont_unfold, i16_to_spec_fe_mont_unfold] at h_lane
  have h_zmod := mul_169_cancel h_lane
  -- Step 3: cast back to Int.  We have:
  --   (a.val : ZMod 3329) = (b.val : ZMod 3329)  with  |a.val|, |b.val| < 1665.
  -- This forces a.val = b.val on Int because the canonical signed
  -- representative of any ZMod 3329 element in (-1664, 1664] is unique.
  set a := (re.coefficients.val[i.val]!.elements.val[j.val]!).val with ha_def
  set b := (re'.coefficients.val[i.val]!.elements.val[j.val]!).val with hb_def
  have ha : a.natAbs < 1665 := h_re i j
  have hb : b.natAbs < 1665 := h_re' i j
  -- `(a : ZMod 3329) = (b : ZMod 3329)` ⇔ `a ≡ b [ZMOD 3329]`.
  rw [ZMod.intCast_eq_intCast_iff a b 3329] at h_zmod
  -- From the bound: |a - b| < 3330, and 3329 ∣ (a - b), so a - b = 0.
  have h_diff_bound : (a - b).natAbs < 3330 := by
    have : (a - b).natAbs ≤ a.natAbs + b.natAbs := Int.natAbs_sub_le a b
    omega
  -- `Int.ModEq.dvd` gives `3329 ∣ b - a`; we want `a - b`.
  have h_div : (3329 : Int) ∣ (a - b) := by
    have h := h_zmod.dvd
    rwa [show (b - a) = -(a - b) by ring, dvd_neg] at h
  -- A multiple of 3329 with absolute value < 3330 is 0.
  have h_zero : a - b = 0 := by
    rcases h_div with ⟨k, hk⟩
    by_contra hne
    have hk_ne : k ≠ 0 := by
      rintro rfl
      simp at hk
      exact hne hk
    have hk_abs : k.natAbs ≥ 1 := Int.natAbs_pos.mpr hk_ne
    have : (a - b).natAbs = 3329 * k.natAbs := by
      rw [hk, Int.natAbs_mul]; rfl
    omega
  omega

/-! ## §D.3 — `canonicalUnlift` and `lift_id` (option (a)). -/

/-- Helper: cast a `ZMod 3329` element to its canonical nonneg
    `Std.I16` representative. `z.val < 3329 < 32768 = 2^15`, so the
    `Std.I16.ofIntCore` bounds-check goal is `decide`. -/
def i16OfZMod (z : ZMod 3329) : Std.I16 :=
  Std.I16.ofIntCore (z.val : Int) (by
    refine ⟨?_, ?_⟩
    · have h_neg : -(2:Int)^(IScalarTy.I16.numBits-1) ≤ 0 := by decide
      have h_nn : (0 : Int) ≤ (z.val : Int) := Int.natCast_nonneg _
      linarith
    · have h_lt : z.val < 3329 := ZMod.val_lt _
      have h_lt_int : (z.val : Int) < 3329 := Int.ofNat_lt.mpr h_lt
      have h_bd : (3329 : Int) < (2:Int)^(IScalarTy.I16.numBits-1) := by decide
      linarith)

/-- `Std.I16.val (i16OfZMod z) = z.val` on the `Int` side. -/
theorem i16OfZMod_val (z : ZMod 3329) : (i16OfZMod z).val = (z.val : Int) := by
  unfold i16OfZMod
  exact I16.ofInt_val_eq _

/-- `canonicalUnlift : MontPoly → PolynomialRingElement PortableVector`.
    Each lane becomes the nonneg `Fin 3329` representative cast to
    `Std.I16` via `i16OfZMod`.

    Used by `to_spec_poly_plain_canonicalUnlift` below. Note: this is
    matched against the **PLAIN** lift, not the Mont lift —
    `canonicalUnlift` does NOT preinject a Mont factor, so feeding it
    through `to_spec_poly_mont` would multiply by `169` (off by R⁻¹).
    M.4 may want a `canonicalUnliftMont` variant; out of scope here. -/
def canonicalUnlift (m : MontPoly) :
    libcrux_iot_ml_kem.polynomial.PolynomialRingElement
      libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector :=
  { coefficients := Std.Array.make 16#usize
      (List.ofFn (n := 16) fun i =>
        { elements := Std.Array.make 16#usize
            (List.ofFn (n := 16) fun j =>
              i16OfZMod (m[16 * i.val + j.val]'(by
                have hi : i.val < 16 := i.isLt
                have hj : j.val < 16 := j.isLt
                omega)))
            (by simp) })
      (by simp) }

/-- Helper: indexing into `canonicalUnlift m`'s coefficients-chunk
    at position `i < 16` yields the inner chunk with elements
    `i16OfZMod m[16*i + j]` for `j < 16`. Drives
    `to_spec_poly_plain_canonicalUnlift`. -/
theorem canonicalUnlift_chunk (m : MontPoly) (i : Fin 16) :
    (canonicalUnlift m).coefficients.val[i.val]! =
      { elements := Std.Array.make 16#usize
          (List.ofFn (n := 16) fun j : Fin 16 =>
            i16OfZMod (m[16 * i.val + j.val]'(by
              have hi : i.val < 16 := i.isLt
              have hj : j.val < 16 := j.isLt
              omega)))
          (by simp) } := by
  unfold canonicalUnlift
  show (List.ofFn _)[i.val]! = _
  rw [getElem!_pos _ _ (by rw [List.length_ofFn]; exact i.isLt),
      List.getElem_ofFn]

/-- Helper: indexing into the chunk at lane `j < 16` yields the
    `i16OfZMod` lane. -/
theorem canonicalUnlift_lane (m : MontPoly) (i j : Fin 16) :
    ((canonicalUnlift m).coefficients.val[i.val]!.elements.val[j.val]!) =
      i16OfZMod (m[16 * i.val + j.val]'(by
        have hi : i.val < 16 := i.isLt
        have hj : j.val < 16 := j.isLt
        omega)) := by
  rw [canonicalUnlift_chunk]
  show (List.ofFn _)[j.val]! = _
  rw [getElem!_pos _ _ (by rw [List.length_ofFn]; exact j.isLt),
      List.getElem_ofFn]

/-- **`lift_id` (option (a)).** After `canonicalUnlift` and re-lifting
    through `to_spec_poly_plain`, we recover the original `MontPoly`. -/
theorem to_spec_poly_plain_canonicalUnlift (m : MontPoly) :
    to_spec_poly_plain (canonicalUnlift m) = m := by
  apply Vector.ext
  intro k hk
  unfold to_spec_poly_plain
  simp only [Vector.getElem_ofFn]
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  have hk_eq : k = 16 * (k / 16) + (k % 16) := by omega
  -- Apply the helper at i = ⟨k/16, ...⟩, j = ⟨k%16, ...⟩.
  rw [canonicalUnlift_lane m ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩]
  unfold i16_to_spec_fe_plain
  rw [i16OfZMod_val]
  -- Goal: (m[16*(k/16) + k%16].val : ZMod 3329) = m[k]. Reduce the
  -- index and apply `ZMod.natCast_zmod_val`.
  have hkidx : (16 * (k / 16) + k % 16) = k := by omega
  -- Use Vector.getElem proof-irrelevance: m at equal indices are equal.
  have hget : m[16 * (k / 16) + k % 16]'(by omega) = m[k] := by
    -- This is `getElem` proof-irrelevance + index equality.
    congr 1
  show ((m[16 * (k / 16) + k % 16]'(by omega)).val : ZMod 3329) = m[k]
  rw [hget]
  exact_mod_cast ZMod.natCast_zmod_val _

/-! ## §D.4 — auxiliary lemma. -/

/-- Helper: indexing into a `List.replicate n a` at any in-bound
    position returns `a`, even with `getElem!`. -/
private theorem List_replicate_getElem!_eq {α : Type*} [Inhabited α]
    {n : Nat} (a : α) {i : Nat} (hi : i < n) :
    (List.replicate n a)[i]! = a := by
  rw [getElem!_pos _ _ (by rw [List.length_replicate]; exact hi)]
  exact List.getElem_replicate _

/-- The zero polynomial (every i16 lane = 0) lifts through
    `to_spec_poly_mont` to the all-zeros `MontPoly`.

    Phrased generically so Lean's elaborator does not eagerly unfold
    the 16×16 literal — the zero impl is constructed via `Std.Array.make`
    against a `List.replicate`-flattened input. -/
theorem to_spec_poly_mont_of_zero
    (re : libcrux_iot_ml_kem.polynomial.PolynomialRingElement
            libcrux_iot_ml_kem.vector.portable.vector_type.PortableVector)
    (h_zero : ∀ i j : Fin 16,
        ((re.coefficients.val[i.val]!).elements.val[j.val]!) = (0#i16 : Std.I16)) :
    to_spec_poly_mont re = Vector.replicate 256 (0 : ZMod 3329) := by
  apply Vector.ext
  intro k hk
  unfold to_spec_poly_mont
  simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  have hdiv_lt : k / 16 < 16 := by omega
  have hmod_lt : k % 16 < 16 := Nat.mod_lt k (by decide)
  rw [h_zero ⟨k / 16, hdiv_lt⟩ ⟨k % 16, hmod_lt⟩]
  unfold i16_to_spec_fe_mont
  show ((0#i16).val : ZMod 3329) * 169 = 0
  simp

end libcrux_iot_ml_kem.Spec.StateIso