import LibcruxIotMlDsa.Spec.Pure
import LibcruxIotMlDsa.Extraction.Funs

/-!
# The lift bridge (impl Montgomery i32 → clean `Z_q`)

Analogue of ML-KEM's `Spec/Lift.lean`. The impl stores coefficients as signed,
possibly non-canonical **Montgomery-domain** `i32` lanes (8 per `Coefficients`
SIMD unit, 32 units per `PolynomialRingElement`). The clean spec
(`Spec/Pure.lean`) uses a flat 256-array of canonical `Z_q`. The lift maps the
former to the latter.

The **impl-independent** core (`liftZ`) lives here. The **impl-shaped**
lifts (`lift_coeffs`, `lift_poly`, `lift_vec`, `lift_matrix`) reference the
extracted types in `Extraction/Funs.lean`.
-/

namespace libcrux_iot_ml_dsa.Spec.Lift
open libcrux_iot_ml_dsa.Spec.Parameters
open libcrux_iot_ml_dsa.Spec

/-- Strip Montgomery from a signed coefficient: interpret the integer mod `q`,
    then multiply by `R⁻¹`. A Montgomery-domain value `x = a·R (mod q)` lifts to
    the clean `a`. -/
def liftZ (x : Int) : Zq := (x : Zq) * (Montgomery.RINV : Zq)

/-- `liftZ` of a plain (already-clean) integer is just its residue — used when a
    seam is asserted to be in the standard (non-Montgomery) domain. Distinguish
    the two via explicit per-seam `scaleZ`-style factors (SKILL §13.13). -/
def liftZ_std (x : Int) : Zq := (x : Zq)

/-! ## `liftZ` seam lemmas (the R-reconciliation algebra)

The NTT impl works entirely in the Montgomery domain (coefficients `= â·R`,
inline zetas `= ζ·R`); the spec is clean `Z_q`. `liftZ` strips exactly one `R`.
The two seams the butterflies need:

* **mont-mul → clean-mul**: `montgomery_multiply_fe_by_fer b c = b·c·R⁻¹` (raw),
  and `liftZ` of that is `liftZ b · liftZ c` — i.e. a Montgomery product lifts to
  a clean product (both sides equal `(b)(c)·R⁻²` in `Z_q`).
* **`liftZ` is additive** over the raw integer values, so the `a ± t` halves of a
  butterfly lift to `liftZ a ± liftZ t`. -/

/-- The Montgomery-multiply seam. If a raw result `r` satisfies the
    `montgomery_multiply_fe_by_fer` post `(r : Z_q) = (b)(c)·R⁻¹` (the
    `liftZ_std` form of `Arithmetic.montgomery_multiply_fe_by_fer_spec`), then
    stripping one more `R` from each side gives the clean product. -/
theorem liftZ_of_mont (r b c : Int)
    (h : (r : Zq) = (b : Zq) * (c : Zq) * (Montgomery.RINV : Zq)) :
    liftZ r = liftZ b * liftZ c := by
  unfold liftZ
  rw [h]; ring

/-- `liftZ` is additive on the raw integer values. -/
theorem liftZ_add (x y : Int) : liftZ (x + y) = liftZ x + liftZ y := by
  unfold liftZ; push_cast; ring

/-- `liftZ` is subtractive on the raw integer values. -/
theorem liftZ_sub (x y : Int) : liftZ (x - y) = liftZ x - liftZ y := by
  unfold liftZ; push_cast; ring

open Aeneas.Std in
/-- 8 lanes of one SIMD unit → 8 clean field elements (`liftZ` strips Montgomery). -/
def lift_coeffs (u : libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) : Array Zq :=
  ((List.range 8).map (fun j => liftZ (u.values.val[j]!).val)).toArray

-- `lift_poly` indexes a list of `Coefficients` with `[·]!`, which needs `Inhabited`.
deriving instance Inhabited for libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients

open Aeneas.Std in
/-- 32 units × 8 lanes → flat 256-array (`simd_units_to_array` analogue), each
    lane mont-stripped via `liftZ`. -/
def lift_poly
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    Pure.SpecPoly :=
  Pure.build (fun i => liftZ ((re.simd_units.val[i / 8]!).values.val[i % 8]!).val)

open Aeneas.Std in
/-- 32 units × 8 lanes (as a raw SIMD-unit array) → flat 256-array. The
    `Array`-level analogue of `lift_poly`; the layer drivers operate on the
    `.simd_units` field directly and speak this. -/
def lift_units
    (arr : Aeneas.Std.Array libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients 32#usize) :
    Pure.SpecPoly :=
  Pure.build (fun i => liftZ ((arr.val[i / 8]!).values.val[i % 8]!).val)

/-- `lift_poly` is `lift_units` on the `.simd_units` field. -/
theorem lift_poly_eq_lift_units
    (re : libcrux_iot_ml_dsa.polynomial.PolynomialRingElement
            libcrux_iot_ml_dsa.simd.portable.vector_type.Coefficients) :
    lift_poly re = lift_units re.simd_units := rfl

/-! ## Zeta-bridge spot-checks (build-time R-reconciliation, SKILL §13.13)

`liftZ (inline montgomery zeta literal) = Parameters.zeta (spec index)` — i.e. the
impl's centered Montgomery zetas satisfy `zeta_r(i) ≡ ζ^BitRev8(i)·R (mod q)`, so
stripping one `R` recovers the clean table entry. Spot-checked here at elaboration
time on the layer-0 within-unit zetas (rounds 0,1 → spec idx 128–135) and the
layer-3 cross-unit zetas (`outer_3_plus` call k → spec idx 16+k). The full
per-literal bridge is proven at the driver level. -/
#guard liftZ (2091667 : Int) == zeta 128
#guard liftZ (3407706 : Int) == zeta 129
#guard liftZ (2316500 : Int) == zeta 130
#guard liftZ (3817976 : Int) == zeta 131
#guard liftZ (-3342478 : Int) == zeta 132
#guard liftZ (2244091 : Int) == zeta 133
#guard liftZ (-2446433 : Int) == zeta 134
#guard liftZ (-3562462 : Int) == zeta 135
#guard liftZ (2725464 : Int) == zeta 16
#guard liftZ (1024112 : Int) == zeta 17
#guard liftZ (-1079900 : Int) == zeta 18

end libcrux_iot_ml_dsa.Spec.Lift
