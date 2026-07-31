import LibcruxIotMlDsa.Spec.Pure
import LibcruxIotMlDsa.Spec.Parameters
import LibcruxIotMlDsa.Spec.Rounding

/-!
# ML-DSA spec validation — build-time, axiom-free (`#guard` only)

Pins the hand-written clean-`Z_q` spec (`Spec/Pure.lean`, `Spec/Parameters.lean`)
to its Rust reference (`~/libcrux-ml-dsa-proofs/specs/ml-dsa/src/ntt.rs`). Mirrors
ML-KEM's committed cross-spec tests. All checks are `#guard` (elaboration-time,
no axioms):

* `bitRev8` is an involution and a bijection on `[0, 256)`;
* the Lean zeta table equals the Rust `ZETAS` literal on all 256 entries
  (`zetaNat i = ZETAS[i]`); externally (Python) the Rust literal was confirmed
  equal to the `ζ^BitRev8(k) mod q` construction, so all three agree;
* `intt (ntt p) = p` on representative inputs, including the exact Rust
  unit-test vector (`p[0]=1, p[1]=2, p[255]=100`).
-/
namespace libcrux_iot_ml_dsa.Spec.Validation
open libcrux_iot_ml_dsa.Spec.Pure
open libcrux_iot_ml_dsa.Spec.Parameters

/-- The Rust `ZETAS` table verbatim (`specs/ml-dsa/src/ntt.rs`, generated). -/
def ZETAS : Array Nat := #[
    1, 4808194, 3765607, 3761513, 5178923, 5496691, 5234739, 5178987, 7778734, 3542485, 2682288, 2129892, 3764867, 7375178, 557458, 7159240,
    5010068, 4317364, 2663378, 6705802, 4855975, 7946292, 676590, 7044481, 5152541, 1714295, 2453983, 1460718, 7737789, 4795319, 2815639, 2283733,
    3602218, 3182878, 2740543, 4793971, 5269599, 2101410, 3704823, 1159875, 394148, 928749, 1095468, 4874037, 2071829, 4361428, 3241972, 2156050,
    3415069, 1759347, 7562881, 4805951, 3756790, 6444618, 6663429, 4430364, 5483103, 3192354, 556856, 3870317, 2917338, 1853806, 3345963, 1858416,
    3073009, 1277625, 5744944, 3852015, 4183372, 5157610, 5258977, 8106357, 2508980, 2028118, 1937570, 4564692, 2811291, 5396636, 7270901, 4158088,
    1528066, 482649, 1148858, 5418153, 7814814, 169688, 2462444, 5046034, 4213992, 4892034, 1987814, 5183169, 1736313, 235407, 5130263, 3258457,
    5801164, 1787943, 5989328, 6125690, 3482206, 4197502, 7080401, 6018354, 7062739, 2461387, 3035980, 621164, 3901472, 7153756, 2925816, 3374250,
    1356448, 5604662, 2683270, 5601629, 4912752, 2312838, 7727142, 7921254, 348812, 8052569, 1011223, 6026202, 4561790, 6458164, 6143691, 1744507,
    1753, 6444997, 5720892, 6924527, 2660408, 6600190, 8321269, 2772600, 1182243, 87208, 636927, 4415111, 4423672, 6084020, 5095502, 4663471,
    8352605, 822541, 1009365, 5926272, 6400920, 1596822, 4423473, 4620952, 6695264, 4969849, 2678278, 4611469, 4829411, 635956, 8129971, 5925040,
    4234153, 6607829, 2192938, 6653329, 2387513, 4768667, 8111961, 5199961, 3747250, 2296099, 1239911, 4541938, 3195676, 2642980, 1254190, 8368000,
    2998219, 141835, 8291116, 2513018, 7025525, 613238, 7070156, 6161950, 7921677, 6458423, 4040196, 4908348, 2039144, 6500539, 7561656, 6201452,
    6757063, 2105286, 6006015, 6346610, 586241, 7200804, 527981, 5637006, 6903432, 1994046, 2491325, 6987258, 507927, 7192532, 7655613, 6545891,
    5346675, 8041997, 2647994, 3009748, 5767564, 4148469, 749577, 4357667, 3980599, 2569011, 6764887, 1723229, 1665318, 2028038, 1163598, 5011144,
    3994671, 8368538, 7009900, 3020393, 3363542, 214880, 545376, 7609976, 3105558, 7277073, 508145, 7826699, 860144, 3430436, 140244, 6866265,
    6195333, 3123762, 2358373, 6187330, 5365997, 6663603, 2926054, 7987710, 8077412, 3531229, 4405932, 4606686, 1900052, 7598542, 1054478, 7648983
]

#guard ZETAS.size = 256
#guard (List.range 256).all (fun i => bitRev8 (bitRev8 i) = i)
#guard ((List.range 256).map bitRev8).toArray.qsort (· < ·) = (List.range 256).toArray
#guard (List.range 256).all (fun i => zetaNat i = ZETAS[i]!)

private def p0 : SpecPoly := build (fun i => (i : Zq))
private def p1 : SpecPoly := build (fun i => (3 * i + 1 : Zq))
/-- Rust `ntt_intt_roundtrip` test vector: `p[0]=1, p[1]=2, p[255]=100`. -/
private def pR : SpecPoly :=
  build (fun i => if i = 0 then (1 : Zq) else if i = 1 then 2 else if i = 255 then 100 else 0)

#guard intt (ntt p0) == p0
#guard intt (ntt p1) == p1
#guard intt (ntt pR) == pR

/-! ## Pointwise poly `add`/`sub` sanity (`Spec/Pure.lean`). -/

-- `poly_add` is lane-wise `+`, `poly_sub` lane-wise `-`.
#guard (poly_add p0 p1)[5]! == p0[5]! + p1[5]!
#guard (poly_sub p0 p1)[5]! == p0[5]! - p1[5]!
-- `add`/`sub` are mutual inverses: `(a + b) - b = a`.
#guard poly_sub (poly_add p0 p1) p1 == p0
#guard poly_sub (poly_add pR p1) p1 == pR
-- `a - a = 0`, `a + 0 = a`.
#guard poly_sub p1 p1 == build (fun _ => (0 : Zq))
#guard poly_add p1 (build (fun _ => (0 : Zq))) == p1

/-! ## Rounding spec (`Spec/Rounding.lean`) — validated vs `arithmetic.rs` + its tests.

Mirrors the Rust unit tests (`power2round_basic`, `decompose_basic`,
`high_low_bits_roundtrip`, `use_hint_no_hint`) plus the reconstruction invariants
and output bounds (Python-confirmed across 200k random inputs each). -/
open libcrux_iot_ml_dsa.Spec.Rounding

private def g44 : Int := 95232   -- (q-1)/88, ML-DSA-44
private def g65 : Int := 261888  -- (q-1)/32, ML-DSA-65/87
/-- Test coefficients: 0, 1, 100, q/2, q-2, q-1 (incl. the boundary q-1). -/
private def rounds : List Int := [0, 1, 100, 4190208, 8380415, 8380416]

-- gamma2 constants match (q-1)/88 and (q-1)/32
#guard g44 = (Qi - 1) / 88
#guard g65 = (Qi - 1) / 32

-- power2round: basic vectors + reconstruction `r ≡ r1·2^D + r0 (mod q)` + `|r0| ≤ 2^12`
#guard power2round 0 = (0, 0)
#guard (let (r1, r0) := power2round 8192; r1 * twoD + r0) = 8192
#guard rounds.all (fun r => decide (let (r1, r0) := power2round r; modQ (r1 * twoD + r0) = modQ r))
#guard rounds.all (fun r => decide ((power2round r).2.natAbs ≤ 4096))

-- decompose: reconstruction `r ≡ r1·alpha + r0 (mod q)` + `|r0| ≤ gamma2`, both gamma2
#guard rounds.all (fun r => decide (let (r1, r0) := decompose r g44; modQ (r1 * (2 * g44) + r0) = modQ r))
#guard rounds.all (fun r => decide (let (r1, r0) := decompose r g65; modQ (r1 * (2 * g65) + r0) = modQ r))
#guard rounds.all (fun r => decide ((decompose r g44).2.natAbs ≤ 95232))
#guard rounds.all (fun r => decide ((decompose r g65).2.natAbs ≤ 261888))
-- boundary `r⁺ − r0 = q − 1` ⇒ `r1 = 0`, returning `(0, r0 − 1)` at `r = q − 1`
#guard decompose 8380416 g44 = (0, -1)
#guard decompose 8380416 g65 = (0, -1)

-- high/low_bits projections + use_hint(false) = high_bits (Rust `use_hint_no_hint`)
#guard rounds.all (fun r => decide (highBits r g65 = (decompose r g65).1 ∧ lowBits r g65 = (decompose r g65).2))
#guard rounds.all (fun r => decide (useHint false r g65 = highBits r g65))

-- compute_hint: SIMD-level bit (`compute_one_hint`) — set iff low leaves `[-gamma2, gamma2]`
#guard computeHint (g65 + 1) 0 g65 = 1        -- low > gamma2
#guard computeHint (-g65 - 1) 0 g65 = 1       -- low < -gamma2
#guard computeHint (-g65) 5 g65 = 1           -- low = -gamma2 ∧ high ≠ 0 (boundary set)
#guard computeHint (-g65) 0 g65 = 0           -- low = -gamma2 ∧ high = 0 (boundary clear)
#guard computeHint 0 0 g65 = 0                -- in range
#guard computeHint g65 0 g65 = 0              -- low = gamma2 (not strictly >)
#guard [(-g65-1,3),(-g65,0),(0,0),(g65,1),(g65+1,0)].all
  (fun p => decide (computeHint p.1 p.2 g65 = 0 ∨ computeHint p.1 p.2 g65 = 1))

/-! ## Infinity-norm-exceeds spec (`Spec/Pure.lean`) — `arithmetic.rs::infinity_norm_exceeds`.

`infinity_norm_exceeds coeffs bound` is `∃ i < 256, bound ≤ |coeffs i|`. Validated on
small explicit polys (true/false cases), plus the `coeff_norm` cross-check that for
CENTERED representatives (`|a| ≤ q/2`) the impl's raw `|a|` agrees with the FIPS
`coeff_norm a` (plausible-first discipline, §D.3). -/

-- `coeff_norm a = |a|` for centered representatives (`|a| ≤ q/2 = 4190208`), so the
-- impl's raw `bound ≤ |a|` agrees with the FIPS `bound ≤ coeff_norm a`.
#guard [(-4190208 : Int), -100, -1, 0, 1, 100, 4190208].all
  (fun a => decide (coeff_norm a = |a|))
-- and the rejection test agrees with `coeff_norm` for centered inputs, both directions.
#guard [((-4190208 : Int), (4190208 : Int)), (100, 50), (100, 101), (-100, 100), (0, 1)].all
  (fun p => decide ((p.2 ≤ |p.1|) = (p.2 ≤ coeff_norm p.1)))

-- TRUE case: a poly with coefficient 5 at index 3, bound 5 (≥, so 5 ≤ |5| holds).
#guard decide (infinity_norm_exceeds (fun i => if i = 3 then 5 else 0) 5)
-- TRUE case: a negative coefficient -7 at index 200, bound 7 (7 ≤ |-7| = 7).
#guard decide (infinity_norm_exceeds (fun i => if i = 200 then -7 else 0) 7)
-- FALSE case: all coefficients 0, bound 1 (no |0| = 0 ≥ 1).
#guard !decide (infinity_norm_exceeds (fun _ => 0) 1)
-- FALSE case: max coefficient 4 everywhere, bound 5 (4 < 5).
#guard !decide (infinity_norm_exceeds (fun _ => 4) 5)
-- boundary: bound 5, coefficient exactly 5 ⇒ TRUE (the check is `≥`, not `>`).
#guard decide (infinity_norm_exceeds (fun i => if i = 0 then 5 else 0) 5)
-- boundary: bound 6, coefficient exactly 5 ⇒ FALSE.
#guard !decide (infinity_norm_exceeds (fun i => if i = 0 then 5 else 0) 6)
-- out-of-range index does not count: coefficient at i=256 ignored (i < 256 required).
#guard !decide (infinity_norm_exceeds (fun i => if i = 256 then 1000 else 0) 1)

/-! ## `zero_poly` sanity (`Spec/Pure.lean`). -/

-- every lane of `zero_poly` is `0`, and it has 256 coefficients.
#guard (List.range 256).all (fun i => zero_poly[i]! == (0 : Zq))
#guard zero_poly.size = 256

end libcrux_iot_ml_dsa.Spec.Validation
