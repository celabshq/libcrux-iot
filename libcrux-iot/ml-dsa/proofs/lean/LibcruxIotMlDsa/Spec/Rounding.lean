import LibcruxIotMlDsa.Spec.Parameters

/-!
# ML-DSA rounding spec (clean integer arithmetic)

Faithful translation of `~/libcrux-ml-dsa-proofs/specs/ml-dsa/src/arithmetic.rs`
(FIPS 204 §7.4): `mod_pm`, `power2round`, `decompose`, `high_bits`/`low_bits`,
`make_hint`, `use_hint`.

These are **integer** functions on a coefficient's canonical `[0, q)` representative
(each begins with `r⁺ = ((r % q) + q) % q ∈ [0, q)`, so they are functions of the
residue class and accept any `Int`). The rounding FC posts bridge the impl's signed
`i32` output to these via that canonical representative.

Constants: `D = 13`, `2^D = 8192`; `gamma2 ∈ {95232 = (q-1)/88, 261888 = (q-1)/32}`,
`alpha = 2·gamma2`. Validated build-time in `Spec/Validation.lean` against the Rust
test vectors (reconstruction invariants, output bounds, the `r⁺−r0 = q−1` boundary,
and `use_hint false = high_bits`).
-/

namespace libcrux_iot_ml_dsa.Spec.Rounding
open libcrux_iot_ml_dsa.Spec.Parameters

/-- Field modulus as an `Int` (`= Parameters.Q`). -/
def Qi : Int := (Q : Int)

/-- `D = BITS_IN_LOWER_PART_OF_T` (FIPS 204). -/
def Dbits : Nat := 13

/-- `2^D = 8192`. -/
def twoD : Int := 2 ^ Dbits

/-- `mod_q`: reduce `a` to `[0, q-1]` (`arithmetic.rs::mod_q`). -/
def modQ (a : Int) : Int :=
  let r := a % Qi
  if r < 0 then r + Qi else r

/-- Centered modular reduction: returns `r ∈ [-(m/2), m/2)` (`arithmetic.rs::mod_pm`).
    Requires `m > 0`. -/
def modPm (a m : Int) : Int :=
  let r := ((a % m) + m) % m
  if r > m / 2 then r - m else r

/-- **Power2Round** — FIPS 204 Alg 35 (`arithmetic.rs::power2round`).
    `r ↦ (r1, r0)` with `r ≡ r1·2^D + r0 (mod q)` and `r0 ∈ (-2^(D-1), 2^(D-1)]`. -/
def power2round (r : Int) : Int × Int :=
  let rPlus := r % Qi
  let rPlus := if rPlus < 0 then rPlus + Qi else rPlus
  let r0 := modPm rPlus twoD
  let r1 := (rPlus - r0) / twoD
  (r1, r0)

/-- **Decompose** — FIPS 204 Alg 36 (`arithmetic.rs::decompose`).
    `r ↦ (r1, r0)` with `r ≡ r1·(2·gamma2) + r0 (mod q)` and `|r0| ≤ gamma2`.
    Boundary: when `r⁺ − r0 = q − 1`, returns `(0, r0 − 1)`. -/
def decompose (r gamma2 : Int) : Int × Int :=
  let rPlus := r % Qi
  let rPlus := if rPlus < 0 then rPlus + Qi else rPlus
  let alpha := 2 * gamma2
  let r0 := modPm rPlus alpha
  if rPlus - r0 = Qi - 1 then (0, r0 - 1)
  else
    let r1 := (rPlus - r0) / alpha
    (r1, r0)

/-- **HighBits** — FIPS 204 Alg 37 (`= (decompose r gamma2).1`). -/
def highBits (r gamma2 : Int) : Int := (decompose r gamma2).1

/-- **LowBits** — FIPS 204 Alg 38 (`= (decompose r gamma2).2`). -/
def lowBits (r gamma2 : Int) : Int := (decompose r gamma2).2

/-- **MakeHint** — FIPS 204 Alg 39 (`arithmetic.rs::make_hint`).
    `true` iff adding `z` to `r` changes the high bits. -/
def makeHint (z r gamma2 : Int) : Bool :=
  highBits r gamma2 != highBits (modQ (r + z)) gamma2

/-- **UseHint** — FIPS 204 Alg 40 (`arithmetic.rs::use_hint`).
    Adjusts the high bits of `r` according to hint `h`. -/
def useHint (hint : Bool) (r gamma2 : Int) : Int :=
  let m := (Qi - 1) / (2 * gamma2)
  let p := decompose r gamma2
  let r1 := p.1
  let r0 := p.2
  if hint = true ∧ r0 > 0 then (r1 + 1) % m
  else if hint = true ∧ r0 ≤ 0 then ((r1 - 1) % m + m) % m
  else r1

/-- **ComputeHint** — the SIMD-level hint bit (`arithmetic.rs::compute_one_hint`).
    Given the already-decomposed `low`/`high` bits of a coefficient, returns `1`
    iff the low bits leave the centered range `[-gamma2, gamma2]` (with the
    `low = -gamma2 ∧ high ≠ 0` boundary set), else `0`.

    NB: this is the libcrux SIMD-level bit on decomposed `(low, high)` inputs; the
    FIPS `makeHint (z, r)` (= `highBits r ≠ highBits (r+z)`) connection is a
    higher-level property (the callers supply `low`/`high` so that they agree). -/
def computeHint (low high gamma2 : Int) : Int :=
  if low > gamma2 ∨ low < -gamma2 ∨ (low = -gamma2 ∧ high ≠ 0) then 1 else 0

end libcrux_iot_ml_dsa.Spec.Rounding
