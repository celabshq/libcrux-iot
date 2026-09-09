import Hax

/-!
# ML-DSA spec parameters (clean Z_q)

Hand-written counterpart of `~/libcrux-ml-dsa-proofs/specs/ml-dsa/src/parameters.rs`
and the `ZETAS` table in `.../ntt.rs`. This is the *clean mathematical* reference
(no Montgomery): coefficients live in `ZMod q`.

The `#guard` lines are elaboration-time checks (no axioms) pinning the zeta
construction to the hacspec `ZETAS` spot-checks and to the F* `zeta` table
(`zeta 1 = 4808194`, `zeta 128 = 1753`).
-/

namespace libcrux_iot_ml_dsa.Spec.Parameters

/-- ML-DSA prime modulus `q = 2²³ − 2¹³ + 1`. -/
abbrev Q : Nat := 8380417

/-- Coefficients per polynomial. -/
abbrev N : Nat := 256

/-- Primitive 512-th root of unity in `Z_q` (`parameters.rs::ZETA`). -/
abbrev ZETA : Nat := 1753

/-- The canonical field used by the clean spec. -/
abbrev Zq := ZMod Q

/-- Reverse the low 8 bits of `i` — the NTT zeta-index permutation `BitRev8`. -/
def bitRev8 (i : Nat) : Nat :=
  (List.range 8).foldl (fun acc b => acc ||| (((i >>> b) &&& 1) <<< (7 - b))) 0

/-- Clean zeta-table entry as a `Nat` in `[0, q)`: `ζ^BitRev8(i) mod q`
    (= hacspec `ZETAS[i]`). -/
def zetaNat (i : Nat) : Nat := (ZETA ^ bitRev8 i) % Q

/-- Clean zeta-table entry in `Z_q`. -/
def zeta (i : Nat) : Zq := (ZETA : Zq) ^ bitRev8 i

#guard bitRev8 1 = 128
#guard bitRev8 128 = 1
#guard zetaNat 0 = 1
#guard zetaNat 1 = 4808194      -- matches the F* `Spec.MLDSA.Ntt.zeta 1`
#guard zetaNat 128 = 1753       -- matches hacspec `ZETAS[128] = ζ`

end libcrux_iot_ml_dsa.Spec.Parameters
