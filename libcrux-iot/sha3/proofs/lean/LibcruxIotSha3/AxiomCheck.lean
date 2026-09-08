import LibcruxIotSha3.Sponge.Shake
import LibcruxIotSha3.Verification.ProofObligations

/-!
# Axiom hygiene regression check

This module makes `lake build` **fail** if any of the six top-level digest
specs (or the `keccak` contract discharge) comes to depend on anything beyond
Lean's three standard axioms `propext`, `Classical.choice`, `Quot.sound`. In
particular that rules out `sorryAx` (an admitted `sorry` anywhere in the proof
tree, including the hand-written Aeneas stdlib models) and `Lean.ofReduceBool`
(the axiom behind `bv_decide`/`native_decide`; the development used `bv_decide`
for its bit-vector identities until they were re-proved per bit).

See the "Axiom hygiene" section of `README.md`.
-/

open Lean Elab Command

/-- `#assert_std_axioms foo` errors (failing the build) if `foo` transitively
depends on any axiom other than `propext`, `Classical.choice`, `Quot.sound`.
On success it logs the axioms actually used. -/
syntax (name := assertStdAxioms) "#assert_std_axioms " ident : command

@[command_elab assertStdAxioms]
def elabAssertStdAxioms : CommandElab := fun stx => do
  match stx with
  | `(#assert_std_axioms $id:ident) =>
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    for c in cs do
      let axioms ← collectAxioms c
      let extra := axioms.filter fun a => !(allowed.contains a)
      if !extra.isEmpty then
        throwError "AXIOM HYGIENE VIOLATION: '{c}' depends on non-standard axioms {extra}"
      logInfo m!"'{c}' uses only standard axioms {axioms}"
  | _ => throwUnsupportedSyntax

namespace libcrux_iot_sha3.Sponge

#assert_std_axioms shake128_spec
#assert_std_axioms shake256_spec
#assert_std_axioms sha224_ema_spec
#assert_std_axioms sha256_ema_spec
#assert_std_axioms sha384_ema_spec
#assert_std_axioms sha512_ema_spec
#assert_std_axioms keccak.keccak_keccak_spec

end libcrux_iot_sha3.Sponge

namespace libcrux_iot_sha3.Verification

#assert_std_axioms keccak_spec_proof
#assert_std_axioms sha256_ema_spec_proof

end libcrux_iot_sha3.Verification
