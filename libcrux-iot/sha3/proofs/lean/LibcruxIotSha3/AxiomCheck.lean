import LibcruxIotSha3.Sponge.Shake

/-!
# Axiom hygiene regression check

This module makes `lake build` **fail** if any of the six top-level digest
specs comes to depend on `sorryAx` — i.e. on an admitted `sorry` anywhere in
its proof tree, including the hand-written Aeneas stdlib models (e.g. the
admitted `core.slice.Slice.get_unchecked` spec).

It deliberately does *not* pin the full axiom set: that set legitimately
includes many `bv_decide` axioms with hygienic (`✝`-suffixed) names that are
not stable enough to match exactly. We only assert the soundness-critical
property — no `sorry` — which is what `propext`/`Classical.choice`/`Quot.sound`
and `bv_decide` are explicitly *not*.

See the "Axiom hygiene" section of `README.md`.
-/

open Lean Elab Command

/-- `#assert_no_sorry foo` errors (failing the build) if `foo` transitively
depends on `sorryAx`. On success it logs a one-line confirmation with the
total axiom count. -/
syntax (name := assertNoSorry) "#assert_no_sorry " ident : command

@[command_elab assertNoSorry]
def elabAssertNoSorry : CommandElab := fun stx => do
  match stx with
  | `(#assert_no_sorry $id:ident) =>
    let cs ← liftCoreM <| realizeGlobalConstWithInfos id
    for c in cs do
      let axioms ← collectAxioms c
      if axioms.contains ``sorryAx then
        throwError "AXIOM HYGIENE VIOLATION: '{c}' transitively depends on `sorryAx`"
      logInfo m!"'{c}' is sorry-free ({axioms.size} axioms)"
  | _ => throwUnsupportedSyntax

namespace libcrux_iot_sha3.Sponge

#assert_no_sorry shake128_spec
#assert_no_sorry shake256_spec
#assert_no_sorry sha224_ema_spec
#assert_no_sorry sha256_ema_spec
#assert_no_sorry sha384_ema_spec
#assert_no_sorry sha512_ema_spec

end libcrux_iot_sha3.Sponge
