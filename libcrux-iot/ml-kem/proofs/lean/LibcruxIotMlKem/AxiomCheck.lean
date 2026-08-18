import LibcruxIotMlKem.SerializeFc
import LibcruxIotMlKem.Matrix.ComputeMessage.FC
import LibcruxIotMlKem.Matrix.ComputeMessage.FC

/-!
# Axiom hygiene regression check

Makes `lake build` **fail** if any listed result comes to depend on `sorryAx` —
i.e. on an admitted `sorry` anywhere in its proof tree.

Ported from `LibcruxIotSha3/AxiomCheck.lean`; ml-dsa carries the equivalent as a
`#print axioms` + `#guard_msgs` build guard. ml-kem had four `#guard_msgs` guards
(the matrix apexes) and **none at all in `SerializeFc.lean`** — precisely the file
that carries sorried obligations.

## Why this matters here specifically

`SerializeFc.lean` currently holds `@[spec]`-tagged theorems whose bodies are
`sorry`. `@[spec]` registers a theorem for `mvcgen` to consume, so a *different*
proof can silently discharge a goal using an unproved — or, worse, a **refuted** —
statement. That is not hypothetical: `deserialize_then_decompress_ring_element_v_fc`
is stated with an unconstrained `V_COMPRESSION_FACTOR` and a `⌜True⌝` precondition,
and **this same file proves its negation** (`specreq_L53_refuted_at_dv_zero`). A
caller-shaped Triple at the refuted instance `dv = 0` closes with a bare `mvcgen`
and compiles with no error or warning; the only signal is `#print axioms`.

So the sorried `@[spec]` theorems below must be **restated**, not proved:
  * `deserialize_then_decompress_ring_element_v_fc`   (refuted at dv = 0 and dv = 4)
  * `compress_then_serialize_ring_element_v_fc`       (refuted)
  * `serialize_uncompressed_ring_element_fc`          (missing `is_bounded_poly 3328`)
  * `compress_then_serialize_message_fc`              (missing `is_bounded_poly 3328`)
  * `deserialize_ring_elements_reduced_fc`            (leaf is the A2 axiom)

This module asserts the sorry-freedom of what IS closed, so those results cannot
silently regress while the open ones are being restated.

It deliberately does not pin the full axiom set per target — that is the driver
gate's job (`driver/verify.sh` compares `#print axioms` against a per-target
allowlist by exact set difference, and rejects any axiom containing `._native.`).
Here we assert only the soundness-critical property: no `sorry`.
-/

open Lean Elab Command

/-- `#assert_no_sorry foo` errors (failing the build) if `foo` transitively
depends on `sorryAx`. On success it logs the total axiom count. -/
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

/-! ## Closed INC-1 obligations (kernel-verified axiom-clean) -/
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.deserialize_to_uncompressed_ring_element_fc
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.deserialize_then_decompress_message_fc

/-! ## Kind exemplars the campaign's readiness gate depends on.
    If one of these acquires a `sorry`, every "FULL" verdict resting on it is void. -/
#assert_no_sorry libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl.loop_chunks_exact_enumerate_spec
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl.loop_chunks_exact_pk_spec

/-! ## Matrix apexes (already `#guard_msgs`-guarded in their own files; this adds
    a sorry-freedom assertion that survives a `#guard_msgs` message drift). -/
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeAsPlusE.compute_As_plus_e_fc
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc
