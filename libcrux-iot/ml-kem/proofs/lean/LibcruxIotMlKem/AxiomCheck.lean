import LibcruxIotMlKem.SerializeFc
import LibcruxIotMlKem.IndCpaFc
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

**UPDATED 2026-08-18.** All five were RESTATED (the refutations above are why the
hypotheses exist; they do not refute the current statements), and three have since been
closed and are asserted below. Current state:
  * `deserialize_ring_elements_reduced_fc`            CLOSED — leaf is the A2 axiom, by design
  * `serialize_uncompressed_ring_element_fc`          CLOSED — axiom-clean
  * `compress_then_serialize_message_fc`              CLOSED — axiom-clean
  * `deserialize_then_decompress_ring_element_v_fc`   CLOSED 2026-08-19 — axiom-clean
  * `compress_then_serialize_ring_element_v_fc`       CLOSED 2026-08-19 — axiom-clean

**UPDATED 2026-08-20**, closing a REAL GAP a reviewer found (INC-2a.4 r1, med/debt): this
module was guarding 5 of the file's closed obligations while 7 were closed, and the three
most expensive closes were among the unguarded. Every closed obligation in the campaign is
now asserted here — the two `_v` siblings above, the two INC-2a `_u` per-element ones, and
the three `IndCpaFc` ones (which needed the import added). If you close another, ADD IT: the
list is hand-maintained, which is itself recorded debt.

This module asserts the sorry-freedom of what IS closed, so those results cannot
silently regress while later obligations are worked on in the same files.

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
-- Phase 3 closes. `deserialize_ring_elements_reduced_fc` rests on the A2 axiom by design
-- (that is its declared allowlist, not a gap); this assertion is about sorry-freedom only,
-- which is exactly the property that must not regress while L5.3/L5.4 are worked on.
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.deserialize_ring_elements_reduced_fc
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.serialize_uncompressed_ring_element_fc
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.compress_then_serialize_message_fc
-- L5.3 / L5.4, closed 2026-08-19. Added 2026-08-20 — they had been closed for a day with no
-- guard here, which is the gap the INC-2a.4 review found.
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.deserialize_then_decompress_ring_element_v_fc
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.compress_then_serialize_ring_element_v_fc

/-! ## Closed INC-2a obligations -/
-- The `_u` per-element family at du ∈ {10,11} (2026-08-20). Same file as L5.3/L5.4 and the
-- same private banks, so a regression here is exactly the cross-obligation kind this guard
-- exists for.
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.deserialize_then_decompress_ring_element_u_fc
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.compress_then_serialize_ring_element_u_fc
-- The ind_cpa lane-2a chain. `serialize_public_key_mut_fc` composes `serialize_vector_fc`,
-- which composes L5.6, so a `sorry` anywhere below is a `sorry` in all three.
#assert_no_sorry libcrux_iot_ml_kem.IndCpaFc.deserialize_vector_fc
#assert_no_sorry libcrux_iot_ml_kem.IndCpaFc.serialize_vector_fc
#assert_no_sorry libcrux_iot_ml_kem.IndCpaFc.serialize_public_key_mut_fc
-- The whole-vector ciphertext-u encode (2026-08-20). It composes
-- `compress_then_serialize_ring_element_u_fc` above, so a `sorry` in that leaf is a `sorry`
-- here too — and this is the guard that says so at build time rather than at review time.
#assert_no_sorry libcrux_iot_ml_kem.IndCpaFc.compress_then_serialize_u_fc

/-! ## Kind exemplars the campaign's readiness gate depends on.
    If one of these acquires a `sorry`, every "FULL" verdict resting on it is void. -/
#assert_no_sorry libcrux_iot_ml_kem.Util.CreateI.createi_pure_eq
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl.loop_chunks_exact_enumerate_spec
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeRingElementV.Impl.loop_chunks_exact_pk_spec
-- The exemplars Phase 3 has actually consumed (kernel-verified, not self-reported):
-- M-B(1,2) carry L5.6, M-D(1,2) carry L5.2. If one of these acquires a `sorry`, the
-- obligation resting on it is void even though its own `#assert_no_sorry` still passes
-- from a stale build.
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.byte_encode_12_eq
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.byte_encode_into_12_eq
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.compress_message_coefficient_eq
#assert_no_sorry libcrux_iot_ml_kem.SerializeFc.compress_1_threshold_eq

/-! ## Matrix apexes (already `#guard_msgs`-guarded in their own files; this adds
    a sorry-freedom assertion that survives a `#guard_msgs` message drift). -/
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeAsPlusE.compute_As_plus_e_fc
#assert_no_sorry libcrux_iot_ml_kem.Matrix.ComputeMessage.FC.compute_message_fc
