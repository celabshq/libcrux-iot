#!/usr/bin/env python3
"""Extraction driver for libcrux-iot ML-KEM → Lean.

Three responsibilities:

1. Pin/check the hax + aeneas toolchain versions
2. Run `cargo hax into lean` with a Charon `--start-from` list
   chosen to bound the extraction boundary.
3. Patch the generated `LibcruxIotMlKem/Extraction/Funs.lean` in-place

The `aeneas-lean` backend was renamed to `lean` in mainline hax, and
`-core-models-lib` is now the default for it, so it is no longer passed
explicitly.
"""

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800"
AENEAS_VERSION = "f8a0eb8"

# Charon translation roots. Anything not reachable from these is
# dropped from `Funs.lean`.
START_FROM = [
    "crate::vector::*",
    "crate::ntt::*",
    "crate::invert_ntt::*",
    "crate::matrix::entry",
    "crate::matrix::compute_As_plus_e",
    "crate::matrix::compute_message",
    "crate::matrix::compute_ring_element_v",
    "crate::matrix::compute_vector_u",
    "crate::matrix::sample_matrix_entry",
    # INC-1: the deterministic (de)serialize + (de)compress layer. Only
    # `deserialize_to_reduced_ring_element` was reachable before (transitively via
    # matrix); this adds the eight compress_then_serialize_{4,5,10,11} /
    # deserialize_then_decompress_{4,5,10,11} entry points. The per-coefficient
    # compress/decompress primitives already extract via `crate::vector::*`
    # (vector::portable::compress). OPAQUE is deliberately unchanged: this layer is
    # deterministic and reaches neither SHAKE nor sampling.
    # INC-1: the whole deterministic (de)serialize + (de)compress layer.
    "crate::serialize::*",
    # INC-2 STEP 0 (2026-08-19): the DETERMINISTIC half of ind_cpa (k-PKE), lane 2a of
    # plans/INC-2-scope.md. `ind_cpa` had ZERO defs in Funs.lean before this — the boundary
    # stopped at serialize — while the llbc already carried the items, so this is a
    # boundary change, not new extraction capability.
    #
    # ENUMERATED, NOT `crate::ind_cpa::*`. The wholesale glob was tried first and aeneas
    # FAILED on it:
    #     Ill-formed builtin information for function ind_cpa::sample_ring_element_cbd:
    #     2 filtering arguments provided for 1 trait clauses (TraitClause0)
    #     Source: 'ml-kem/src/ind_cpa.rs', lines 176:4-182:5
    # i.e. it broke at exactly the 2a/2b boundary the scope document predicted, on a
    # SAMPLING function. That is a toolchain-level reason to keep the lanes apart, on top
    # of the proof-level ones. `crate::sampling::*` is already OPAQUE below; the sampling
    # ind_cpa entry points are simply not roots, so they stay out of Funs.lean until lane
    # 2b is a real project with the exemplars it needs.
    # Both were held back at Step 0 and are now unblocked by KB decisions (2026-08-19):
    #   serialize_vector            -> the missing core.SharedAArray…into_iter is delegated
    #                                  in FunsExternal.lean, with an upstream note; it is a
    #                                  `def` over the existing slice model, so no new axiom
    #   serialize_unpacked_secret_key -> serialize_public_key_mut was REMOVED from OPAQUE
    "crate::ind_cpa::serialize_vector",
    "crate::ind_cpa::serialize_unpacked_secret_key",
    "crate::ind_cpa::compress_then_serialize_u",
    "crate::ind_cpa::deserialize_then_decompress_u",
    "crate::ind_cpa::deserialize_vector",
    "crate::ind_cpa::encrypt_c2",
    "crate::ind_cpa::decrypt_unpacked",
    "crate::ind_cpa::decrypt",
    # NB `ind_cpa::serialize_public_key_mut` is deterministic too, but it is listed in
    # OPAQUE below (pre-existing, no rationale recorded). Left exactly as it was: Step 0
    # changes ONE thing. Un-opaquing it is a lane-2a decision, and it is a target 2a will
    # want, so it needs a deliberate answer before 2a is scaffolded.
]

# Items to keep opaque (extract signature only, skip body).
#
# The whole hash_functions module is opaque. The SHA-3 verification can be
# found in libcrux-iot/sha3.
#
# Sampling stays opaque because it calls SHAKE. Serialization is NO LONGER
# omitted as of INC-1 (see START_FROM) -- it is deterministic and SHAKE-free.
#
OPAQUE = [
    "crate::hash_functions::portable::*",
    "crate::sampling::*",
    "crate::matrix::sample_matrix_A",
    "crate::matrix::sample_matrix_entry",
]


def check_version(cmd: list[str], name: str, expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        if os.environ.get("SKIP_VERSION_CHECK") == "1":
            print(f"warning: version mismatch for {name} (expected {expected!r}); continuing because SKIP_VERSION_CHECK=1", file=sys.stderr)
            return
        print(f"Version mismatch for {name}: expected {expected!r} in output:\n{output}", file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], "hax", HAX_VERSION)
# As of cargo-hax 0.4, aeneas and charon are downloaded and checksum-verified
# by cargo-hax itself into a machine-wide cache and are not put on PATH, so
# ask cargo-hax which version the project resolves to instead of running the
# binary. `cargo hax tools install` fetches them if they are missing.
check_version(["cargo", "hax", "tools", "show"], "aeneas", AENEAS_VERSION)

charon_args = " ".join(
    [f"--start-from {root}" for root in START_FROM] +
    [f"--opaque {item}" for item in OPAQUE]
)

result = subprocess.run(
    ["cargo", "hax", "into", "lean",
     f"--charon-args={charon_args}"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
)
if result.returncode != 0:
    # HARD FAILURE, not a warning (tightened 2026-08-19, before the INC-2 root change).
    # Post-processing rewrites Funs.lean IN PLACE. Continuing past a failed extractor
    # therefore writes a plausible-looking Funs.lean built from whatever partial output
    # landed — and that file is the campaign's entire trust boundary: every proof in the
    # tree is a statement ABOUT it, and the driver gates on its sha256. A truncated
    # extraction that still parses is the worst possible outcome, because nothing
    # downstream can tell it from a good one.
    # Override deliberately with ALLOW_PARTIAL_EXTRACTION=1 if you are debugging the
    # extractor itself; never in a run whose output will be committed or locked.
    if os.environ.get("ALLOW_PARTIAL_EXTRACTION") == "1":
        print(f"warning: hax/aeneas exited {result.returncode}; continuing anyway "
              f"because ALLOW_PARTIAL_EXTRACTION=1. Output is UNTRUSTWORTHY.",
              file=sys.stderr)
    else:
        print(f"FATAL: hax/aeneas exited with code {result.returncode}. Refusing to "
              f"post-process: Funs.lean is rewritten in place and a partial extraction "
              f"would be indistinguishable from a good one.\n"
              f"  NOTE: hax/aeneas write Extraction/*.lean THEMSELVES, before this script "
              f"runs. Whatever they managed to emit is ON DISK NOW and is UNPATCHED "
              f"(no opaque->axiom rewrite, no trait-clause fixups, Specs.lean and "
              f"ProofObligations.lean not removed). It is NOT the committed extraction.\n"
              f"  RESTORE IT before doing anything else:\n"
              f"    git checkout -- proofs/lean/LibcruxIotMlKem/Extraction/\n"
              f"  Diagnostics: proofs/lean/aeneas-error.log",
              file=sys.stderr)
        sys.exit(result.returncode)

funs_lean = Path("proofs/lean/LibcruxIotMlKem/Extraction/Funs.lean")
content = funs_lean.read_text()

# Convert `axiom` declarations emitted for `--opaque` items to `opaque`.
# `axiom` adds an item to `#print axioms`; `opaque` does not. Since these
# are value-level (Result-returning) declarations whose types are
# inhabited, `opaque` is the correct keyword.
# Tracked upstream: https://github.com/AeneasVerif/aeneas/issues/1130
content = re.sub(r"^axiom ", "opaque ", content, flags=re.MULTILINE)

# Aeneas drops the second trait clause
# (`hash_functionsHashInst : hash_functions.Hash Hasher`) at call sites that
# reach `sample_matrix_entry` through nested loops. The DEFINITIONS still carry
# both trait clauses, so we only patch the CALL sites by inserting
# `hash_functionsHashInst` right after `vectortraitsOperationsInst`.
_AFFECTED_FNS = [
    "compute_vector_u_loop1_loop0.body",
    "compute_vector_u_loop1_loop0",
    "compute_vector_u_loop1.body",
    "compute_vector_u_loop1",
    "compute_vector_u_loop0.body",
    "compute_vector_u_loop0",
    "sample_matrix_entry",
]
for _fn in _AFFECTED_FNS:
    _pat = re.compile(
        r"matrix\." + re.escape(_fn) + r" (K )?vectortraitsOperationsInst(?!\s*hash_functionsHashInst)"
    )
    content = _pat.sub(
        lambda m: f"matrix.{_fn} " + (m.group(1) or "") + "vectortraitsOperationsInst hash_functionsHashInst",
        content,
    )


# cargo-hax 0.4 emits `hax_lib::loop_invariant!` as a call to
# `hax_lib._internal_loop_invariant`, a marker with no computational content that
# neither hax-lean v0.3.12 nor the generated FunsExternal template declares.
# 0.3.7 emitted nothing for it. Erase the statements rather than modelling them:
# a model that `mvcgen` steps through adds a binding to every affected body,
# which shifts the generated hypothesis names that the proofs are written
# against. Erasing keeps the body shape identical to the 0.3.7 extraction. The
# marker is a proof hint, so dropping it loses no information about behaviour.
def _erase_loop_invariant_markers(text: str) -> str:
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        stripped = lines[i].lstrip()
        if stripped.startswith("hax_lib._internal_loop_invariant"):
            indent = len(lines[i]) - len(stripped)
            i += 1
            # swallow the call's continuation lines (strictly deeper indentation)
            while i < len(lines):
                nxt = lines[i]
                if not nxt.strip():
                    break
                if len(nxt) - len(nxt.lstrip()) > indent:
                    i += 1
                else:
                    break
            continue
        out.append(lines[i])
        i += 1
    return "\n".join(out)


content = _erase_loop_invariant_markers(content)

funs_lean.write_text(content)

# The lean backend also emits per-function Specs.lean + ProofObligations.lean
# (proof-obligation scaffolding). They are not imported by the hand-written
# proofs and currently have codegen quirks (e.g. a swapped tuple order in
# `rej_sample.post`: `Usize × Slice I16` vs `Slice I16 × Usize`), so drop them.
for _f in ("Specs.lean", "ProofObligations.lean"):
    _p = Path("proofs/lean/LibcruxIotMlKem/Extraction") / _f
    if _p.exists():
        _p.unlink()
