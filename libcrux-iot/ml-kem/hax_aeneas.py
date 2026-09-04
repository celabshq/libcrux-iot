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

HAX_VERSION = "cbce2c3bfcf50e853d3115c45cd592004d7d092f"
AENEAS_VERSION = "6852e64"

# Charon translation roots. Anything not reachable from these is
# dropped from `Funs.lean`.
START_FROM = [
    "crate::vector::*",
    "crate::polynomial::*",
    "crate::ntt::*",
    "crate::invert_ntt::*",
    # NOTE on globs vs enumerated roots. The hax lean backend emits
    # `<fn>.pre`/`.post`/`.spec` ONLY for items covered by a GLOB root. While
    # these were enumerated one by one, the 8 `#[hax_lib::requires]` /
    # `#[ensures]` in matrix.rs produced NO generated specs at all -- silently,
    # nothing in the hax or aeneas output. Confirmed by globbing
    # `crate::polynomial::*` above, which immediately produced `polynomial.zeta`'s
    # missing spec.
    #
    # `crate::matrix::*` WAS tried and has to stay enumerated: the glob generates
    # specs for the whole module, and three of them do not compile.
    #   1. `matrix.entry.spec` -- its own parameter is named `matrix`, shadowing
    #      the module, so the generated body's `matrix.entry.pre ...` resolves to
    #      a field projection on the slice:
    #        Invalid field `entry`: ... does not contain `Subtype.entry`
    #   2. `matrix.compute_vector_u.spec` -- the `.post` is applied WITH the
    #      `Hasher` instance but the function itself is called WITHOUT it:
    #        Application type mismatch ... Specs.lean:585:55
    #   3. `matrix.sample_matrix_{entry,A}.spec` -- these are OPAQUE (signature
    #      only), so their generated specs reference bodies that were never
    #      extracted: Unknown identifier `matrix.sample_matrix_A`.
    # All three are aeneas-side spec-generation bugs, independent of this project.
    # As of hax v0.4.0-rc.2 the glob WORKS with two driver fix-ups (below):
    # bug 1 (parameter shadowing the module) is FIXED upstream -- charon now
    # renames the parameter to `matrix1`. Bug 2 changed shape but persists:
    # the extracted `compute_vector_u` DOES take `hash_functionsHashInst`, but
    # the generated `.spec` calls it WITHOUT (fixed textually below, like the
    # Funs.lean pass further down). Bug 3 persists: opaque
    # `sample_matrix_{entry,A}` still get generated specs that do not compile
    # (partially-applied `pre` projected with `.holds`, references to the
    # never-extracted body) -- those blocks are DELETED below.
    "crate::matrix::*",
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

# The `&mut`-pair CODEGEN BUG this used to patch (rej_sample's `post`
# destructuring `(future out, result)` while the function returns
# `(result, future out)`) is FIXED as of hax v0.4.0-rc.2: `post` now takes
# `(Usize x Slice I16)` in the function's own order and `spec` applies it to
# `res` directly. Swapping now is itself the type error. Tripwire only:
_specs = Path("proofs/lean/LibcruxIotMlKem/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()
    for _fn in ("vector.portable.sampling.rej_sample",
                "vector.portable.OperationsPortableVector.rej_sample"):
        if f"{_fn}.post a out (res.2, res.1))" in _s:
            print(f"error: `{_fn}.post` is applied to a swapped pair again in "
                  f"Specs.lean -- the `&mut` pairing bug is back; restore the "
                  f"swap pass this comment replaced.", file=sys.stderr)
            sys.exit(1)

# The lean backend emits per-function Specs.lean + ProofObligations.lean from the
# `#[hax_lib::requires]` / `#[ensures]` annotations.
#
# Specs.lean is KEPT: it is pure statements (`<fn>.pre` as a `RustM Bool`, and
# `<fn>.spec` as `pre.holds -> triple`), and the top-level ones are discharged in
# Verification/ProofObligations.lean from the hand-written correctness theorems.
#
# ProofObligations.lean is DROPPED: its generated bodies are `sorry`, and every
# one is `@[spec]`-tagged, so keeping it would both put sorries in the build and
# feed unproved specs to `hax_mvcgen`.
_p = Path("proofs/lean/LibcruxIotMlKem/Extraction/ProofObligations.lean")
if _p.exists():
    _p.unlink()

# The 0.4 extraction also generates an `Extraction.lean` aggregator that imports
# the two modules deleted just above, so strip those imports or the package has a
# bad import. The lakefile globs every module under the package, so the deleted
# files must not be referenced anywhere.
_agg = Path("proofs/lean/LibcruxIotMlKem/Extraction.lean")
if _agg.exists():
    _agg.write_text("".join(
        l for l in _agg.read_text().splitlines(keepends=True)
        if "Extraction.ProofObligations" not in l
    ))


# ---- GLOB FIX-UPS (rc.2): crate::matrix::* spec generation ------------------
# 1. DELETE the generated spec blocks for the OPAQUE sampling items: their
#    functions are extracted signature-only (axioms), and the generated
#    `pre`/`spec` for them do not compile (aeneas-side bug; see the note at the
#    START_FROM glob). Each block runs from its `::pre]:` docstring to the next
#    top-level docstring.
# 2. INSERT `hash_functionsHashInst` into `compute_vector_u`'s spec-side CALL:
#    the extracted function takes the Hasher instance, the generated `.spec`
#    call omits it (same class as the Funs.lean pass above).
_specs = Path("proofs/lean/LibcruxIotMlKem/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()

    for _fn in ("sample_matrix_entry", "sample_matrix_A"):
        _start_marker = f"/-- [libcrux_iot_ml_kem::matrix::{_fn}::pre]:"
        if _start_marker not in _s:
            continue
        _start = _s.index(_start_marker)
        # end of the block: the next docstring after the block's `.spec` def
        _spec_pos = _s.index(f"matrix.{_fn}.spec", _start)
        _end = _s.find("/-- [", _spec_pos)
        if _end == -1:
            _end = _s.index("end libcrux_iot_ml_kem", _spec_pos)
        _s = _s[:_start] + _s[_end:]

    _old = "matrix.compute_vector_u K vectortraitsOperationsInst matrix_entry seed"
    _new = ("matrix.compute_vector_u K vectortraitsOperationsInst "
            "hash_functionsHashInst matrix_entry seed")
    if _s.count(_old) != 1:
        print(f"error: expected exactly one Hasher-less `compute_vector_u` call in "
              f"Specs.lean, found {_s.count(_old)}. If aeneas now passes the "
              f"instance itself, delete this pass.", file=sys.stderr)
        sys.exit(1)
    _s = _s.replace(_old, _new)

    _specs.write_text(_s)
    print("Patched Specs.lean (matrix glob fix-ups)")
