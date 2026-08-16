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

HAX_VERSION = "2fedcb2b196f5adea55975d0a023596ec6383ff2"
AENEAS_VERSION = "52fd438"

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
    "crate::ind_cpa::serialize_public_key_mut",
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
check_version(["aeneas", "-version"], "aeneas", AENEAS_VERSION)

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
    print(f"warning: hax/aeneas exited with code {result.returncode}; "
          f"continuing with post-processing.", file=sys.stderr)

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

funs_lean.write_text(content)

# The lean backend also emits per-function Specs.lean + ProofObligations.lean
# (proof-obligation scaffolding). They are not imported by the hand-written
# proofs and currently have codegen quirks (e.g. a swapped tuple order in
# `rej_sample.post`: `Usize × Slice I16` vs `Slice I16 × Usize`), so drop them.
for _f in ("Specs.lean", "ProofObligations.lean"):
    _p = Path("proofs/lean/LibcruxIotMlKem/Extraction") / _f
    if _p.exists():
        _p.unlink()
