#!/usr/bin/env python3
"""Extraction driver for libcrux-iot ML-DSA NTT → Lean.

Mirrors `libcrux-iot/ml-kem/hax_aeneas.py`. Three responsibilities:

1. Pin/check the hax + aeneas toolchain versions.
2. Run `cargo hax into lean` with a Charon `--start-from` list chosen
   to bound the extraction to the NTT / arithmetic / matrix core.
3. Patch the generated `proofs/lean/LibcruxIotMlDsa/Extraction/Funs.lean`.

TOOLCHAIN NOTE: migrated to mainline hax `2fedcb2b` (= cargo-hax-v0.3.7-288) +
hax-lean v0.2.0 / CoreModels, aeneas `nightly-2026.07.21` (`52fd438`). Run inside
`nix develop .#lean` from the repo root (provides the version-wrapped `cargo hax`
+ aeneas). The `lean` backend writes to `proofs/lean/` and uses the CoreModels
library by default (the old `--aeneas-args=-core-models-lib` is implicit now).

The ML-DSA impl carries one `#[hax_lib::loop_invariant!]` (gated `#[cfg(hax)]`
so the dummy-mode lean compile skips it; F* still sees it) and uses const generics
(`outer_3_plus<OFFSET, STEP_BY, ZETA>`, `shift_left_then_reduce<SHIFT_BY>`).
Extraction does not *require* annotations, but confirm aeneas monomorphizes the
const-generic layer steps into usable `Funs.lean` defs (ML-KEM's parametric
`ntt_at_layer_4_plus` is the precedent that this works).
"""

import os
import re
import shlex
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800"
AENEAS_VERSION = "f8a0eb8"

# Charon translation roots. Anything not reachable from these is dropped from
# `Funs.lean`. The NTT/arithmetic core lives in the portable SIMD module; the
# matrix pipelines drive iNTT.
START_FROM = [
    "crate::ntt::*",
    "crate::polynomial::*",
    "crate::arithmetic::*",
    "crate::simd::portable::ntt::*",
    "crate::simd::portable::invntt::*",
    "crate::simd::portable::arithmetic::*",
    "crate::simd::portable::vector_type::*",
    # The concrete `Operations for Coefficients` trait instance. ML-DSA's only
    # monomorphic users of it (matrix / ml_dsa_generic) are kept opaque, so
    # without naming the impl here Charon finds no use of the instance and
    # prunes it — which drops `portable_ops_inst` (and the whole polynomial
    # layer) from the extraction. Starting from the impl block retains the
    # instance and all its methods. (Mirrors ML-KEM, where non-opaque
    # `matrix::compute_*` keep the analogous instance alive for free.)
    # `--start-from` requires an impl pattern to be the first path element (no
    # module prefix), so the instance is named by its trait + concrete type.
    "{impl crate::simd::traits::Operations for crate::simd::portable::vector_type::Coefficients}",
    # The poly-layer `PolynomialRingElement::{add,subtract}` have no non-opaque
    # caller (only matrix / ml_dsa_generic use them, and those are opaque), so
    # without naming them they would be pruned; the impl's other methods are
    # reached via the NTT free functions. (`--start-from` rejects inherent-impl
    # patterns, so the methods are named directly.)
    "crate::polynomial::PolynomialRingElement::add",
    "crate::polynomial::PolynomialRingElement::subtract",
    "crate::simd::traits::*",
    "crate::matrix::compute_as1_plus_s2",
    "crate::matrix::compute_matrix_x_mask",
]

# Items to keep opaque (extract signature only). The hash/sampling/encoding
# glue is out of scope for the NTT campaign; SHA-3 is verified in
# libcrux-iot/sha3.
OPAQUE = [
    "crate::hash_functions::*",
    "crate::sample::*",
    "crate::samplex4::*",
    "crate::encoding::*",
    "crate::ml_dsa_generic::*",
    "crate::pre_hash::*",
    # The impl's serialize/sample methods forward to these nested portable
    # modules, whose bodies use unmodeled chunks_exact/as_u8. They are out of
    # the NTT/arithmetic scope, so keep them opaque (signature only); the
    # Operations instance's serialize/sample fields then forward to opaque
    # leaves, while the NTT/arith fields forward to the verified concrete fns.
    "crate::simd::portable::encoding::*",
    "crate::simd::portable::sample::*",
    # Phase-7 vector drivers that iterate a `&mut [PolynomialRingElement]` with a
    # nested slice iterator (hax issue #720). The installed aeneas cannot
    # translate that region pattern and emits a `sorry` body; keep them opaque
    # (signature only) so the extraction stays axiom-/sorry-free. The NTT core
    # (Phases 2–6) does not use them; the per-element `power2round_element` /
    # `decompose_element` (the actual Phase-7 FC targets) extract fine.
    "crate::arithmetic::power2round_vector",
    "crate::arithmetic::decompose_vector",
    # Phase-8 (matrix-level) drivers: the pinned aeneas renders their nested
    # loops with a malformed `matrix.compute_*_loop0` field-projection on the
    # bounded-`Vec` subtype (`{ l // l.length ≤ Usize.max }`). Phase 8 is the
    # last/optional phase (and may instead compose from `Spec/Pure` per
    # `Plan.lean`), so keep them opaque to get a clean NTT-core (Phases 2–7)
    # build; revisit the matrix extraction when Phase 8 starts.
    "crate::matrix::compute_as1_plus_s2",
    "crate::matrix::compute_matrix_x_mask",
]


def check_version(cmd: list[str], expected: str) -> None:
    result = subprocess.run(cmd, capture_output=True, text=True)
    output = result.stdout + result.stderr
    if expected not in output:
        if os.environ.get("SKIP_VERSION_CHECK") == "1":
            print(f"warning: version mismatch for {cmd[0]} (expected {expected!r}); "
                  f"continuing because SKIP_VERSION_CHECK=1", file=sys.stderr)
            return
        print(f"Version mismatch for {cmd[0]}: expected {expected!r} in output:\n{output}",
              file=sys.stderr)
        sys.exit(1)


check_version(["cargo", "hax", "--version"], HAX_VERSION)
# As of cargo-hax 0.4, aeneas and charon are downloaded and checksum-verified
# by cargo-hax itself into a machine-wide cache and are not put on PATH, so
# ask cargo-hax which version the project resolves to instead of running the
# binary. `cargo hax tools install` fetches them if they are missing.
check_version(["cargo", "hax", "tools", "show"], AENEAS_VERSION)

# `--charon-args` is shell-word split by hax, so each pattern is `shlex.quote`d:
# name-matcher patterns like `{impl Trait for _}` contain spaces and must arrive
# as a single token.
charon_args = " ".join(
    [f"--start-from {shlex.quote(root)}" for root in START_FROM] +
    [f"--opaque {shlex.quote(item)}" for item in OPAQUE]
)

result = subprocess.run(
    ["cargo", "hax", "into", "lean",
     f"--charon-args={charon_args}"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
)
if result.returncode != 0:
    sys.exit(result.returncode)

# The `lean` backend writes to `proofs/lean/` and emits the `Types` / `FunsExternal`
# imports itself (no manual `import Missing` patch needed — FunsExternal supersedes it).
funs_lean = Path("proofs/lean/LibcruxIotMlDsa/Extraction/Funs.lean")
content = funs_lean.read_text()

# Convert `axiom` declarations emitted for `--opaque` items to `opaque`
# (`axiom` shows up in `#print axioms`; `opaque` does not).
content = re.sub(r"^axiom ", "opaque ", content, flags=re.MULTILINE)

# TODO(Phase 0): add ML-DSA-specific call-site patches here if aeneas drops
# trait-instance arguments (the ml-kem driver patches `vectortraitsOperationsInst`
# / `hash_functionsHashInst` insertions). Re-derive empirically from the first
# extraction's build errors — do NOT copy the ml-kem patch list blind.


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
print("Patched", funs_lean)

# The lean backend also emits per-function Specs.lean + ProofObligations.lean
# (proof-obligation scaffolding). They are not imported by the hand-written
# proofs and carry codegen quirks, so drop them (mirrors the ml-kem driver).
for _f in ("Specs.lean", "ProofObligations.lean"):
    _p = Path("proofs/lean/LibcruxIotMlDsa/Extraction") / _f
    if _p.exists():
        _p.unlink()
