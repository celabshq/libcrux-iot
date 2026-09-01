#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "4c9e2b7c75ab1e2b645a4a8361ae86c4504f9800"
AENEAS_VERSION = "f8a0eb8"


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

# The `aeneas-lean` backend was renamed to `lean` in mainline hax, and
# `-core-models-lib` is now the default for it, so neither needs to be passed
# explicitly anymore.
result = subprocess.run(
    ["cargo", "hax", "into", "lean"],
    env={**os.environ, "RUSTFLAGS": "--cfg hax_backend_lean"},
)

# Aeneas reports a non-zero exit when it can't generate a definition for an
# extracted external item (here: the `Debug` derive on `Algorithm`). The
# generated Funs.lean still has the axiom inline, so we tolerate this
# specific failure and continue with the post-processing below.
if result.returncode != 0:
    print(f"warning: aeneas exited with code {result.returncode}; "
          f"continuing with post-processing (axiom remains inline).",
          file=sys.stderr)

funs_lean = Path("proofs/lean/LibcruxIotSha3/Extraction/Funs.lean")
content = funs_lean.read_text()

# The `lean` backend already imports `FunsExternal`/`Types` from the generated
# Funs.lean, so (unlike the old `aeneas-lean` backend) there is no `import
# Missing` line to inject here anymore.

# Wrong signature of `core_models.fmt.rt.Argument.new_display`
panic_block = (
    "    let a ←\n"
    "      core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay i\n"
    "    let a1 ←\n"
    "      core.fmt.rt.Argument.new_display core.Usize.Insts.CoreFmtDisplay RATE\n"
    "    let _ ←\n"
    "      core.fmt.Arguments.new\n"
    "        (Array.make 7#usize [\n"
    "          192#u8, 3#u8, 32#u8, 62#u8, 32#u8, 192#u8, 0#u8\n"
    "          ]) (Array.make 2#usize [ a, a1 ])\n"
    "    fail panic"
)
content = content.replace(panic_block, "/-\n" + panic_block + "\n-/\n    fail panic", 1)

# `state::load_block_2u32` binds a local named `lane` (state.rs: `let lane =
# Lane2U32::from(...).interleave()`), which shadows the `lane` sub-namespace, so
# every later `lane.Lane2U32.…` is parsed as a field projection on that local
# ("Invalid field `Lane2U32`: … does not contain `Subtype.Lane2U32`"). Force
# top-level resolution, as the specs/ml-kem driver does for `matrix`.
content = content.replace(
    "lane.Lane2U32.", "_root_.libcrux_iot_sha3.lane.Lane2U32."
)


# aeneas omits fields that `CoreModels`'s `cmp` traits declare without defaults:
# `PartialEq.ne` and `PartialOrd.{lt,le,gt,ge}`. The generated record literals are
# then rejected ("Fields missing: `ne`" / "`lt`, `le`, `gt`, `ge`"). Fill them from
# the CoreModels defaults, self-referentially, the way CoreModels does for its own
# instances; the self-reference needs `impl_def`, which aeneas only emits when it
# fills the fields itself, so promote the declaration.
_CMP_FIELDS = {"core.cmp.PartialEq": ("ne",), "core.cmp.PartialOrd": ("lt", "le", "gt", "ge")}


def _complete_cmp_records(text: str) -> str:
    lines = text.split("\n")
    DECL = re.compile(r"^(impl_def|def) (\S+)")
    for k in range(len(lines) - 1, -1, -1):   # back-to-front: edits never shift pending sites
        if not lines[k].rstrip().endswith(":= {"):
            continue
        # walk back over the (possibly wrapped) signature to its declaration line
        d = k
        while d >= 0 and not DECL.match(lines[d]):
            d -= 1
        if d < 0 or k - d > 4:
            continue
        header = " ".join(lines[d:k + 1])
        trait = next((t for t in _CMP_FIELDS if t + " " in header), None)
        if trait is None:
            continue
        fields = _CMP_FIELDS[trait]
        name = DECL.match(lines[d]).group(2)
        close = next((j for j in range(k + 1, min(k + 40, len(lines))) if lines[j] == "}"), None)
        if close is None or any(l.startswith(f"  {fields[0]} :=") for l in lines[k + 1:close]):
            continue
        add = []
        for f in fields:
            add += [f"  {f} := {trait}.{f}.default", f"    {name}"]
        lines[close:close] = add
        lines[d] = re.sub(r"^def ", "impl_def ", lines[d])
    return "\n".join(lines)


content = _complete_cmp_records(content)


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

# CODEGEN BUG (hax 4c9e2b7c): for a method taking `&mut self` and returning a
# value, the extracted function returns `(return value, future self)` -- e.g.
# `absorb_full(&mut self, inputs) -> usize` becomes
# `RustM (Usize x KeccakXofState RATE)` -- but the `post` generated from its
# `#[ensures]` destructures the pair the OTHER way round
# (`let (self__future, remainder) := p`, i.e. `(future self, return value)`).
# The `post`'s logical content is right; only the pairing convention disagrees,
# so `<fn>.spec` fails to typecheck with
#   "argument res has type Usize x KeccakXofState RATE
#    but is expected to have type KeccakXofState RATE x Usize".
#
# Fixed here by applying the generated `post` to the swapped pair, which leaves
# `post` itself exactly as hax emitted it (so it still reads against the Rust
# `ensures`). Keyed on the affected names and asserted, so that when hax fixes
# the ordering upstream this pass fails loudly instead of silently re-swapping a
# now-correct application.
_specs = Path("proofs/lean/LibcruxIotSha3/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()
    for _fn in ("keccak.KeccakXofState.absorb_full",
                "keccak.KeccakXofState.fill_buffer"):
        # ASCII-only anchor on purpose: the surrounding Lean brackets are
        # U+231C/U+231D/U+2984 and easy to get wrong in a source-level pass.
        _old = f"{_fn}.post self inputs res)"
        _new = f"{_fn}.post self inputs (res.2, res.1))"
        if _s.count(_old) != 1:
            print(f"error: expected exactly one un-swapped `{_fn}.post` application in "
                  f"Specs.lean, found {_s.count(_old)}. If hax now emits the pair in "
                  f"declaration order, delete this pass.", file=sys.stderr)
            sys.exit(1)
        _s = _s.replace(_old, _new)
    _specs.write_text(_s)

# The lean backend emits per-function Specs.lean + ProofObligations.lean from the
# `#[hax_lib::requires]` / `#[ensures]` annotations.
#
# Specs.lean is KEPT: it is pure statements (`<fn>.pre` as a `RustM Bool`, and
# `<fn>.spec` as `pre.holds -> triple`), and the top-level ones are discharged in
# Verification/GeneratedSpecs.lean from the hand-written correctness theorems.
#
# ProofObligations.lean is DROPPED: its generated bodies are `sorry`, and every
# one is `@[spec]`-tagged, so keeping it would both put sorries in the build and
# feed unproved specs to `hax_mvcgen`. Its import is stripped from the
# `Extraction.lean` aggregator too (the lakefile globs every module).
_p = Path("proofs/lean/LibcruxIotSha3/Extraction/ProofObligations.lean")
if _p.exists():
    _p.unlink()

_agg = Path("proofs/lean/LibcruxIotSha3/Extraction.lean")
if _agg.exists():
    _agg.write_text("".join(
        l for l in _agg.read_text().splitlines(keepends=True)
        if "Extraction.ProofObligations" not in l
    ))
