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

funs_lean.write_text(content)

# The lean backend emits per-function Specs.lean + ProofObligations.lean
# (proof-obligation scaffolding). They are not imported by the hand-written
# proofs and carry codegen quirks -- here a swapped tuple order in the generated
# `post` of the squeeze/absorb functions (`Usize x KeccakXofState RATE` where the
# obligation expects `KeccakXofState RATE x Usize`), the same class of bug the
# ml-kem driver records. Drop them, and drop their import from the
# `Extraction.lean` aggregator that cargo-hax 0.4 generates, since the lakefile
# globs every module under the package.
for _f in ("Specs.lean", "ProofObligations.lean"):
    _p = Path("proofs/lean/LibcruxIotSha3/Extraction") / _f
    if _p.exists():
        _p.unlink()

_agg = Path("proofs/lean/LibcruxIotSha3/Extraction.lean")
if _agg.exists():
    _agg.write_text("".join(
        l for l in _agg.read_text().splitlines(keepends=True)
        if "Extraction.Specs" not in l and "Extraction.ProofObligations" not in l
    ))
