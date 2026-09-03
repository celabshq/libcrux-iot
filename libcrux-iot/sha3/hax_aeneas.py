#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "cbce2c3bfcf50e853d3115c45cd592004d7d092f"
AENEAS_VERSION = "6852e64"


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

# Wrong signature of `core_models.fmt.rt.Argument.new_display` (formerly
# emitted around a panicking `unreachable!`-style branch). FIXED as of hax
# v0.4.0-rc.2: that branch now extracts directly as `fail panic`, with no
# malformed formatting call to comment out. This `.replace()` is a no-op
# against current output (kept, harmless, as a tripwire against older hax).
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

# `state::load_block_2u32` used to bind a local named `lane` (state.rs: `let
# lane = Lane2U32::from(...).interleave()`), shadowing the `lane` sub-namespace
# so that every later `lane.Lane2U32.…` parsed as a field projection on that
# local. FIXED as of hax v0.4.0-rc.2: charon now renames the shadowing local to
# `lane1`, so the blanket `_root_.` rewrite this replaced is obsolete -- and
# actively harmful: it also rewrote the NEW (rc.2) `clone_from :=
# core.clone.Clone.clone_from.default <SELF>` self-reference inside the
# `Lane2U32` `impl_def`, whose forward-declaration only resolves the unprefixed
# name form, giving "Unknown constant
# `libcrux_iot_sha3.lane.Lane2U32.Insts.CoreCloneClone`". Tripwire only:
if "\n  let lane ←" in content or "\n  let lane =" in content:
    print("error: Funs.lean binds a local named `lane` again -- the charon "
          "namespace-shadowing rename is gone; restore the `_root_.` rewrite "
          "this comment replaced.", file=sys.stderr)
    sys.exit(1)


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

# Both aeneas bugs formerly patched here are FIXED as of hax v0.4.0-rc.2
# (aeneas nightly-2026.09.03-6852e64). Kept as history, and as a tripwire if a
# future bump regresses either:
#
# 1. `&mut self` pairing (absorb_full/fill_buffer): aeneas used to destructure
#    `post`'s pair as `(future self, return value)` while the function itself
#    returns `(return value, future self)`, so `<fn>.spec` had to apply `post`
#    to a swapped `(res.2, res.1)`. As of rc.2, `post` destructures the pair in
#    the SAME order the function returns it (`let (remainder, self__future) :=
#    p` for a `RustM (Usize x KeccakXofState RATE)`), and `<fn>.spec` applies
#    `post` to `res` directly -- swapping now is not just unneeded but a type
#    error (`res.2, res.1` has type `KeccakXofState x Usize`, the post's
#    binder wants `Usize x KeccakXofState`).
#
# 2. Const-generic binder (shake128/shake256): aeneas used to bind `post`'s
#    `BYTES` implicitly while `<fn>.spec` applied it explicitly
#    (`shake128.post BYTES data res`). As of rc.2, `<fn>.spec` no longer
#    applies it explicitly (`shake128.post data res`), so the implicit binder
#    and the call site already agree; making the binder explicit now leaves
#    `spec`'s two-argument call short by one (BYTES) and misassigned in type.
_specs = Path("proofs/lean/LibcruxIotSha3/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()
    for _fn in ("keccak.KeccakXofState.absorb_full",
                "keccak.KeccakXofState.fill_buffer"):
        _bug = f"{_fn}.post self inputs (res.2, res.1))"
        if _bug in _s:
            print(f"error: `{_fn}.post` is applied to a swapped pair again in "
                  f"Specs.lean -- the aeneas `&mut self` pairing bug is back; "
                  f"restore the swap pass this comment replaced.", file=sys.stderr)
            sys.exit(1)
    for _fn in ("shake128", "shake256"):
        if f"{_fn}.post BYTES data res" in _s:
            print(f"error: `{_fn}.spec` applies `post` with an explicit `BYTES` "
                  f"again -- the aeneas const-generic binder bug is back; restore "
                  f"the explicit-binder pass this comment replaced.", file=sys.stderr)
            sys.exit(1)

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
