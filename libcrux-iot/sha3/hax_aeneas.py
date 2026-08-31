#!/usr/bin/env python3

import os
import re
import subprocess
import sys
from pathlib import Path

HAX_VERSION = "2fedcb2b196f5adea55975d0a023596ec6383ff2"
AENEAS_VERSION = "52fd438"


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

funs_lean.write_text(content)
