#!/usr/bin/env bash
# Check the sha3 Lean proofs against hax's generated proof obligations with
# leanprover/comparator (see LibcruxIotSha3/Verification/Solution.lean).
#
#   ./comparator.sh            # from libcrux-iot/sha3/proofs/lean, inside `nix develop .#lean`
#
# Needs on PATH (or via the COMPARATOR_* variables comparator reads):
#   comparator   -- https://github.com/leanprover/comparator, `lake build comparator`
#                   (builds fine with this project's Lean toolchain)
#   lean4export  -- https://github.com/leanprover/lean4export at the tag matching
#                   `lean-toolchain` (v4.31.0), `lake build`
#   landrun      -- the Landlock sandbox comparator runs lean/lake in. comparator wants
#                   landrun built from its main branch; with an older release (such as
#                   the one the `lean` devShell provides from nixpkgs) its `-ldd`
#                   detection aborts on the elan/lake wrapper scripts -- use
#                   `COMPARATOR_LANDRUN=./comparator-landrun-compat.sh ./comparator.sh`.
# The challenge module (Extraction/ProofObligations.lean) is imported by nothing, so it
# is built here on demand; `lake build` must have succeeded first so the solution is
# up to date.
set -euo pipefail
cd "$(dirname "$0")"
: "${COMPARATOR_BIN:=comparator}"
command -v "${COMPARATOR_LANDRUN:-landrun}" >/dev/null || { echo "landrun not found (COMPARATOR_LANDRUN)"; exit 2; }
command -v "${COMPARATOR_LEAN4EXPORT:-lean4export}" >/dev/null || { echo "lean4export not found (COMPARATOR_LEAN4EXPORT)"; exit 2; }
command -v "$COMPARATOR_BIN" >/dev/null || { echo "comparator not found (COMPARATOR_BIN)"; exit 2; }
exec lake env "$COMPARATOR_BIN" comparator.json
