#!/usr/bin/env bash
# Compatibility shim for comparator + an older `landrun` release (e.g. the 0.1.x in
# nixpkgs). comparator invokes landrun with `-ldd` (auto-detect shared-library
# dependencies of the command), which those releases treat as fatal when the command
# is a script or a static binary -- and both the elan proxies and the toolchain's
# `lake` are exactly that -- and it grants exec permission only to the Lean prefix, so
# the dynamic loader itself (under /nix/store on NixOS, /lib64 elsewhere) cannot run.
# This shim drops `-ldd` and grants read+exec on the system directories, then defers
# to the real landrun; the Landlock sandbox is otherwise unchanged. Use it as
#
#     COMPARATOR_LANDRUN=./comparator-landrun-compat.sh ./comparator.sh
#
# Not needed with landrun built from its main branch, which comparator documents as
# its requirement.
set -euo pipefail
args=()
for a in "$@"; do [ "$a" = "-ldd" ] || args+=("$a"); done
exec landrun --rox /nix --rox /usr --rox /lib --rox /lib64 --rox /bin \
  --rox "$HOME/.elan" --rox "${ELAN_HOME:-$HOME/.elan}" "${args[@]}"
