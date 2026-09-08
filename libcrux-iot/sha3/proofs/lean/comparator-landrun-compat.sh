#!/usr/bin/env bash
# Fallback shim between comparator and landrun. comparator invokes landrun with `-ldd`
# (auto-detect the command's shared-library dependencies) and grants exec permission
# only to the Lean prefix. Two things can go wrong with that:
#   * landrun 0.1.x releases (e.g. nixpkgs') treat `-ldd` as fatal when the command is a
#     script or a static binary -- the elan proxies and the toolchain's `lake` wrapper
#     script are exactly that. landrun's main branch (what the `lean` devShell
#     provides) resolves dependencies in-process and skips non-ELF commands instead.
#   * the toolchain's `lake` is a shell script, so its interpreter (bash, `/usr/bin/env`,
#     the dynamic loader) must be executable inside the sandbox; comparator's flags
#     grant read-only access to `/`, not exec.
# This shim drops `-ldd` and grants read+exec on the system directories, then defers
# to the real landrun; the Landlock sandbox is otherwise unchanged. Use it as
#
#     COMPARATOR_LANDRUN=./comparator-landrun-compat.sh ./comparator.sh
#
# only if the plain `./comparator.sh` fails for one of those reasons.
set -euo pipefail
args=()
for a in "$@"; do [ "$a" = "-ldd" ] || args+=("$a"); done
exec landrun --rox /nix --rox /usr --rox /lib --rox /lib64 --rox /bin \
  --rox "$HOME/.elan" --rox "${ELAN_HOME:-$HOME/.elan}" "${args[@]}"
