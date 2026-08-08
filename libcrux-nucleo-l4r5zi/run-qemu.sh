#!/usr/bin/env bash
# Build a libcrux-nucleo-l4r5zi binary and run it under qemu-system-arm.
#
# Usage:
#   ./run-qemu.sh --bin mldsa_stack_keygen --features stack,mldsa87,mlkem512
#   ./run-qemu.sh --release --bin mlkem_stack_keygen --features stack,mlkem512,mldsa44
#
# You must select the variant via its cargo feature (one of mldsa44/mldsa65/
# mldsa87 and mlkem512/mlkem768/mlkem1024, they are mutually exclusive
# within each family). All arguments are forwarded verbatim to `cargo run`.
# The `qemu` feature is added automatically and the `board` default-feature
# is disabled.

set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"

for tool in "${QEMU:-qemu-system-arm}" defmt-print; do
    if ! command -v "$tool" >/dev/null 2>&1; then
        echo "error: $tool not found in PATH (use the nix dev shell)" >&2
        exit 1
    fi
done

export CARGO_TARGET_THUMBV7EM_NONE_EABIHF_RUNNER="$here/qemu-runner.sh"

exec cargo run --no-default-features --features qemu "$@"
