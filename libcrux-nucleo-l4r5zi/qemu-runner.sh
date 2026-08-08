#!/usr/bin/env bash
# cargo runner for the `qemu` feature: boots an ELF under qemu-system-arm and
# decodes the defmt stream (emitted over ARM semihosting) with defmt-print.
#
# cargo invokes a runner as `<runner> <elf-path>`. We need the ELF both for
# qemu (`-kernel`) and for defmt-print (`-e`, for symbol resolution), so this
# wrapper exists rather than being expressible as a plain runner arg list.
#
# Not meant to be called directly, `run-qemu.sh` points
# CARGO_TARGET_THUMBV7EM_NONE_EABIHF_RUNNER at it. QEMU/QEMU_MACHINE/QEMU_CPU
# can be overridden via the environment.

set -euo pipefail

elf="$1"
exec "${QEMU:-qemu-system-arm}" -M "${QEMU_MACHINE:-mps2-an386}" -cpu "${QEMU_CPU:-cortex-m4}" \
    -nographic -semihosting-config enable=on,target=native -kernel "$elf" \
    | defmt-print -e "$elf"
