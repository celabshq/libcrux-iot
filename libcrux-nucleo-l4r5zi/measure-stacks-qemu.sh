#!/usr/bin/env bash

# QEMU counterpart of measure-stacks.sh: builds the stack measurement binaries
# in release mode under qemu-system-arm and writes results to
# stack-${REV}-qemu.dat.
#
# By default the most expensive variants (mldsa87, mlkem1024) are measured. To
# measure other variants, pass the cargo features for the variant(s) you want;
# they replace the defaults and are forwarded to argo. The
# variants are mutually exclusive within each family (mldsa*/mlkem*), so supply
# exactly one of each plus `stack`, e.g.:
#   ./measure-stacks-qemu.sh --features stack,mldsa44,mlkem512

set -euo pipefail

cd "$(dirname "$0")"

REV=$(git rev-parse HEAD)
FILE="stack-${REV}-qemu.dat"

echo "Repository at commit: $REV (qemu)" > "$FILE"

# Default to the most expensive variants; any args override them verbatim.
feature_args=(--features stack,mldsa87,mlkem1024)
if [ "$#" -gt 0 ]; then
    feature_args=("$@")
fi

echo "Starting QEMU measurements (mps2-an386)"
for bin in mlkem_stack_keygen mlkem_stack_encaps mlkem_stack_decaps \
           mldsa_stack_keygen mldsa_stack_sign mldsa_stack_verify; do
    echo "[$bin]"
    ./run-qemu.sh --release --quiet --bin "$bin" "${feature_args[@]}" >> "$FILE"
done
echo "wrote $FILE"
