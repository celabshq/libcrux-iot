#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

REV=$(git rev-parse HEAD)
FILE_MLKEM="perf-${REV}-mlkem.dat"
FILE_MLDSA="perf-${REV}-mldsa.dat"
FILE_MLDSA_STACK="perf-${REV}-mldsa-stack.dat"

echo "Repository at commit: $REV" > "$FILE_MLKEM"

for mlkem in mlkem512 mlkem768 mlkem1024; do
    echo "[$mlkem]"
    DEFMT_LOG=info cargo measure-cycles mlkem --quiet --no-default-features --features mldsa44,"$mlkem",board >> "$FILE_MLKEM"
done

echo "wrote $FILE_MLKEM"

echo "Repository at commit: $REV" > "$FILE_MLDSA"

for mldsa in mldsa44 mldsa65 mldsa87; do
    echo "[$mldsa]"
    DEFMT_LOG=info cargo measure-cycles mldsa --quiet --no-default-features --features "$mldsa",mlkem512,board >> "$FILE_MLDSA"
done

echo "wrote $FILE_MLDSA"

echo "Repository at commit: $REV" > "$FILE_MLDSA_STACK"

for mldsa in mldsa44 mldsa65 mldsa87; do
    echo "[$mldsa - stack]"
    DEFMT_LOG=info cargo measure-cycles mldsa --quiet --no-default-features --features "$mldsa",mlkem512,stack,board >> "$FILE_MLDSA_STACK"
done

echo "wrote $FILE_MLDSA_STACK"
