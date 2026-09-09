#!/usr/bin/env python3
"""Extract `libcrux-iot-ml-kem` to Lean and apply the residual fix-ups.

    ./hax_mlkem.py              # `cargo hax extract libcrux-iot-ml-kem`, then patch
    ./hax_mlkem.py --no-extract # patch only (a FRESH, still unpatched extraction)

Lives next to the workspace `hax.toml` (which pins the tool versions); runs
from any directory, inside `nix develop .#lean` (from the repo root). The
scenario itself -- backend, output dir, the charon `--start-from`/`--opaque`
scope -- lives in `ml-kem/hax.toml`. The
scenario is named after the cargo package because hax derives the Lean package
name (`LibcruxIotMlKem`) from it.

Everything the old `hax_aeneas.py` driver did is now handled by hax v0.4.0 +
hax.toml + the source cfg-gates (`#[cfg(not(hax_backend_lean))]` on
`loop_invariant!`) + the glob-free lakefile + `Assumptions/HaxLibAlias.lean`
(the duplicate-crate `hax_lib_1.*` names) -- EXCEPT the fix-ups below, which
hax.toml cannot express and which still reproduce with hax v0.4.0 (charon
nightly-2026.09.02, aeneas nightly-2026.09.03-6852e64). A fresh extraction plus
one run of this script reproduces the committed `Extraction/` byte for byte;
the raw extraction differs from it ONLY in these places:

 Funs.lean -- 10 call sites drop the `hash_functionsHashInst` ARGUMENT while the
    callee's definition keeps the `(hash_functionsHashInst : hash_functions.Hash
    Hasher)` binder (always the binder right after `vectortraitsOperationsInst`):
    `sample_matrix_entry` (x3, the opaque axiom), `compute_vector_u_loop0[.body]`,
    `compute_vector_u_loop1_loop0[.body]`, `compute_vector_u_loop1[.body]`,
    `compute_vector_u`. Without the fix the next positional argument lands in
    the Hasher slot ("`start` is not a field of hash_functions.Hash" /
    "Application type mismatch"). Repaired systematically (pass 2): collect every
    def/axiom with that binder pair (18 functions), then at every call
    `<fn> [K] vectortraitsOperationsInst` not already followed by the instance,
    insert it (K-arity taken from the def; binder positions excluded).

 Specs.lean -- 5 spec-side calls drop trait-clause instance arguments (pass 1,
    one exact textual pattern each):
      `lift_t_as_ntt_from_public_key K public_key`  -> + `vectortraitsOperationsInst`
          (x2: `compute_u_and_v.post`, `compute_ring_element_v.post`)
      `lift_matrix_from_seed K seed`                -> + both instances
          (`compute_vector_u.post`)
      `compute_vector_u K vectortraitsOperationsInst matrix_entry seed`
                                                    -> + `hash_functionsHashInst`
          (`compute_vector_u.spec`)
      `compute_u_and_v K vectortraitsOperationsInst seed public_key`
                                                    -> + `hash_functionsHashInst`
          (`compute_u_and_v.spec`)

(The opaque `matrix::sample_matrix_{entry,A}` used to get generated `.pre`/`.post`/
`.spec` blocks from their `#[requires]`/`#[ensures]` too -- non-type-checking
partial applications of the axioms; those contracts are now
`#[cfg_attr(not(hax_backend_lean), ...)]`-gated in `matrix.rs`, so they only
reach the F* extraction and no Lean-side deletion is needed.)

The passes are guarded by exact-count tripwires and are NOT idempotent: run once
on a fresh extraction (which is what the default mode guarantees). Each pass
fails loudly, or reports zero work, once upstream fixes its bug -- delete it then.
"""
import re
import subprocess
import sys
from pathlib import Path

WORKSPACE = Path(__file__).resolve().parent          # libcrux-iot/, has hax.toml
CRATE = WORKSPACE / "ml-kem"
SCENARIO = "libcrux-iot-ml-kem"
LEAN = CRATE / "proofs"  / "libcrux-iot-ml-kem" / "lean" / "LibcruxIotMlKem"
SPECS = LEAN / "Extraction" / "Specs.lean"
FUNS = LEAN / "Extraction" / "Funs.lean"
FUNS_EXTERNAL = LEAN / "Assumptions" / "FunsExternal.lean"


def die(msg):
    print(f"error: {msg}", file=sys.stderr)
    sys.exit(1)


def extract():
    cmd = ["cargo", "hax", "extract", SCENARIO]
    print("+", " ".join(cmd), f"(in {CRATE})")
    if subprocess.run(cmd, cwd=CRATE).returncode != 0:
        die("`cargo hax extract` failed; nothing patched")


# ---- pass 1: re-insert dropped trait-clause instances at spec-side calls --------
SPEC_CALL_FIXES = [
    # (old, new, expected count)
    ("matrix.lift_t_as_ntt_from_public_key K public_key",
     "matrix.lift_t_as_ntt_from_public_key K vectortraitsOperationsInst public_key", 2),
    ("matrix.lift_matrix_from_seed K seed",
     "matrix.lift_matrix_from_seed K vectortraitsOperationsInst hash_functionsHashInst seed", 1),
    ("matrix.compute_vector_u K vectortraitsOperationsInst matrix_entry seed",
     "matrix.compute_vector_u K vectortraitsOperationsInst hash_functionsHashInst matrix_entry seed", 1),
    ("matrix.compute_u_and_v K vectortraitsOperationsInst seed public_key",
     "matrix.compute_u_and_v K vectortraitsOperationsInst hash_functionsHashInst seed public_key", 1),
]


def fix_spec_calls(s):
    n = 0
    for old, new, expected in SPEC_CALL_FIXES:
        c = s.count(old)
        if c != expected:
            die(f"expected {expected} instance-less call(s) `{old}` in Specs.lean, found {c}. "
                f"If the generator now passes the instance itself, delete this entry.")
        s = s.replace(old, new)
        n += c
    return s, n


# ---- pass 2: re-insert the dropped `hash_functionsHashInst` argument in Funs ----
def hasher_taking_names(*texts):
    """{name: k} for every def/axiom/opaque whose binders have
    `(hash_functionsHashInst :` right after `(vectortraitsOperationsInst :`;
    k = number of EXPLICIT binders before the Vector binder (e.g. `(K : Std.Usize)`),
    i.e. how many positional args a call passes before `vectortraitsOperationsInst`."""
    names = {}
    for t in texts:
        for m in re.finditer(r"^(?:def|axiom|opaque)\s+(\S+)(.*?)(?=:=|\n\n|\n/--)",
                             t, re.S | re.M):
            sig = m.group(2)
            vm = re.search(r"\(vectortraitsOperationsInst\s*:[^)]*\)\s*\(hash_functionsHashInst\s*:", sig)
            if vm:
                before = sig[:vm.start()]
                names[m.group(1)] = len(re.findall(r"\((?!vectortraitsOperationsInst)[A-Za-z_]\w*\s*:", before))
    return names


def reinsert_hasher(t, names):
    total = 0
    for n, k in sorted(names.items(), key=lambda kv: -len(kv[0])):
        mid = r"(?:\s+\S+){%d}" % k   # the k positional args (e.g. `K`) before the Vector instance
        pat = re.compile(r"(?<![\w.])" + re.escape(n) + mid +
                         r"\s+vectortraitsOperationsInst(?=\s)(?!\s*:)(?!\s+hash_functionsHashInst\b)")
        t, c = pat.subn(lambda m: m.group(0) + " hash_functionsHashInst", t)
        total += c
    return t, total


def patch():
    if not SPECS.exists() or not FUNS.exists():
        die(f"missing {SPECS} or {FUNS}; run the extraction first")

    s, n_spec = fix_spec_calls(SPECS.read_text())
    SPECS.write_text(s)
    print(f"Specs.lean: re-inserted instances at {n_spec} call site(s)")

    names = hasher_taking_names(FUNS.read_text(),
                                FUNS_EXTERNAL.read_text() if FUNS_EXTERNAL.exists() else "")
    t, n_funs = reinsert_hasher(FUNS.read_text(), names)
    FUNS.write_text(t)
    print(f"Funs.lean: re-inserted hash_functionsHashInst at {n_funs} call site(s) "
          f"({len(names)} Hasher-taking functions)")
    if n_funs == 0:
        print("note: zero Funs.lean insertions -- if this persists, aeneas fixed the drop; "
              "delete pass 2.", file=sys.stderr)


if __name__ == "__main__":
    args = sys.argv[1:]
    if args not in ([], ["--no-extract"]):
        die(f"usage: {sys.argv[0]} [--no-extract]")
    if not args:
        extract()
    patch()
