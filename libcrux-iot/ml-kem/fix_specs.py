#!/usr/bin/env python3
"""Residual post-processing for the ml-kem Lean extraction.

Run ONCE, right after `cargo hax extract` (see hax.toml), on a FRESH extraction:
the passes below are guarded by exact-count tripwires and are NOT idempotent (a
second run on an already-patched tree exits 1 at the first tripwire).

Everything the old `hax_aeneas.py` driver did is now handled by hax v0.4.0 +
hax.toml (extraction scope) + the source cfg-gates (`#[cfg(not(hax_backend_lean))]`
on `loop_invariant!`) + the glob-free lakefile + `Assumptions/HaxLibAlias.lean`
(the duplicate-crate `hax_lib_1.*` names) -- EXCEPT three aeneas-side bugs that
hax.toml cannot express and that still reproduce with hax v0.4.0 / aeneas
nightly-2026.09.03-6852e64:

 1. Specs.lean: opaque `matrix::sample_matrix_{entry,A}` still get generated
    `.pre`/`.spec` blocks referencing their never-extracted bodies: DELETED.
 2. Specs.lean: four generated spec-side CALLS drop trait-clause instance arguments
    (`vectortraitsOperationsInst` / `hash_functionsHashInst`) the extracted
    functions take: re-inserted textually (exact patterns, one each).
 3. Funs.lean: aeneas drops the `hash_functionsHashInst` ARGUMENT at generated call
    sites of Hasher-taking functions (the `compute_vector_u` loop chain and the
    opaque `sample_matrix_entry`) while the DEFS keep the binder. Repaired
    systematically: collect every def/axiom whose binders have
    `(hash_functionsHashInst :` right after `(vectortraitsOperationsInst :`, then at
    every call `<fn> [K] vectortraitsOperationsInst` not already followed by the
    instance, insert it (K-arity taken from the def; binder positions excluded).

Each pass fails loudly ("delete this pass") once upstream fixes its bug.
"""
import sys
from pathlib import Path

_specs = Path("proofs/lean/LibcruxIotMlKem/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()
    for _fn in ("vector.portable.sampling.rej_sample",
                "vector.portable.OperationsPortableVector.rej_sample"):
        if f"{_fn}.post a out (res.2, res.1))" in _s:
            print(f"error: `{_fn}.post` is applied to a swapped pair again in "
                  f"Specs.lean -- the `&mut` pairing bug is back; restore the "
                  f"swap pass this comment replaced.", file=sys.stderr)
            sys.exit(1)



# ---- GLOB FIX-UPS (rc.2): crate::matrix::* spec generation ------------------
# 1. DELETE the generated spec blocks for the OPAQUE sampling items: their
#    functions are extracted signature-only (axioms), and the generated
#    `pre`/`spec` for them do not compile (aeneas-side bug; see the note at the
#    START_FROM glob). Each block runs from its `::pre]:` docstring to the next
#    top-level docstring.
# 2. INSERT `hash_functionsHashInst` into `compute_vector_u`'s spec-side CALL:
#    the extracted function takes the Hasher instance, the generated `.spec`
#    call omits it (same class as the Funs.lean pass above).
_specs = Path("proofs/lean/LibcruxIotMlKem/Extraction/Specs.lean")
if _specs.exists():
    _s = _specs.read_text()

    for _fn in ("sample_matrix_entry", "sample_matrix_A"):
        _start_marker = f"/-- [libcrux_iot_ml_kem::matrix::{_fn}::pre]:"
        if _start_marker not in _s:
            continue
        _start = _s.index(_start_marker)
        # end of the block: the next docstring after the block's `.spec` def
        _spec_pos = _s.index(f"matrix.{_fn}.spec", _start)
        _end = _s.find("/-- [", _spec_pos)
        if _end == -1:
            _end = _s.index("end libcrux_iot_ml_kem", _spec_pos)
        _s = _s[:_start] + _s[_end:]

    _old = "matrix.compute_vector_u K vectortraitsOperationsInst matrix_entry seed"
    _new = ("matrix.compute_vector_u K vectortraitsOperationsInst "
            "hash_functionsHashInst matrix_entry seed")
    if _s.count(_old) != 1:
        print(f"error: expected exactly one Hasher-less `compute_vector_u` call in "
              f"Specs.lean, found {_s.count(_old)}. If aeneas now passes the "
              f"instance itself, delete this pass.", file=sys.stderr)
        sys.exit(1)
    _s = _s.replace(_old, _new)

    # Same aeneas trait-clause drop hits the `lift_matrix_from_seed` call in
    # `compute_vector_u.post` (both the Vector AND Hasher instances are dropped).
    _oldm = "matrix.lift_matrix_from_seed K seed"
    _newm = "matrix.lift_matrix_from_seed K vectortraitsOperationsInst hash_functionsHashInst seed"
    if _s.count(_oldm) != 1:
        print(f"error: expected exactly one instance-less `lift_matrix_from_seed` call in "
              f"Specs.lean, found {_s.count(_oldm)}. If aeneas now passes the "
              f"instances itself, delete this pass.", file=sys.stderr)
        sys.exit(1)
    _s = _s.replace(_oldm, _newm)

    # Same aeneas trait-clause drop hits the `lift_t_as_ntt_from_public_key` call
    # in `compute_u_and_v.post` (the Vector instance is dropped).
    _oldt = "matrix.lift_t_as_ntt_from_public_key K public_key"
    _newt = "matrix.lift_t_as_ntt_from_public_key K vectortraitsOperationsInst public_key"
    if _s.count(_oldt) < 1:
        print(f"error: expected the instance-less `lift_t_as_ntt_from_public_key` call in "
              f"Specs.lean, found none. If aeneas now passes the instance itself, delete "
              f"this pass.", file=sys.stderr)
        sys.exit(1)
    _s = _s.replace(_oldt, _newt)  # both the compute_u_and_v and compute_ring_element_v posts

    # And the Hasher instance is dropped from the `compute_u_and_v` CALL inside its
    # own `.spec` (the wrapper takes both instances; same class as compute_vector_u).
    _olduv = "matrix.compute_u_and_v K vectortraitsOperationsInst seed public_key"
    _newuv = ("matrix.compute_u_and_v K vectortraitsOperationsInst "
              "hash_functionsHashInst seed public_key")
    if _s.count(_olduv) != 1:
        print(f"error: expected exactly one Hasher-less `compute_u_and_v` call in "
              f"Specs.lean, found {_s.count(_olduv)}. If aeneas now passes the "
              f"instance itself, delete this pass.", file=sys.stderr)
        sys.exit(1)
    _s = _s.replace(_olduv, _newuv)

    _specs.write_text(_s)
    print("Patched Specs.lean (matrix glob fix-ups)")

# ---------------------------------------------------------------------------
# Funs.lean / Specs.lean: aeneas (hax v0.4.0) drops the `hash_functionsHashInst`
# trait-clause ARGUMENT from many generated CALLS while the callee DEFS still take
# it (the axiom `sample_matrix_entry` in Assumptions/FunsExternal too). In every
# affected def the Hasher binder immediately follows the Vector binder, so the
# systematic repair is: for each Hasher-taking function, at every call where
# `vectortraitsOperationsInst` is NOT followed by `hash_functionsHashInst`, insert
# it. Binder positions (`(vectortraitsOperationsInst :`) are excluded. Reports the
# insertion count; zero insertions means aeneas fixed it -- delete this pass then.
import re as _re

def _hasher_taking_names(*texts):
    """{name: n} where n = number of EXPLICIT binders before the Vector binder
    (e.g. the const-generic `(K : Std.Usize)`), i.e. how many positional args a
    call passes between the function name and `vectortraitsOperationsInst`."""
    names = {}
    for t in texts:
        for m in _re.finditer(r"^(?:def|axiom|opaque)\s+(\S+)(.*?)(?=:=|\n\n|\n/--)", t, _re.S | _re.M):
            sig = m.group(2)
            vm = _re.search(r"\(vectortraitsOperationsInst\s*:[^)]*\)\s*\(hash_functionsHashInst\s*:", sig)
            if vm:
                before = sig[:vm.start()]
                names[m.group(1)] = len(_re.findall(r"\((?!vectortraitsOperationsInst)[A-Za-z_]\w*\s*:", before))
    return names

def _reinsert_hasher(path, names):
    t = path.read_text(); total = 0
    for n, k in sorted(names.items(), key=lambda kv: -len(kv[0])):
        mid = r"(?:\s+\S+){%d}" % k          # the k positional args (e.g. `K`) before the Vector instance
        pat = _re.compile(r"(?<![\w.])" + _re.escape(n) + mid +
                          r"\s+vectortraitsOperationsInst(?=\s)(?!\s*:)(?!\s+hash_functionsHashInst\b)")
        t, c = pat.subn(lambda m: m.group(0) + " hash_functionsHashInst", t); total += c
    path.write_text(t); return total

_funs = Path("proofs/lean/LibcruxIotMlKem/Extraction/Funs.lean")
_ext  = Path("proofs/lean/LibcruxIotMlKem/Assumptions/FunsExternal.lean")
if _funs.exists():
    _names = _hasher_taking_names(_funs.read_text(), _ext.read_text() if _ext.exists() else "")
    _k = _reinsert_hasher(_funs, _names)
    print(f"Patched Funs.lean: re-inserted hash_functionsHashInst at {_k} call site(s) "
          f"({len(_names)} Hasher-taking functions)")
    if _k == 0:
        print("note: zero Funs.lean insertions -- if this persists, aeneas fixed the drop; delete this pass.",
              file=sys.stderr)
