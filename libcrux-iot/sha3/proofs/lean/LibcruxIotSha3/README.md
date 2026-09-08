# SHA-3 Verification

This directory contains the Lean 4 proof that the IOT-friendly
implementation of SHA-3 in `libcrux-iot/sha3/src/` computes
the same function as the hacspec-style FIPS-202 specification in
the `hacspec_sha3` crate (from
[`cryspen/libcrux`](https://github.com/cryspen/libcrux)). Both sides are
extracted from Rust into Lean
via the `cargo hax into lean` pipeline. Most of the verification
code is AI-generated.

## Main theorems

The top-level results are the Keccak equivalence theorem and its corollaries, 
which state equivalence of the SHA-3 and SHAKE functions. The Keccak
equivalence is stated as follows:

[`Sponge/Keccak.lean`](Sponge/Keccak.lean) — `keccak.keccak_keccak_spec`:

```lean
theorem keccak.keccak_keccak_spec
    (RATE : Std.Usize) (DELIM : Std.U8)
    (data : Slice Std.U8) (out : Slice Std.U8)
    (h_RATE_mod : RATE.val % 8 = 0)
    (h_RATE_ge_1 : 1 ≤ RATE.val)
    (h_RATE_le_200 : RATE.val ≤ 200) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccak RATE DELIM data out
    ⦃ ⇓ r => ⌜ ∃ spec_out : Std.Array Std.U8 (Std.Slice.len out),
                sponge.keccak (Std.Slice.len out) RATE DELIM data
                  = .ok spec_out
                ∧ r.val.length = out.val.length
                ∧ ∀ k : Nat, k < out.val.length →
                    r.val[k]! = spec_out.val[k]! ⌝ ⦄
```

Informally: the IOT-friendly implementation `keccak.keccak` (for some rate `RATE`,
delimiter `DELIM`, input `data`, output buffer `out`) produces the same
byte sequence as the hacspec-style specification `sponge.keccak`.

The same statement is carried by `keccak`'s hax contract in
[`src/keccak.rs`](../../../src/keccak.rs):

```rust
#[cfg_attr(hax, hax_lib::requires(
    RATE > 0 && RATE % 8 == 0 && RATE <= 168
))]
#[cfg_attr(hax, hax_lib::ensures(|_|
    hax_lib::prop::Prop::from_bool(future(out).len() == out.len())
        .and(keccak_matches(RATE, DELIM, data.declassify_ref(), future(out).declassify_ref()))))]
pub(crate) fn keccak<const RATE: usize, const DELIM: u8>(data: &[U8], out: &mut [U8])
```

where `keccak_matches(rate, delim, message, out)` is `∀ k < out.len(),
out[k] == keccak_spec_byte(rate, delim, message, k)` and `keccak_spec_byte` is
the byte-wise form of the hacspec sponge output: block `k / rate` of
`iterate_keccak_f(k / rate, absorb(rate, delim, message))`, byte `k mod rate`
of its little-endian lane serialization — literally the body of the hacspec
`sponge::squeeze` closure. The contract is stated per byte because the hacspec
`sponge::keccak::<OUTPUT_LEN>` takes its output length as a const generic,
which a runtime `out.len()` cannot instantiate; the Lean theorem can pass
`out.len` as a term. (The Rust precondition keeps `RATE <= 168`, which the
inner block functions require; the Lean theorem is stated for `RATE ≤ 200`.)
The generated `keccak.keccak.spec` is discharged from `keccak_keccak_spec` by
`keccak_spec_proof` in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean): the
spec's `sponge.keccak` is `absorb` followed by a `createi` of exactly that
closure, so the two forms agree by inverting `createi` — no arithmetic and no
totality assumption on the spec permutation is needed.

The public SHA-3 and SHAKE functions in [`src/lib.rs`](../../../src/lib.rs), in
contrast, carry their equivalence with the hacspec as hax contracts. For example:

```rust
#[cfg_attr(hax, hax_lib::requires(payload.len() <= u32::MAX as usize && digest.len() == SHA3_256_DIGEST_SIZE))]
#[cfg_attr(hax, hax_lib::ensures(|_| future(digest).len() == SHA3_256_DIGEST_SIZE
    && future(digest).declassify_ref()
        == &hacspec_sha3::sha3_256(payload.declassify_ref())[..]))]
pub fn sha256_ema(digest: &mut [U8], payload: &[U8])
```

```rust
#[cfg_attr(hax, hax_lib::requires(BYTES <= u32::MAX as usize))]
#[cfg_attr(hax, hax_lib::ensures(|out| (&out[..]).declassify_ref()
    == &hacspec_sha3::shake128::<BYTES>(data.declassify_ref())[..]))]
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES]
```

hax generates a `<fn>.spec` from each contract in
[`Extraction/Specs.lean`](Extraction/Specs.lean), and
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean)
discharges all six (`<fn>_spec_proof`) from the corollaries of
`keccak_keccak_spec` in [`Sponge/Shake.lean`](Sponge/Shake.lean) (and, as
described above, `keccak`'s own contract from `keccak_keccak_spec` itself):

| impl function | `ensures` (hacspec function) | instance of `keccak_keccak_spec` | Lean corollary |
|---|---|---|---|
| `shake128::<BYTES>` | `hacspec_sha3::shake128::<BYTES>` | RATE 168, DELIM 0x1f | `shake128_spec` |
| `shake256::<BYTES>` | `hacspec_sha3::shake256::<BYTES>` | RATE 136, DELIM 0x1f | `shake256_spec` |
| `sha224_ema` | `hacspec_sha3::sha3_224`, 28-byte digest | RATE 144, DELIM 0x06 | `sha224_ema_spec` |
| `sha256_ema` | `hacspec_sha3::sha3_256`, 32-byte digest | RATE 136, DELIM 0x06 | `sha256_ema_spec` |
| `sha384_ema` | `hacspec_sha3::sha3_384`, 48-byte digest | RATE 104, DELIM 0x06 | `sha384_ema_spec` |
| `sha512_ema` | `hacspec_sha3::sha3_512`, 64-byte digest | RATE  72, DELIM 0x06 | `sha512_ema_spec` |

All six require `payload.len() <= u32::MAX as usize` (resp. `BYTES <= u32::MAX
as usize`), and the `_ema` variants a correctly sized `digest` buffer. The
`declassify_ref` calls only strip the secret-independence wrapper `U8`.

The incremental API is not part of this verification.

### Axiom hygiene

Every top-level digest spec, `keccak_keccak_spec` itself and the discharges of
the Rust contracts depend on exactly Lean's three standard axioms `propext`,
`Classical.choice`, `Quot.sound` — the usual classical-logic foundation shared
by all Mathlib-based proofs — and nothing else. In particular no
`Lean.ofReduceBool` (the axiom behind `bv_decide` and `native_decide`): the
bit-vector identities of the interleaved lane representation (the 26 rotation
lemmas, XOR/AND/NOT distributivity, the interleave/deinterleave bridges, the
LE-byte split) used to be closed by `bv_decide`, one hygienically-named axiom
per call, and are now proved bit by bit from a single per-bit
characterisation of the lift ([`Foundation/Lift.lean`](Foundation/Lift.lean),
`spread_to_even_getLsbD` / `lift_lane_bv_getLsbD`) with the core
`BitVec.getLsbD_*` lemmas.

There are **no hand-introduced, domain-specific assumptions left.** The three
sub-slice `≤`-specs (`Slice.subslice_le_eq`, `Slice.update_subslice_le_eq`,
`Array.update_subslice_le_eq`, in
[`Sponge/SliceSpecs.lean`](Sponge/SliceSpecs.lean)) used to be the only ones, and
they are now **theorems**. They existed because Aeneas's `Slice.subslice` /
`update_subslice` required a *strict* `start < end` and failed on an empty range
(`start = end`), whereas Rust's `&xs[i..i]` is a valid empty slice that the
extracted code produces. As of aeneas nightly-2026.08.24 those primitives guard on
`start ≤ end`, so the intended `≤` behaviour follows from the definitions
(`if_pos`/`dif_pos` + `rfl`); the statements are kept verbatim so no use site
changed.

That also closed a soundness gap rather than just a bookkeeping one: while the
model was strict, `Slice.subslice_le_eq` asserted success exactly where the
definition failed, so `False` was derivable from it at `s = ⟨[], _⟩`, `r = ⟨0,0⟩`
— and because the `@[spec]`-tagged range-index specs are selected automatically by
`hax_mvcgen` on any slice-range subscript, it could be inherited without a
deliberate citation. The ML-KEM and ML-DSA trees carried the same three and close
them on the same fix.

The axiom set is enforced on every build by
[`AxiomCheck.lean`](AxiomCheck.lean): it runs an `#assert_std_axioms` command on
each of the six digest specs, on `keccak_keccak_spec`, and on the contract
discharges `keccak_spec_proof` / `sha256_ema_spec_proof`, failing the build if
any of them comes to depend on an axiom outside the standard three (an admitted
`sorry` anywhere in the proof tree, including the hand-written Aeneas stdlib
models, or a reintroduced `bv_decide`/`native_decide`). To inspect the axioms
of any declaration manually, use `#print axioms <name>`.


## Proof architecture

The proof has two major stages: first establishing Keccak-f[1600]
permutation equivalence as a central intermediate result, then building
the full sponge construction on top of it.

### Keccak-f[1600] permutation equivalence

[`Composition/HacspecBridge.lean`](Composition/HacspecBridge.lean):

```lean
theorem keccakf1600_equiv_hacspec (s : state.KeccakState)
    (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccak_f.keccak_f (lift s) = .ok (lift r_impl) ⌝ ⦄
```

Informally: the implementation's `keccak.keccakf1600` result, lifted
to the specification's state representation, equals what the specification's
`keccak_f.keccak_f` produces when applied to the same lifted input.

The two sides represent state differently. **Spec**: 25 lanes of
`u64`. **Impl**: 25 lanes split into bit-interleaved 32-bit half
pairs. Additionally, the impl uses storage
relabeling for π: each round reads from a different physical layout.

Each impl round is split into 11 θ sub-functions
(`theta_c_x{0..4}_z{0,1}` and `theta_d`), a `pi_rho_chi_1` (handles
rows y=0,1 plus the ι constant XOR), and a `pi_rho_chi_2` (rows
y=2,3,4). The π step is implemented as a *storage relabeling* — each
round reads lanes from different physical positions — so after one
round the canonical `5*x + y` mapping no longer holds. The relabeling
has order 4 (`impl_perm⁴ = id`), so every 4 rounds the layout
re-aligns with the spec. The full 24 rounds factor as 6 bundles of 4.

The bridge `lift : KeccakState → Array u64 25` (in
[`Foundation/Lift.lean`](Foundation/Lift.lean)) interleaves halves
back into `u64`s. A generalised `lift_perm s p sw` reads each lane
through a permutation `p` and an optional half-swap `sw : Fin 25 → Bool`.

The proof factors through a **pure-Lean intermediate spec**
`bit_keccak_spec : KState → KState` (in
[`BitSpec/Spec.lean`](BitSpec/Spec.lean)) that mirrors the impl's
bit-side data flow without the Aeneas monad.

Three named pieces (one file each at the top of the proof tree):

- **`StructuralEquiv.lean`** (impl ≡ `bit_keccak_spec`). Proves the
  Rust extraction equals the pure-Lean bit spec under
  `KState.fromAeneas`.

- **`AlgebraicEquiv.lean`** (`bit_keccak_spec` lifted ≡ spec). Proves the
  pure-Lean bit spec, lifted to `u64`, equals the hacspec 24-round
  application of the round body (θ; ρ; π; χ; ι).

- **`Composition/`**:
  - **`ViaBit.lean`** — composes the two equivalences above to show that
    the impl, lifted to `u64`, equals the 24-round spec chain.
  - **`HacspecBridge.lean`** — bridges the 24-round spec chain to the
    hacspec `keccak_f.keccak_f` loop to yield `keccakf1600_equiv_hacspec`
    as stated above.

### Sponge construction proof

The sponge proof ([`Sponge/`](Sponge/)) builds on `keccakf1600_equiv_hacspec`
and proceeds as follows:

- **Opacity** ([`Sponge/Opaque.lean`](Sponge/Opaque.lean)):
  seals both `keccakf1600` and `keccak_f.keccak_f` as `[local irreducible]`
  so that later sponge reasoning cannot unfold the permutation internals
  and must reason about it only via `keccakf1600_equiv_hacspec`.

- **Byte ↔ lane bridge**
  ([`Sponge/Bytes.lean`](Sponge/Bytes.lean),
  [`Sponge/AbsorbBlock.lean`](Sponge/AbsorbBlock.lean)):
  establishes that `load_block` / `store_block` correctly convert between
  the byte-oriented sponge state and the impl's bit-interleaved lane
  representation, and that `absorb_block` on the impl side matches
  `sponge.absorb_block` on the spec side.

- **Absorb loop** ([`Sponge/Absorb.lean`](Sponge/Absorb.lean)):
  proves the absorb phase loop (`keccak_loop0`) matches
  `sponge.absorb` unfolded as a pure fold over input blocks.

- **Squeeze**
  ([`Sponge/SqueezeBlock.lean`](Sponge/SqueezeBlock.lean),
  [`Sponge/Squeeze.lean`](Sponge/Squeeze.lean)):
  covers the four cases of squeeze blocks (first-only, first, next,
  last) and the squeeze loop (`keccak_loop1`) with a per-byte loop
  invariant. The key lemma `iterate_keccak_f_eq_fold` lifts the
  single-permutation result into repeated applications across blocks.

- **Final absorb** ([`Sponge/AbsorbFinal.lean`](Sponge/AbsorbFinal.lean)):
  proves `absorb_final` (padding + final permutation call) matches
  `sponge.absorb_final`.

- **Keccak** ([`Sponge/Keccak.lean`](Sponge/Keccak.lean)):
  assembles the absorb and squeeze stages into `keccak.keccak_keccak_spec`,
  case-splitting on whether there are zero or at least one full input blocks.

- **Corollaries** ([`Sponge/Shake.lean`](Sponge/Shake.lean)):
  instantiates `keccak_keccak_spec` at concrete `(RATE, DELIM)` pairs to
  yield `shake128_spec`, `shake256_spec`, and the SHA3-ema variants.


## Extraction pipeline

The specification and the implementation are extracted separately. The
implementation is a plain hax scenario declared in
[`libcrux-iot/sha3/hax.toml`](../../../hax.toml) and run with `cargo hax extract`
(no post-processing); the specification is extracted by
`specs/sha3/hax_aeneas.py` in the [`cryspen/libcrux`](https://github.com/cryspen/libcrux)
repo, which calls `cargo hax into lean` and applies small fixes to the output.
The resulting Lean files are:
* `specs/sha3/proofs/lean/HacspecSha3/Extraction/Funs.lean` (in `cryspen/libcrux`)
* [`libcrux-iot/sha3/proofs/lean/LibcruxIotSha3/Extraction/Funs.lean`](Extraction/Funs.lean)

## Reproduction

### Prerequisites

- For running the proofs:
  - Lean 4 toolchain `leanprover/lean4:v4.31.0` (pinned in `lean-toolchain`).
  - The Hax Lean proof library `cryspen/hax-lean` at `v0.3.17` (pulled in as a
    `lake` dependency via `lakefile.toml`).
  - The extracted hacspec (`HacspecSha3`, from `specs/sha3` of
    https://github.com/cryspen/libcrux) at commit `daba41a6bffa3bbdbb0e3f5710590086f95da1d0`
    (pinned in `lakefile.toml`; the same commit `Cargo.toml` pins for the
    `hacspec_sha3` crate the contracts name).
- For extraction:
  - Hax at commit `f8fe69339b69e48a01b8a6a6bcb2ab5e5c5e424d` (`cargo-hax-v0.4.0`)
    (mainline https://github.com/cryspen/hax) providing the `lean` backend,
    with the charon/aeneas binaries pinned workspace-wide in `libcrux-iot/hax.toml`:
    - Charon at https://github.com/AeneasVerif/charon/releases/tag/nightly-2026.09.02
    - Aeneas at https://github.com/cryspen/aeneas/releases/tag/nightly-2026.09.03-6852e64
    These are fetched automatically by `cargo hax tools install` inside the
    `nix develop .#lean` shell.

### Building

From `libcrux-iot/sha3/proofs/lean/`:

```bash
lake exe cache get        # downloading the Mathlib cache
lake build                # building the project
```

### Cross-spec regression (Rust)

We have a couple of Rust tests in place as a first sanity check that
implementation and specification agree:

```bash
cargo test --lib cross_spec --tests
```

This catches lane-layout / round-constant / endianness mismatches at
the Rust level, before they propagate into Lean proof failures.

### Extraction from Rust into Lean

```bash
# Spec side (from a checkout of cryspen/libcrux):
cd specs/sha3/
./hax_aeneas.py

# Impl side:
cd libcrux-iot/sha3/
cargo hax extract
```

