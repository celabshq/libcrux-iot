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
which state equivalence of the SHA-3 and SHAKE functions.

### Keccak

The functional correctness property of the `keccak` function is stated as follows in [`src/keccak.rs`](../../../../src/keccak.rs):

```rust
#[hax_lib::requires(RATE > 0 && RATE % 8 == 0 && RATE <= 168)]
#[hax_lib::ensures(|_| {
    let mut result = out;
    keccak::<RATE, DELIM>(data, &mut result);
    result.declassify() == hacspec_sha3::sponge::keccak::<OUT_LEN>(RATE, DELIM, data.declassify_ref())
})]
pub(crate) fn keccak_fc<const RATE: usize, const DELIM: u8, const OUT_LEN: usize>(
    data: &[U8],
    out: [U8; OUT_LEN],
) {
}
```
Informally: the IOT-friendly implementation `keccak` (for some rate `RATE`,
delimiter `DELIM`, input `data`, output buffer `out`) produces the same
byte sequence as the hacspec-style specification `hacspec_sha3::sponge::keccak`.
The preconditions are that `RATE` is a multiple of 8 and that `0 < RATE <= 168`;
if these are not fulfilled, our verification makes no claims about what the implementation might do.
The signatures of `keccak` and `hacspec_sha3::sponge::keccak` are slighty different: The
`keccak` function expects an externally allocated array for the result and it used a custom
integer type `U8` instead of `u8`, which is why we must call `declassify()` before comparing with
with `hacspec_sha3::sponge::keccak`.

We would prefer to state the property directly as annotations on the `keccak` function,
but this is not possible in this case because the hacspec-variant expects `OUT_LEN` as a const
generic, which is not part of `keccak`'s signature.

The corresponding Lean theorem is
`keccak_fc_spec_proof` in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean).

### SHA-3 and SHAKE

The functional correctness of the SHA-3 and SHAKE functions in [`src/lib.rs`](../../../../src/lib.rs)
is specified using Rust annotations directly on the functions. For example:

```rust
#[cfg_attr(hax, hax_lib::requires(BYTES <= u32::MAX as usize))]
#[cfg_attr(hax, hax_lib::ensures(|out| out.declassify()
    == hacspec_sha3::shake128::<BYTES>(data.declassify_ref())))]
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES]
```
Informally: the IOT-friendly implementation `shake128` yields the same result as
`hacspec_sha3::shake128`. The only precondition is that the number of requested output bytes
must can be at most `u32::MAX`; otherwise, our verification makes no claims about how the
function might behave. Again, we must call `declassify()` to convert between the implementation's
custom integer type `U8` and Rust's integers `u8`.


```rust
#[hax_lib::requires(payload.len() <= u32::MAX as usize && digest.len() == SHA3_256_DIGEST_SIZE)]
#[hax_lib::ensures(|_| future(digest).len() == SHA3_256_DIGEST_SIZE
    && future(digest).declassify_ref()
        == &hacspec_sha3::sha3_256(payload.declassify_ref())[..])]
pub fn sha256_ema(digest: &mut [U8], payload: &[U8])
```


hax generates a `<fn>.spec` from each contract in
[`Extraction/Specs.lean`](Extraction/Specs.lean), and
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean)
discharges all six (`<fn>_spec_proof`) from the corollaries of
`keccak_keccak_spec` in [`Sponge/Shake.lean`](Sponge/Shake.lean) (and, as
described above, the `keccak_fc` contract from `keccak_keccak_spec` itself):

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
`declassify`/`declassify_ref` calls only strip the secret-independence wrapper `U8`. The
`_ema` variants compare through `[..]` because their `digest` is a slice while the hacspec
returns an array, and CoreModels models `==` only between two slices or two arrays.

The incremental API is not part of this verification.

### Axiom hygiene

All of the main theorems presented above are proved using only
Lean's three standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.
This set of axioms is checked on every build by `#guard_msgs` guards in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean).

Beyond Lean's axioms, the proof trusts the hand-written models in
[`Assumptions/`](Assumptions/), which stand in for what hax leaves external.
`FunsExternal.lean` models the `libcrux_secrets` helpers the extraction does
not define — `classify`, the blanket `declassify`, `declassify_ref` on a
shared slice, and the `u32`/`u64` casts — each as an identity or a no-op,
which is what those secret-independence wrappers are at the value level. The
shared `CoreModels.core.*` helpers are NOT redefined here: they come from the
`HacspecSha3` spec's own `FunsExternal`, since defining them twice clashes in
any proof that imports both. `TypesExternal.lean` declares no external types.
`HaxLibAlias.lean` aliases `hax_lib_1.*` onto `hax_lib.*`, a name-only repair
for the duplicate hax-lib crate in the dependency graph. Being definitions
rather than axioms, none of these show up in `#print axioms`, so they are a
trust item to read separately from the guards above.

## Proof architecture

The proof has two major stages: first establishing Keccak-f[1600]
permutation equivalence as a central intermediate result, then building
the full sponge construction on top of it.

The tree divides as follows, bottom to top:

| directory | holds |
|---|---|
| [`Extraction/`](Extraction/) | the hax/aeneas output: `Funs`/`Types`/`Specs` plus the `*External` templates. Generated, never edited. Its `ProofObligations.lean` is the generated, `sorry`-filled statement of every Rust contract; the lakefile keeps it out of the build (see [Extraction pipeline](#extraction-pipeline)) |
| [`Assumptions/`](Assumptions/) | the hand-written models for the items hax leaves external, described under [Axiom hygiene](#axiom-hygiene) |
| [`Foundation/`](Foundation/) | the `lift` bridge, the θ and π-ρ-χ round-level lemmas (`ThetaLift*`, `PrcLift*`), round-constant equivalence (`RcEquiv`), and the loop-spec helpers everything above reuses |
| [`BitSpec/`](BitSpec/) | the pure-Lean intermediate bit spec `bit_keccak_spec` and its state isomorphism |
| `StructuralEquiv.lean`, `AlgebraicEquiv.lean` | the two halves of the permutation argument, detailed below |
| [`Composition/`](Composition/) | composes those halves (`ViaBit`) and bridges the result to the hacspec permutation (`HacspecBridge`), with a slice-equality helper (`SliceEq`) |
| [`Sponge/`](Sponge/) | absorb, squeeze, padding and the top-level corollaries, plus the loop- and slice-spec helpers they share |
| [`Verification/`](Verification/) | `ProofObligations.lean`, the hand-written discharge of the generated `<fn>.spec` obligations (so the Rust contracts hold), and the `#guard_msgs` axiom guards |

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

## Reproduction

### Prerequisites

- For running the proofs:
  - [Lean](https://lean-lang.org/install/)
- For extraction:
  - [cargo](https://rust-lang.org/tools/install/)
  - [cargo-binstall](https://github.com/cargo-bins/cargo-binstall#installation)
  - (hax, charon, aeneas will be downloaded automatically)

### Building

From `libcrux-iot/sha3/proofs/libcrux-iot-sha3/lean`:

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
cd specs
cargo hax extract hacspec-sha3

# Impl side:
cd libcrux-iot
cargo hax extract libcrux-iot-sha3
```

