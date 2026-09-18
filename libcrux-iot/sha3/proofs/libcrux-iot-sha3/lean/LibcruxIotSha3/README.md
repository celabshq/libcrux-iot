# SHA-3 Verification

This directory contains the Lean 4 proof that the IOT-friendly
implementation of SHA-3 in `libcrux-iot/sha3/src/` computes
the same function as FIPS 202. The Standard is represented by the
`hacspec_sha3_pedantic` crate, a hacspec-style *transcript* of it: its modules and
functions follow the Standard's sections and algorithm numbers, its state is the
state array `A[x, y, z]` of bits, and its byte layer is nothing but Appendix B.1's
`h2b`/`b2h`. Both sides are extracted from Rust into Lean via the hax/Lean pipeline.
Most of the verification code is AI-generated.

Between the two sits a *lane model* -- the Keccak state as 25 `u64` lanes with the rate
in bytes, the shape the implementation is written in -- as ordinary total Lean functions.
The implementation side proves it computes the model; [`Composition/Pedantic/`](Composition/Pedantic/)
proves the model is the transcript, bit for bit.  See
[The lane model](#the-lane-model).

## Main theorems

The top-level results are the six SHA-3 and SHAKE functions' contracts. They rest on a
Keccak sponge equivalence theorem, which in turn rests on a Keccak-f[1600] permutation
equivalence theorem; only the six are stated in Rust.

### Keccak

The internal `keccak` function in [`src/keccak.rs`](../../../../src/keccak.rs) carries no
Rust contract. Its correctness is the Lean theorem
`keccak.keccak_keccak_spec` in [`Sponge/Keccak.lean`](Sponge/Keccak.lean), which is what
the six contracts below are proved through.

It used to be stated in Rust too, as the `#[ensures]` of a body-less, `#[cfg(hax)]`-only
`keccak_fc` -- a separate function because the specification it was compared against took
the output length as a const generic that `keccak`'s own `out: &mut [U8]` cannot provide.
That comparison was against an older specification's byte sponge, which is no longer the
specification this crate's contracts name, and which the FIPS-202 transcript has no
counterpart for: the transcript exposes `KECCAK[c]` and the six standard functions, not a
rate-and-delimiter-parameterised byte sponge. So the wrapper was asserting, to no
audience, a claim about an internal stepping stone, and it is gone. Nothing about the
proof changed with it.

### SHA-3 and SHAKE

The functional correctness of the SHA-3 and SHAKE functions in [`src/lib.rs`](../../../../src/lib.rs)
is specified using Rust annotations directly on the functions. For example:

```rust
#[hax_lib::requires(BYTES <= MAX_INPUT_LEN && data.len() <= MAX_INPUT_LEN)]
#[hax_lib::ensures(|out| out.declassify()[..]
    == hacspec_sha3_pedantic::bytes::shake128(data.declassify_ref(), BYTES)[..])]
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES]
```
Informally: the IOT-friendly implementation `shake128` yields the same result as FIPS
202's SHAKE128. The preconditions bound the requested output length and the input by
`MAX_INPUT_LEN` (see [The input bound](#the-input-bound)); outside them, our verification
makes no claims about how the function might behave. Again, we must call `declassify()`
to convert between the implementation's custom integer type `U8` and Rust's integers
`u8`, and the `[..]` on both sides because the transcript's SHAKE returns a `Vec<u8>`
(its output length is a runtime argument, not a const generic).


```rust
#[hax_lib::requires(payload.len() <= MAX_INPUT_LEN && digest.len() == SHA3_256_DIGEST_SIZE)]
#[hax_lib::ensures(|_| future(digest).declassify_ref()
        == &hacspec_sha3_pedantic::bytes::sha3_256(payload.declassify_ref())[..])]
pub fn sha256_ema(digest: &mut [U8], payload: &[U8])
```
Informally: the IOT-friendly implementation `sha256_ema` yields the same result as FIPS
202's SHA3-256. The precondition is that the payload length is at most `MAX_INPUT_LEN`
and that the `digest` slice has the expected length.

The `[..]` is technically unnecessary, too, but we need it because hax's model of Rust core
currently models `==` only between two slices or two arrays, not between one slice and one array.

We have analogous annotations on `shake256`, 
`sha224_ema`, `sha384_ema`, and `sha512_ema`.
hax generates a proof obligation for each of these, and they are discharged
by Lean theorems in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean):

| impl function | FIPS-202 function | Lean theorem |
|---|---|---|
| `shake128` | `hacspec_sha3_pedantic::bytes::shake128` | `shake128_spec_proof` |
| `shake256` | `hacspec_sha3_pedantic::bytes::shake256` | `shake256_spec_proof` |
| `sha224_ema` | `hacspec_sha3_pedantic::bytes::sha3_224` | `sha224_ema_spec_proof` |
| `sha256_ema` | `hacspec_sha3_pedantic::bytes::sha3_256` | `sha256_ema_spec_proof` |
| `sha384_ema` | `hacspec_sha3_pedantic::bytes::sha3_384` | `sha384_ema_spec_proof` |
| `sha512_ema` | `hacspec_sha3_pedantic::bytes::sha3_512` | `sha512_ema_spec_proof` |

Each of these is discharged by composing the sponge proof (which produces the lane
model's `keccakLanes`) with the corresponding agreement theorem from
[`Composition/Pedantic/`](Composition/Pedantic/) -- `sha3_256_lanes_agree`,
`shake128_lanes_agree`, and so on -- so the generated post is *produced*, not weakened.

### The input bound

Naming the transcript costs one thing. It works on BIT strings, so it expands its input
to `8 * len` bits and then appends the domain-separation suffix and `pad10*1`; that
padded bit length has to be a representable `usize` on every supported target, the
smallest being 32-bit. The six contracts therefore bound their input by

```rust
pub const MAX_INPUT_LEN: usize = 536_870_399; // == (u32::MAX as usize - 4096) / 8
```

rather than by `u32::MAX` -- a narrowing from 4 GB to 512 MB, far above anything an IoT
target will hash, and the price of stating correctness against the Standard's own text
instead of against a specification shaped like the implementation.

### The specification

One specification is involved. **`hacspec_sha3_pedantic`** (`specs/sha3-pedantic`) is the
transcript of FIPS 202 described at the top of this file; it is extracted from
[`celabshq/libcrux`](https://github.com/celabshq/libcrux) and pinned by commit SHA --
never by branch -- in [`lakefile.toml`](../lakefile.toml) and in the crate's
[`Cargo.toml`](../../../../Cargo.toml), at the same revision. It is what the crate's
contracts name, and what the trust argument rests on: auditing this proof means reading
it against the Standard.

### The lane model

FIPS 202 describes the state as an array of bits `A[x, y, z]`; the implementation keeps it
as 25 `u64` lanes, and absorbs and squeezes whole bytes. Proving the one computes the
other directly would mean doing the bit bookkeeping and the interleaving bookkeeping at
once, so the proof goes through a midpoint.

[`LaneModel.lean`](LaneModel.lean) and [`SpongeModel.lean`](SpongeModel.lean) define that
midpoint: the permutation and the sponge on 25 lanes, as ordinary total Lean functions --
`thetaLanes`, ..., `keccakFLanes`, `absorbBlockLanes`, `squeezeLanes`, `keccakLanes`. They
take `List`s and `Nat`s, carry no bounds proofs, and can be unfolded freely.

Nothing in them is trusted, and nothing rests on their being *right* -- only on the two
halves that meet there:

* [`Foundation/`](Foundation/) and [`Sponge/`](Sponge/) prove the implementation computes
  the model (`keccakf1600_equiv_lanes`, `keccak_keccak_spec`, and the six entry points);
* [`Composition/Pedantic/`](Composition/Pedantic/) proves the model *is* the transcript,
  read bit by bit (`theta_bit`, ..., `keccakF_lanesToBits`, and the six
  `*_lanes_agree`).

A mistake in the model cannot make a contract hold that should not: the contract is stated
against the transcript, and both halves are proved.

### Assumptions

All of the main theorems presented above are proved using only
Lean's three standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.
This set of axioms is checked on every build by `#guard_msgs` guards in
[`Verification/ProofObligations.lean`](Verification/ProofObligations.lean).

Beyond Lean's axioms, the proof trusts the hand-written models in
[`Assumptions/`](Assumptions/), which stand in for what hax leaves external.
`FunsExternal.lean` models the `libcrux_secrets` helpers the extraction does
not define. We do not verify secret-independence, so these are modeled as identities
and no-ops. That file is also where the two specification packages enter the generated
extraction's import tree: hax emits `Extraction/FunsExternal.lean` as a one-line shim
onto it and adds no specification imports of its own, so the `#[ensures]` clauses'
`hacspec_sha3_pedantic::bytes::*` are in scope only because they are imported there.
In addition, a duplicate hax-lib crate in the dependency graph currently causes some
references to `hax_lib` to be emitted under a mangled name, `hax_lib_1` or `hax_lib_2`,
with the index assigned by dependency order -- so it shifts if a dependency moves between
`[dependencies]` and `[dev-dependencies]`. The file `HaxLibAlias.lean` aliases both onto
`hax_lib.*` to work around this. Every abbreviation in it is an alias, not a definition,
so nothing is assumed there.

Because the FIPS-202 transcript is now the specification the contracts name, its own two
hand-written models are part of the trusted base as well. Both live in
`HacspecSha3Pedantic`'s `Assumptions/FunsExternal.lean`:

* an `Iterator` instance for `RangeInclusive`. `core-models` declares the type but ships
  neither `new` nor an iterator, so `for j in a..=b` does not extract; the model is
  CoreModels' half-open `Range` iterator with `≤` in place of `<`.
  **Caveat.** Rust's `RangeInclusive` carries an `exhausted` flag that the modelled type
  does not have -- it is a bare `{ start, end }` -- so `next` cannot distinguish "already
  yielded `end`" from "start > end" when `end` is the largest value of the type, and the
  model panics (on the overflow in `forward_checked`) where Rust would yield `A::MAX` and
  then stop. Every inclusive range in the transcript is small and fixed (`0..=l` with
  `l ≤ 6`, `1..=t mod 255`, and Algorithm 7's round indices), so the difference is
  unreachable there -- but a proof about this model is a proof about non-saturating
  ranges only. The corresponding Lean lemmas in
  [`Composition/Pedantic/LoopEq.lean`](Composition/Pedantic/LoopEq.lean) carry the
  side condition (`hsafe`) that keeps the proofs away from that corner.
* a `marker.Copy` instance for `bool`. CoreModels has `marker.Copy` for every integer
  type and `clone.Clone` for `Bool`, but not this one, so `copy_from_slice` on a
  `[bool]` does not resolve. It is the instance those two already determine; nothing is
  assumed.

Moreover, the correctness of the verification depends on:
* the FIPS-202 transcript correctly reflecting the FIPS standard;
* the transcript being extracted faithfully;
* the extraction of the transcript being pinned correctly in the lakefile;
* hax extracting the implementation faithfully;
* hax's Lean libraries modeling Rust faithfully;
* Lean checking the proofs correctly (we could aim for more confidence here by using [comparator](https://github.com/leanprover/comparator), but this is not set up yet);
* the Rust compiler correctly translating into machine code;
* the environment on which the compilation, extraction, and verification is executed functioning correctly.

### What is left out

We do not verify the incremental API here (neither buffered nor unbuffered), and we do not verify the `Digest`/`Hasher` implementations.
There are more Rust specification in the code base, but only the ones above are verified in Lean.

## Proof architecture

The proof has three major stages: first establishing Keccak-f[1600]
permutation equivalence as a central intermediate result, then building
the full sponge construction on top of it -- both against the lane model -- and
finally showing the lane model is the FIPS-202 transcript.

The tree divides as follows, bottom to top:

| directory | holds |
|---|---|
| [`Extraction/`](Extraction/) | the hax/aeneas output: `Funs`/`Types`/`Specs` plus the `*External` templates. Generated, never edited. Its `ProofObligations.lean` is the generated, `sorry`-filled statement of every Rust contract; the lakefile keeps it out of the build (see [Extraction pipeline](#extraction-pipeline)) |
| [`Assumptions/`](Assumptions/) | the hand-written models for the items hax leaves external, described under [Assumptions](#assumptions) |
| [`Foundation/`](Foundation/) | the `lift` bridge, the θ and π-ρ-χ round-level lemmas (`ThetaLift*`, `PrcLift*`), round-constant equivalence (`RcEquiv`), and the loop-spec helpers everything above reuses |
| [`BitSpec/`](BitSpec/) | the pure-Lean intermediate bit spec `bit_keccak_spec` and its state isomorphism |
| `StructuralEquiv.lean`, `AlgebraicEquiv.lean` | the two halves of the permutation argument, detailed below |
| [`Composition/`](Composition/) | composes those halves (`ViaBit`) and reads the result as the lane model's `keccakFLanes` (`LaneBridge`), with a slice-equality helper (`SliceEq`) |
| [`Composition/Pedantic/`](Composition/Pedantic/) | the second half: the lane model = the FIPS-202 transcript, detailed below |
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

### The FIPS-202 transcript bridge

[`Composition/Pedantic/`](Composition/Pedantic/) proves that the lane model and
`hacspec_sha3_pedantic` compute the same six functions. The two are written against
different data: the transcript's state is the state array `A[x, y, z]` of bits and its
sponge absorbs a bit string; the lane model keeps 25 `u64` lanes and absorbs bytes. The
bridge is therefore bit-level throughout, and runs bottom-up:

| file | holds |
|---|---|
| `../../Tables.lean` | the two Keccak constant tables (`RC[0..23]`, ρ's rotation offsets), local copies so that no proof has to name a specification's |
| `../../SpongeModel.lean` | the lane model of the sponge: a block XOR-ed in lane by lane, `pad10*1` in a 200-byte buffer, the absorb recursion, squeezing. Total functions over `List`s and `Nat`s |
| `../../Foundation/LaneEq.lean` | `Foundation/`'s five `*_applied` step semantics are the lane model's, and its 24-fold `spec_chain` is `keccakFLanes` |
| `../../Composition/LaneBridge.lean` | `keccakf1600_equiv_lanes`: the implementation computes `keccakFLanes`. No specification appears in it |
| `../../LaneModel.lean` | the lane model: the state as 25 `u64` lanes, the five step mappings, `roundsUpTo` / `keccakFLanes` and `lanesToBits`, all as ordinary total functions. This is the midpoint the two proof halves meet at |
| `Parameters.lean`, `StateMap.lean`, `Grid.lean` | the state correspondence: `ofLanes` / `toLanes` between 25 lanes and `A[x, y, z]`, mutually inverse |
| `LoopEq.lean` | the reusable equational loop inductions and scalar/container equations the rest is written with |
| `Theta.lean`, `Rho.lean`, `Pi.lean`, `Chi.lean`, `Iota.lean` | the five step mappings (FIPS 202, Algorithms 1-6) as functions of the bits |
| `RoundConstants.lean` | Algorithm 5's LFSR equals the tabulated round constants -- checked by `decide`, so by the kernel, not by `native_decide` |
| `Round.lean`, `Permutation.lean`, `Bits.lean`, `KeccakP.lean` | `Rnd`, the round loop, the state-array/bit-string conversions, and `Keccak-p[1600, n_r]` |
| `BitsOps.lean`, `Padding.lean`, `Sponge.lean`, `KeccakC.lean` | the `bits` operations, `pad10*1` (Algorithm 9), the sponge (Algorithm 8) and `KECCAK[c]` |
| `Bytes.lean`, `Sha3.lean` | `h2b`/`b2h` (Algorithms 10 and 11) and the six entry points at both the bit and the byte level |
| `Lanes.lean` | the lane model *is* the transcript's bit-level permutation: `theta_bit`, `rho_bit`, ..., each triple loop over `(x, y, z)` read off the lanes, up to `keccakF_lanesToBits` |
| `LaneSponge.lean`, `LaneAbsorb.lean`, `LaneSqueeze.lean` | the byte-rate sponge: XORing a block into the lanes is XORing its bits into the bit string; the padded last block is the transcript's last block; the absorb recursion is `absorbFrom`; `squeeze` is `squeezeFrom`; and finally the six `*_lanes_agree` theorems |

The two ends that make the last step work are worth naming. On the absorb side, the
delimiter byte is exactly the domain-separation suffix followed by the `1` that opens
`pad10*1` -- `0x06` is `01` then `1`, `0x1f` is `1111` then `1` -- and the `0x80` OR-ed
into the last byte of the block is that padding's trailing `1`. On the output side,
`b2h` inverts `h2b`, which is what lets the two specifications' byte-level results be
compared at all.

Every result in the directory is `#print axioms`-pinned to Lean's three standard axioms,
including the `decide` over the round-constant table.

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

They run against the FIPS-202 transcript, the same specification the contracts name.
Since it works on bit strings, the comparisons go through a lane/bit-string conversion
(`state::cross_spec::lanes_to_bits` and its inverse, which is Sec. 3.1.2 and nothing
else) and are composed out of the Standard's own operations -- `h2b`, `b2h`, `xor`,
`Trunc`, `pad10*1`, `KECCAK-f`. Where the implementation bundles several of those into
one function, the test spells the bundle out: `absorb_block` is "XOR the block in, then
permute", and `absorb_final` is "append the domain-separation suffix and `pad10*1`, then
do that" -- which is how the delimiter byte the implementation carries (`0x06`, `0x1F`)
gets checked against the suffix the Standard prescribes.

### Extraction from Rust into Lean

```bash
# Spec side (from a checkout of celabshq/libcrux) -- the transcript, which is
# what the contracts name:
cd specs
cargo bin cargo-hax extract hacspec-sha3-pedantic

# Impl side:
cd libcrux-iot
cargo hax extract libcrux-iot-sha3
```

Note that hax adds no specification imports to the generated tree: it writes
`Extraction/FunsExternal.lean` as a one-line shim onto the hand-written
`Assumptions/FunsExternal.lean`, and that is where `HacspecSha3Pedantic` is
imported so the `#[ensures]` clauses resolve.

