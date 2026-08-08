//! Cross-spec property/boundary tests reflecting the Lean equivalence
//! theorems proved in `libcrux-iot/sha3/proofs/aeneas-lean/`.
//!
//! Canonical theorem index: `LibcruxIotSha3/README.md`.
//!
//! | Lean theorem                          | Boundary test                       | Proptest                              |
//! |---------------------------------------|-------------------------------------|---------------------------------------|
//! | `keccak_keccak_spec(144, 0x06)`       | `sha3_224_input_boundaries`         | `sha3_224_random_at_boundaries`       |
//! | `keccak_keccak_spec(136, 0x06)`       | `sha3_256_input_boundaries`         | `sha3_256_random_at_boundaries`       |
//! | `keccak_keccak_spec(104, 0x06)`       | `sha3_384_input_boundaries`         | `sha3_384_random_at_boundaries`       |
//! | `keccak_keccak_spec( 72, 0x06)`       | `sha3_512_input_boundaries`         | `sha3_512_random_at_boundaries`       |
//! | `shake128_spec`                       | `shake128_input_output_boundaries`  | `shake128_random_at_boundaries`       |
//! | `shake256_spec`                       | `shake256_input_output_boundaries`  | `shake256_random_at_boundaries`       |
//!
//! The permutation-level theorem `keccakf1600_equiv_hacspec` is exercised
//! by `cross_spec::keccakf1600_matches_keccak_f` and the broader
//! `keccakf1600_matches_keccak_f_broad` test in `src/keccak.rs` (the
//! `keccakf1600` entry point is `pub(crate)` and only reachable from
//! inside the impl crate).
//!
//! Per the proof's experience report: the dominant failure mode for
//! sponge constructions is in the absorb/squeeze block boundary logic.
//! So the primary axis here is *length* corner cases — input lengths
//! around `k·RATE ± 1` and (for SHAKE) output lengths around the same.
//! Content randomization is supplementary, layered via `proptest` at
//! the boundary lengths.

use proptest::prelude::*;
use rand::{rngs::StdRng, Rng, SeedableRng};

// ============================================================
// ctx: thin U8 ↔ u8 wrapper layer.
// Isolates the libcrux-secrets boundary so the rest of the file
// reads in plain `&[u8]`. If `check-secret-independence` ever gets
// enabled on this crate, only this module needs to change.
// ============================================================
mod ctx {
    use libcrux_secrets::{Classify, ClassifyRef, Declassify, DeclassifyRef, U8};

    pub fn impl_sha3_224(msg: &[u8]) -> [u8; 28] {
        let d = libcrux_iot_sha3::sha224(msg.classify_ref());
        let mut out = [0u8; 28];
        out.copy_from_slice(d.declassify_ref());
        out
    }
    pub fn impl_sha3_256(msg: &[u8]) -> [u8; 32] {
        let d = libcrux_iot_sha3::sha256(msg.classify_ref());
        let mut out = [0u8; 32];
        out.copy_from_slice(d.declassify_ref());
        out
    }
    pub fn impl_sha3_384(msg: &[u8]) -> [u8; 48] {
        let d = libcrux_iot_sha3::sha384(msg.classify_ref());
        let mut out = [0u8; 48];
        out.copy_from_slice(d.declassify_ref());
        out
    }
    pub fn impl_sha3_512(msg: &[u8]) -> [u8; 64] {
        let d = libcrux_iot_sha3::sha512(msg.classify_ref());
        let mut out = [0u8; 64];
        out.copy_from_slice(d.declassify_ref());
        out
    }

    pub fn impl_shake128_ema(msg: &[u8], out_len: usize) -> Vec<u8> {
        let mut buf: Vec<U8> = vec![0u8.classify(); out_len];
        libcrux_iot_sha3::shake128_ema(buf.as_mut_slice(), msg.classify_ref());
        buf.into_iter().map(|b| b.declassify()).collect()
    }

    pub fn impl_shake256_ema(msg: &[u8], out_len: usize) -> Vec<u8> {
        let mut buf: Vec<U8> = vec![0u8.classify(); out_len];
        libcrux_iot_sha3::shake256_ema(buf.as_mut_slice(), msg.classify_ref());
        buf.into_iter().map(|b| b.declassify()).collect()
    }
}

// ============================================================
// Length corner-case helpers.
// ============================================================

/// Input length corners that exercise absorb block transitions.
/// For a sponge with rate `rate`, returns lengths around 0 and
/// `k * rate ± 1` for `k ∈ {1, 2, 3, 4}`, plus a multi-block tail.
fn boundary_lens(rate: usize) -> Vec<usize> {
    let mut v = vec![0usize, 1, 7, 8, rate - 2, rate - 1, rate, rate + 1];
    for k in 2..=4 {
        v.extend_from_slice(&[k * rate - 1, k * rate, k * rate + 1]);
    }
    v.push(5 * rate + rate / 2 + 7); // multi-block + odd tail
    v
}

/// Output length corners for variable-output XOFs (SHAKE).
/// Same shape as `boundary_lens`, plus 31/32/33 to capture
/// `ML-KEM`-shaped requests and 7·rate to stress `iterate_keccak_f`.
fn output_lens(rate: usize) -> Vec<usize> {
    let mut v = vec![0usize, 1, 31, 32, 33, rate - 1, rate, rate + 1];
    for k in 2..=4 {
        v.extend_from_slice(&[k * rate - 1, k * rate, k * rate + 1]);
    }
    v.push(7 * rate + 13); // many-block output
    v
}

/// Three deterministic byte patterns at the given length.
/// Pattern 0 — all-zero bytes.
/// Pattern 1 — all-`0xFF` bytes (catches delim/pad XOR collisions).
/// Pattern 2 — `StdRng`-derived bytes seeded by `(kind, len)`.
fn patterns(len: usize, seed_kind: u64) -> [Vec<u8>; 3] {
    let zeros = vec![0u8; len];
    let ones = vec![0xFFu8; len];
    let mut rng = StdRng::seed_from_u64(0xC0FFEE_u64 ^ seed_kind ^ (len as u64));
    let mut rnd = vec![0u8; len];
    for b in &mut rnd {
        *b = rng.gen();
    }
    [zeros, ones, rnd]
}

// ============================================================
// Fixed-output SHA-3 — input-length axis only.
// Reflects `keccak.keccak_keccak_spec(RATE, 0x06)` instantiated
// at each fixed digest length.
// ============================================================

#[test]
fn sha3_224_input_boundaries() {
    for &len in &boundary_lens(144) {
        for (p, msg) in patterns(len, 224).iter().enumerate() {
            let imp = ctx::impl_sha3_224(msg);
            let spc = hacspec_sha3::sha3_224(msg);
            assert_eq!(imp, spc, "sha3_224 mismatch len={} pattern={}", len, p);
        }
    }
}

#[test]
fn sha3_256_input_boundaries() {
    for &len in &boundary_lens(136) {
        for (p, msg) in patterns(len, 256).iter().enumerate() {
            let imp = ctx::impl_sha3_256(msg);
            let spc = hacspec_sha3::sha3_256(msg);
            assert_eq!(imp, spc, "sha3_256 mismatch len={} pattern={}", len, p);
        }
    }
}

#[test]
fn sha3_384_input_boundaries() {
    for &len in &boundary_lens(104) {
        for (p, msg) in patterns(len, 384).iter().enumerate() {
            let imp = ctx::impl_sha3_384(msg);
            let spc = hacspec_sha3::sha3_384(msg);
            assert_eq!(imp, spc, "sha3_384 mismatch len={} pattern={}", len, p);
        }
    }
}

#[test]
fn sha3_512_input_boundaries() {
    for &len in &boundary_lens(72) {
        for (p, msg) in patterns(len, 512).iter().enumerate() {
            let imp = ctx::impl_sha3_512(msg);
            let spc = hacspec_sha3::sha3_512(msg);
            assert_eq!(imp, spc, "sha3_512 mismatch len={} pattern={}", len, p);
        }
    }
}

// ============================================================
// SHAKE — full Cartesian input-length × output-length boundary.
//
// The spec's `shake128/256::<N>` is const-generic in output length,
// so we cannot vary N at runtime. Instead, call the spec once per
// (input, pattern) with `N = MAX_OUT` and slice to each runtime
// `out_len`. The hacspec sponge construction's squeeze stream is
// stable in its output-length parameter (per-block squeeze loop
// reads leading bytes of an unbounded keystream), so
// `shake::<MAX>(msg)[..k] = shake::<k>(msg)` is a property of the
// spec itself. Combined with the Lean `shake{128,256}_spec`, this
// gives an equivalent check at every runtime `out_len`.
// ============================================================

#[test]
fn shake128_input_output_boundaries() {
    const RATE: usize = 168;
    const MAX_OUT: usize = 7 * 168 + 13;
    let in_lens = boundary_lens(RATE);
    let out_lens = output_lens(RATE);

    for &in_len in &in_lens {
        for (p, msg) in patterns(in_len, 128).iter().enumerate() {
            let spec_full = hacspec_sha3::shake128::<MAX_OUT>(msg);
            for &out_len in &out_lens {
                let imp = ctx::impl_shake128_ema(msg, out_len);
                let spc = &spec_full[..out_len];
                assert_eq!(
                    imp.as_slice(),
                    spc,
                    "shake128 mismatch in_len={} out_len={} pattern={}",
                    in_len,
                    out_len,
                    p
                );
            }
        }
    }
}

#[test]
fn shake256_input_output_boundaries() {
    const RATE: usize = 136;
    const MAX_OUT: usize = 7 * 136 + 13;
    let in_lens = boundary_lens(RATE);
    let out_lens = output_lens(RATE);

    for &in_len in &in_lens {
        for (p, msg) in patterns(in_len, 256).iter().enumerate() {
            let spec_full = hacspec_sha3::shake256::<MAX_OUT>(msg);
            for &out_len in &out_lens {
                let imp = ctx::impl_shake256_ema(msg, out_len);
                let spc = &spec_full[..out_len];
                assert_eq!(
                    imp.as_slice(),
                    spc,
                    "shake256 mismatch in_len={} out_len={} pattern={}",
                    in_len,
                    out_len,
                    p
                );
            }
        }
    }
}

// ============================================================
// Proptest layer — randomize CONTENT at known boundary lengths.
// Length is sampled from the boundary table (so every iteration
// hits an interesting boundary); bytes are fully arbitrary.
// ============================================================

/// Strategy: pick a length from `lens`, then generate exactly that many bytes.
fn length_indexed_strategy(lens: Vec<usize>) -> impl Strategy<Value = Vec<u8>> {
    proptest::sample::select(lens)
        .prop_flat_map(|len| proptest::collection::vec(any::<u8>(), len..=len))
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 64,
        .. ProptestConfig::default()
    })]

    #[test]
    fn sha3_224_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(144))) {
        prop_assert_eq!(ctx::impl_sha3_224(&msg), hacspec_sha3::sha3_224(&msg));
    }

    #[test]
    fn sha3_256_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(136))) {
        prop_assert_eq!(ctx::impl_sha3_256(&msg), hacspec_sha3::sha3_256(&msg));
    }

    #[test]
    fn sha3_384_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(104))) {
        prop_assert_eq!(ctx::impl_sha3_384(&msg), hacspec_sha3::sha3_384(&msg));
    }

    #[test]
    fn sha3_512_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(72))) {
        prop_assert_eq!(ctx::impl_sha3_512(&msg), hacspec_sha3::sha3_512(&msg));
    }

    #[test]
    fn shake128_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(168))) {
        // Single fixed output length (512); the input × output Cartesian
        // is covered by `shake128_input_output_boundaries`.
        let imp = ctx::impl_shake128_ema(&msg, 512);
        let spc = hacspec_sha3::shake128::<512>(&msg);
        prop_assert_eq!(imp.as_slice(), &spc[..]);
    }

    #[test]
    fn shake256_random_at_boundaries(msg in length_indexed_strategy(boundary_lens(136))) {
        let imp = ctx::impl_shake256_ema(&msg, 512);
        let spc = hacspec_sha3::shake256::<512>(&msg);
        prop_assert_eq!(imp.as_slice(), &spc[..]);
    }
}
