#[cfg(hax)]
use hax_lib::ToInt;
use libcrux_secrets::{U32, U8};

use crate::lane::Lane2U32;

#[derive(Clone, Copy)]
#[cfg_attr(not(any(eurydice, hax_backend_lean)), derive(Debug))]
pub(crate) struct KeccakState {
    pub(super) st: [Lane2U32; 25],
    pub(super) c: [Lane2U32; 5],
    pub(super) d: [Lane2U32; 5],
    pub(super) i: usize,
}

#[hax_lib::attributes]
impl KeccakState {
    #[inline(always)]
    pub(crate) fn new() -> Self {
        Self {
            st: [Lane2U32::zero(); 25],
            c: [Lane2U32::zero(); 5],
            d: [Lane2U32::zero(); 5],
            i: 0,
        }
    }

    #[inline(always)]
    #[hax_lib::requires(i < 5 && j < 5 && zeta < 2)]
    pub(crate) fn get_with_zeta(&self, i: usize, j: usize, zeta: usize) -> U32 {
        self.st[5 * j + i][zeta]
    }

    #[inline(always)]
    #[hax_lib::requires(i < 5 && j < 5 && zeta < 2)]
    pub(crate) fn set_with_zeta(&mut self, i: usize, j: usize, zeta: usize, v: U32) {
        self.st[5 * j + i].0[zeta] = v
    }

    #[inline(always)]
    #[hax_lib::requires(i < 5 && j < 5)]
    pub(crate) fn get_lane(&self, i: usize, j: usize) -> Lane2U32 {
        self.st[5 * j + i]
    }

    #[inline(always)]
    #[hax_lib::requires(i < 5 && j < 5)]
    pub(crate) fn set_lane(&mut self, i: usize, j: usize, lane: Lane2U32) {
        self.st[5 * j + i] = lane
    }

    #[inline(always)]
    #[hax_lib::requires(i < 5 && j < 2)]
    pub(crate) fn set_lane_value(&mut self, i: usize, j: usize, value: U32) {
        // XXX: We can't implement IndexMut for `Lane2U32` because of hax
        self.c[i].0[j] = value
    }

    #[inline(always)]
    #[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && start.to_int() + RATE.to_int() <= blocks.len().to_int())]
    pub(crate) fn load_block<const RATE: usize>(&mut self, blocks: &[U8], start: usize) {
        load_block_2u32::<RATE>(self, blocks, start)
    }

    #[inline(always)]
    #[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
    pub(crate) fn store_block<const RATE: usize>(&self, out: &mut [U8]) {
        store_block_2u32::<RATE>(self, out)
    }

    #[inline(always)]
    #[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && start <= 200 && start + RATE <= 168)]
    pub(crate) fn load_block_full<const RATE: usize>(&mut self, blocks: &[U8; 200], start: usize) {
        load_block_full_2u32::<RATE>(self, blocks, start)
    }

    #[inline(always)]
    #[hax_lib::requires(RATE % 8 == 0 && RATE <= 168)]
    pub(crate) fn store_block_full<const RATE: usize>(&self, out: &mut [U8; 200]) {
        store_block_full_2u32::<RATE>(self, out);
    }

    /// `out` has the exact size we want here. It must be less than or equal to
    /// `RATE`.
    #[inline(always)]
    #[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && out.len() <= RATE)]
    #[hax_lib::ensures(|_| future(out).len() == out.len())]
    pub(crate) fn store<const RATE: usize>(self, out: &mut [U8]) {
        #[cfg(not(any(eurydice, hax)))]
        debug_assert!(out.len() <= RATE, "{} > {}", out.len(), RATE);

        #[cfg(hax)]
        let _out_len = out.len();

        let num_full_blocks = out.len() / 8;
        let last_block_len = out.len() % 8;

        for i in 0..num_full_blocks {
            hax_lib::loop_invariant!(|i: usize| out.len() == _out_len);
            let keccak_lane = self.get_lane(i / 5, i % 5).deinterleave();
            out[i * 8..i * 8 + 4].copy_from_slice(&keccak_lane[0].to_le_bytes());
            out[i * 8 + 4..i * 8 + 8].copy_from_slice(&keccak_lane[1].to_le_bytes());
        }

        if last_block_len > 4 {
            let keccak_lane = self
                .get_lane(num_full_blocks / 5, num_full_blocks % 5)
                .deinterleave();
            let last_half_block_len = last_block_len - 4;

            out[num_full_blocks * 8..num_full_blocks * 8 + 4]
                .copy_from_slice(&keccak_lane[0].to_le_bytes());
            out[num_full_blocks * 8 + 4..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&keccak_lane[1].to_le_bytes()[0..last_half_block_len]);
        } else if last_block_len > 0 {
            let keccak_lane = self
                .get_lane(num_full_blocks / 5, num_full_blocks % 5)
                .deinterleave();

            out[num_full_blocks * 8..num_full_blocks * 8 + last_block_len]
                .copy_from_slice(&keccak_lane[0].to_le_bytes()[0..last_block_len]);
        }
    }
}

#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && start.to_int() + RATE.to_int() <= blocks.len().to_int())]
#[inline(always)]
fn load_block_2u32<const RATE: usize>(keccak_state: &mut KeccakState, blocks: &[U8], start: usize) {
    #[cfg(not(eurydice))]
    debug_assert!(RATE <= blocks.len() && RATE % 8 == 0);
    for i in 0..RATE / 8 {
        let offset = start + 8 * i;
        // Perform `u64::from_le_bytes` on our 32-bit representation:
        let a = U32::from_le_bytes(blocks[offset..offset + 4].try_into().unwrap());
        let b = U32::from_le_bytes(blocks[offset + 4..offset + 8].try_into().unwrap());
        let lane = Lane2U32::from([a, b]).interleave();
        let got = keccak_state.get_lane(i / 5, i % 5);
        keccak_state.set_lane(
            i / 5,
            i % 5,
            Lane2U32::from_ints([got[0] ^ lane[0], got[1] ^ lane[1]]),
        );
    }
}

#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && start.to_int() + RATE.to_int() <= 200.to_int())]
#[inline(always)]
fn load_block_full_2u32<const RATE: usize>(
    keccak_state: &mut KeccakState,
    blocks: &[U8; 200],
    start: usize,
) {
    load_block_2u32::<RATE>(keccak_state, blocks, start);
}

#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
#[inline(always)]
fn store_block_2u32<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    #[cfg(hax)]
    let _out_len = out.len();
    for i in 0..RATE / 8 {
        hax_lib::loop_invariant!(|i: usize| out.len() == _out_len);
        let keccak_lane = s.get_lane(i / 5, i % 5).deinterleave();
        out[8 * i..8 * i + 4].copy_from_slice(&keccak_lane[0].to_le_bytes());
        out[8 * i + 4..8 * i + 8].copy_from_slice(&keccak_lane[1].to_le_bytes());
    }
}

#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168)]
#[inline(always)]
fn store_block_full_2u32<const RATE: usize>(s: &KeccakState, out: &mut [U8; 200]) {
    // `out[..]` is a workaround for https://github.com/cryspen/hax/issues/1983
    #[cfg(hax)]
    store_block_2u32::<RATE>(s, &mut out[..]);
    #[cfg(not(hax))]
    store_block_2u32::<RATE>(s, out);
}

/// Helpers used by cross-specification tests against `hacspec_sha3`.
///
/// `state_to_spec` is the "deinterleave" function: it converts the
/// implementation's bit-interleaved `KeccakState` into the spec's flat
/// `[u64; 25]` Keccak state. `state_from_spec` is its inverse, used to
/// seed the implementation from a known `[u64; 25]` state for tests.
///
/// The two crates use *transposed* lane layouts:
///
/// * The spec stores lane `A[x, y]` at flat index `5*y + x` (as  described in
///   FIPS 202 §3.1.2), so byte-lane `l` lives directly at `state[l]`.
/// * The impl stores lane `A[x, y]` at flat index `5*x + y` — its byte I/O
///   (`store` / `load_block`) reaches rate-lane `l` via
///   `get_lane(l / 5, l % 5)`, i.e. `st[5 * (l % 5) + (l / 5)]`.
///
/// The two layouts are therefore related by the 5×5 transpose
/// `T(l) = 5 * (l % 5) + (l / 5)`. Spec index `l` corresponds to impl
/// index `T(l)`, so both helpers map through `T`.
#[cfg(test)]
pub(crate) mod cross_spec {
    use super::KeccakState;
    use crate::lane::Lane2U32;
    use libcrux_secrets::{Classify, Declassify};

    /// Transpose between spec and impl flat lane indices.
    fn transpose(idx: usize) -> usize {
        5 * (idx % 5) + (idx / 5)
    }

    /// Deinterleave a single bit-interleaved lane and recombine its two
    /// 32-bit halves into the spec's `u64` lane value.
    pub(crate) fn lane_to_u64(l: &Lane2U32) -> u64 {
        let arr = l.deinterleave().0.declassify();
        (arr[0] as u64) | ((arr[1] as u64) << 32)
    }

    /// Deinterleave: read the impl state into the spec's flat `[u64; 25]`.
    pub(crate) fn state_to_spec(s: &KeccakState) -> [u64; 25] {
        core::array::from_fn(|idx| lane_to_u64(&s.st[transpose(idx)]))
    }

    /// Re-interleave a flat `[u64; 25]` back into the impl's `KeccakState`.
    pub(crate) fn state_from_spec(flat: [u64; 25]) -> KeccakState {
        let mut s = KeccakState::new();
        for idx in 0..25 {
            let lo = (flat[idx] as u32).classify();
            let hi = ((flat[idx] >> 32) as u32).classify();
            s.st[transpose(idx)] = Lane2U32::from_ints([lo, hi]).interleave();
        }
        s
    }
}

#[cfg(test)]
mod cross_spec_tests {
    use super::cross_spec::{state_from_spec, state_to_spec};
    use libcrux_secrets::{Classify, Declassify};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    fn random_state(rng: &mut StdRng) -> [u64; 25] {
        core::array::from_fn(|_| rng.gen())
    }

    #[test]
    fn state_roundtrip_random() {
        let mut rng = StdRng::seed_from_u64(0xC0FFEE);
        for _ in 0..256 {
            let v = random_state(&mut rng);
            let back = state_to_spec(&state_from_spec(v));
            assert_eq!(v, back);
        }
    }

    #[test]
    fn state_roundtrip_edge_cases() {
        let cases: [[u64; 25]; 5] = [
            [0u64; 25],
            [u64::MAX; 25],
            core::array::from_fn(|i| i as u64),
            [0x5555_5555_5555_5555u64; 25],
            [0xAAAA_AAAA_AAAA_AAAAu64; 25],
        ];
        for v in cases {
            assert_eq!(v, state_to_spec(&state_from_spec(v)));
        }
    }

    /// `load_block` corresponds to `Spec::xor_block_into_state` followed by no permutation.
    #[test]
    fn load_block_matches_xor_block_into_state() {
        let mut rng = StdRng::seed_from_u64(0xBEEF);

        fn run<const RATE: usize>(rng: &mut StdRng) {
            let initial: [u64; 25] = core::array::from_fn(|_| rng.gen());
            // load_block reads RATE bytes starting at offset 0.
            let block_u8: [u8; RATE] = core::array::from_fn(|_| rng.gen());
            let block_secret: [libcrux_secrets::U8; RATE] =
                core::array::from_fn(|i| block_u8[i].classify());

            let spec_out = hacspec_sha3::sponge::xor_block_into_state(initial, &block_u8, RATE);

            let mut s = state_from_spec(initial);
            s.load_block::<RATE>(&block_secret, 0);

            assert_eq!(spec_out, state_to_spec(&s), "rate={}", RATE);
        }

        run::<72>(&mut rng);
        run::<104>(&mut rng);
        run::<136>(&mut rng);
        run::<144>(&mut rng);
        run::<168>(&mut rng);
    }

    /// `store_block` (used by `squeeze_first_block`) corresponds to extracting the
    /// first `RATE` bytes via `Spec::squeeze_state`.
    #[test]
    fn store_block_matches_squeeze_state() {
        let mut rng = StdRng::seed_from_u64(0xFACE);

        fn run<const RATE: usize>(rng: &mut StdRng) {
            let spec_state: [u64; 25] = core::array::from_fn(|_| rng.gen());
            let impl_state = state_from_spec(spec_state);

            let spec_out: [u8; RATE] =
                hacspec_sha3::sponge::squeeze_state::<RATE>(&spec_state, [0u8; RATE], 0, RATE);

            let mut out_secret = [0u8.classify(); RATE];
            impl_state.store_block::<RATE>(&mut out_secret);
            let out_pub: [u8; RATE] = core::array::from_fn(|i| out_secret[i].declassify());

            assert_eq!(spec_out, out_pub, "rate={}", RATE);
        }

        run::<72>(&mut rng);
        run::<104>(&mut rng);
        run::<136>(&mut rng);
        run::<144>(&mut rng);
        run::<168>(&mut rng);
    }
}
