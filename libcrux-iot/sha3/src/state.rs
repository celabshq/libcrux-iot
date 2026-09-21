#[cfg(hax)]
use hax_lib::ToInt;
#[cfg(feature = "check-secret-independence")]
use libcrux_secrets::{Classify, Declassify};
use libcrux_secrets::{U32, U8};

use crate::lane::Lane2U32;
#[cfg(feature = "check-secret-independence")]
use crate::{FromLeBytes, ToLeBytes};

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

#[cfg(feature = "check-secret-independence")]
impl ToLeBytes<4> for U32 {
    fn to_le_bytes(self) -> [U8; 4] {
        self.declassify().to_le_bytes().classify()
    }
}

#[cfg(feature = "check-secret-independence")]
impl FromLeBytes<4> for U32 {
    fn from_le_bytes(bytes: [U8; 4]) -> Self {
        u32::from_le_bytes(bytes.declassify()).classify()
    }
}
