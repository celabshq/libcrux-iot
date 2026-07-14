//! The generic SHA3 implementation that uses portable or platform specific
//! sub-routines.

#[cfg(hax)]
use hax_lib::ToInt;
use libcrux_secrets::{Classify, U8};

use crate::state::KeccakState;

/// The internal keccak state that can also buffer inputs to absorb.
/// This is used in the general xof APIs and the incremental hashers in [`crate::hasher`].
#[derive(Clone)]
pub(crate) struct KeccakSpongeState<const RATE: usize> {
    inner: KeccakState,

    // Buffer inputs on absorb.
    buf: [U8; RATE],

    // Buffered length.
    pub(crate) buf_len: usize,

    // Needs sponge.
    sponge: bool,
}

#[hax_lib::attributes]
impl<const RATE: usize> KeccakSpongeState<RATE> {
    /// An all zero block
    pub(crate) fn zero_block() -> [U8; RATE] {
        [0; RATE].classify()
    }

    /// Generate a new keccak xof state.
    pub(crate) fn new() -> Self {
        Self {
            inner: KeccakState::new(),
            buf: Self::zero_block(),
            buf_len: 0,
            sponge: false,
        }
    }

    /// Absorb
    ///
    /// This function takes any number of bytes to absorb and buffers if it's not enough.
    /// The function assumes that all input slices in `blocks` have the same length.
    ///
    /// Only a multiple of `RATE` blocks are absorbed.
    /// For the remaining bytes [`absorb_final`] needs to be called.
    ///
    /// This works best with relatively small `inputs`.
    #[inline(always)]
    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE 
    )]
    pub(crate) fn absorb(&mut self, inputs: &[U8]) {
        let input_remainder_len = self.absorb_full(inputs);

        // ... buffer the rest if there's not enough input (left).
        if input_remainder_len > 0 {
            #[cfg(not(eurydice))]
            debug_assert!(
                self.buf_len == 0  // We consumed everything (or it was empty all along).
                     || self.buf_len + input_remainder_len <= RATE
            );

            let input_len = inputs.len();
            self.buf[self.buf_len..self.buf_len + input_remainder_len]
                .copy_from_slice(&inputs[input_len - input_remainder_len..]);
            self.buf_len += input_remainder_len;
        }
    }

    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE
    )]
    #[hax_lib::ensures(|remainder|
        remainder < RATE
        && remainder <= inputs.len()
        && future(self).buf_len < RATE
    )]
    fn absorb_full(&mut self, inputs: &[U8]) -> usize {
        #[cfg(not(eurydice))]
        debug_assert!(self.buf_len < RATE);

        // Check if there are buffered bytes to absorb first and consume them.
        let input_consumed = self.fill_buffer(inputs);

        if input_consumed > 0 {
            self.inner.load_block::<RATE>(&self.buf, 0);
            keccakf1600(&mut self.inner);

            // "empty" the local buffer
            self.buf_len = 0;
        }

        // We only need to consume the rest of the input.
        let input_to_consume = inputs.len() - input_consumed;

        // Consume the (rest of the) input ...
        let num_blocks = input_to_consume / RATE;
        let remainder = input_to_consume % RATE;

        #[cfg(hax)]
        let _buf_len = self.buf_len;
        for i in 0..num_blocks {
            hax_lib::loop_invariant!(|_i: usize| self.buf_len == _buf_len);

            // We only get in here if `input_len / RATE > 0`.
            self.inner
                .load_block::<RATE>(inputs, input_consumed + i * RATE);
            keccakf1600(&mut self.inner);
        }

        remainder
    }

    /// Consume the internal buffer and the required amount of the input to pad to
    /// `RATE`.
    ///
    /// Returns the `consumed` bytes from `inputs` if there's enough buffered
    /// content to consume, and `0` otherwise.
    /// If `consumed > 0` is returned, `self.buf` contains a full block to be
    /// loaded.
    #[hax_lib::requires(
        self.buf_len < RATE 
    )]
    #[hax_lib::ensures(|res|
        res <= RATE
        && future(self).buf_len <= RATE
    )]
    fn fill_buffer(&mut self, inputs: &[U8]) -> usize {
        let input_len = inputs.len();
        let mut consumed = 0;
        if self.buf_len > 0 {
            // There's something buffered internally to consume.
            if input_len >= RATE - self.buf_len {
                // We have enough data when combining the internal buffer and
                // the input.
                consumed = RATE - self.buf_len;
                self.buf[self.buf_len..].copy_from_slice(&inputs[..consumed]);
                self.buf_len += consumed;
            }
        }
        consumed
    }

    /// Absorb a final block.
    ///
    /// The `inputs` block may be empty. Everything in the `inputs` block beyond
    /// `RATE` bytes is ignored.
    #[inline(always)]
    #[hax_lib::requires(
        RATE > 0 &&
        RATE % 8 == 0 &&
        RATE <= 168 &&
        self.buf_len < RATE 
    )]
    pub(crate) fn absorb_final<const DELIMITER: u8>(&mut self, inputs: &[U8]) {
        let input_remainder_len = self.absorb_full(inputs);

        // Consume the remaining bytes.
        // This may be in the local buffer or in the input.
        let input_len = inputs.len();
        let mut blocks = [0u8; 200].classify();
        if self.buf_len > 0 {
            blocks[0..self.buf_len].copy_from_slice(&self.buf[0..self.buf_len]);
        }
        if input_remainder_len > 0 {
            blocks[self.buf_len..self.buf_len + input_remainder_len]
                .copy_from_slice(&inputs[input_len - input_remainder_len..]);
        }
        blocks[self.buf_len + input_remainder_len] = DELIMITER.classify();
        blocks[RATE - 1] |= 0x80;

        self.inner.load_block_full::<RATE>(&blocks, 0);
        keccakf1600(&mut self.inner);
    }

    /// Squeeze `N` x `LEN` bytes.
    #[inline(always)]
    #[hax_lib::requires(RATE == 168 || RATE == 144 || RATE == 136 || RATE == 104 || RATE == 72)]
    // The code verifies with the z3rlimit specified below, but we
    // can't use the `options` attribute in the impl block because of
    // a hax issue. Therefore we pull out the function and put it
    // there instead.  cf. https://github.com/cryspen/hax/issues/1698
    // #[hax_lib::fstar::options("--z3rlimit 60")]
    pub(crate) fn squeeze(&mut self, out: &mut [U8]) {
        _squeeze(self, out);
    }
}

#[inline(always)]
#[hax_lib::requires(RATE == 168 || RATE == 144 || RATE == 136 || RATE == 104 || RATE == 72)]
#[hax_lib::fstar::options("--z3rlimit 60")]
fn _squeeze<const RATE: usize>(keccak_state: &mut KeccakSpongeState<RATE>, out: &mut [U8]) {
    if keccak_state.sponge {
        // If we called `squeeze` before, call f1600 first.
        // We do it this way around so that we don't call f1600 at the end
        // when we don't need it.
        keccakf1600(&mut keccak_state.inner);
    }

    // How many blocks do we need to squeeze out?
    let out_len = out.len();
    let blocks = out_len / RATE;
    let last = out_len - (out_len % RATE);

    // Squeeze out one to start with.
    // XXX: Eurydice does not extract `core::cmp::min`, so we do
    // this instead. (cf. https://github.com/AeneasVerif/eurydice/issues/49)
    let mid = if RATE >= out_len { out_len } else { RATE };
    keccak_state.inner.store::<RATE>(&mut out[..mid]);

    // If we got asked for more than one block, squeeze out more.
    let mut offset = mid;
    for _k in 1..blocks {
        hax_lib::loop_invariant!(|_k: usize| {
            out.len() == out_len && offset.to_int() == _k.to_int() * RATE.to_int()
        });
        // Here we know that we always have full blocks to write out.
        keccakf1600(&mut keccak_state.inner);
        keccak_state
            .inner
            .store::<RATE>(&mut out[offset..offset + RATE]);
        offset += RATE;
    }

    if last > 0 && last < out_len {
        debug_assert_eq!(last, offset);
        // Squeeze out the last partial block
        keccakf1600(&mut keccak_state.inner);
        keccak_state.inner.store::<RATE>(&mut out[offset..]);
    }

    keccak_state.sponge = true;
}
//// From here, everything is generic

#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::opaque]
const RC_INTERLEAVED_0: [u32; 255] = [
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000,
    0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000000,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
    0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000000,
    0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000001,
    0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000001,
    0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000000, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000001,
    0x00000001, 0x00000000, 0x00000000, 0x00000001, 0x00000000, 0x00000000, 0x00000000, 0x00000001,
    0x00000000, 0x00000001, 0x00000001, 0x00000001, 0x00000000, 0x00000000, 0x00000000,
];

#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::opaque]
const RC_INTERLEAVED_1: [u32; 255] = [
    0x00000000, 0x00000089, 0x8000008b, 0x80008080, 0x0000008b, 0x00008000, 0x80008088, 0x80000082,
    0x0000000b, 0x0000000a, 0x00008082, 0x00008003, 0x0000808b, 0x8000000b, 0x8000008a, 0x80000081,
    0x80000081, 0x80000008, 0x00000083, 0x80008003, 0x80008088, 0x80000088, 0x00008000, 0x80008082,
    0x80008089, 0x80008083, 0x80000001, 0x80008002, 0x80000089, 0x00000082, 0x80000008, 0x00000089,
    0x80000008, 0x00000000, 0x00000083, 0x80008080, 0x00000008, 0x80000080, 0x80008080, 0x00000002,
    0x8000808b, 0x00000008, 0x80000009, 0x0000800b, 0x80008082, 0x80008000, 0x00008008, 0x00008081,
    0x80008089, 0x80008089, 0x8000800a, 0x0000008a, 0x00000082, 0x80000002, 0x00008082, 0x00008080,
    0x8000000b, 0x80000003, 0x0000000a, 0x00008001, 0x80000083, 0x00008083, 0x0000008b, 0x0000800a,
    0x80000083, 0x0000800a, 0x80000000, 0x8000008a, 0x80000008, 0x0000000a, 0x00008088, 0x00000008,
    0x80000003, 0x00000000, 0x0000000a, 0x0000800b, 0x80008088, 0x8000000b, 0x80000080, 0x8000808a,
    0x00008009, 0x00000003, 0x80000003, 0x00000089, 0x80000081, 0x8000008b, 0x80008003, 0x8000800b,
    0x00008008, 0x00008008, 0x00008002, 0x00000009, 0x80008081, 0x0000808a, 0x8000800a, 0x00000080,
    0x00008089, 0x0000808a, 0x80008089, 0x80008000, 0x00008081, 0x8000800a, 0x00000009, 0x80008002,
    0x8000000a, 0x80008002, 0x80000000, 0x80000009, 0x00008088, 0x00000002, 0x80008008, 0x80008088,
    0x80000001, 0x8000808b, 0x00000002, 0x80008002, 0x80000083, 0x00008089, 0x00008080, 0x80000082,
    0x00000088, 0x8000808a, 0x0000808a, 0x80008083, 0x8000000b, 0x80000009, 0x00008001, 0x80000089,
    0x00000088, 0x80008003, 0x80008001, 0x00000003, 0x80000080, 0x80008009, 0x80000089, 0x0000000b,
    0x00000083, 0x80008009, 0x80000083, 0x00008000, 0x8000800b, 0x00008002, 0x00000003, 0x8000008a,
    0x80000002, 0x00008001, 0x80000000, 0x80000003, 0x00000083, 0x8000808a, 0x00008003, 0x00008008,
    0x0000808b, 0x80000082, 0x00000001, 0x00008001, 0x8000000a, 0x80008008, 0x8000800b, 0x00008081,
    0x80008083, 0x80000082, 0x00000082, 0x80000081, 0x80000002, 0x00008088, 0x0000008b, 0x00008083,
    0x00000008, 0x8000008a, 0x8000008b, 0x8000808a, 0x00008080, 0x80000088, 0x00008083, 0x00000002,
    0x80008081, 0x00008003, 0x00008081, 0x80008000, 0x00008002, 0x0000008a, 0x00000001, 0x00008082,
    0x0000808a, 0x80008000, 0x0000808b, 0x80000001, 0x80008081, 0x00008009, 0x0000008a, 0x00000088,
    0x80008009, 0x8000000a, 0x8000808b, 0x0000008b, 0x00008089, 0x00008003, 0x00008002, 0x00000080,
    0x0000800a, 0x8000000a, 0x80008081, 0x00008080, 0x80000001, 0x80008008, 0x80008082, 0x8000800a,
    0x00000003, 0x80000009, 0x00008082, 0x00008009, 0x00000080, 0x00008083, 0x00000081, 0x00000001,
    0x0000800b, 0x80008001, 0x00000080, 0x00008000, 0x80008001, 0x00000009, 0x8000808b, 0x00000081,
    0x00000082, 0x8000008b, 0x80008009, 0x80000000, 0x80000080, 0x80008003, 0x80008082, 0x80008083,
    0x80000088, 0x00008089, 0x00008009, 0x00000009, 0x80008008, 0x80008001, 0x0000008a, 0x0000000b,
    0x00000089, 0x80000002, 0x0000800b, 0x8000800b, 0x0000808b, 0x80000088, 0x0000800a, 0x80000089,
    0x00000001, 0x00008088, 0x00000081, 0x00000088, 0x80008080, 0x00000081, 0x0000000b,
];

// Insert Generated code here, e.g.
// ```
// :r !python libcrux/libcrux-sha3/codegen.py
// ```
#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta_d(s: &mut KeccakState) {
    // D[x] = C[x-1] XOR ROT64(C[x+1], 1)
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[0] = d_x0_zeta0;
    let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
    s.d[2].0[1] = d_x2_zeta1;
    let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[0] = d_x4_zeta0;
    let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
    s.d[1].0[1] = d_x1_zeta1;
    let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[0] = d_x3_zeta0;
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta0 = s.c[0][0];
    let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
    s.d[0].0[1] = d_x0_zeta1;
    let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[0] = d_x2_zeta0;
    let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
    s.d[4].0[1] = d_x4_zeta1;
    let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[0] = d_x1_zeta0;
    let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
    s.d[3].0[1] = d_x3_zeta1;
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_theta(s: &mut KeccakState) {
    // C[x][zeta] = A[0,x][zeta] ^ A[1,x][zeta] ^ A[2,x][zeta] ^ A[3,x][zeta] ^ A[4,x][zeta]
    // https://github.com/hacl-star/hacl-star/blob/main/specs/Spec.SHA3.fst#L28C1-L29C74
    keccakf1600_round0_theta_c_x0_z0(s);
    keccakf1600_round0_theta_c_x0_z1(s);
    keccakf1600_round0_theta_c_x1_z0(s);
    keccakf1600_round0_theta_c_x1_z1(s);
    keccakf1600_round0_theta_c_x2_z0(s);
    keccakf1600_round0_theta_c_x2_z1(s);
    keccakf1600_round0_theta_c_x3_z0(s);
    keccakf1600_round0_theta_c_x3_z1(s);
    keccakf1600_round0_theta_c_x4_z0(s);
    keccakf1600_round0_theta_c_x4_z1(s);
    keccakf1600_round0_theta_d(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y0_zeta0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(1, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(2, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(3, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(4, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(22),
            (a3 ^ d3).rotate_left(11),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 0];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[s.i];
    };
    s.set_with_zeta(0, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y0_zeta1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(1, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(2, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(3, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(4, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(21),
            (a3 ^ d3).rotate_left(10),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 0];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[s.i];
        s.i = s.i + 1;
    };
    s.set_with_zeta(0, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y1_zeta0(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(2, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(3, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(4, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(0, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(1, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y1_zeta1(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(2, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(3, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(4, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(0, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(1, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(30),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0_pi_rho_chi_y0_zeta0::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_y0_zeta1::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_y1_zeta0(s);
    keccakf1600_round0_pi_rho_chi_y1_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y2_zeta0(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(4, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(0, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(1, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(2, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(3, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(13),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y2_zeta1(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(4, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(0, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(1, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(2, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(3, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(12),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y3_zeta0(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(1, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(2, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(4, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(0, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(8),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(14),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y3_zeta1(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(1, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(2, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(4, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(0, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(7),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(13),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y4_zeta0(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(3, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(4, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(0, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(1, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(2, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(20),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_y4_zeta1(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(3, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(4, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(0, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(1, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(2, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(27),
            (a4 ^ d4).rotate_left(19),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round0_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round0_pi_rho_chi_y2_zeta0(s);
    keccakf1600_round0_pi_rho_chi_y2_zeta1(s);
    keccakf1600_round0_pi_rho_chi_y3_zeta0(s);
    keccakf1600_round0_pi_rho_chi_y3_zeta1(s);
    keccakf1600_round0_pi_rho_chi_y4_zeta0(s);
    keccakf1600_round0_pi_rho_chi_y4_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta_d(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[0] = d_x0_zeta0;
    let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
    s.d[2].0[1] = d_x2_zeta1;
    let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[0] = d_x4_zeta0;
    let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
    s.d[1].0[1] = d_x1_zeta1;
    let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[0] = d_x3_zeta0;
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta0 = s.c[0][0];
    let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
    s.d[0].0[1] = d_x0_zeta1;
    let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[0] = d_x2_zeta0;
    let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
    s.d[4].0[1] = d_x4_zeta1;
    let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[0] = d_x1_zeta0;
    let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
    s.d[3].0[1] = d_x3_zeta1;
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_theta(s: &mut KeccakState) {
    keccakf1600_round1_theta_c_x0_z0(s);
    keccakf1600_round1_theta_c_x0_z1(s);
    keccakf1600_round1_theta_c_x1_z0(s);
    keccakf1600_round1_theta_c_x1_z1(s);
    keccakf1600_round1_theta_c_x2_z0(s);
    keccakf1600_round1_theta_c_x2_z1(s);
    keccakf1600_round1_theta_c_x3_z0(s);
    keccakf1600_round1_theta_c_x3_z1(s);
    keccakf1600_round1_theta_c_x4_z0(s);
    keccakf1600_round1_theta_c_x4_z1(s);
    keccakf1600_round1_theta_d(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y0_zeta0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(3, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(1, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(4, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(2, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(22),
            (a3 ^ d3).rotate_left(11),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 1];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[s.i];
    };
    s.set_with_zeta(0, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y0_zeta1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(3, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(1, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(4, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(2, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(21),
            (a3 ^ d3).rotate_left(10),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 1];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[s.i];
        s.i = s.i + 1;
    };
    s.set_with_zeta(0, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y1_zeta0(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(4, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(2, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(0, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(3, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(1, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y1_zeta1(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(4, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(2, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(0, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(3, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(1, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(30),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round1_pi_rho_chi_y0_zeta0::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_y0_zeta1::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_y1_zeta0(s);
    keccakf1600_round1_pi_rho_chi_y1_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y2_zeta0(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(3, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(1, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(4, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(2, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(0, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(13),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y2_zeta1(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(3, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(1, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(4, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(2, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(0, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(12),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y3_zeta0(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(2, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(0, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(1, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(4, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(8),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(14),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y3_zeta1(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(2, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(0, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(1, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(4, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(7),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(13),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y4_zeta0(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(1, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(4, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(2, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(0, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(3, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(20),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_y4_zeta1(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(1, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(4, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(2, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(0, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(3, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(27),
            (a4 ^ d4).rotate_left(19),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round1_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round1_pi_rho_chi_y2_zeta0(s);
    keccakf1600_round1_pi_rho_chi_y2_zeta1(s);
    keccakf1600_round1_pi_rho_chi_y3_zeta0(s);
    keccakf1600_round1_pi_rho_chi_y3_zeta1(s);
    keccakf1600_round1_pi_rho_chi_y4_zeta0(s);
    keccakf1600_round1_pi_rho_chi_y4_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_3 = s.get_with_zeta(3, 4, 1);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_3 = s.get_with_zeta(3, 4, 0);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta_d(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[0] = d_x0_zeta0;
    let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
    s.d[2].0[1] = d_x2_zeta1;
    let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[0] = d_x4_zeta0;
    let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
    s.d[1].0[1] = d_x1_zeta1;
    let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[0] = d_x3_zeta0;
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta0 = s.c[0][0];
    let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
    s.d[0].0[1] = d_x0_zeta1;
    let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[0] = d_x2_zeta0;
    let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
    s.d[4].0[1] = d_x4_zeta1;
    let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[0] = d_x1_zeta0;
    let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
    s.d[3].0[1] = d_x3_zeta1;
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_theta(s: &mut KeccakState) {
    keccakf1600_round2_theta_c_x0_z0(s);
    keccakf1600_round2_theta_c_x0_z1(s);
    keccakf1600_round2_theta_c_x1_z0(s);
    keccakf1600_round2_theta_c_x1_z1(s);
    keccakf1600_round2_theta_c_x2_z0(s);
    keccakf1600_round2_theta_c_x2_z1(s);
    keccakf1600_round2_theta_c_x3_z0(s);
    keccakf1600_round2_theta_c_x3_z1(s);
    keccakf1600_round2_theta_c_x4_z0(s);
    keccakf1600_round2_theta_c_x4_z1(s);
    keccakf1600_round2_theta_d(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y0_zeta0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(2, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(4, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(1, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(3, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(22),
            (a3 ^ d3).rotate_left(11),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 2];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[s.i];
    };
    s.set_with_zeta(0, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y0_zeta1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(2, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(4, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(1, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(3, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(21),
            (a3 ^ d3).rotate_left(10),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 2];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[s.i];
        s.i = s.i + 1;
    };
    s.set_with_zeta(0, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y1_zeta0(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(3, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(0, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(2, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(4, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(1, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y1_zeta1(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(3, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(0, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(2, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(4, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(1, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(30),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round2_pi_rho_chi_y0_zeta0::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_y0_zeta1::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_y1_zeta0(s);
    keccakf1600_round2_pi_rho_chi_y1_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y2_zeta0(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(1, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(3, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(0, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(2, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(4, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(13),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y2_zeta1(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(1, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(3, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(0, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(2, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(4, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(12),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y3_zeta0(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(4, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(1, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(0, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(2, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(8),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(14),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y3_zeta1(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(4, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(1, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(0, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(2, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(7),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(13),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y4_zeta0(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(2, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(4, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(1, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(3, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(0, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(20),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_y4_zeta1(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(2, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(4, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(1, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(3, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(0, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(27),
            (a4 ^ d4).rotate_left(19),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round2_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round2_pi_rho_chi_y2_zeta0(s);
    keccakf1600_round2_pi_rho_chi_y2_zeta1(s);
    keccakf1600_round2_pi_rho_chi_y3_zeta0(s);
    keccakf1600_round2_pi_rho_chi_y3_zeta1(s);
    keccakf1600_round2_pi_rho_chi_y4_zeta0(s);
    keccakf1600_round2_pi_rho_chi_y4_zeta1(s);
}

#[inline(always)]
#[cfg_attr(
    hax_backend_lean,
    hax_lib::lean::before("set_option maxRecDepth 1000 in")
)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x0_z0(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 0);
    let ax_3 = s.get_with_zeta(3, 0, 0);
    let ax_1 = s.get_with_zeta(1, 0, 1);
    let ax_4 = s.get_with_zeta(4, 0, 1);
    let ax_2 = s.get_with_zeta(2, 0, 0);
    s.set_lane_value(0, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x0_z1(s: &mut KeccakState) {
    let ax_0 = s.get_with_zeta(0, 0, 1);
    let ax_3 = s.get_with_zeta(3, 0, 1);
    let ax_1 = s.get_with_zeta(1, 0, 0);
    let ax_4 = s.get_with_zeta(4, 0, 0);
    let ax_2 = s.get_with_zeta(2, 0, 1);
    s.set_lane_value(0, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x1_z0(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 1, 1);
    let ax_0 = s.get_with_zeta(0, 1, 0);
    let ax_3 = s.get_with_zeta(3, 1, 0);
    let ax_1 = s.get_with_zeta(1, 1, 1);
    let ax_4 = s.get_with_zeta(4, 1, 0);
    s.set_lane_value(1, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x1_z1(s: &mut KeccakState) {
    let ax_2 = s.get_with_zeta(2, 1, 0);
    let ax_0 = s.get_with_zeta(0, 1, 1);
    let ax_3 = s.get_with_zeta(3, 1, 1);
    let ax_1 = s.get_with_zeta(1, 1, 0);
    let ax_4 = s.get_with_zeta(4, 1, 1);
    s.set_lane_value(1, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x2_z0(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 2, 0);
    let ax_2 = s.get_with_zeta(2, 2, 0);
    let ax_0 = s.get_with_zeta(0, 2, 1);
    let ax_3 = s.get_with_zeta(3, 2, 1);
    let ax_1 = s.get_with_zeta(1, 2, 1);
    s.set_lane_value(2, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x2_z1(s: &mut KeccakState) {
    let ax_4 = s.get_with_zeta(4, 2, 1);
    let ax_2 = s.get_with_zeta(2, 2, 1);
    let ax_0 = s.get_with_zeta(0, 2, 0);
    let ax_3 = s.get_with_zeta(3, 2, 0);
    let ax_1 = s.get_with_zeta(1, 2, 0);
    s.set_lane_value(2, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x3_z0(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 3, 0);
    let ax_4 = s.get_with_zeta(4, 3, 1);
    let ax_2 = s.get_with_zeta(2, 3, 1);
    let ax_0 = s.get_with_zeta(0, 3, 1);
    let ax_3 = s.get_with_zeta(3, 3, 0);
    s.set_lane_value(3, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x3_z1(s: &mut KeccakState) {
    let ax_1 = s.get_with_zeta(1, 3, 1);
    let ax_4 = s.get_with_zeta(4, 3, 0);
    let ax_2 = s.get_with_zeta(2, 3, 0);
    let ax_0 = s.get_with_zeta(0, 3, 0);
    let ax_3 = s.get_with_zeta(3, 3, 1);
    s.set_lane_value(3, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x4_z0(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 4, 1);
    let ax_1 = s.get_with_zeta(1, 4, 0);
    let ax_4 = s.get_with_zeta(4, 4, 1);
    let ax_2 = s.get_with_zeta(2, 4, 0);
    let ax_0 = s.get_with_zeta(0, 4, 0);
    s.set_lane_value(4, 0, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_c_x4_z1(s: &mut KeccakState) {
    let ax_3 = s.get_with_zeta(3, 4, 0);
    let ax_1 = s.get_with_zeta(1, 4, 1);
    let ax_4 = s.get_with_zeta(4, 4, 0);
    let ax_2 = s.get_with_zeta(2, 4, 1);
    let ax_0 = s.get_with_zeta(0, 4, 1);
    s.set_lane_value(4, 1, ax_0 ^ ax_1 ^ ax_2 ^ ax_3 ^ ax_4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta_d(s: &mut KeccakState) {
    let c_x4_zeta0 = s.c[4][0];
    let c_x1_zeta1 = s.c[1][1];
    let c_x3_zeta0 = s.c[3][0];
    let c_x0_zeta1 = s.c[0][1];
    let c_x2_zeta0 = s.c[2][0];
    let c_x4_zeta1 = s.c[4][1];
    let d_x0_zeta0 = c_x4_zeta0 ^ c_x1_zeta1.rotate_left(1);
    s.d[0].0[0] = d_x0_zeta0;
    let d_x2_zeta1 = c_x1_zeta1 ^ c_x3_zeta0;
    s.d[2].0[1] = d_x2_zeta1;
    let d_x4_zeta0 = c_x3_zeta0 ^ c_x0_zeta1.rotate_left(1);
    s.d[4].0[0] = d_x4_zeta0;
    let d_x1_zeta1 = c_x0_zeta1 ^ c_x2_zeta0;
    s.d[1].0[1] = d_x1_zeta1;
    let d_x3_zeta0 = c_x2_zeta0 ^ c_x4_zeta1.rotate_left(1);
    s.d[3].0[0] = d_x3_zeta0;
    let c_x1_zeta0 = s.c[1][0];
    let c_x3_zeta1 = s.c[3][1];
    let c_x2_zeta1 = s.c[2][1];
    let c_x0_zeta0 = s.c[0][0];
    let d_x0_zeta1 = c_x4_zeta1 ^ c_x1_zeta0;
    s.d[0].0[1] = d_x0_zeta1;
    let d_x2_zeta0 = c_x1_zeta0 ^ c_x3_zeta1.rotate_left(1);
    s.d[2].0[0] = d_x2_zeta0;
    let d_x4_zeta1 = c_x3_zeta1 ^ c_x0_zeta0;
    s.d[4].0[1] = d_x4_zeta1;
    let d_x1_zeta0 = c_x0_zeta0 ^ c_x2_zeta1.rotate_left(1);
    s.d[1].0[0] = d_x1_zeta0;
    let d_x3_zeta1 = c_x2_zeta1 ^ c_x4_zeta0;
    s.d[3].0[1] = d_x3_zeta1;
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_theta(s: &mut KeccakState) {
    keccakf1600_round3_theta_c_x0_z0(s);
    keccakf1600_round3_theta_c_x0_z1(s);
    keccakf1600_round3_theta_c_x1_z0(s);
    keccakf1600_round3_theta_c_x1_z1(s);
    keccakf1600_round3_theta_c_x2_z0(s);
    keccakf1600_round3_theta_c_x2_z1(s);
    keccakf1600_round3_theta_c_x3_z0(s);
    keccakf1600_round3_theta_c_x3_z1(s);
    keccakf1600_round3_theta_c_x4_z0(s);
    keccakf1600_round3_theta_c_x4_z1(s);
    keccakf1600_round3_theta_d(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y0_zeta0<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(0, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(0, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(0, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(0, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(22),
            (a3 ^ d3).rotate_left(11),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[BASE_ROUND + 3];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_0[s.i];
    };
    s.set_with_zeta(0, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y0_zeta1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    let (bx0, bx1) = {
        let a0 = s.get_with_zeta(0, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(0, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(0), (a1 ^ d1).rotate_left(22))
    };
    let (bx2, bx3, bx4) = {
        let a2 = s.get_with_zeta(0, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(0, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(0, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(21),
            (a3 ^ d3).rotate_left(10),
            (a4 ^ d4).rotate_left(7),
        )
    };

    let ax0;
    #[cfg(feature = "full-unroll")]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[BASE_ROUND + 3];
    };
    #[cfg(not(feature = "full-unroll"))]
    {
        ax0 = bx0 ^ ((!bx1) & bx2) ^ RC_INTERLEAVED_1[s.i];
        s.i = s.i + 1;
    };
    s.set_with_zeta(0, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(0, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(0, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(0, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(0, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y1_zeta0(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(1, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(1, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(2), (a1 ^ d1).rotate_left(23))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(1, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(1, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(1, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y1_zeta1(s: &mut KeccakState) {
    let (bx2, bx3) = {
        let a0 = s.get_with_zeta(1, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(1, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(1), (a1 ^ d1).rotate_left(22))
    };
    let (bx4, bx0, bx1) = {
        let a2 = s.get_with_zeta(1, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(1, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(1, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(30),
            (a3 ^ d3).rotate_left(14),
            (a4 ^ d4).rotate_left(10),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(1, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(1, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(1, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(1, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(1, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_1<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round3_pi_rho_chi_y0_zeta0::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_y0_zeta1::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_y1_zeta0(s);
    keccakf1600_round3_pi_rho_chi_y1_zeta1(s);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y2_zeta0(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(2, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(2, 1, 0);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(1))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(2, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(2, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(2, 4, 0);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(13),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y2_zeta1(s: &mut KeccakState) {
    let (bx4, bx0) = {
        let a0 = s.get_with_zeta(2, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(2, 1, 1);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(9), (a1 ^ d1).rotate_left(0))
    };
    let (bx1, bx2, bx3) = {
        let a2 = s.get_with_zeta(2, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(2, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(2, 4, 1);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(3),
            (a3 ^ d3).rotate_left(12),
            (a4 ^ d4).rotate_left(4),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(2, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(2, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(2, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(2, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(2, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y3_zeta0(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(3, 0, 0);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(3, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 0);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(3, 3, 0);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(3, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(8),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(14),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y3_zeta1(s: &mut KeccakState) {
    let (bx1, bx2) = {
        let a0 = s.get_with_zeta(3, 0, 1);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(3, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(18), (a1 ^ d1).rotate_left(5))
    };
    let (bx3, bx4, bx0) = {
        let a2 = s.get_with_zeta(3, 2, 1);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(3, 3, 1);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(3, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(7),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(13),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(3, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(3, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(3, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(3, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(3, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y4_zeta0(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(4, 0, 0);
        let d0 = s.d[0][1];
        let a1 = s.get_with_zeta(4, 1, 0);
        let d1 = s.d[1][0];
        ((a0 ^ d0).rotate_left(21), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(4, 2, 0);
        let d2 = s.d[2][0];
        let a3 = s.get_with_zeta(4, 3, 0);
        let d3 = s.d[3][1];
        let a4 = s.get_with_zeta(4, 4, 0);
        let d4 = s.d[4][1];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(28),
            (a4 ^ d4).rotate_left(20),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 0, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 0, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 0, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 0, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 0, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_y4_zeta1(s: &mut KeccakState) {
    let (bx3, bx4) = {
        let a0 = s.get_with_zeta(4, 0, 1);
        let d0 = s.d[0][0];
        let a1 = s.get_with_zeta(4, 1, 1);
        let d1 = s.d[1][1];
        ((a0 ^ d0).rotate_left(20), (a1 ^ d1).rotate_left(1))
    };
    let (bx0, bx1, bx2) = {
        let a2 = s.get_with_zeta(4, 2, 1);
        let d2 = s.d[2][1];
        let a3 = s.get_with_zeta(4, 3, 1);
        let d3 = s.d[3][0];
        let a4 = s.get_with_zeta(4, 4, 1);
        let d4 = s.d[4][0];
        (
            (a2 ^ d2).rotate_left(31),
            (a3 ^ d3).rotate_left(27),
            (a4 ^ d4).rotate_left(19),
        )
    };
    let ax0 = bx0 ^ ((!bx1) & bx2);
    s.set_with_zeta(4, 0, 1, ax0);
    let ax1 = bx1 ^ ((!bx2) & bx3);
    s.set_with_zeta(4, 1, 1, ax1);
    let ax2 = bx2 ^ ((!bx3) & bx4);
    s.set_with_zeta(4, 2, 1, ax2);
    let ax3 = bx3 ^ ((!bx4) & bx0);
    s.set_with_zeta(4, 3, 1, ax3);
    let ax4 = bx4 ^ ((!bx0) & bx1);
    s.set_with_zeta(4, 4, 1, ax4);
}

#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_round3_pi_rho_chi_2(s: &mut KeccakState) {
    keccakf1600_round3_pi_rho_chi_y2_zeta0(s);
    keccakf1600_round3_pi_rho_chi_y2_zeta1(s);
    keccakf1600_round3_pi_rho_chi_y3_zeta0(s);
    keccakf1600_round3_pi_rho_chi_y3_zeta1(s);
    keccakf1600_round3_pi_rho_chi_y4_zeta0(s);
    keccakf1600_round3_pi_rho_chi_y4_zeta1(s);
}

// What is interesting is that I assumed that not inlining here should be relatively cheap, because
// it's just 6 calls more per permutation, but commenting out the inline here gives a 10%
// performance hit, e.g.
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 21535 cycles
// vs
//   [CYCLE_MEASUREMENT libcrux SHAKE256 (PRF_ETA1_RANDOMNESS_1024)] : + 19139 cycles
#[inline(always)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600_4rounds<const BASE_ROUND: usize>(s: &mut KeccakState) {
    keccakf1600_round0_theta(s);
    keccakf1600_round0_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round0_pi_rho_chi_2(s);
    keccakf1600_round1_theta(s);
    keccakf1600_round1_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round1_pi_rho_chi_2(s);
    keccakf1600_round2_theta(s);
    keccakf1600_round2_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round2_pi_rho_chi_2(s);
    keccakf1600_round3_theta(s);
    keccakf1600_round3_pi_rho_chi_1::<BASE_ROUND>(s);
    keccakf1600_round3_pi_rho_chi_2(s);
}

#[inline(never)]
#[hax_lib::opaque]
pub(crate) fn keccakf1600(s: &mut KeccakState) {
    #[cfg(not(feature = "full-unroll"))]
    for _ in 0..6 {
        // dummy base round, is ignored if we don't unroll
        keccakf1600_4rounds::<0>(s);
    }
    #[cfg(feature = "full-unroll")]
    {
        keccakf1600_4rounds::<0>(s);
        keccakf1600_4rounds::<4>(s);
        keccakf1600_4rounds::<8>(s);
        keccakf1600_4rounds::<12>(s);
        keccakf1600_4rounds::<16>(s);
        keccakf1600_4rounds::<20>(s);
    }
    s.i = 0;
}

#[inline(always)]
#[hax_lib::requires(
    RATE % 8 == 0
    && RATE <= 168
    && start.to_int() + RATE.to_int() <= blocks.len().to_int()
)]
pub(crate) fn absorb_block<const RATE: usize>(s: &mut KeccakState, blocks: &[U8], start: usize) {
    s.load_block::<RATE>(blocks, start);
    keccakf1600(s)
}

#[inline(always)]
#[hax_lib::requires(
    RATE > 0
    && RATE % 8 == 0
    && RATE <= 168
    && len < RATE
    && start.to_int() + len.to_int() <= last.len().to_int())]
pub(crate) fn absorb_final<const RATE: usize, const DELIM: u8>(
    s: &mut KeccakState,
    last: &[U8],
    start: usize,
    len: usize,
) {
    #[cfg(not(eurydice))]
    debug_assert!(len < RATE); // && last[0].len() < RATE

    let mut blocks = [0u8; WIDTH].classify();
    if len > 0 {
        blocks[0..len].copy_from_slice(&last[start..start + len]);
    }
    blocks[len] = DELIM.classify();
    blocks[RATE - 1] |= 0x80;
    s.load_block_full::<RATE>(&blocks, 0);
    keccakf1600(s);
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_first_block<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    s.store_block::<RATE>(out)
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && RATE <= out.len())]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn squeeze_next_block<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    keccakf1600(s);
    s.store_block::<RATE>(out)
}

#[inline(always)]
#[cfg(feature = "unbuffered-xof")]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && 3 * RATE <= out.len())]
pub(crate) fn squeeze_first_three_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    squeeze_first_block::<RATE>(s, out);
    squeeze_next_block::<RATE>(s, &mut out[RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[2 * RATE..]);
}

#[inline(always)]
#[cfg(feature = "unbuffered-xof")]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && 5 * RATE <= out.len())]
pub(crate) fn squeeze_first_five_blocks<const RATE: usize>(s: &mut KeccakState, out: &mut [U8]) {
    squeeze_first_block::<RATE>(s, out);
    squeeze_next_block::<RATE>(s, &mut out[RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[2 * RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[3 * RATE..]);
    squeeze_next_block::<RATE>(s, &mut out[4 * RATE..]);
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && out.len() <= 200)]
pub(crate) fn squeeze_last<const RATE: usize>(mut s: KeccakState, out: &mut [U8]) {
    keccakf1600(&mut s);
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

#[inline(always)]
#[hax_lib::requires(RATE % 8 == 0 && RATE <= 168 && out.len() <= 200)]
pub(crate) fn squeeze_first_and_last<const RATE: usize>(s: &KeccakState, out: &mut [U8]) {
    let mut b = [0u8; 200].classify();
    s.store_block_full::<RATE>(&mut b);
    out.copy_from_slice(&b[0..out.len()]);
}

// in bytes; this is the 1600 (in bits) in keccak-f[1600]
const WIDTH: usize = 200;

#[inline(always)]
#[hax_lib::requires(
    RATE > 0 && RATE % 8 == 0 && RATE <= 168
)]
#[hax_lib::ensures(|_| future(out).len() == out.len())]
pub(crate) fn keccak<const RATE: usize, const DELIM: u8>(data: &[U8], out: &mut [U8]) {
    let n = data.len() / RATE;
    let rem = data.len() % RATE;

    let outlen = out.len();
    let blocks = outlen / RATE;
    let last = outlen - (outlen % RATE);

    let mut s = KeccakState::new();

    let mut start = 0;
    for _i in 0..n {
        hax_lib::loop_invariant!(|_i: usize| { start == _i * RATE });

        absorb_block::<RATE>(&mut s, &data, start);
        start += RATE;
    }

    absorb_final::<RATE, DELIM>(&mut s, data, data.len() - rem, rem);

    if blocks == 0 {
        squeeze_first_and_last::<RATE>(&s, out)
    } else {
        squeeze_first_block::<RATE>(&s, out);
        let mut offset = RATE;
        for _i in 1..blocks {
            hax_lib::loop_invariant!(|_i: usize| { out.len() == outlen && offset == _i * RATE });
            squeeze_next_block::<RATE>(&mut s, &mut out[offset..]);
            offset += RATE;
        }
        if last < outlen {
            debug_assert_eq!(last, offset);
            squeeze_last::<RATE>(s, &mut out[offset..])
        }
    }
}


#[cfg(test)]
mod cross_spec {
    //! Cross-specification tests: compare every observable stage of the impl
    //! against the `hacspec_sha3` spec crate. The state
    //! conversion helpers live in `crate::state::cross_spec`.
    //!
    //! Properties have the form `Spec::f(to_spec(input)) == to_spec(Impl::f(input))`.

    extern crate alloc;

    use super::*;
    use crate::state::cross_spec::{lane_to_u64, state_from_spec, state_to_spec};
    use libcrux_secrets::{Classify, ClassifyRef, Declassify};
    use rand::rngs::StdRng;
    use rand::{Rng, SeedableRng};

    /// Compute the spec's column-parity array `C` from a flat `[u64; 25]` state.
    ///
    /// Under the spec layout `state[5*y + x] = A[x, y]`,
    /// `C[x] = ⊕_{y=0..4} state[5*y + x]`.
    fn spec_c(state: &[u64; 25]) -> [u64; 5] {
        core::array::from_fn(|x| {
            state[x] ^ state[5 + x] ^ state[5 * 2 + x] ^ state[5 * 3 + x] ^ state[5 * 4 + x]
        })
    }

    /// Compute the spec's `D` array: `D[x] = C[x-1] ⊕ rot(C[x+1], 1)`.
    fn spec_d(c: &[u64; 5]) -> [u64; 5] {
        core::array::from_fn(|x| c[(x + 4) % 5] ^ c[(x + 1) % 5].rotate_left(1))
    }

    /// Run one spec round = `iota(chi(pi(rho(theta(state)))), round)`.
    fn spec_one_round(state: [u64; 25], round: usize) -> [u64; 25] {
        use hacspec_sha3::keccak_f as kf;
        kf::iota(kf::chi(kf::pi(kf::rho(kf::theta(state)))), round)
    }

    /// Run `n` consecutive spec rounds starting at `start`.
    fn spec_rounds(mut state: [u64; 25], start: usize, n: usize) -> [u64; 25] {
        for r in 0..n {
            state = spec_one_round(state, start + r);
        }
        state
    }

    fn random_state(rng: &mut StdRng) -> [u64; 25] {
        core::array::from_fn(|_| rng.gen())
    }

    // ---------------------------------------------------------------------
    // Theta auxiliaries (the impl exposes C and D in `s.c` / `s.d`).
    // ---------------------------------------------------------------------

    #[test]
    fn theta_c_d_match() {
        let mut rng = StdRng::seed_from_u64(0xCDCD);
        for _ in 0..32 {
            let spec_state = random_state(&mut rng);
            let mut s = state_from_spec(spec_state);
            // After _round0_theta, `s.c` and `s.d` are populated but `s.st` is unchanged.
            keccakf1600_round0_theta(&mut s);

            let c_spec = spec_c(&spec_state);
            let d_spec = spec_d(&c_spec);
            let c_impl: [u64; 5] = core::array::from_fn(|x| lane_to_u64(&s.c[x]));
            let d_impl: [u64; 5] = core::array::from_fn(|x| lane_to_u64(&s.d[x]));

            assert_eq!(c_spec, c_impl, "C mismatch");
            assert_eq!(d_spec, d_impl, "D mismatch");
            // The state itself must NOT change yet — theta only fills c/d here.
            assert_eq!(
                spec_state,
                state_to_spec(&s),
                "state changed by _round0_theta"
            );
        }
    }

    // ---------------------------------------------------------------------
    // Full Keccak-f[1600] permutation.
    // ---------------------------------------------------------------------

    #[test]
    fn keccakf1600_matches_keccak_f() {
        let mut rng = StdRng::seed_from_u64(0xBABE);
        let mut cases: alloc::vec::Vec<[u64; 25]> = alloc::vec![
            [0u64; 25],
            [u64::MAX; 25],
            core::array::from_fn(|i| i as u64),
        ];
        for _ in 0..6 {
            cases.push(random_state(&mut rng));
        }

        for case in cases {
            let spec_out = hacspec_sha3::keccak_f::keccak_f(case);
            let mut s = state_from_spec(case);
            keccakf1600(&mut s);
            assert_eq!(spec_out, state_to_spec(&s));
        }
    }

    /// Broader random + boundary corpus for `keccakf1600` vs the hacspec
    /// `keccak_f` permutation. Reflects the Lean theorem
    /// `keccakf1600_equiv_hacspec` (see
    /// `LibcruxIotSha3/Equivalence/HacspecBridge.lean`).
    #[test]
    fn keccakf1600_matches_keccak_f_broad() {
        let mut rng = StdRng::seed_from_u64(0xCAFE_F1600);
        let mut cases: alloc::vec::Vec<[u64; 25]> = alloc::vec![
            [0u64; 25],
            [u64::MAX; 25],
            [u64::MAX >> 1; 25],
            core::array::from_fn(|i| 1u64 << (i % 64)),
            core::array::from_fn(|i| i as u64),
            core::array::from_fn(|i| (i as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)),
        ];
        for _ in 0..256 {
            cases.push(random_state(&mut rng));
        }

        for (idx, case) in cases.into_iter().enumerate() {
            let spec_out = hacspec_sha3::keccak_f::keccak_f(case);
            let mut s = state_from_spec(case);
            keccakf1600(&mut s);
            assert_eq!(spec_out, state_to_spec(&s), "case #{}", idx);
        }
    }

    // ---------------------------------------------------------------------
    // Per-round granularity NOTE
    //
    // The impl performs π implicitly as a *storage relabeling*: each round
    // reads from different physical positions (compare the addressing in
    // `keccakf1600_round0_pi_rho_chi_y0_zeta0` at line 420 with the
    // `round1`/`round2`/`round3` analogues). After one round the canonical
    // impl mapping `st[5*x + y] ↔ A[x, y]` no longer holds; instead the
    // physical layout is a non-trivial permutation of the logical layout.
    // The permutation has order 4, so the layout *only* re-aligns with the
    // spec every 4 rounds. A per-round cross-spec comparison would require
    // deriving that permutation by hand; the `four_rounds_*` tests below
    // cover the smallest impl-aligned granularity where a direct comparison
    // is meaningful.
    // ---------------------------------------------------------------------

    // ---------------------------------------------------------------------
    // Four-round bundles (`keccakf1600_4rounds<BASE_ROUND>`).
    // ---------------------------------------------------------------------

    fn check_four_rounds<const BASE: usize>() {
        let mut rng = StdRng::seed_from_u64(0x4000 + BASE as u64);
        for _ in 0..4 {
            let spec_state = random_state(&mut rng);
            let mut s = state_from_spec(spec_state);
            s.i = BASE; // for non-full-unroll, RC index is taken from s.i
            keccakf1600_4rounds::<BASE>(&mut s);
            let expected = spec_rounds(spec_state, BASE, 4);
            assert_eq!(expected, state_to_spec(&s), "base round {}", BASE);
        }
    }

    #[test]
    fn four_rounds_base_0() {
        check_four_rounds::<0>();
    }
    #[test]
    fn four_rounds_base_4() {
        check_four_rounds::<4>();
    }
    #[test]
    fn four_rounds_base_8() {
        check_four_rounds::<8>();
    }
    #[test]
    fn four_rounds_base_12() {
        check_four_rounds::<12>();
    }
    #[test]
    fn four_rounds_base_16() {
        check_four_rounds::<16>();
    }
    #[test]
    fn four_rounds_base_20() {
        check_four_rounds::<20>();
    }

    // ---------------------------------------------------------------------
    // Sponge layer: absorb_block, absorb_final, squeeze_first/next_block.
    // ---------------------------------------------------------------------

    /// `absorb_block::<RATE>` corresponds to `Spec::absorb_block`.
    #[test]
    fn absorb_block_matches() {
        let mut rng = StdRng::seed_from_u64(0xABBA);
        fn run<const RATE: usize>(rng: &mut StdRng) {
            for &start in &[0usize, RATE] {
                for _ in 0..4 {
                    let spec_state = core::array::from_fn(|_| rng.gen::<u64>());
                    let block_u8: alloc::vec::Vec<u8> =
                        (0..start + RATE).map(|_| rng.gen()).collect();
                    let block_secret = block_u8[..].classify_ref();

                    let spec_out = hacspec_sha3::sponge::absorb_block(
                        spec_state,
                        &block_u8[start..start + RATE],
                        RATE,
                    );

                    let mut s = state_from_spec(spec_state);
                    absorb_block::<RATE>(&mut s, block_secret, start);

                    assert_eq!(spec_out, state_to_spec(&s), "rate={} start={}", RATE, start);
                }
            }
        }
        run::<72>(&mut rng);
        run::<104>(&mut rng);
        run::<136>(&mut rng);
        run::<144>(&mut rng);
        run::<168>(&mut rng);
    }

    /// `absorb_final::<RATE, DELIM>` matches `Spec::absorb_final` for partial blocks.
    #[test]
    fn absorb_final_matches() {
        let mut rng = StdRng::seed_from_u64(0xF1AA);
        fn run<const RATE: usize, const DELIM: u8>(rng: &mut StdRng) {
            for &start in &[0usize, RATE] {
                for &len in &[0usize, 1, RATE / 2, RATE - 1] {
                    for _ in 0..4 {
                        let spec_state = core::array::from_fn(|_| rng.gen::<u64>());
                        let msg_u8: alloc::vec::Vec<u8> =
                            (0..start + len).map(|_| rng.gen()).collect();
                        let msg_secret = msg_u8[..].classify_ref();

                        let spec_out = hacspec_sha3::sponge::absorb_final(
                            spec_state, &msg_u8, start, len, RATE, DELIM,
                        );

                        let mut s = state_from_spec(spec_state);
                        absorb_final::<RATE, DELIM>(&mut s, msg_secret, start, len);

                        assert_eq!(
                            spec_out,
                            state_to_spec(&s),
                            "rate={} delim={:#x} start={} len={}",
                            RATE,
                            DELIM,
                            start,
                            len
                        );
                    }
                }
            }
        }
        // SHA3: delim 0x06; SHAKE: delim 0x1F.
        run::<144, 0x06>(&mut rng); // SHA3-224
        run::<136, 0x06>(&mut rng); // SHA3-256
        run::<104, 0x06>(&mut rng); // SHA3-384
        run::<72, 0x06>(&mut rng); // SHA3-512
        run::<168, 0x1F>(&mut rng); // SHAKE128
        run::<136, 0x1F>(&mut rng); // SHAKE256
    }

    /// `squeeze_first_block::<RATE>` matches the first-block-only extraction
    /// (`Spec::squeeze_state` without any prior permutation).
    #[test]
    fn squeeze_first_block_matches() {
        let mut rng = StdRng::seed_from_u64(0x5555);
        fn run<const RATE: usize>(rng: &mut StdRng) {
            for _ in 0..4 {
                let spec_state: [u64; 25] = core::array::from_fn(|_| rng.gen());
                let impl_state = state_from_spec(spec_state);

                let spec_out: [u8; RATE] =
                    hacspec_sha3::sponge::squeeze_state::<RATE>(&spec_state, [0u8; RATE], 0, RATE);

                let mut out_secret = [0u8; RATE].classify();
                squeeze_first_block::<RATE>(&impl_state, &mut out_secret);
                let out_pub: [u8; RATE] = out_secret.declassify();

                assert_eq!(spec_out, out_pub, "rate={}", RATE);
            }
        }
        run::<72>(&mut rng);
        run::<104>(&mut rng);
        run::<136>(&mut rng);
        run::<144>(&mut rng);
        run::<168>(&mut rng);
    }

    /// `squeeze_next_block::<RATE>` does one permutation step then extracts;
    /// this matches `Spec::squeeze_state(keccak_f(state), ...)`.
    #[test]
    fn squeeze_next_block_matches() {
        let mut rng = StdRng::seed_from_u64(0x7777);
        fn run<const RATE: usize>(rng: &mut StdRng) {
            for _ in 0..4 {
                let spec_state: [u64; 25] = core::array::from_fn(|_| rng.gen());
                let permuted = hacspec_sha3::keccak_f::keccak_f(spec_state);
                let spec_out: [u8; RATE] =
                    hacspec_sha3::sponge::squeeze_state::<RATE>(&permuted, [0u8; RATE], 0, RATE);

                let mut s = state_from_spec(spec_state);
                let mut out_secret = [0u8; RATE].classify();
                squeeze_next_block::<RATE>(&mut s, &mut out_secret);
                let out_pub: [u8; RATE] = out_secret.declassify();

                assert_eq!(spec_out, out_pub, "rate={}", RATE);
            }
        }
        run::<72>(&mut rng);
        run::<104>(&mut rng);
        run::<136>(&mut rng);
        run::<144>(&mut rng);
        run::<168>(&mut rng);
    }

    // ---------------------------------------------------------------------
    // Top-level: full keccak sponge for SHA3 and SHAKE variants.
    // ---------------------------------------------------------------------

    fn run_impl_keccak<const RATE: usize, const DELIM: u8, const OUT_LEN: usize>(
        msg: &[u8],
    ) -> [u8; OUT_LEN] {
        let msg_secret = msg[..].classify_ref();
        let mut out_secret = [0u8; OUT_LEN].classify();
        keccak::<RATE, DELIM>(msg_secret, &mut out_secret);
        out_secret.declassify()
    }

    /// Sample input messages: edges + a few randoms across a range of sizes.
    fn message_corpus() -> alloc::vec::Vec<alloc::vec::Vec<u8>> {
        let mut msgs: alloc::vec::Vec<alloc::vec::Vec<u8>> = alloc::vec![
            alloc::vec![],
            alloc::vec![0u8; 1],
            alloc::vec![0xFFu8; 1],
            b"abc".to_vec(),
            // Around SHA3-256 rate boundary (136 B):
            alloc::vec![0x5Au8; 135],
            alloc::vec![0x5Au8; 136],
            alloc::vec![0x5Au8; 137],
            // Multi-block with non-rate tail:
            alloc::vec![0xA5u8; 3 * 136 + 17],
        ];
        let mut rng = StdRng::seed_from_u64(0xDEC0DED);
        for &len in &[0usize, 7, 64, 200, 512] {
            let mut buf = alloc::vec![0u8; len];
            for b in &mut buf {
                *b = rng.gen();
            }
            msgs.push(buf);
        }
        msgs
    }

    #[test]
    fn sha3_224_matches_spec() {
        for msg in message_corpus() {
            let impl_d = run_impl_keccak::<144, 0x06, 28>(&msg);
            let spec_d = hacspec_sha3::sha3_224(&msg);
            assert_eq!(impl_d, spec_d, "msg.len={}", msg.len());
        }
    }

    #[test]
    fn sha3_256_matches_spec() {
        for msg in message_corpus() {
            let impl_d = run_impl_keccak::<136, 0x06, 32>(&msg);
            let spec_d = hacspec_sha3::sha3_256(&msg);
            assert_eq!(impl_d, spec_d, "msg.len={}", msg.len());
        }
    }

    #[test]
    fn sha3_384_matches_spec() {
        for msg in message_corpus() {
            let impl_d = run_impl_keccak::<104, 0x06, 48>(&msg);
            let spec_d = hacspec_sha3::sha3_384(&msg);
            assert_eq!(impl_d, spec_d, "msg.len={}", msg.len());
        }
    }

    #[test]
    fn sha3_512_matches_spec() {
        for msg in message_corpus() {
            let impl_d = run_impl_keccak::<72, 0x06, 64>(&msg);
            let spec_d = hacspec_sha3::sha3_512(&msg);
            assert_eq!(impl_d, spec_d, "msg.len={}", msg.len());
        }
    }

    fn shake_check<const RATE: usize, const N: usize>(spec_shake: fn(&[u8]) -> [u8; N]) {
        for msg in message_corpus() {
            let impl_d = run_impl_keccak::<RATE, 0x1F, N>(&msg);
            let spec_d = spec_shake(&msg);
            assert_eq!(impl_d, spec_d, "msg.len={} N={}", msg.len(), N);
        }
    }

    #[test]
    fn shake128_matches_spec_16() {
        shake_check::<168, 16>(hacspec_sha3::shake128::<16>);
    }
    #[test]
    fn shake128_matches_spec_32() {
        shake_check::<168, 32>(hacspec_sha3::shake128::<32>);
    }
    #[test]
    fn shake128_matches_spec_200() {
        shake_check::<168, 200>(hacspec_sha3::shake128::<200>);
    }
    #[test]
    fn shake128_matches_spec_512() {
        shake_check::<168, 512>(hacspec_sha3::shake128::<512>);
    }
    #[test]
    fn shake256_matches_spec_32() {
        shake_check::<136, 32>(hacspec_sha3::shake256::<32>);
    }
    #[test]
    fn shake256_matches_spec_64() {
        shake_check::<136, 64>(hacspec_sha3::shake256::<64>);
    }
    #[test]
    fn shake256_matches_spec_200() {
        shake_check::<136, 200>(hacspec_sha3::shake256::<200>);
    }
    #[test]
    fn shake256_matches_spec_512() {
        shake_check::<136, 512>(hacspec_sha3::shake256::<512>);
    }
}
