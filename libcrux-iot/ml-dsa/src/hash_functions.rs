#![allow(non_snake_case)]

/// Abstraction and platform multiplexing for SHAKE 256
pub(crate) mod shake256 {
    use libcrux_secrets::U8;

    pub(crate) const BLOCK_SIZE: usize = 136;

    /// An ML-DSA specific Xof trait
    /// This trait is not actually a full Xof implementation but opererates only
    /// on multiple of blocks. The only real Xof API for SHAKE256 is [`Xof`].
    #[hax_lib::attributes]
    pub(crate) trait DsaXof {
        #[hax_lib::requires(out.len() <= u32::MAX as usize)]
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[U8], out: &mut [U8; OUTPUT_LENGTH]);
        #[hax_lib::requires(input.len() < 136)]
        fn init_absorb_final(input: &[U8]) -> Self;
        // TODO: There should only be a `squeeze_block`
        #[hax_lib::requires(true)]
        fn squeeze_first_block(&mut self) -> [U8; BLOCK_SIZE];
        #[hax_lib::requires(true)]
        fn squeeze_next_block(&mut self) -> [U8; BLOCK_SIZE];
    }

    #[hax_lib::attributes]
    pub(crate) trait XofX4 {
        #[hax_lib::requires(
        input0.len() < 136
        && input1.len() < 136
        && input2.len() < 136
        && input3.len() < 136
    )]

        fn init_absorb_x4(input0: &[U8], input1: &[U8], input2: &[U8], input3: &[U8]) -> Self;
        #[hax_lib::requires(true)]
        fn squeeze_first_block_x4(
            &mut self,
        ) -> (
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
        );
        #[hax_lib::requires(true)]
        fn squeeze_next_block_x4(
            &mut self,
        ) -> (
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
        );
        #[hax_lib::requires(
            out0.len() <= u32::MAX as usize
            &&  out1.len() <= u32::MAX as usize
            &&  out2.len() <= u32::MAX as usize
            &&  out3.len() <= u32::MAX as usize
             )]
        fn shake256_x4<const OUT_LEN: usize>(
            input0: &[U8],
            input1: &[U8],
            input2: &[U8],
            input3: &[U8],
            out0: &mut [U8; OUT_LEN],
            out1: &mut [U8; OUT_LEN],
            out2: &mut [U8; OUT_LEN],
            out3: &mut [U8; OUT_LEN],
        );
    }

    /// A generic Xof trait
    #[hax_lib::attributes]
    pub(crate) trait Xof {
        /// Initialize the state
        #[hax_lib::requires(true)]
        fn init() -> Self;

        /// Absorb
        // #[hax_lib::requires(self.state.buf_len < 136)]
        fn absorb(&mut self, input: &[U8]);

        /// Absorb final input
        // #[hax_lib::requires(self.state.buf_len < 136)]
        fn absorb_final(&mut self, input: &[U8]);

        /// Squeeze output bytes
        #[hax_lib::requires(true)]
        fn squeeze(&mut self, out: &mut [U8]);
    }
}

/// Abstraction and platform multiplexing for SHAKE 128
pub(crate) mod shake128 {
    use libcrux_secrets::U8;

    pub(crate) const BLOCK_SIZE: usize = 168;
    pub(crate) const FIVE_BLOCKS_SIZE: usize = BLOCK_SIZE * 5;

    #[hax_lib::attributes]
    pub(crate) trait Xof {
        #[hax_lib::requires(out.len() <= u32::MAX as usize)]
        #[hax_lib::ensures(|_| future(out).len() == out.len())]
        fn shake128(input: &[U8], out: &mut [U8]);
    }

    /// When sampling matrix A we always want to do 4 absorb/squeeze calls in
    /// parallel.
    #[hax_lib::attributes]
    pub(crate) trait XofX4 {
        #[hax_lib::requires(
        input0.len() < 168
        && input1.len() < 168
        && input2.len() < 168
        && input3.len() < 168
    )]
        fn init_absorb(input0: &[U8], input1: &[U8], input2: &[U8], input3: &[U8]) -> Self;
        #[hax_lib::requires(true)]
        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [U8; FIVE_BLOCKS_SIZE],
            out1: &mut [U8; FIVE_BLOCKS_SIZE],
            out2: &mut [U8; FIVE_BLOCKS_SIZE],
            out3: &mut [U8; FIVE_BLOCKS_SIZE],
        );
        #[hax_lib::requires(true)]
        fn squeeze_next_block(
            &mut self,
        ) -> (
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
            [U8; BLOCK_SIZE],
        );
    }
}

/// A portable implementation of [`shake128::Xof`] and [`shake256::Xof`].
pub(crate) mod portable {
    use libcrux_iot_sha3::incremental::{self, UnbufferedXofState, Xof};
    use libcrux_secrets::{Classify as _, U8};

    use super::{shake128, shake256};

    /// Portable SHAKE 128 x4 state.
    ///
    /// We're using a portable implementation so this is actually sequential.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Shake128X4 {
        state0: UnbufferedXofState,
        state1: UnbufferedXofState,
        state2: UnbufferedXofState,
        state3: UnbufferedXofState,
    }

    #[inline(always)]
    #[hax_lib::requires(
        input0.len() < 168
        && input1.len() < 168
        && input2.len() < 168
        && input3.len() < 168
    )]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake128_init_absorb_x4(
        input0: &[U8],
        input1: &[U8],
        input2: &[U8],
        input3: &[U8],
    ) -> Shake128X4 {
        let mut state0 = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state0, input0);

        let mut state1 = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state1, input1);

        let mut state2 = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state2, input2);

        let mut state3 = incremental::shake128_init();
        incremental::shake128_absorb_final(&mut state3, input3);

        Shake128X4 {
            state0,
            state1,
            state2,
            state3,
        }
    }

    #[hax_lib::attributes]
    impl Shake128 {
        #[inline(always)]
        #[hax_lib::requires(input.len() < 168)]
        #[cfg_attr(hax, hax_lib::opaque)]
        pub(crate) fn shake128_init_absorb(input: &[U8]) -> Self {
            let mut state = incremental::shake128_init();
            incremental::shake128_absorb_final(&mut state, input);

            Shake128 { state }
        }

        #[inline(always)]
        #[cfg_attr(hax, hax_lib::opaque)]
        pub(crate) fn shake128_squeeze_first_five_blocks(
            &mut self,
            out: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            incremental::shake128_squeeze_first_five_blocks(&mut self.state, out);
        }

        #[inline(always)]
        #[cfg_attr(hax, hax_lib::opaque)]
        pub(crate) fn shake128_squeeze_next_block(&mut self, out: &mut [U8; shake128::BLOCK_SIZE]) {
            incremental::shake128_squeeze_next_block(&mut self.state, out);
        }
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake128_squeeze_first_five_blocks_x4(
        state: &mut Shake128X4,
        out0: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
        out1: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
        out2: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
        out3: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
    ) {
        incremental::shake128_squeeze_first_five_blocks(&mut state.state0, out0);
        incremental::shake128_squeeze_first_five_blocks(&mut state.state1, out1);
        incremental::shake128_squeeze_first_five_blocks(&mut state.state2, out2);
        incremental::shake128_squeeze_first_five_blocks(&mut state.state3, out3);
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake128_squeeze_next_block_x4(
        state: &mut Shake128X4,
    ) -> (
        [U8; shake128::BLOCK_SIZE],
        [U8; shake128::BLOCK_SIZE],
        [U8; shake128::BLOCK_SIZE],
        [U8; shake128::BLOCK_SIZE],
    ) {
        let mut out0 = [0u8.classify(); shake128::BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(&mut state.state0, &mut out0);
        let mut out1 = [0u8.classify(); shake128::BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(&mut state.state1, &mut out1);
        let mut out2 = [0u8.classify(); shake128::BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(&mut state.state2, &mut out2);
        let mut out3 = [0u8.classify(); shake128::BLOCK_SIZE];
        incremental::shake128_squeeze_next_block(&mut state.state3, &mut out3);

        (out0, out1, out2, out3)
    }

    #[hax_lib::attributes]
    impl shake128::XofX4 for Shake128X4 {
        #[inline(always)]
        #[hax_lib::requires(
        input0.len() < 168
        && input1.len() < 168
        && input2.len() < 168
        && input3.len() < 168
    )]
        fn init_absorb(input0: &[U8], input1: &[U8], input2: &[U8], input3: &[U8]) -> Self {
            shake128_init_absorb_x4(input0, input1, input2, input3)
        }

        #[inline(always)]
        fn squeeze_first_five_blocks(
            &mut self,
            out0: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
            out1: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
            out2: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
            out3: &mut [U8; shake128::FIVE_BLOCKS_SIZE],
        ) {
            shake128_squeeze_first_five_blocks_x4(self, out0, out1, out2, out3);
        }

        #[inline(always)]
        fn squeeze_next_block(
            &mut self,
        ) -> (
            [U8; shake128::BLOCK_SIZE],
            [U8; shake128::BLOCK_SIZE],
            [U8; shake128::BLOCK_SIZE],
            [U8; shake128::BLOCK_SIZE],
        ) {
            shake128_squeeze_next_block_x4(self)
        }
    }

    /// Portable SHAKE 128 state
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Shake128 {
        state: UnbufferedXofState,
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    #[hax_lib::requires(out.len() <= u32::MAX as usize)]
    fn shake128(input: &[U8], out: &mut [U8]) {
        libcrux_iot_sha3::shake128_ema(out, input);
    }

    #[hax_lib::attributes]
    impl shake128::Xof for Shake128 {
        #[inline(always)]
        #[hax_lib::requires(out.len() <= u32::MAX as usize)]
        fn shake128(input: &[U8], out: &mut [U8]) {
            shake128(input, out);
        }
    }

    /// Portable SHAKE 256 state
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Shake256 {
        state: UnbufferedXofState,
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    #[hax_lib::requires(out.len() <= u32::MAX as usize)]
    fn shake256<const OUTPUT_LENGTH: usize>(input: &[U8], out: &mut [U8; OUTPUT_LENGTH]) {
        libcrux_iot_sha3::shake256_ema(out, input);
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    #[hax_lib::requires(input.len() < 136)]
    fn init_absorb_final_shake256(input: &[U8]) -> Shake256 {
        let mut state = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state, input);
        Shake256 { state }
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn squeeze_first_block_shake256(state: &mut Shake256) -> [U8; shake256::BLOCK_SIZE] {
        let mut out = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(&mut state.state, &mut out);
        out
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn squeeze_next_block_shake256(state: &mut Shake256) -> [U8; shake256::BLOCK_SIZE] {
        let mut out = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(&mut state.state, &mut out);
        out
    }

    #[hax_lib::attributes]
    impl shake256::DsaXof for Shake256 {
        #[inline(always)]
        #[hax_lib::requires(out.len() <= u32::MAX as usize)]
        fn shake256<const OUTPUT_LENGTH: usize>(input: &[U8], out: &mut [U8; OUTPUT_LENGTH]) {
            shake256(input, out);
        }

        #[inline(always)]
        #[hax_lib::requires(input.len() < 136)]
        fn init_absorb_final(input: &[U8]) -> Self {
            init_absorb_final_shake256(input)
        }

        #[inline(always)]
        fn squeeze_first_block(&mut self) -> [U8; shake256::BLOCK_SIZE] {
            squeeze_first_block_shake256(self)
        }

        #[inline(always)]
        fn squeeze_next_block(&mut self) -> [U8; shake256::BLOCK_SIZE] {
            squeeze_next_block_shake256(self)
        }
    }

    /// Portable SHAKE 256 x4 state.
    ///
    /// We're using a portable implementation so this is actually sequential.
    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Shake256X4 {
        state0: incremental::UnbufferedXofState,
        state1: incremental::UnbufferedXofState,
        state2: incremental::UnbufferedXofState,
        state3: incremental::UnbufferedXofState,
    }

    #[inline(always)]
    #[hax_lib::requires(
        input0.len() < 136
        && input1.len() < 136
        && input2.len() < 136
        && input3.len() < 136
    )]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake256_init_absorb_x4(
        input0: &[U8],
        input1: &[U8],
        input2: &[U8],
        input3: &[U8],
    ) -> Shake256X4 {
        let mut state0 = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state0, input0);

        let mut state1 = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state1, input1);

        let mut state2 = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state2, input2);

        let mut state3 = incremental::shake256_init();
        incremental::shake256_absorb_final(&mut state3, input3);

        Shake256X4 {
            state0,
            state1,
            state2,
            state3,
        }
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake256_squeeze_first_block_x4(
        state: &mut Shake256X4,
    ) -> (
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
    ) {
        let mut out0 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(&mut state.state0, &mut out0);
        let mut out1 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(&mut state.state1, &mut out1);
        let mut out2 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(&mut state.state2, &mut out2);
        let mut out3 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_first_block(&mut state.state3, &mut out3);

        (out0, out1, out2, out3)
    }

    #[inline(always)]
    #[cfg_attr(hax, hax_lib::opaque)]
    fn shake256_squeeze_next_block_x4(
        state: &mut Shake256X4,
    ) -> (
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
        [U8; shake256::BLOCK_SIZE],
    ) {
        let mut out0 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(&mut state.state0, &mut out0);
        let mut out1 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(&mut state.state1, &mut out1);
        let mut out2 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(&mut state.state2, &mut out2);
        let mut out3 = [0u8.classify(); shake256::BLOCK_SIZE];
        incremental::shake256_squeeze_next_block(&mut state.state3, &mut out3);

        (out0, out1, out2, out3)
    }

    #[hax_lib::attributes]
    impl shake256::XofX4 for Shake256X4 {
        #[inline(always)]
        #[hax_lib::requires(
        input0.len() < 136
        && input1.len() < 136
        && input2.len() < 136
        && input3.len() < 136
    )]
        fn init_absorb_x4(input0: &[U8], input1: &[U8], input2: &[U8], input3: &[U8]) -> Self {
            shake256_init_absorb_x4(input0, input1, input2, input3)
        }

        #[inline(always)]
        fn squeeze_first_block_x4(
            &mut self,
        ) -> (
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
        ) {
            shake256_squeeze_first_block_x4(self)
        }

        #[inline(always)]
        fn squeeze_next_block_x4(
            &mut self,
        ) -> (
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
            [U8; shake256::BLOCK_SIZE],
        ) {
            shake256_squeeze_next_block_x4(self)
        }

        #[inline(always)]
        #[hax_lib::requires(
            out0.len() <= u32::MAX as usize
            &&  out1.len() <= u32::MAX as usize
            &&  out2.len() <= u32::MAX as usize
            &&  out3.len() <= u32::MAX as usize
             )]
        fn shake256_x4<const OUT_LEN: usize>(
            input0: &[U8],
            input1: &[U8],
            input2: &[U8],
            input3: &[U8],
            out0: &mut [U8; OUT_LEN],
            out1: &mut [U8; OUT_LEN],
            out2: &mut [U8; OUT_LEN],
            out3: &mut [U8; OUT_LEN],
        ) {
            shake256(input0, out0);
            shake256(input1, out1);
            shake256(input2, out2);
            shake256(input3, out3);
        }
    }

    #[cfg_attr(hax, hax_lib::opaque)]
    pub(crate) struct Shake256Xof {
        state: incremental::Shake256Xof,
    }

    #[hax_lib::attributes]
    // There may be an issue here in that the pre-conditions make reference to `self.buf_len` for the Keccak state, which is not something the callers here can control.
    impl shake256::Xof for Shake256Xof {
        #[cfg_attr(hax, hax_lib::opaque)]
        fn init() -> Self {
            Shake256Xof {
                state: incremental::Shake256Xof::new(),
            }
        }

        // #[hax_lib::requires(
        //     self.state.buf_len < 136
        // )]
        #[cfg_attr(hax, hax_lib::opaque)]
        fn absorb(&mut self, input: &[U8]) {
            self.state.absorb(input);
        }

        // #[hax_lib::requires(self.state.buf_len < 136)]
        #[cfg_attr(hax, hax_lib::opaque)]
        fn absorb_final(&mut self, input: &[U8]) {
            self.state.absorb_final(input);
        }
        #[cfg_attr(hax, hax_lib::opaque)]
        fn squeeze(&mut self, out: &mut [U8]) {
            self.state.squeeze(out)
        }
    }
}
