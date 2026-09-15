// SPDX-License-Identifier: MIT OR Apache-2.0
// SPDX-FileCopyrightText: Inria-AIO, Cryspen, and Christian Amsüss
#![no_std]
#![no_main]

use defmt_rtt as _;
use embedded_alloc::LlffHeap as Heap;
use embedded_cal::plumbing::ec::P256;
use embedded_cal_stm32wba55::Stm32wba55Cal;
use hexlit::hex;
use panic_probe as _;

// XXX: `libcrux-iot-p256` still depends on a version of `libcrux-hacl-rs`
// that needs a global allocator.
#[global_allocator]
static HEAP: Heap = Heap::empty();

struct TestState {
    board_cal: Stm32wba55Cal,
}

#[defmt_test::tests]
mod tests {
    use embedded_cal::plumbing::ec::Ec;

    use super::*;

    #[init]
    fn init() -> super::TestState {
        let board_cal = embedded_cal_stm32wba55::Stm32wba55Cal::new(
            stm32_metapac::HASH,
            stm32_metapac::RCC,
            stm32_metapac::RNG,
            stm32_metapac::AES,
            stm32_metapac::PKA,
        );

        super::TestState { board_cal }
    }

    #[test]
    fn test_ecc_p256(state: &mut super::TestState) {
        let ec = state.board_cal.p256();

        for v in RFC5903_P256 {
            v.test_with(ec);
        }
    }
}

pub struct EccVector {
    // extend as needed
    ecdh_curve: i8,
    alice_private: &'static [u8],
    alice_public: &'static [u8],
    bob_private: &'static [u8],
    bob_public: &'static [u8],
    shared_secret: &'static [u8],
}

impl EccVector {
    /// Runs the test vector by the Cal implementation.
    ///
    /// Panics if either the algorithm is not supported, or either direction of running DH does not
    /// result in the expected shared secret.
    pub fn test_with<C: embedded_cal::plumbing::ec::EcPrimitives<P256>>(&self, ec: &mut C) {
        let mut alice_public_computed = [0u8; 64];
        assert!(libcrux_iot_p256::embedded_cal_integration::dh_initiator_ec(
            ec,
            &mut alice_public_computed,
            self.alice_private
        ));
        assert_eq!(self.alice_public, alice_public_computed.as_ref());

        let mut bob_public_computed = [0u8; 64];
        assert!(libcrux_iot_p256::embedded_cal_integration::dh_initiator_ec(
            ec,
            &mut bob_public_computed,
            self.bob_private
        ));
        assert_eq!(self.bob_public, bob_public_computed.as_ref());

        let mut alice_shared_secret = [0u8; 32];
        assert!(libcrux_iot_p256::embedded_cal_integration::dh_responder_ec(
            ec,
            &mut alice_shared_secret,
            self.bob_public,
            self.alice_private,
        ));
        assert_eq!(alice_shared_secret, self.shared_secret.as_ref());

        let mut bob_shared_secret = [0u8; 32];
        assert!(libcrux_iot_p256::embedded_cal_integration::dh_responder_ec(
            ec,
            &mut bob_shared_secret,
            self.alice_public,
            self.bob_private,
        ));
        assert_eq!(bob_shared_secret, self.shared_secret.as_ref());
    }
}

pub const RFC5903_P256: &[EccVector] = &[EccVector {
    ecdh_curve: 1,
    // "initiator"
    alice_private: &hex!("C88F01F5 10D9AC3F 70A292DA A2316DE5 44E9AAB8 AFE84049 C62A9C57 862D1433"),
    alice_public: &hex!("DAD0B653 94221CF9 B051E1FE CA5787D0 98DFE637 FC90B9EF 945D0C37 72581180"),
    // "responder"
    bob_private: &hex!("C6EF9C5D 78AE012A 011164AC B397CE20 88685D8F 06BF9BE0 B283AB46 476BEE53"),
    bob_public: &hex!("D12DFB52 89C8D4F8 1208B702 70398C34 2296970A 0BCCB74C 736FC755 4494BF63"),
    shared_secret: &hex!("D6840F6B 42F6EDAF D13116E0 E1256520 2FEF8E9E CE7DCE03 812464D0 4B9442DE"),
}];
