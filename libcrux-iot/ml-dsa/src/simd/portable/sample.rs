use libcrux_secrets::{CastOps as _, Classify as _, Declassify as _, I32, U8};

use crate::constants::FIELD_MODULUS;

#[inline(always)]
#[hax_lib::requires(randomness.len() / 3 <= 4_294_967_295 && out.len() >= randomness.len() / 3)]
#[hax_lib::ensures(|_| out.len() == future(out).len())]
pub fn rejection_sample_less_than_field_modulus(randomness: &[u8], out: &mut [i32]) -> usize {
    let mut sampled = 0;

    #[cfg(hax)]
    let _out_len = out.len();

    for i in 0..randomness.len() / 3 {
        hax_lib::loop_invariant!(|k: usize| sampled <= k && out.len() == _out_len);
        let b0 = randomness[i * 3 + 0] as i32;
        let b1 = randomness[i * 3 + 1] as i32;
        let b2 = randomness[i * 3 + 2] as i32;

        let coefficient = ((b2 << 16) | (b1 << 8) | b0) & 0x00_7F_FF_FF;

        if coefficient < FIELD_MODULUS {
            out[sampled] = coefficient;
            sampled += 1;
        }
    }

    sampled
}

#[inline(always)]
#[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
#[hax_lib::ensures(|_| out.len() == future(out).len())]
pub fn rejection_sample_less_than_eta_equals_2(randomness: &[U8], out: &mut [I32]) -> usize {
    let mut sampled = 0;

    #[cfg(hax)]
    let _out_len = out.len();

    for i in 0..randomness.len() {
        hax_lib::loop_invariant!(|k: usize| sampled <= 2 * k && out.len() == _out_len);
        let try_0 = randomness[i] & 0xF;
        let try_1 = randomness[i] >> 4;

        // Declassification: This may leak the index of the
        // coefficient being sampled, which is safe to do
        // according to the NIST submission.
        // (cf. Section 5.5 in https://pq-crystals.org/dilithium/data/dilithium-specification-round3-20210208.pdf)
        if try_0.declassify() < 15 {
            let try_0 = try_0.as_i32();

            // (try_0 * 26) >> 7 computes ⌊try_0 / 5⌋
            let try_0_mod_5 = try_0 - ((try_0 * 26) >> 7) * 5;

            out[sampled] = 2.classify() - try_0_mod_5;

            sampled += 1;
        }
        // Declassification: This may leak the index of the
        // coefficient being sampled, which is safe to do
        // according to the NIST submission.
        // (cf. Section 5.5 in https://pq-crystals.org/dilithium/data/dilithium-specification-round3-20210208.pdf)
        if try_1.declassify() < 15 {
            let try_1 = try_1.as_i32();
            let try_1_mod_5 = try_1 - ((try_1 * 26) >> 7) * 5;

            out[sampled] = 2.classify() - try_1_mod_5;

            sampled += 1;
        }
    }

    sampled
}

#[inline(always)]
#[hax_lib::requires(randomness.len() <= 4_294_967_295 / 2 && randomness.len() * 2 <= out.len())]
#[hax_lib::ensures(|_| out.len() == future(out).len())]
pub fn rejection_sample_less_than_eta_equals_4(randomness: &[U8], out: &mut [I32]) -> usize {
    let mut sampled = 0;

    #[cfg(hax)]
    let _out_len = out.len();

    for i in 0..randomness.len() {
        hax_lib::loop_invariant!(|k: usize| sampled <= 2 * k && out.len() == _out_len);
        let try_0 = randomness[i] & 0xF;
        let try_1 = randomness[i] >> 4;

        // Declassification: This may leak the index of the
        // coefficient being sampled, which is safe to do
        // according to the NIST submission.
        // (cf. Section 5.5 in https://pq-crystals.org/dilithium/data/dilithium-specification-round3-20210208.pdf)
        if try_0.declassify() < 9 {
            out[sampled] = 4.classify() - (try_0.as_i32());
            sampled += 1;
        }

        // Declassification: This may leak the index of the
        // coefficient being sampled, which is safe to do
        // according to the NIST submission.
        // (cf. Section 5.5 in https://pq-crystals.org/dilithium/data/dilithium-specification-round3-20210208.pdf)
        if try_1.declassify() < 9 {
            out[sampled] = 4.classify() - (try_1.as_i32());
            sampled += 1;
        }
    }

    sampled
}
