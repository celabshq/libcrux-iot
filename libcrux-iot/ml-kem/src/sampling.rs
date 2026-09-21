use libcrux_secrets::{CastOps as _, Classify as _, I16, U32, U8};

use crate::{
    constants::COEFFICIENTS_IN_RING_ELEMENT, hash_functions::*, helper::cloop, vector::Operations,
};

/// If `bytes` contains a set of uniformly random bytes, this function
/// uniformly samples a ring element `â` that is treated as being the NTT representation
/// of the corresponding polynomial `a`.
///
/// Since rejection sampling is used, it is possible the supplied bytes are
/// not enough to sample the element, in which case an `Err` is returned and the
/// caller must try again with a fresh set of bytes.
///
/// This function <strong>partially</strong> implements <strong>Algorithm 6</strong> of the NIST FIPS 203 standard,
/// We say "partially" because this implementation only accepts a finite set of
/// bytes as input and returns an error if the set is not enough; Algorithm 6 of
/// the FIPS 203 standard on the other hand samples from an infinite stream of bytes
/// until the ring element is filled. Algorithm 6 is reproduced below:
///
/// ```plaintext
/// Input: byte stream B ∈ 𝔹*.
/// Output: array â ∈ ℤ₂₅₆.
///
/// i ← 0
/// j ← 0
/// while j < 256 do
///     d₁ ← B[i] + 256·(B[i+1] mod 16)
///     d₂ ← ⌊B[i+1]/16⌋ + 16·B[i+2]
///     if d₁ < q then
///         â[j] ← d₁
///         j ← j + 1
///     end if
///     if d₂ < q and j < 256 then
///         â[j] ← d₂
///         j ← j + 1
///     end if
///     i ← i + 3
/// end while
/// return â
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[hax_lib::requires(
    randomness.len() == K &&
    sampled_coefficients.len() == K &&
    out.len() == K
)]
#[hax_lib::ensures(|_|
    future(sampled_coefficients).len() == sampled_coefficients.len() &&
    future(out).len() == out.len()
)]
#[inline(always)]
// We only use this to sample entries of the public matrix A, from the public seeds.
fn sample_from_uniform_distribution_next<Vector: Operations, const K: usize, const N: usize>(
    randomness: &[[u8; N]],
    sampled_coefficients: &mut [usize],
    out: &mut [[i16; 272]],
) -> bool {
    // Would be great to trigger auto-vectorization or at least loop unrolling here
    for i in 0..K {
        hax_lib::loop_invariant!(|_: usize| sampled_coefficients.len() == K && out.len() == K);
        for r in 0..N / 24 {
            hax_lib::loop_invariant!(|_: usize| sampled_coefficients.len() == K && out.len() == K);
            if sampled_coefficients[i] < COEFFICIENTS_IN_RING_ELEMENT {
                #[cfg(eurydice)]
                {
                    // XXX: We need to use these temporaries to work around a Eurydice
                    //      bug. (see https://github.com/AeneasVerif/eurydice/issues/285)
                    let randomness_i = &randomness[i];
                    let out_i = &mut out[i];
                    let sampled_coefficients_i = sampled_coefficients[i];

                    let sampled = Vector::rej_sample(
                        &randomness_i[r * 24..(r * 24) + 24],
                        &mut out_i[sampled_coefficients_i..sampled_coefficients_i + 16],
                    );
                    sampled_coefficients[i] = sampled_coefficients[i].wrapping_add(sampled);
                }
                #[cfg(not(eurydice))]
                {
                    let sampled = Vector::rej_sample(
                        &randomness[i][r * 24..(r * 24) + 24],
                        &mut out[i][sampled_coefficients[i]..sampled_coefficients[i] + 16],
                    );
                    sampled_coefficients[i] = sampled_coefficients[i].wrapping_add(sampled);
                }
            }
        }
    }
    let mut done = true;
    for i in 0..K {
        hax_lib::loop_invariant!(|_: usize| sampled_coefficients.len() == K);
        if sampled_coefficients[i] >= COEFFICIENTS_IN_RING_ELEMENT {
            sampled_coefficients[i] = COEFFICIENTS_IN_RING_ELEMENT;
        } else {
            done = false
        }
    }
    done
}

// XXX: The `while` loop here does not allow us to prove panic freedom, at the moment.
#[hax_lib::fstar::verification_status(lax)]
#[hax_lib::requires(sampled_coefficients.len() == K && out.len() == K)]
#[hax_lib::ensures(|_| future(sampled_coefficients).len() == K && future(out).len() == K)]
// We only use this to sample entries of the public matrix A, from the public seeds.
#[inline(always)]
pub(super) fn sample_from_xof<const K: usize, Vector: Operations, Hasher: Hash>(
    seeds: &[[u8; 34]],
    sampled_coefficients: &mut [usize],
    out: &mut [[i16; 272]],
) {
    let mut xof_state = Hasher::shake128_init_absorb_final(seeds);
    let mut randomness = [[0u8; THREE_BLOCKS]; K];
    let mut randomness_blocksize = [[0u8; BLOCK_SIZE]; K];
    xof_state.shake128_squeeze_first_three_blocks(&mut randomness);

    let mut done = sample_from_uniform_distribution_next::<Vector, K, THREE_BLOCKS>(
        &randomness,
        sampled_coefficients,
        out,
    );

    // Requiring more than 5 blocks to sample a ring element should be very
    // unlikely according to:
    // https://eprint.iacr.org/2023/708.pdf
    // To avoid failing here, we squeeze more blocks out of the state until
    // we have enough.
    while !done {
        hax_lib::loop_invariant!(|_: usize| randomness_blocksize.len() == K
            && sampled_coefficients.len() == K
            && out.len() == K);
        xof_state.shake128_squeeze_next_block(&mut randomness_blocksize);
        done = sample_from_uniform_distribution_next::<Vector, K, BLOCK_SIZE>(
            &randomness_blocksize,
            sampled_coefficients,
            out,
        );
    }
}

/// Given a series of uniformly random bytes in `randomness`, for some number `eta`,
/// the `sample_from_binomial_distribution_{eta}` functions sample
/// a ring element from a binomial distribution centered at 0 that uses two sets
/// of `eta` coin flips. If, for example,
/// `eta = ETA`, each ring coefficient is a value `v` such
/// such that `v ∈ {-ETA, -ETA + 1, ..., 0, ..., ETA + 1, ETA}` and:
///
/// ```plaintext
/// - If v < 0, Pr[v] = Pr[-v]
/// - If v >= 0, Pr[v] = BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2 ^ (2 * ETA)
/// ```
///
/// The values `v < 0` are mapped to the appropriate `KyberFieldElement`.
///
/// The expected value is:
///
/// ```plaintext
/// E[X] = (-ETA)Pr[-ETA] + (-(ETA - 1))Pr[-(ETA - 1)] + ... + (ETA - 1)Pr[ETA - 1] + (ETA)Pr[ETA]
///      = 0 since Pr[-v] = Pr[v] when v < 0.
/// ```
///
/// And the variance is:
///
/// ```plaintext
/// Var(X) = E[(X - E[X])^2]
///        = E[X^2]
///        = sum_(v=-ETA to ETA)v^2 * (BINOMIAL_COEFFICIENT(2 * ETA; ETA - v) / 2^(2 * ETA))
///        = ETA / 2
/// ```
///
/// This function implements <strong>Algorithm 7</strong> of the NIST FIPS 203 standard, which is
/// reproduced below:
///
/// ```plaintext
/// Input: byte array B ∈ 𝔹^{64η}.
/// Output: array f ∈ ℤ₂₅₆.
///
/// b ← BytesToBits(B)
/// for (i ← 0; i < 256; i++)
///     x ← ∑(j=0 to η - 1) b[2iη + j]
///     y ← ∑(j=0 to η - 1) b[2iη + η + j]
///     f[i] ← x−y mod q
/// end for
/// return f
/// ```
///
/// The NIST FIPS 203 standard can be found at
/// <https://csrc.nist.gov/pubs/fips/203/ipd>.
#[hax_lib::requires(randomness.len() == 128)]
#[inline(always)]
fn sample_from_binomial_distribution_2<Vector: Operations>(
    randomness: &[U8],
    sampled_i16s: &mut [I16; 256],
) {
    cloop! {
        for (chunk_number, byte_chunk) in randomness.chunks_exact(4).enumerate() {
            let random_bits_as_u32: U32 = (byte_chunk[0].as_u32())
                | (byte_chunk[1].as_u32()) << 8
                | (byte_chunk[2].as_u32()) << 16
                | (byte_chunk[3].as_u32()) << 24;

            let even_bits = random_bits_as_u32 & 0x55555555.classify();
            let odd_bits = (random_bits_as_u32 >> 1) & 0x55555555.classify();

            let coin_toss_outcomes = even_bits.wrapping_add(odd_bits);

            cloop! {
                for outcome_set in (0..32u32).step_by(4) { // u32::BITS
                    let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x3.classify()).as_i16();
                    let outcome_2 = ((coin_toss_outcomes >> (outcome_set.wrapping_add(2))) & 0x3.classify()).as_i16();

                    let offset = (outcome_set >> 2) as usize;
                    sampled_i16s[8 * chunk_number + offset] = outcome_1.wrapping_sub(outcome_2);
                }
            }
        }
    }
}

#[hax_lib::requires(randomness.len() == 3 * 64)]
#[inline(always)]
fn sample_from_binomial_distribution_3<Vector: Operations>(
    randomness: &[U8],
    sampled_i16s: &mut [I16; 256],
) {
    cloop! {
        for (chunk_number, byte_chunk) in randomness.chunks_exact(3).enumerate() {
            let random_bits_as_u24: U32 =
            (byte_chunk[0].as_u32()) | (byte_chunk[1].as_u32()) << 8 | (byte_chunk[2].as_u32()) << 16;

            let first_bits = random_bits_as_u24 & 0x00249249.classify();
            let second_bits = (random_bits_as_u24 >> 1) & 0x00249249.classify();
            let third_bits = (random_bits_as_u24 >> 2) & 0x00249249.classify();

            let coin_toss_outcomes = first_bits.wrapping_add(second_bits.wrapping_add(third_bits));

            cloop! {
                for outcome_set in (0u8..24).step_by(6) {
                    let outcome_1 = ((coin_toss_outcomes >> outcome_set) & 0x7.classify()).as_i16();
                    let outcome_2 = ((coin_toss_outcomes >> (outcome_set.wrapping_add(3))) & 0x7.classify()).as_i16();

                    let offset = (outcome_set / 6) as usize;
                    sampled_i16s[4 * chunk_number + offset] = outcome_1.wrapping_sub(outcome_2);
                }
            }
        }
    }
}

#[hax_lib::requires((ETA == 2 || ETA == 3) && randomness.len() == ETA * 64)]
#[inline(always)]
pub(super) fn sample_from_binomial_distribution<const ETA: usize, Vector: Operations>(
    randomness: &[U8],
    output: &mut [I16; 256],
) {
    match ETA as u32 {
        2 => sample_from_binomial_distribution_2::<Vector>(randomness, output),
        3 => sample_from_binomial_distribution_3::<Vector>(randomness, output),
        _ => unreachable!(),
    };
}
