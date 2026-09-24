//! The FIPS-202 Keccak-f[1600] permutation as Verus specification functions.
//!
//! This mirrors `hacspec_sha3::keccak_f` one step mapping at a time: the state
//! is 25 lanes of 64 bits, lane `A[x, y]` living at flat index `5*y + x`
//! (FIPS 202 §3.1.2). Verus cannot call the hacspec's `exec` functions from a
//! specification, so the definitions are restated here; keeping them in the
//! same shape as the hacspec is what makes the correspondence checkable by
//! reading the two side by side.

use vstd::prelude::*;

use super::lane_bridge::rotl64;

verus! {

/// Round constants `RC[ir]`, `ir = 0..23` -- FIPS 202, Algorithm 5.
pub open spec fn round_constant(round: int) -> u64 {
    seq![
        0x0000_0000_0000_0001u64, 0x0000_0000_0000_8082u64, 0x8000_0000_0000_808Au64,
        0x8000_0000_8000_8000u64, 0x0000_0000_0000_808Bu64, 0x0000_0000_8000_0001u64,
        0x8000_0000_8000_8081u64, 0x8000_0000_0000_8009u64, 0x0000_0000_0000_008Au64,
        0x0000_0000_0000_0088u64, 0x0000_0000_8000_8009u64, 0x0000_0000_8000_000Au64,
        0x0000_0000_8000_808Bu64, 0x8000_0000_0000_008Bu64, 0x8000_0000_0000_8089u64,
        0x8000_0000_0000_8003u64, 0x8000_0000_0000_8002u64, 0x8000_0000_0000_0080u64,
        0x0000_0000_0000_800Au64, 0x8000_0000_8000_000Au64, 0x8000_0000_8000_8081u64,
        0x8000_0000_0000_8080u64, 0x0000_0000_8000_0001u64, 0x8000_0000_8000_8008u64,
    ][round]
}

/// Rotation offsets for the rho step, indexed as `RHO_OFFSETS[5*y + x]`
/// -- FIPS 202, Table 2, already reduced modulo the 64-bit lane size.
pub open spec fn rho_offset(idx: int) -> u64 {
    seq![
        0u64, 1u64, 62u64, 28u64, 27u64,
        36u64, 44u64, 6u64, 55u64, 20u64,
        3u64, 10u64, 43u64, 25u64, 39u64,
        41u64, 45u64, 15u64, 21u64, 8u64,
        18u64, 2u64, 61u64, 56u64, 14u64,
    ][idx]
}

/// A well-formed state: 25 lanes.
pub open spec fn wf_state(state: Seq<u64>) -> bool {
    state.len() == 25
}

/// Lane `A[x, y]`.
pub open spec fn get(state: Seq<u64>, x: int, y: int) -> u64 {
    state[5 * y + x]
}

/// `C[x] = A[x,0] ^ A[x,1] ^ A[x,2] ^ A[x,3] ^ A[x,4]` -- FIPS 202, Algorithm 1.
pub open spec fn theta_c(state: Seq<u64>, x: int) -> u64 {
    get(state, x, 0) ^ get(state, x, 1) ^ get(state, x, 2) ^ get(state, x, 3) ^ get(state, x, 4)
}

/// `D[x] = C[x-1 mod 5] ^ rot(C[x+1 mod 5], 1)` -- FIPS 202, Algorithm 1.
pub open spec fn theta_d(state: Seq<u64>, x: int) -> u64 {
    theta_c(state, (x + 4) % 5) ^ rotl64(theta_c(state, (x + 1) % 5), 1)
}

/// theta -- FIPS 202, Algorithm 1.
pub open spec fn theta(state: Seq<u64>) -> Seq<u64> {
    Seq::new(25, |idx: int| state[idx] ^ theta_d(state, idx % 5))
}

/// rho -- FIPS 202, Algorithm 2.
pub open spec fn rho(state: Seq<u64>) -> Seq<u64> {
    Seq::new(25, |idx: int| rotl64(state[idx], rho_offset(idx)))
}

/// pi: `A'[x,y] = A[(x + 3y) mod 5, x]` -- FIPS 202, Algorithm 3.
pub open spec fn pi(state: Seq<u64>) -> Seq<u64> {
    Seq::new(25, |idx: int| get(state, (idx % 5 + 3 * (idx / 5)) % 5, idx % 5))
}

/// chi: `A'[x,y] = A[x,y] ^ ((!A[x+1,y]) & A[x+2,y])` -- FIPS 202, Algorithm 4.
pub open spec fn chi(state: Seq<u64>) -> Seq<u64> {
    Seq::new(
        25,
        |idx: int|
            {
                let y = idx / 5;
                let x = idx % 5;
                get(state, x, y) ^ (!get(state, (x + 1) % 5, y) & get(state, (x + 2) % 5, y))
            },
    )
}

/// iota: `A'[0,0] = A[0,0] ^ RC[round]` -- FIPS 202, Algorithm 6.
pub open spec fn iota(state: Seq<u64>, round: int) -> Seq<u64> {
    state.update(0, state[0] ^ round_constant(round))
}

/// The lane pi brings to `(x, y)`, after theta and rho.
///
/// `pi` sets `A'[x, y] = A[(x + 3y) % 5, x]`, at specification index
/// `5*x + (x + 3y) % 5`, rotated by that lane's rho offset.
pub open spec fn prc_b_spec(state: Seq<u64>, x: int, y: int) -> u64 {
    rotl64(
        state[5 * x + (x + 3 * y) % 5] ^ theta_d(state, (x + 3 * y) % 5),
        rho_offset(5 * x + (x + 3 * y) % 5),
    )
}

/// Output `(x, y)` after chi, before iota.
pub open spec fn chi_spec(state: Seq<u64>, x: int, y: int) -> u64 {
    prc_b_spec(state, x, y) ^ ((!prc_b_spec(state, (x + 1) % 5, y)) & prc_b_spec(
        state,
        (x + 2) % 5,
        y,
    ))
}

/// Every rho offset is below 63, which is what the rotation bridge needs.
pub proof fn lemma_rho_offset_bound(idx: int)
    requires
        0 <= idx < 25,
    ensures
        0 <= rho_offset(idx) < 63,
{
    if idx == 0 {
    }
    if idx == 1 {
    }
    if idx == 2 {
    }
    if idx == 3 {
    }
    if idx == 4 {
    }
    if idx == 5 {
    }
    if idx == 6 {
    }
    if idx == 7 {
    }
    if idx == 8 {
    }
    if idx == 9 {
    }
    if idx == 10 {
    }
    if idx == 11 {
    }
    if idx == 12 {
    }
    if idx == 13 {
    }
    if idx == 14 {
    }
    if idx == 15 {
    }
    if idx == 16 {
    }
    if idx == 17 {
    }
    if idx == 18 {
    }
    if idx == 19 {
    }
    if idx == 20 {
    }
    if idx == 21 {
    }
    if idx == 22 {
    }
    if idx == 23 {
    }
    if idx == 24 {
    }
}

/// One round: theta; rho; pi; chi; iota.
///
/// Opaque: unfolding it drags in the whole permutation, which is ruinous
/// anywhere the rounds are merely being chained. The two places that need the
/// body reveal it.
#[verifier::opaque]
pub open spec fn round(state: Seq<u64>, ir: int) -> Seq<u64> {
    iota(chi(pi(rho(theta(state)))), ir)
}

/// `n` rounds starting at round index `ir`.
pub open spec fn rounds_from(state: Seq<u64>, ir: int, n: nat) -> Seq<u64>
    decreases n,
{
    if n == 0 {
        state
    } else {
        round(rounds_from(state, ir, (n - 1) as nat), ir + n - 1)
    }
}

/// Four rounds spelled out. Isolating the unfolding of the recursion keeps it
/// out of the callers' proof obligations.
pub proof fn lemma_rounds_from_4(state: Seq<u64>, ir: int)
    ensures
        rounds_from(state, ir, 4) == round(round(round(round(state, ir), ir + 1), ir + 2), ir + 3),
{
    reveal_with_fuel(rounds_from, 5);
}

/// Any number of rounds leaves the state well formed.
pub proof fn lemma_rounds_from_wf(state: Seq<u64>, ir: int, n: nat)
    requires
        wf_state(state),
    ensures
        wf_state(rounds_from(state, ir, n)),
    decreases n,
{
    if n > 0 {
        lemma_rounds_from_wf(state, ir, (n - 1) as nat);
        lemma_round_wf(rounds_from(state, ir, (n - 1) as nat), ir + n - 1);
    }
}

/// Rounds compose: `k` rounds then `n` more is `k + n` rounds.
pub proof fn lemma_rounds_from_split(state: Seq<u64>, k: nat, n: nat)
    ensures
        rounds_from(rounds_from(state, 0, k), k as int, n) == rounds_from(state, 0, (k + n) as nat),
    decreases n,
{
    if n > 0 {
        lemma_rounds_from_split(state, k, (n - 1) as nat);
    }
}

/// A round leaves the state well formed.
pub proof fn lemma_round_wf(state: Seq<u64>, ir: int)
    requires
        wf_state(state),
    ensures
        wf_state(round(state, ir)),
{
    reveal(round);
}

/// Keccak-f[1600]: 24 rounds -- FIPS 202, Section 3.3.
pub open spec fn keccak_f(state: Seq<u64>) -> Seq<u64> {
    rounds_from(state, 0, 24)
}

} // verus!
