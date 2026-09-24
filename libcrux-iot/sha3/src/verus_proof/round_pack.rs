//! What each round's implementation functions promise, and the quantified form
//! [`super::round`] wants.
//!
//! `theta_facts_<r>`, `prc1_facts_<r>` and `prc2_facts_<r>` are exactly the
//! postconditions the round's three composite functions carry. They are opaque:
//! a caller sequencing twelve of these should see twelve atomic terms, not the
//! twelve hundred lane-level facts behind them. Each composite reveals its own
//! bundle to prove it, and the lemmas here reveal what they consume.
//!
//! `lemma_round_pack_<r>` turns the lane-by-lane form into the quantified one,
//! which needs the range of the bound variable enumerated -- the case splits.
//! `lemma_round_<r>` then discharges the whole round.

use vstd::prelude::*;

use super::lane_bridge::lemma_xor_zero;
use super::layout::{
    lemma_round_inv_wf, lemma_round_layout_len, round_inv, round_place, round_swapped,
};
use super::prc::prc_chi_at;
use super::round::{lemma_index_split, lemma_round_from_halves};
use super::spec::{round, wf_state};
use super::state::{lane_half, lifts_to_layout};
use super::theta::{impl_col_xor_at, impl_d_half};
use super::theta_order::{
    lemma_col_order_0, lemma_col_order_1, lemma_col_order_2, lemma_col_order_3,
};
use crate::state::KeccakState;

verus! {

/// What round 0's theta promises.
#[verifier::opaque]
pub(crate) open spec fn theta_facts_0(s0: KeccakState, s1: KeccakState) -> bool {
    &&& s1.st == s0.st
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), crate::verus_proof::layout::round_inv(0), x, 0)
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), crate::verus_proof::layout::round_inv(0), x, 1)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1)
}

/// What round 0's first pi-rho-chi half promises: rows 0 and 1 computed, and
/// the inputs of rows 2 to 4 left alone.
#[verifier::opaque]
pub(crate) open spec fn prc1_facts_0(s1: KeccakState, s1h: KeccakState, ir: int) -> bool {
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 0, 0) ^ crate::keccak::RC_INTERLEAVED_0[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 0, 1) ^ crate::keccak::RC_INTERLEAVED_1[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 1, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 1)
}

/// What round 0's second half promises: rows 2 to 4 computed, and the first
/// half's results left alone.
#[verifier::opaque]
pub(crate) open spec fn prc2_facts_0(s1h: KeccakState, s2: KeccakState) -> bool {
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 5, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 6, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 7, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 8, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 9, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 10, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 10, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 11, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 11, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 12, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 12, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 13, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 13, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 14, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 14, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 15, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 15, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 16, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 16, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 17, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 17, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 18, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 18, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 19, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 19, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 20, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 20, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 0, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 21, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 21, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 1, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 22, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 22, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 2, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 23, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 23, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 3, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 24, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 24, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), 4, 4, 1)
}

/// Both halves.
pub(crate) open spec fn prc_facts_0(
    s1: KeccakState,
    s1h: KeccakState,
    s2: KeccakState,
    ir: int,
) -> bool {
    prc1_facts_0(s1, s1h, ir) && prc2_facts_0(s1h, s2)
}

/// Round 0, quantified.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_pack_0(s1: KeccakState, s1h: KeccakState, s2: KeccakState, ir: int)
    requires
        0 <= ir < 24,
        prc_facts_0(s1, s1h, s2, ir),
    ensures
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z) == lane_half(
                s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z,
            ),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z) == prc_chi_at(
                s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z,
            ),
{
    reveal(prc1_facts_0);
    reveal(prc2_facts_0);
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
        crate::keccak::RC_INTERLEAVED_0[ir]
    } else if l == 0 {
        crate::keccak::RC_INTERLEAVED_1[ir]
    } else {
        0u32
    }) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
        if l != 0 {
            lemma_xor_zero(prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z));
        }
    }
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z,
    ) == lane_half(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] prc_chi_at(
        s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l, z,
    ) == prc_chi_at(s1h, crate::verus_proof::layout::round_place(0), crate::verus_proof::layout::round_swapped(0), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
}

/// Round 0, from the four states the implementation passes through.
#[verifier::rlimit(400)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_0(
    spec_state: Seq<u64>,
    a: KeccakState,
    at: KeccakState,
    ah: KeccakState,
    b: KeccakState,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(a, spec_state, round_place(0), round_swapped(0)),
        0 <= ir < 24,
        theta_facts_0(a, at),
        prc_facts_0(at, ah, b, ir),
    ensures
        lifts_to_layout(b, round(spec_state, ir), round_place(1), round_swapped(1)),
{
    reveal(theta_facts_0);
    lemma_col_order_0(spec_state);
    lemma_round_inv_wf(0);
    lemma_round_layout_len(1);
    lemma_round_pack_0(at, ah, b, ir);
    lemma_round_from_halves(
        a, spec_state, round_place(0), round_swapped(0), round_inv(0), at, ah, b,
        round_place(1), round_swapped(1), ir,
    );
}

/// What round 1's theta promises.
#[verifier::opaque]
pub(crate) open spec fn theta_facts_1(s0: KeccakState, s1: KeccakState) -> bool {
    &&& s1.st == s0.st
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), crate::verus_proof::layout::round_inv(1), x, 0)
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), crate::verus_proof::layout::round_inv(1), x, 1)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1)
}

/// What round 1's first pi-rho-chi half promises: rows 0 and 1 computed, and
/// the inputs of rows 2 to 4 left alone.
#[verifier::opaque]
pub(crate) open spec fn prc1_facts_1(s1: KeccakState, s1h: KeccakState, ir: int) -> bool {
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 0, 0) ^ crate::keccak::RC_INTERLEAVED_0[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 0, 1) ^ crate::keccak::RC_INTERLEAVED_1[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 1, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 1)
}

/// What round 1's second half promises: rows 2 to 4 computed, and the first
/// half's results left alone.
#[verifier::opaque]
pub(crate) open spec fn prc2_facts_1(s1h: KeccakState, s2: KeccakState) -> bool {
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 5, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 6, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 7, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 8, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 9, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 10, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 10, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 11, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 11, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 12, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 12, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 13, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 13, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 14, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 14, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 15, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 15, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 16, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 16, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 17, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 17, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 18, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 18, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 19, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 19, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 20, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 20, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 0, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 21, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 21, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 1, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 22, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 22, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 2, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 23, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 23, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 3, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 24, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 24, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), 4, 4, 1)
}

/// Both halves.
pub(crate) open spec fn prc_facts_1(
    s1: KeccakState,
    s1h: KeccakState,
    s2: KeccakState,
    ir: int,
) -> bool {
    prc1_facts_1(s1, s1h, ir) && prc2_facts_1(s1h, s2)
}

/// Round 1, quantified.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_pack_1(s1: KeccakState, s1h: KeccakState, s2: KeccakState, ir: int)
    requires
        0 <= ir < 24,
        prc_facts_1(s1, s1h, s2, ir),
    ensures
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z) == lane_half(
                s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z,
            ),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z) == prc_chi_at(
                s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z,
            ),
{
    reveal(prc1_facts_1);
    reveal(prc2_facts_1);
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
        crate::keccak::RC_INTERLEAVED_0[ir]
    } else if l == 0 {
        crate::keccak::RC_INTERLEAVED_1[ir]
    } else {
        0u32
    }) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
        if l != 0 {
            lemma_xor_zero(prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z));
        }
    }
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z,
    ) == lane_half(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] prc_chi_at(
        s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l, z,
    ) == prc_chi_at(s1h, crate::verus_proof::layout::round_place(1), crate::verus_proof::layout::round_swapped(1), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
}

/// Round 1, from the four states the implementation passes through.
#[verifier::rlimit(400)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_1(
    spec_state: Seq<u64>,
    a: KeccakState,
    at: KeccakState,
    ah: KeccakState,
    b: KeccakState,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(a, spec_state, round_place(1), round_swapped(1)),
        0 <= ir < 24,
        theta_facts_1(a, at),
        prc_facts_1(at, ah, b, ir),
    ensures
        lifts_to_layout(b, round(spec_state, ir), round_place(2), round_swapped(2)),
{
    reveal(theta_facts_1);
    lemma_col_order_1(spec_state);
    lemma_round_inv_wf(1);
    lemma_round_layout_len(2);
    lemma_round_pack_1(at, ah, b, ir);
    lemma_round_from_halves(
        a, spec_state, round_place(1), round_swapped(1), round_inv(1), at, ah, b,
        round_place(2), round_swapped(2), ir,
    );
}

/// What round 2's theta promises.
#[verifier::opaque]
pub(crate) open spec fn theta_facts_2(s0: KeccakState, s1: KeccakState) -> bool {
    &&& s1.st == s0.st
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), crate::verus_proof::layout::round_inv(2), x, 0)
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), crate::verus_proof::layout::round_inv(2), x, 1)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1)
}

/// What round 2's first pi-rho-chi half promises: rows 0 and 1 computed, and
/// the inputs of rows 2 to 4 left alone.
#[verifier::opaque]
pub(crate) open spec fn prc1_facts_2(s1: KeccakState, s1h: KeccakState, ir: int) -> bool {
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 0, 0) ^ crate::keccak::RC_INTERLEAVED_0[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 0, 1) ^ crate::keccak::RC_INTERLEAVED_1[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 1, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 1)
}

/// What round 2's second half promises: rows 2 to 4 computed, and the first
/// half's results left alone.
#[verifier::opaque]
pub(crate) open spec fn prc2_facts_2(s1h: KeccakState, s2: KeccakState) -> bool {
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 5, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 6, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 7, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 8, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 9, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 10, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 10, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 11, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 11, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 12, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 12, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 13, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 13, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 14, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 14, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 15, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 15, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 16, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 16, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 17, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 17, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 18, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 18, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 19, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 19, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 20, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 20, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 0, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 21, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 21, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 1, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 22, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 22, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 2, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 23, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 23, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 3, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 24, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 24, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), 4, 4, 1)
}

/// Both halves.
pub(crate) open spec fn prc_facts_2(
    s1: KeccakState,
    s1h: KeccakState,
    s2: KeccakState,
    ir: int,
) -> bool {
    prc1_facts_2(s1, s1h, ir) && prc2_facts_2(s1h, s2)
}

/// Round 2, quantified.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_pack_2(s1: KeccakState, s1h: KeccakState, s2: KeccakState, ir: int)
    requires
        0 <= ir < 24,
        prc_facts_2(s1, s1h, s2, ir),
    ensures
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z) == lane_half(
                s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z,
            ),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z) == prc_chi_at(
                s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z,
            ),
{
    reveal(prc1_facts_2);
    reveal(prc2_facts_2);
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
        crate::keccak::RC_INTERLEAVED_0[ir]
    } else if l == 0 {
        crate::keccak::RC_INTERLEAVED_1[ir]
    } else {
        0u32
    }) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
        if l != 0 {
            lemma_xor_zero(prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z));
        }
    }
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z,
    ) == lane_half(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] prc_chi_at(
        s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l, z,
    ) == prc_chi_at(s1h, crate::verus_proof::layout::round_place(2), crate::verus_proof::layout::round_swapped(2), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
}

/// Round 2, from the four states the implementation passes through.
#[verifier::rlimit(400)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_2(
    spec_state: Seq<u64>,
    a: KeccakState,
    at: KeccakState,
    ah: KeccakState,
    b: KeccakState,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(a, spec_state, round_place(2), round_swapped(2)),
        0 <= ir < 24,
        theta_facts_2(a, at),
        prc_facts_2(at, ah, b, ir),
    ensures
        lifts_to_layout(b, round(spec_state, ir), round_place(3), round_swapped(3)),
{
    reveal(theta_facts_2);
    lemma_col_order_2(spec_state);
    lemma_round_inv_wf(2);
    lemma_round_layout_len(3);
    lemma_round_pack_2(at, ah, b, ir);
    lemma_round_from_halves(
        a, spec_state, round_place(2), round_swapped(2), round_inv(2), at, ah, b,
        round_place(3), round_swapped(3), ir,
    );
}

/// What round 3's theta promises.
#[verifier::opaque]
pub(crate) open spec fn theta_facts_3(s0: KeccakState, s1: KeccakState) -> bool {
    &&& s1.st == s0.st
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), crate::verus_proof::layout::round_inv(3), x, 0)
    &&& forall|x: int|
        0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), crate::verus_proof::layout::round_inv(3), x, 1)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0)
    &&& forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1)
}

/// What round 3's first pi-rho-chi half promises: rows 0 and 1 computed, and
/// the inputs of rows 2 to 4 left alone.
#[verifier::opaque]
pub(crate) open spec fn prc1_facts_3(s1: KeccakState, s1h: KeccakState, ir: int) -> bool {
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 0, 0) ^ crate::keccak::RC_INTERLEAVED_0[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 0, 1) ^ crate::keccak::RC_INTERLEAVED_1[ir]
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 0, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 0, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 1, 1)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 1, 0)
    &&& lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 1, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 1)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 0)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 0)
    &&& prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 1)
        == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 1)
}

/// What round 3's second half promises: rows 2 to 4 computed, and the first
/// half's results left alone.
#[verifier::opaque]
pub(crate) open spec fn prc2_facts_3(s1h: KeccakState, s2: KeccakState) -> bool {
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 0, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 1, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 5, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 6, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 7, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 8, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 0)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 1)
        == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 9, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 10, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 10, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 11, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 11, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 12, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 12, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 13, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 13, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 14, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 14, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 2, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 15, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 15, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 16, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 16, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 17, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 17, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 18, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 18, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 19, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 19, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 3, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 20, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 20, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 0, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 21, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 21, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 1, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 22, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 22, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 2, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 23, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 23, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 3, 4, 1)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 24, 0)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 0)
    &&& lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), 24, 1)
        == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), 4, 4, 1)
}

/// Both halves.
pub(crate) open spec fn prc_facts_3(
    s1: KeccakState,
    s1h: KeccakState,
    s2: KeccakState,
    ir: int,
) -> bool {
    prc1_facts_3(s1, s1h, ir) && prc2_facts_3(s1h, s2)
}

/// Round 3, quantified.
#[verifier::rlimit(800)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_pack_3(s1: KeccakState, s1h: KeccakState, s2: KeccakState, ir: int)
    requires
        0 <= ir < 24,
        prc_facts_3(s1, s1h, s2, ir),
    ensures
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z) == lane_half(
                s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z,
            ),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z)
                == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] lane_half(s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z) == prc_chi_at(
                s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z,
            ),
{
    reveal(prc1_facts_3);
    reveal(prc2_facts_3);
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
        crate::keccak::RC_INTERLEAVED_0[ir]
    } else if l == 0 {
        crate::keccak::RC_INTERLEAVED_1[ir]
    } else {
        0u32
    }) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
        if l != 0 {
            lemma_xor_zero(prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z));
        }
    }
    assert forall|l: int, z: int| 0 <= l < 10 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z,
    ) == lane_half(s1h, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z) by {
        if l == 0 {
            lemma_index_split(0, 0);
        }
        if l == 1 {
            lemma_index_split(1, 0);
        }
        if l == 2 {
            lemma_index_split(2, 0);
        }
        if l == 3 {
            lemma_index_split(3, 0);
        }
        if l == 4 {
            lemma_index_split(4, 0);
        }
        if l == 5 {
            lemma_index_split(0, 1);
        }
        if l == 6 {
            lemma_index_split(1, 1);
        }
        if l == 7 {
            lemma_index_split(2, 1);
        }
        if l == 8 {
            lemma_index_split(3, 1);
        }
        if l == 9 {
            lemma_index_split(4, 1);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] prc_chi_at(
        s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z,
    ) == prc_chi_at(s1, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
    assert forall|l: int, z: int| 10 <= l < 25 && 0 <= z < 2 implies #[trigger] lane_half(
        s2, crate::verus_proof::layout::round_place(4), crate::verus_proof::layout::round_swapped(4), l, z,
    ) == prc_chi_at(s1h, crate::verus_proof::layout::round_place(3), crate::verus_proof::layout::round_swapped(3), l % 5, l / 5, z) by {
        if l == 10 {
            lemma_index_split(0, 2);
        }
        if l == 11 {
            lemma_index_split(1, 2);
        }
        if l == 12 {
            lemma_index_split(2, 2);
        }
        if l == 13 {
            lemma_index_split(3, 2);
        }
        if l == 14 {
            lemma_index_split(4, 2);
        }
        if l == 15 {
            lemma_index_split(0, 3);
        }
        if l == 16 {
            lemma_index_split(1, 3);
        }
        if l == 17 {
            lemma_index_split(2, 3);
        }
        if l == 18 {
            lemma_index_split(3, 3);
        }
        if l == 19 {
            lemma_index_split(4, 3);
        }
        if l == 20 {
            lemma_index_split(0, 4);
        }
        if l == 21 {
            lemma_index_split(1, 4);
        }
        if l == 22 {
            lemma_index_split(2, 4);
        }
        if l == 23 {
            lemma_index_split(3, 4);
        }
        if l == 24 {
            lemma_index_split(4, 4);
        }
    }
}

/// Round 3, from the four states the implementation passes through.
#[verifier::rlimit(400)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_round_3(
    spec_state: Seq<u64>,
    a: KeccakState,
    at: KeccakState,
    ah: KeccakState,
    b: KeccakState,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(a, spec_state, round_place(3), round_swapped(3)),
        0 <= ir < 24,
        theta_facts_3(a, at),
        prc_facts_3(at, ah, b, ir),
    ensures
        lifts_to_layout(b, round(spec_state, ir), round_place(4), round_swapped(4)),
{
    reveal(theta_facts_3);
    lemma_col_order_3(spec_state);
    lemma_round_inv_wf(3);
    lemma_round_layout_len(4);
    lemma_round_pack_3(at, ah, b, ir);
    lemma_round_from_halves(
        a, spec_state, round_place(3), round_swapped(3), round_inv(3), at, ah, b,
        round_place(4), round_swapped(4), ir,
    );
}

} // verus!
