//! One whole round: theta's column phase, then pi-rho-chi over all five rows.
//!
//! The implementation splits a round into `keccakf1600_round<n>_theta`, which
//! fills `c` and `d` and leaves `st` alone, and two pi-rho-chi functions that
//! rewrite `st` in place. This module composes their postconditions into the
//! statement that the round computes `spec::round`, carrying the state from the
//! layout the round starts in to the one it leaves behind.

use vstd::prelude::*;

use super::lane_bridge::{is_lane, lemma_xor_zero};
use super::prc::prc_chi_at;
use super::prc_bridge::lemma_prc_row;
use super::spec::{lemma_round_wf, round, theta_d, wf_state};
use super::state::{lane_half, lemma_lifts_to_st, lifts_to_layout};
use super::theta_order::col_order_ok;
use super::theta::{impl_col_xor_at, impl_d_half, lemma_theta_cd, wf_inv};
use crate::state::KeccakState;

verus! {

/// Row `y` of the round's output is right, in the layout the step writes into.
pub(crate) open spec fn row_correct(
    s2: KeccakState,
    spec_state: Seq<u64>,
    place_out: Seq<int>,
    swapped_out: Seq<bool>,
    ir: int,
    y: int,
) -> bool {
    forall|j: int|
        0 <= j < 5 ==> #[trigger] is_lane(
            round(spec_state, ir)[5 * y + j],
            lane_half(s2, place_out, swapped_out, 5 * y + j, 0),
            lane_half(s2, place_out, swapped_out, 5 * y + j, 1),
        )
}

/// `5*y + j` splits back into `j` and `y`.
pub(crate) proof fn lemma_index_split(j: int, y: int)
    requires
        0 <= j < 5,
        0 <= y < 5,
    ensures
        (5 * y + j) % 5 == j,
        (5 * y + j) / 5 == y,
        0 <= 5 * y + j < 25,
{
    assert((5 * y + j) % 5 == j) by (nonlinear_arith)
        requires
            0 <= j < 5,
            0 <= y < 5,
    ;
    assert((5 * y + j) / 5 == y) by (nonlinear_arith)
        requires
            0 <= j < 5,
            0 <= y < 5,
    ;
}

/// One round.
///
/// `s0` is the state before theta, in the layout `(place, swapped)`; `s1` the
/// state after theta -- `st` untouched, `c` and `d` filled -- and `s2` the state
/// the two pi-rho-chi functions leave, in the layout
/// `(place_out, swapped_out)`. The hypotheses are exactly the postconditions
/// those functions carry.
pub(crate) proof fn lemma_round_step(
    s0: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    inv: Seq<int>,
    s1: KeccakState,
    s2: KeccakState,
    place_out: Seq<int>,
    swapped_out: Seq<bool>,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(s0, spec_state, place, swapped),
        wf_inv(inv),
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, inv, x),
        0 <= ir < 24,
        s1.st == s0.st,
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, place, swapped, inv, x, 0),
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, place, swapped, inv, x, 1),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1),
        forall|l: int|
            0 <= l < 25 ==> #[trigger] lane_half(s2, place_out, swapped_out, l, 0)
                == prc_chi_at(s1, place, swapped, l % 5, l / 5, 0) ^ (if l == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else {
                0u32
            }),
        forall|l: int|
            0 <= l < 25 ==> #[trigger] lane_half(s2, place_out, swapped_out, l, 1)
                == prc_chi_at(s1, place, swapped, l % 5, l / 5, 1) ^ (if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        place_out.len() == 25,
        swapped_out.len() == 25,
    ensures
        lifts_to_layout(s2, round(spec_state, ir), place_out, swapped_out),
{
    // `round` is opaque, so its length has to come from the lemma.
    lemma_round_wf(spec_state, ir);
    lemma_lifts_to_st(s0, s1, spec_state, place, swapped);
    lemma_theta_cd(s0, spec_state, place, swapped, inv, s1);

    assert forall|y: int| 0 <= y < 5 implies #[trigger] row_correct(
        s2,
        spec_state,
        place_out,
        swapped_out,
        ir,
        y,
    ) by {
        // Re-index the hypotheses from `l` to `(j, y)`.
        assert forall|j: int| 0 <= j < 5 implies #[trigger] lane_half(
            s2,
            place_out,
            swapped_out,
            5 * y + j,
            0,
        ) == prc_chi_at(s1, place, swapped, j, y, 0) ^ (if j == 0 && y == 0 {
            crate::keccak::RC_INTERLEAVED_0[ir]
        } else {
            0u32
        }) by {
            lemma_index_split(j, y);
        }
        assert forall|j: int| 0 <= j < 5 implies #[trigger] lane_half(
            s2,
            place_out,
            swapped_out,
            5 * y + j,
            1,
        ) == prc_chi_at(s1, place, swapped, j, y, 1) ^ (if j == 0 && y == 0 {
            crate::keccak::RC_INTERLEAVED_1[ir]
        } else {
            0u32
        }) by {
            lemma_index_split(j, y);
        }
        lemma_prc_row(s1, spec_state, place, swapped, s2, place_out, swapped_out, ir, y);
    }

    assert forall|l: int| 0 <= l < 25 implies #[trigger] is_lane(
        round(spec_state, ir)[l],
        lane_half(s2, place_out, swapped_out, l, 0),
        lane_half(s2, place_out, swapped_out, l, 1),
    ) by {
        lemma_index_split(l % 5, l / 5);
        assert(row_correct(s2, spec_state, place_out, swapped_out, ir, l / 5));
    }
}

/// One round, as the implementation actually sequences it.
///
/// The round is four calls: theta, then `pi_rho_chi_1` (rows 0 and 1,
/// specification lanes 0 to 10) and `pi_rho_chi_2` (rows 2 to 4, lanes 10 to
/// 25). `s1h` is the state between the two pi-rho-chi halves. They write
/// disjoint lanes, so each carries what the other needs across it, and those
/// two facts are the third and fourth hypotheses here.
pub(crate) proof fn lemma_round_from_halves(
    s0: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    inv: Seq<int>,
    s1: KeccakState,
    s1h: KeccakState,
    s2: KeccakState,
    place_out: Seq<int>,
    swapped_out: Seq<bool>,
    ir: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(s0, spec_state, place, swapped),
        wf_inv(inv),
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, inv, x),
        0 <= ir < 24,
        s1.st == s0.st,
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s1.c[x].0[0] == impl_col_xor_at(s0, place, swapped, inv, x, 0),
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s1.c[x].0[1] == impl_col_xor_at(s0, place, swapped, inv, x, 1),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[0] == impl_d_half(s1, x, 0),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s1.d[x].0[1] == impl_d_half(s1, x, 1),
        // The first half's results, and the second half carrying them through.
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s1h, place_out, swapped_out, l, z)
                == prc_chi_at(s1, place, swapped, l % 5, l / 5, z) ^ (if l == 0 && z == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else if l == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
        forall|l: int, z: int|
            0 <= l < 10 && 0 <= z < 2 ==> #[trigger] lane_half(s2, place_out, swapped_out, l, z)
                == lane_half(s1h, place_out, swapped_out, l, z),
        // The second half's results, and the first half leaving its inputs alone.
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] prc_chi_at(s1h, place, swapped, l % 5, l / 5, z)
                == prc_chi_at(s1, place, swapped, l % 5, l / 5, z),
        forall|l: int, z: int|
            10 <= l < 25 && 0 <= z < 2 ==> #[trigger] lane_half(s2, place_out, swapped_out, l, z)
                == prc_chi_at(s1h, place, swapped, l % 5, l / 5, z),
        place_out.len() == 25,
        swapped_out.len() == 25,
    ensures
        lifts_to_layout(s2, round(spec_state, ir), place_out, swapped_out),
{
    assert forall|l: int| 0 <= l < 25 implies #[trigger] lane_half(
        s2,
        place_out,
        swapped_out,
        l,
        0,
    ) == prc_chi_at(s1, place, swapped, l % 5, l / 5, 0) ^ (if l == 0 {
        crate::keccak::RC_INTERLEAVED_0[ir]
    } else {
        0u32
    }) by {
        if l >= 10 {
            lemma_xor_zero(prc_chi_at(s1, place, swapped, l % 5, l / 5, 0));
        }
    }
    assert forall|l: int| 0 <= l < 25 implies #[trigger] lane_half(
        s2,
        place_out,
        swapped_out,
        l,
        1,
    ) == prc_chi_at(s1, place, swapped, l % 5, l / 5, 1) ^ (if l == 0 {
        crate::keccak::RC_INTERLEAVED_1[ir]
    } else {
        0u32
    }) by {
        if l >= 10 {
            lemma_xor_zero(prc_chi_at(s1, place, swapped, l % 5, l / 5, 1));
        }
    }
    lemma_round_step(s0, spec_state, place, swapped, inv, s1, s2, place_out, swapped_out, ir);
}

} // verus!
