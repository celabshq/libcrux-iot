//! Bridging the implementation's row-0 pi-rho-chi to FIPS-202.
//!
//! Two things have to hold. On the specification side, that output row `y = 0`
//! of a round really is chi applied to the rotated diagonal, with the round
//! constant on column 0 -- `lemma_round_row0`, pure unfolding of
//! `iota . chi . pi . rho . theta`. On the implementation side, that its 32-bit
//! arithmetic computes the interleaved form of each piece.

use vstd::prelude::*;

use super::lane_bridge::{
    is_lane, lemma_lane_and, lemma_lane_not, lemma_lane_rotl, lemma_lane_xor, lemma_xor_zero,
    rot_half, rotl64,
};
use super::prc::{prc_b_at, prc_chi_at, prc_src, prc_src_col};
use super::rc::lemma_rc_lane;
use super::spec::{
    chi, chi_spec, get, lemma_rho_offset_bound, pi, prc_b_spec, rho, rho_offset, round,
    round_constant, theta, theta_d, wf_state,
};
use super::state::{lane_half, lifts_to_layout};
use crate::state::KeccakState;

verus! {

/// The implementation's `b` values are the interleaved form of the
/// specification's, for every output position.
pub(crate) proof fn lemma_prc_b(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    x: int,
    y: int,
)
    requires
        lifts_to_layout(s, spec_state, place, swapped),
        0 <= x < 5,
        0 <= y < 5,
        forall|w: int|
            0 <= w < 5 ==> #[trigger] is_lane(theta_d(spec_state, w), s.d[w].0[0], s.d[w].0[1]),
    ensures
        is_lane(prc_b_spec(spec_state, x, y), prc_b_at(s, place, swapped, x, y, 0), prc_b_at(s, place, swapped, x, y, 1)),
{
    let src = prc_src(x, y);
    let col = prc_src_col(x, y);
    assert(0 <= src < 25);
    assert(0 <= col < 5);
    assert(is_lane(
        spec_state[src],
        lane_half(s, place, swapped, src, 0),
        lane_half(s, place, swapped, src, 1),
    ));
    assert(is_lane(theta_d(spec_state, col), s.d[col].0[0], s.d[col].0[1]));

    lemma_lane_xor(
        spec_state[src],
        lane_half(s, place, swapped, src, 0),
        lane_half(s, place, swapped, src, 1),
        theta_d(spec_state, col),
        s.d[col].0[0],
        s.d[col].0[1],
    );
    lemma_rho_offset_bound(src);
    lemma_lane_rotl(
        spec_state[src] ^ theta_d(spec_state, col),
        lane_half(s, place, swapped, src, 0) ^ s.d[col].0[0],
        lane_half(s, place, swapped, src, 1) ^ s.d[col].0[1],
        rho_offset(src) as int,
    );
}

/// Chi acts on the interleaved halves exactly as it does on lanes.
pub(crate) proof fn lemma_prc_chi(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    x: int,
    y: int,
)
    requires
        0 <= x < 5,
        0 <= y < 5,
        forall|w: int|
            0 <= w < 5 ==> #[trigger] is_lane(
                prc_b_spec(spec_state, w, y),
                prc_b_at(s, place, swapped, w, y, 0),
                prc_b_at(s, place, swapped, w, y, 1),
            ),
    ensures
        is_lane(chi_spec(spec_state, x, y), prc_chi_at(s, place, swapped, x, y, 0), prc_chi_at(s, place, swapped, x, y, 1)),
{
    let x1 = (x + 1) % 5;
    let x2 = (x + 2) % 5;
    assert(0 <= x1 < 5);
    assert(0 <= x2 < 5);
    assert(is_lane(prc_b_spec(spec_state, x, y), prc_b_at(s, place, swapped, x, y, 0), prc_b_at(s, place, swapped, x, y, 1)));
    assert(is_lane(prc_b_spec(spec_state, x1, y), prc_b_at(s, place, swapped, x1, y, 0), prc_b_at(s, place, swapped, x1, y, 1)));
    assert(is_lane(prc_b_spec(spec_state, x2, y), prc_b_at(s, place, swapped, x2, y, 0), prc_b_at(s, place, swapped, x2, y, 1)));

    lemma_lane_not(prc_b_spec(spec_state, x1, y), prc_b_at(s, place, swapped, x1, y, 0), prc_b_at(s, place, swapped, x1, y, 1));
    lemma_lane_and(
        !prc_b_spec(spec_state, x1, y),
        !prc_b_at(s, place, swapped, x1, y, 0),
        !prc_b_at(s, place, swapped, x1, y, 1),
        prc_b_spec(spec_state, x2, y),
        prc_b_at(s, place, swapped, x2, y, 0),
        prc_b_at(s, place, swapped, x2, y, 1),
    );
    lemma_lane_xor(
        prc_b_spec(spec_state, x, y),
        prc_b_at(s, place, swapped, x, y, 0),
        prc_b_at(s, place, swapped, x, y, 1),
        (!prc_b_spec(spec_state, x1, y)) & prc_b_spec(spec_state, x2, y),
        (!prc_b_at(s, place, swapped, x1, y, 0)) & prc_b_at(s, place, swapped, x2, y, 0),
        (!prc_b_at(s, place, swapped, x1, y, 1)) & prc_b_at(s, place, swapped, x2, y, 1),
    );
}

/// Iota, at `(0, 0)`: XORing the implementation's two table entries into the
/// halves is XORing the FIPS-202 round constant into the lane.
pub(crate) proof fn lemma_prc_iota(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    ir: int,
)
    requires
        0 <= ir < 24,
        is_lane(chi_spec(spec_state, 0, 0), prc_chi_at(s, place, swapped, 0, 0, 0), prc_chi_at(s, place, swapped, 0, 0, 1)),
    ensures
        is_lane(
            chi_spec(spec_state, 0, 0) ^ round_constant(ir),
            prc_chi_at(s, place, swapped, 0, 0, 0) ^ crate::keccak::RC_INTERLEAVED_0[ir],
            prc_chi_at(s, place, swapped, 0, 0, 1) ^ crate::keccak::RC_INTERLEAVED_1[ir],
        ),
{
    lemma_rc_lane(ir);
    lemma_lane_xor(
        chi_spec(spec_state, 0, 0),
        prc_chi_at(s, place, swapped, 0, 0, 0),
        prc_chi_at(s, place, swapped, 0, 0, 1),
        round_constant(ir),
        crate::keccak::RC_INTERLEAVED_0[ir],
        crate::keccak::RC_INTERLEAVED_1[ir],
    );
}

/// A round's output at `(x, y)`: chi over pi's selection, with the round
/// constant on `(0, 0)`.
pub(crate) proof fn lemma_round_at(state: Seq<u64>, ir: int, x: int, y: int)
    requires
        wf_state(state),
        0 <= ir < 24,
        0 <= x < 5,
        0 <= y < 5,
    ensures
        round(state, ir)[5 * y + x] == if x == 0 && y == 0 {
            chi_spec(state, 0, 0) ^ round_constant(ir)
        } else {
            chi_spec(state, x, y)
        },
{
    reveal(round);
    let t = theta(state);
    let r = rho(t);
    let p = pi(r);

    assert forall|w: int| 0 <= w < 5 implies #[trigger] p[5 * y + w] == prc_b_spec(state, w, y) by {
        assert((5 * y + w) / 5 == y) by (nonlinear_arith)
            requires
                0 <= w < 5,
                0 <= y < 5,
        ;
        assert((5 * y + w) % 5 == w) by (nonlinear_arith)
            requires
                0 <= w < 5,
                0 <= y < 5,
        ;
        let src = prc_src(w, y);
        assert(get(r, (w + 3 * y) % 5, w) == r[src]);
        assert(r[src] == rotl64(t[src], rho_offset(src)));
        assert(t[src] == state[src] ^ theta_d(state, src % 5));
        assert(src % 5 == prc_src_col(w, y)) by (nonlinear_arith)
            requires
                src == 5 * w + prc_src_col(w, y),
                0 <= prc_src_col(w, y) < 5,
        ;
    }

    assert(chi(p)[5 * y + x] == chi_spec(state, x, y)) by {
        assert((5 * y + x) / 5 == y) by (nonlinear_arith)
            requires
                0 <= x < 5,
                0 <= y < 5,
        ;
        assert((5 * y + x) % 5 == x) by (nonlinear_arith)
            requires
                0 <= x < 5,
                0 <= y < 5,
        ;
        assert(get(p, x, y) == p[5 * y + x]);
        assert(get(p, (x + 1) % 5, y) == p[5 * y + (x + 1) % 5]);
        assert(get(p, (x + 2) % 5, y) == p[5 * y + (x + 2) % 5]);
    }
}

/// Round `ir`'s output row `y`, complete.
///
/// `s` is the state the row's two pi-rho-chi functions read -- after theta, so
/// `d` holds `D` -- in the layout `(place, swapped)` the round started in, and
/// `s2` the state they leave, in the layout `(place_out, swapped_out)` they
/// write into.
pub(crate) proof fn lemma_prc_row(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    s2: KeccakState,
    place_out: Seq<int>,
    swapped_out: Seq<bool>,
    ir: int,
    y: int,
)
    requires
        wf_state(spec_state),
        lifts_to_layout(s, spec_state, place, swapped),
        0 <= ir < 24,
        0 <= y < 5,
        forall|w: int|
            0 <= w < 5 ==> #[trigger] is_lane(theta_d(spec_state, w), s.d[w].0[0], s.d[w].0[1]),
        forall|j: int|
            0 <= j < 5 ==> #[trigger] lane_half(s2, place_out, swapped_out, 5 * y + j, 0)
                == prc_chi_at(s, place, swapped, j, y, 0) ^ (if j == 0 && y == 0 {
                crate::keccak::RC_INTERLEAVED_0[ir]
            } else {
                0u32
            }),
        forall|j: int|
            0 <= j < 5 ==> #[trigger] lane_half(s2, place_out, swapped_out, 5 * y + j, 1)
                == prc_chi_at(s, place, swapped, j, y, 1) ^ (if j == 0 && y == 0 {
                crate::keccak::RC_INTERLEAVED_1[ir]
            } else {
                0u32
            }),
    ensures
        forall|j: int|
            0 <= j < 5 ==> #[trigger] is_lane(
                round(spec_state, ir)[5 * y + j],
                lane_half(s2, place_out, swapped_out, 5 * y + j, 0),
                lane_half(s2, place_out, swapped_out, 5 * y + j, 1),
            ),
{
    assert forall|w: int| 0 <= w < 5 implies #[trigger] is_lane(
        prc_b_spec(spec_state, w, y),
        prc_b_at(s, place, swapped, w, y, 0),
        prc_b_at(s, place, swapped, w, y, 1),
    ) by {
        lemma_prc_b(s, spec_state, place, swapped, w, y);
    }

    assert forall|j: int| 0 <= j < 5 implies #[trigger] is_lane(
        round(spec_state, ir)[5 * y + j],
        lane_half(s2, place_out, swapped_out, 5 * y + j, 0),
        lane_half(s2, place_out, swapped_out, 5 * y + j, 1),
    ) by {
        lemma_prc_chi(s, spec_state, place, swapped, j, y);
        lemma_round_at(spec_state, ir, j, y);
        if j == 0 && y == 0 {
            lemma_prc_iota(s, spec_state, place, swapped, ir);
        } else {
            lemma_xor_zero(prc_chi_at(s, place, swapped, j, y, 0));
            lemma_xor_zero(prc_chi_at(s, place, swapped, j, y, 1));
        }
    }
}

} // verus!
