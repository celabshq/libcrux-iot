//! The theta step, column by column.
//!
//! The implementation computes each column accumulator `C[x]` as two separate
//! 32-bit XOR chains, one per interleaved half. Putting the two halves back
//! together gives the specification's 64-bit `C[x]`.

use vstd::prelude::*;

use super::lane_bridge::{is_lane, lemma_lane_rotl_odd, lemma_lane_xor, rotl32, rotl64};
use super::spec::{theta_c, theta_d};
use super::state::{lane_half, lifts_to_layout};
use super::theta_order::col_order_ok;
use crate::state::KeccakState;

verus! {

/// Half `z` of the implementation's column-`x` XOR chain.
///
/// Theta reads the five implementation lanes `5*x .. 5*x + 5` in turn and XORs
/// them in that order; `inv` says which specification lane each of those holds,
/// and the layout says which way up. Written in the implementation's order so
/// that it matches the body directly -- putting it back into the
/// specification's order is what [`col_order_ok`] is for.
pub(crate) open spec fn impl_col_xor_at(
    s: KeccakState,
    place: Seq<int>,
    swapped: Seq<bool>,
    inv: Seq<int>,
    x: int,
    z: int,
) -> u32 {
    lane_half(s, place, swapped, inv[5 * x], z) ^ lane_half(s, place, swapped, inv[5 * x + 1], z)
        ^ lane_half(s, place, swapped, inv[5 * x + 2], z) ^ lane_half(
        s,
        place,
        swapped,
        inv[5 * x + 3],
        z,
    ) ^ lane_half(s, place, swapped, inv[5 * x + 4], z)
}

/// A layout's inverse is well formed: every entry is a specification lane.
pub(crate) open spec fn wf_inv(inv: Seq<int>) -> bool {
    &&& inv.len() == 25
    &&& forall|p: int| 0 <= p < 25 ==> 0 <= #[trigger] inv[p] < 25
}

/// The implementation's `C[x]`, computed half by half, is the interleaved form
/// of the specification's `C[x]`.
pub(crate) proof fn lemma_theta_c(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    inv: Seq<int>,
    s2: KeccakState,
    x: int,
)
    requires
        lifts_to_layout(s, spec_state, place, swapped),
        wf_inv(inv),
        0 <= x < 5,
        col_order_ok(spec_state, inv, x),
        s2.c[x].0[0] == impl_col_xor_at(s, place, swapped, inv, x, 0),
        s2.c[x].0[1] == impl_col_xor_at(s, place, swapped, inv, x, 1),
    ensures
        is_lane(theta_c(spec_state, x), s2.c[x].0[0], s2.c[x].0[1]),
{
    let l0 = inv[5 * x];
    let l1 = inv[5 * x + 1];
    let l2 = inv[5 * x + 2];
    let l3 = inv[5 * x + 3];
    let l4 = inv[5 * x + 4];
    assert(is_lane(spec_state[l0], lane_half(s, place, swapped, l0, 0), lane_half(s, place, swapped, l0, 1)));
    assert(is_lane(spec_state[l1], lane_half(s, place, swapped, l1, 0), lane_half(s, place, swapped, l1, 1)));
    assert(is_lane(spec_state[l2], lane_half(s, place, swapped, l2, 0), lane_half(s, place, swapped, l2, 1)));
    assert(is_lane(spec_state[l3], lane_half(s, place, swapped, l3, 0), lane_half(s, place, swapped, l3, 1)));
    assert(is_lane(spec_state[l4], lane_half(s, place, swapped, l4, 0), lane_half(s, place, swapped, l4, 1)));

    lemma_lane_xor(
        spec_state[l0],
        lane_half(s, place, swapped, l0, 0),
        lane_half(s, place, swapped, l0, 1),
        spec_state[l1],
        lane_half(s, place, swapped, l1, 0),
        lane_half(s, place, swapped, l1, 1),
    );
    lemma_lane_xor(
        spec_state[l0] ^ spec_state[l1],
        lane_half(s, place, swapped, l0, 0) ^ lane_half(s, place, swapped, l1, 0),
        lane_half(s, place, swapped, l0, 1) ^ lane_half(s, place, swapped, l1, 1),
        spec_state[l2],
        lane_half(s, place, swapped, l2, 0),
        lane_half(s, place, swapped, l2, 1),
    );
    lemma_lane_xor(
        spec_state[l0] ^ spec_state[l1] ^ spec_state[l2],
        lane_half(s, place, swapped, l0, 0) ^ lane_half(s, place, swapped, l1, 0)
            ^ lane_half(s, place, swapped, l2, 0),
        lane_half(s, place, swapped, l0, 1) ^ lane_half(s, place, swapped, l1, 1)
            ^ lane_half(s, place, swapped, l2, 1),
        spec_state[l3],
        lane_half(s, place, swapped, l3, 0),
        lane_half(s, place, swapped, l3, 1),
    );
    lemma_lane_xor(
        spec_state[l0] ^ spec_state[l1] ^ spec_state[l2] ^ spec_state[l3],
        lane_half(s, place, swapped, l0, 0) ^ lane_half(s, place, swapped, l1, 0)
            ^ lane_half(s, place, swapped, l2, 0) ^ lane_half(s, place, swapped, l3, 0),
        lane_half(s, place, swapped, l0, 1) ^ lane_half(s, place, swapped, l1, 1)
            ^ lane_half(s, place, swapped, l2, 1) ^ lane_half(s, place, swapped, l3, 1),
        spec_state[l4],
        lane_half(s, place, swapped, l4, 0),
        lane_half(s, place, swapped, l4, 1),
    );
}

/// Half `z` of the implementation's `D[x]`.
///
/// `D[x] = C[x-1] ^ rot(C[x+1], 1)`, and rotating a lane by one -- the odd case
/// of the bridge with `n = 0` -- makes the even half of the rotated value the
/// old odd half rotated by one, and its odd half the old even half unchanged.
/// That is why only the even half below rotates.
pub(crate) open spec fn impl_d_half(s: KeccakState, x: int, z: int) -> u32 {
    if z == 0 {
        s.c[(x + 4) % 5].0[0] ^ rotl32(s.c[(x + 1) % 5].0[1], 1)
    } else {
        s.c[(x + 4) % 5].0[1] ^ s.c[(x + 1) % 5].0[0]
    }
}

/// The implementation's `D[x]`, computed half by half from `C`, is the
/// interleaved form of the specification's `D[x]`.
pub(crate) proof fn lemma_theta_d(s: KeccakState, spec_state: Seq<u64>, s2: KeccakState, x: int)
    requires
        0 <= x < 5,
        forall|w: int|
            0 <= w < 5 ==> #[trigger] is_lane(theta_c(spec_state, w), s.c[w].0[0], s.c[w].0[1]),
        s2.d[x].0[0] == impl_d_half(s, x, 0),
        s2.d[x].0[1] == impl_d_half(s, x, 1),
    ensures
        is_lane(theta_d(spec_state, x), s2.d[x].0[0], s2.d[x].0[1]),
{
    let xm = (x + 4) % 5;
    let xp = (x + 1) % 5;
    assert(0 <= xm < 5);
    assert(0 <= xp < 5);
    assert(is_lane(theta_c(spec_state, xm), s.c[xm].0[0], s.c[xm].0[1]));
    assert(is_lane(theta_c(spec_state, xp), s.c[xp].0[0], s.c[xp].0[1]));

    // Rotating `C[x+1]` by one: the odd case of the bridge at `n = 0`.
    lemma_lane_rotl_odd(theta_c(spec_state, xp), s.c[xp].0[0], s.c[xp].0[1], 0);
    assert(rotl32(s.c[xp].0[0], 0) == s.c[xp].0[0]);

    lemma_lane_xor(
        theta_c(spec_state, xm),
        s.c[xm].0[0],
        s.c[xm].0[1],
        rotl64(theta_c(spec_state, xp), 1),
        rotl32(s.c[xp].0[1], 1),
        s.c[xp].0[0],
    );
}

/// The whole column phase of theta: after `keccakf1600_round*_theta`, the `d`
/// accumulators hold the interleaved form of the specification's `D`.
///
/// `s2` serves as both the post-column state, whose `c` holds the column XORs,
/// and the post-`theta_d` state -- `theta_d` leaves `c` alone, so they are the
/// same state.
pub(crate) proof fn lemma_theta_cd(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
    inv: Seq<int>,
    s2: KeccakState,
)
    requires
        lifts_to_layout(s, spec_state, place, swapped),
        wf_inv(inv),
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, inv, x),
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s2.c[x].0[0] == impl_col_xor_at(s, place, swapped, inv, x, 0),
        forall|x: int|
            0 <= x < 5 ==> #[trigger] s2.c[x].0[1] == impl_col_xor_at(s, place, swapped, inv, x, 1),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s2.d[x].0[0] == impl_d_half(s2, x, 0),
        forall|x: int| 0 <= x < 5 ==> #[trigger] s2.d[x].0[1] == impl_d_half(s2, x, 1),
    ensures
        forall|x: int|
            0 <= x < 5 ==> #[trigger] is_lane(theta_d(spec_state, x), s2.d[x].0[0], s2.d[x].0[1]),
{
    assert forall|w: int| 0 <= w < 5 implies #[trigger] is_lane(
        theta_c(spec_state, w),
        s2.c[w].0[0],
        s2.c[w].0[1],
    ) by {
        lemma_theta_c(s, spec_state, place, swapped, inv, s2, w);
    }
    assert forall|x: int| 0 <= x < 5 implies #[trigger] is_lane(
        theta_d(spec_state, x),
        s2.d[x].0[0],
        s2.d[x].0[1],
    ) by {
        lemma_theta_d(s2, spec_state, s2, x);
    }
}

} // verus!
