//! Lifting a whole `KeccakState` to the specification's flat `[u64; 25]`.
//!
//! The two sides index lanes differently. The specification puts `A[x, y]` at
//! `5*y + x`; the implementation reaches the same lane as `get_with_zeta(y, x,
//! _)`, which is `st[5*x + y]`. The two flat layouts are therefore related by
//! the 5x5 transpose `T(l) = 5*(l % 5) + (l / 5)`.

use vstd::prelude::*;

use super::lane_bridge::is_lane;
use crate::lane::Lane2U32;
use crate::state::KeccakState;

verus! {

/// The bound `Lane2U32`'s `Index` implementation needs. Verus reads a trait
/// implementation's preconditions off the trait declaration, so for `Index`
/// this extension point carries it instead.
impl vstd::std_specs::core::IndexSpecImpl<usize> for Lane2U32 {
    open spec fn index_req(&self, index: &usize) -> bool {
        *index < 2
    }
}

/// Specification lane index `l` lives at implementation index `T(l)`.
pub(crate) open spec fn transpose(idx: int) -> int {
    5 * (idx % 5) + (idx / 5)
}

/// Half `z` of specification lane `l`, read out of the implementation state
/// through the layout `(place, swapped)`.
pub(crate) open spec fn lane_half(
    s: KeccakState,
    place: Seq<int>,
    swapped: Seq<bool>,
    l: int,
    z: int,
) -> u32 {
    if swapped[l] {
        s.st[place[l]].0[1 - z]
    } else {
        s.st[place[l]].0[z]
    }
}

/// `spec_state` is the specification view of `s` under the storage layout
/// `(place, swapped)`: specification lane `l` is held in implementation lane
/// `place[l]`, with its two halves stored in swapped order when `swapped[l]`.
///
/// The implementation does not keep one fixed layout. Each round's pi step is
/// carried out by relabelling where lanes live rather than by moving them, and
/// the odd rho rotations leave some lanes with their halves the other way up.
/// The relabelling has order four, so the layout returns to `identity_layout`
/// every four of the twenty-four rounds.
pub(crate) open spec fn lifts_to_layout(
    s: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
) -> bool {
    &&& spec_state.len() == 25
    &&& place.len() == 25
    &&& swapped.len() == 25
    &&& forall|l: int|
        0 <= l < 25 ==> #[trigger] is_lane(
            spec_state[l],
            lane_half(s, place, swapped, l, 0),
            lane_half(s, place, swapped, l, 1),
        )
}

/// The layout a freshly loaded state is in: the plain transpose, no half-swaps.
pub(crate) open spec fn identity_place() -> Seq<int> {
    Seq::new(25, |l: int| transpose(l))
}

/// No lane has its halves swapped.
pub(crate) open spec fn no_swap() -> Seq<bool> {
    Seq::new(25, |l: int| false)
}

/// `spec_state` is the specification view of the implementation state `s` in
/// the layout the permutation starts and ends in.
pub(crate) open spec fn lifts_to(s: KeccakState, spec_state: Seq<u64>) -> bool {
    lifts_to_layout(s, spec_state, identity_place(), no_swap())
}

/// The lift only looks at `st`, so a step that leaves `st` alone -- theta's
/// column phase, which writes only `c` and `d` -- preserves it.
pub(crate) proof fn lemma_lifts_to_st(
    s: KeccakState,
    s2: KeccakState,
    spec_state: Seq<u64>,
    place: Seq<int>,
    swapped: Seq<bool>,
)
    requires
        lifts_to_layout(s, spec_state, place, swapped),
        s2.st == s.st,
    ensures
        lifts_to_layout(s2, spec_state, place, swapped),
{
    assert forall|l: int| 0 <= l < 25 implies #[trigger] is_lane(
        spec_state[l],
        lane_half(s2, place, swapped, l, 0),
        lane_half(s2, place, swapped, l, 1),
    ) by {
        assert(is_lane(
            spec_state[l],
            lane_half(s, place, swapped, l, 0),
            lane_half(s, place, swapped, l, 1),
        ));
    }
}

/// Specification lane `A[x, y]`, at specification index `5*y + x`, is the
/// implementation's lane `5*x + y`.
pub(crate) proof fn lemma_transpose_col(x: int, y: int)
    requires
        0 <= x < 5,
        0 <= y < 5,
    ensures
        transpose(5 * y + x) == 5 * x + y,
{
    assert((5 * y + x) % 5 == x) by (nonlinear_arith)
        requires
            0 <= x < 5,
            0 <= y < 5,
    ;
    assert((5 * y + x) / 5 == y) by (nonlinear_arith)
        requires
            0 <= x < 5,
            0 <= y < 5,
    ;
}

/// Read one lane out of the lifting relation, at the implementation index the
/// transpose sends `l` to. Stated separately so callers do not have to match
/// the quantifier's trigger by hand.
pub(crate) proof fn lemma_lift_at(s: KeccakState, spec_state: Seq<u64>, l: int)
    requires
        lifts_to(s, spec_state),
        0 <= l < 25,
    ensures
        is_lane(spec_state[l], s.st[transpose(l)].0[0], s.st[transpose(l)].0[1]),
{
    assert(is_lane(
        spec_state[l],
        lane_half(s, identity_place(), no_swap(), l, 0),
        lane_half(s, identity_place(), no_swap(), l, 1),
    ));
}

} // verus!
