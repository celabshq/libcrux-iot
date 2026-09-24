//! The pi-rho-chi step, for any output row and any storage layout.
//!
//! In FIPS-202 terms a round's output at `(x, y)` is
//! `iota(chi(pi(rho(theta(A)))))`. Because `pi` sets `A'[x, y] = A[(x + 3y) %
//! 5, x]`, each output row is a function of one selection of five input lanes,
//! and the implementation reads exactly that selection -- through whatever
//! layout the round starts in.
//!
//! The rho offset of the selected lane decides how its two interleaved halves
//! are read: an even offset rotates each half in place, an odd one makes each
//! half read the other. That is the whole content of the implementation's two
//! `zeta` functions per row.

use vstd::prelude::*;

use super::lane_bridge::rot_half;
use super::spec::rho_offset;
use super::state::lane_half;
use crate::state::KeccakState;

verus! {

/// The specification index of the lane pi brings to output `(x, y)`:
/// `A[(x + 3y) % 5, x]`, which is `5*x + (x + 3y) % 5`.
pub(crate) open spec fn prc_src(x: int, y: int) -> int {
    5 * x + (x + 3 * y) % 5
}

/// The column of `D` that theta added to it.
pub(crate) open spec fn prc_src_col(x: int, y: int) -> int {
    (x + 3 * y) % 5
}

/// The value the step derives from that lane, half `z`: the lane XORed with its
/// `D` column, then rotated by its rho offset.
///
/// `d` is not subject to the layout -- theta stores each `D[x]` with its even
/// half in slot 0 -- so only the state lane is read through `place`/`swapped`.
pub(crate) open spec fn prc_b_at(
    s: KeccakState,
    place: Seq<int>,
    swapped: Seq<bool>,
    x: int,
    y: int,
    z: int,
) -> u32 {
    rot_half(
        lane_half(s, place, swapped, prc_src(x, y), 0) ^ s.d[prc_src_col(x, y)].0[0],
        lane_half(s, place, swapped, prc_src(x, y), 1) ^ s.d[prc_src_col(x, y)].0[1],
        rho_offset(prc_src(x, y)) as int,
        z,
    )
}

/// The chi output at `(x, y)`, half `z`, before iota.
pub(crate) open spec fn prc_chi_at(
    s: KeccakState,
    place: Seq<int>,
    swapped: Seq<bool>,
    x: int,
    y: int,
    z: int,
) -> u32 {
    prc_b_at(s, place, swapped, x, y, z) ^ ((!prc_b_at(s, place, swapped, (x + 1) % 5, y, z))
        & prc_b_at(s, place, swapped, (x + 2) % 5, y, z))
}

} // verus!
