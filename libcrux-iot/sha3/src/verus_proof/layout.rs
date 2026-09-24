//! The storage layouts the four rounds of a `keccakf1600_4rounds` pass through.
//!
//! The implementation carries out pi by relabelling where lanes live rather
//! than by moving them, and the odd rho rotations leave some lanes with their
//! halves the other way up. A round therefore reads one layout and writes
//! another. The relabelling has order four: after four rounds the layout is
//! back to the transpose it started from, which is what makes `keccakf1600`
//! sound in running `keccakf1600_4rounds` six times over.
//!
//! Every entry is read off the round's own code.

use vstd::prelude::*;

verus! {

/// The implementation lane holding each specification lane on entry to round `r`.
pub(crate) open spec fn round_place(r: int) -> Seq<int> {
    if r == 0 {
        seq![
            0int, 5int, 10int, 15int, 20int,
            1int, 6int, 11int, 16int, 21int,
            2int, 7int, 12int, 17int, 22int,
            3int, 8int, 13int, 18int, 23int,
            4int, 9int, 14int, 19int, 24int,
        ]
    } else if r == 1 {
        seq![
            0int, 6int, 12int, 18int, 24int,
            2int, 8int, 14int, 15int, 21int,
            4int, 5int, 11int, 17int, 23int,
            1int, 7int, 13int, 19int, 20int,
            3int, 9int, 10int, 16int, 22int,
        ]
    } else if r == 2 {
        seq![
            0int, 8int, 11int, 19int, 22int,
            4int, 7int, 10int, 18int, 21int,
            3int, 6int, 14int, 17int, 20int,
            2int, 5int, 13int, 16int, 24int,
            1int, 9int, 12int, 15int, 23int,
        ]
    } else if r == 3 {
        seq![
            0int, 7int, 14int, 16int, 23int,
            3int, 5int, 12int, 19int, 21int,
            1int, 8int, 10int, 17int, 24int,
            4int, 6int, 13int, 15int, 22int,
            2int, 9int, 11int, 18int, 20int,
        ]
    } else if r == 4 {
        seq![
            0int, 5int, 10int, 15int, 20int,
            1int, 6int, 11int, 16int, 21int,
            2int, 7int, 12int, 17int, 22int,
            3int, 8int, 13int, 18int, 23int,
            4int, 9int, 14int, 19int, 24int,
        ]
    } else {
        Seq::empty()
    }
}

/// Whether each specification lane is stored with its halves swapped on entry to round `r`.
pub(crate) open spec fn round_swapped(r: int) -> Seq<bool> {
    if r == 0 {
        seq![
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
        ]
    } else if r == 1 {
        seq![
            false, false, true, true, false,
            true, true, true, false, false,
            false, true, false, true, false,
            false, false, true, false, true,
            true, false, false, true, true,
        ]
    } else if r == 2 {
        seq![
            false, true, true, true, true,
            true, true, true, true, false,
            true, true, true, false, true,
            true, true, false, true, true,
            true, false, true, true, true,
        ]
    } else if r == 3 {
        seq![
            false, true, false, false, true,
            false, false, false, true, false,
            true, false, true, true, true,
            true, true, true, true, false,
            false, false, true, false, false,
        ]
    } else if r == 4 {
        seq![
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
            false, false, false, false, false,
        ]
    } else {
        Seq::empty()
    }
}

/// The specification lane held by each implementation lane on entry to round `r` -- the inverse of [`round_place`].
pub(crate) open spec fn round_inv(r: int) -> Seq<int> {
    if r == 0 {
        seq![
            0int, 5int, 10int, 15int, 20int,
            1int, 6int, 11int, 16int, 21int,
            2int, 7int, 12int, 17int, 22int,
            3int, 8int, 13int, 18int, 23int,
            4int, 9int, 14int, 19int, 24int,
        ]
    } else if r == 1 {
        seq![
            0int, 15int, 5int, 20int, 10int,
            11int, 1int, 16int, 6int, 21int,
            22int, 12int, 2int, 17int, 7int,
            8int, 23int, 13int, 3int, 18int,
            19int, 9int, 24int, 14int, 4int,
        ]
    } else if r == 2 {
        seq![
            0int, 20int, 15int, 10int, 5int,
            16int, 11int, 6int, 1int, 21int,
            7int, 2int, 22int, 17int, 12int,
            23int, 18int, 13int, 8int, 3int,
            14int, 9int, 4int, 24int, 19int,
        ]
    } else if r == 3 {
        seq![
            0int, 10int, 20int, 5int, 15int,
            6int, 16int, 1int, 11int, 21int,
            12int, 22int, 7int, 17int, 2int,
            18int, 3int, 13int, 23int, 8int,
            24int, 9int, 19int, 4int, 14int,
        ]
    } else if r == 4 {
        seq![
            0int, 5int, 10int, 15int, 20int,
            1int, 6int, 11int, 16int, 21int,
            2int, 7int, 12int, 17int, 22int,
            3int, 8int, 13int, 18int, 23int,
            4int, 9int, 14int, 19int, 24int,
        ]
    } else {
        Seq::empty()
    }
}

/// Every layout's inverse is well formed.
pub(crate) proof fn lemma_round_inv_wf(r: int)
    requires
        0 <= r < 5,
    ensures
        crate::verus_proof::theta::wf_inv(round_inv(r)),
{
    assert(round_inv(0).len() == 25);
    assert(round_inv(1).len() == 25);
    assert(round_inv(2).len() == 25);
    assert(round_inv(3).len() == 25);
    assert(round_inv(4).len() == 25);
    assert forall|p: int| 0 <= p < 25 implies 0 <= #[trigger] round_inv(r)[p] < 25 by {
    }
}

/// Every layout is 25 lanes wide.
pub(crate) proof fn lemma_round_layout_len(r: int)
    requires
        0 <= r < 5,
    ensures
        round_place(r).len() == 25,
        round_swapped(r).len() == 25,
{
}

/// Four rounds bring the layout back to where it started.
pub(crate) proof fn lemma_layout_order_four()
    ensures
        round_place(4) =~= round_place(0),
        round_swapped(4) =~= round_swapped(0),
        round_inv(4) =~= round_inv(0),
{
}

/// The layout a freshly loaded state is in is the one round 0 expects.
pub(crate) proof fn lemma_layout_initial()
    ensures
        round_place(0) =~= crate::verus_proof::state::identity_place(),
        round_swapped(0) =~= crate::verus_proof::state::no_swap(),
{
}

} // verus!
