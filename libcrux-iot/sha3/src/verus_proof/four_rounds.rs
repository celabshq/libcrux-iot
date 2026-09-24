//! Four rounds -- one pass of `keccakf1600_4rounds`.
//!
//! The four rounds carry the state through the four layouts and back to the one
//! they started in, which is what lets `keccakf1600` run this pass six times
//! over. Each round is discharged by its own lemma, so this chain never holds
//! more than one round's facts at a time.

use vstd::prelude::*;

use super::layout::{lemma_layout_initial, round_place, round_swapped};
use super::round_pack::{
    lemma_round_0, lemma_round_1, lemma_round_2, lemma_round_3, prc_facts_0, prc_facts_1,
    prc_facts_2, prc_facts_3, theta_facts_0, theta_facts_1, theta_facts_2, theta_facts_3,
};
use super::spec::{lemma_round_wf, lemma_rounds_from_4, round, rounds_from, wf_state};
use super::state::{lifts_to, lifts_to_layout};
use crate::state::KeccakState;

verus! {

/// One pass of `keccakf1600_4rounds`, from the states it passes through.
///
/// `a<k>` is the state entering round `k`, `a<k>t` the state after its theta,
/// and `a<k>h` the state between its two pi-rho-chi halves.
#[verifier::rlimit(200)]
#[verifier::spinoff_prover]
pub(crate) proof fn lemma_four_rounds(
    spec_state: Seq<u64>,
    a0: KeccakState,
    a0t: KeccakState,
    a0h: KeccakState,
    a1: KeccakState,
    a1t: KeccakState,
    a1h: KeccakState,
    a2: KeccakState,
    a2t: KeccakState,
    a2h: KeccakState,
    a3: KeccakState,
    a3t: KeccakState,
    a3h: KeccakState,
    a4: KeccakState,
    ir: int,
)
    requires
        0 <= ir && ir + 4 <= 24,
        wf_state(spec_state),
        lifts_to(a0, spec_state),
        theta_facts_0(a0, a0t),
        prc_facts_0(a0t, a0h, a1, ir),
        theta_facts_1(a1, a1t),
        prc_facts_1(a1t, a1h, a2, ir + 1),
        theta_facts_2(a2, a2t),
        prc_facts_2(a2t, a2h, a3, ir + 2),
        theta_facts_3(a3, a3t),
        prc_facts_3(a3t, a3h, a4, ir + 3),
    ensures
        lifts_to(a4, rounds_from(spec_state, ir, 4)),
{
    lemma_layout_initial();
    assert(lifts_to_layout(a0, spec_state, round_place(0), round_swapped(0)));

    let t1 = round(spec_state, ir);
    let t2 = round(t1, ir + 1);
    let t3 = round(t2, ir + 2);
    let t4 = round(t3, ir + 3);
    lemma_round_wf(spec_state, ir);
    lemma_round_wf(t1, ir + 1);
    lemma_round_wf(t2, ir + 2);
    lemma_round_wf(t3, ir + 3);

    lemma_round_0(spec_state, a0, a0t, a0h, a1, ir);
    lemma_round_1(t1, a1, a1t, a1h, a2, ir + 1);
    lemma_round_2(t2, a2, a2t, a2h, a3, ir + 2);
    lemma_round_3(t3, a3, a3t, a3h, a4, ir + 3);

    lemma_rounds_from_4(spec_state, ir);
}

} // verus!
