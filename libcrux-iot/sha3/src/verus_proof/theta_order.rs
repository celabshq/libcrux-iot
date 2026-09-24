//! Reordering theta's column XOR.
//!
//! Each round's theta XORs a column in implementation lane order -- `st[5x]`,
//! `st[5x+1]`, and so on -- while the specification's `C[x]` XORs in
//! specification lane order, `A[x,0]`, `A[x,1]`, ... The layout decides how the
//! two orders relate, and only for round 0 do they coincide.
//!
//! Verus does not reassociate or commute `^` on its own, so the reordering is
//! proved here: one lemma per distinct permutation, each a single bit-vector
//! query over five fresh words, and one fact per round and column naming which
//! permutation applies.

use vstd::prelude::*;

use super::layout::round_inv;
use super::spec::{theta_c, wf_state};

verus! {

/// Five-way XOR under the permutation (0, 1, 2, 3, 4).
pub proof fn lemma_xor5_perm_01234(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a1 ^ a2 ^ a3 ^ a4,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a1 ^ a2 ^ a3 ^ a4) by (bit_vector);
}

/// Five-way XOR under the permutation (0, 2, 4, 1, 3).
pub proof fn lemma_xor5_perm_02413(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a2 ^ a4 ^ a1 ^ a3,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a2 ^ a4 ^ a1 ^ a3) by (bit_vector);
}

/// Five-way XOR under the permutation (0, 3, 1, 4, 2).
pub proof fn lemma_xor5_perm_03142(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a3 ^ a1 ^ a4 ^ a2,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a3 ^ a1 ^ a4 ^ a2) by (bit_vector);
}

/// Five-way XOR under the permutation (0, 4, 3, 2, 1).
pub proof fn lemma_xor5_perm_04321(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a4 ^ a3 ^ a2 ^ a1,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a0 ^ a4 ^ a3 ^ a2 ^ a1) by (bit_vector);
}

/// Five-way XOR under the permutation (1, 0, 4, 3, 2).
pub proof fn lemma_xor5_perm_10432(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a0 ^ a4 ^ a3 ^ a2,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a0 ^ a4 ^ a3 ^ a2) by (bit_vector);
}

/// Five-way XOR under the permutation (1, 3, 0, 2, 4).
pub proof fn lemma_xor5_perm_13024(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a3 ^ a0 ^ a2 ^ a4,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a3 ^ a0 ^ a2 ^ a4) by (bit_vector);
}

/// Five-way XOR under the permutation (1, 4, 2, 0, 3).
pub proof fn lemma_xor5_perm_14203(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a4 ^ a2 ^ a0 ^ a3,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a1 ^ a4 ^ a2 ^ a0 ^ a3) by (bit_vector);
}

/// Five-way XOR under the permutation (2, 0, 3, 1, 4).
pub proof fn lemma_xor5_perm_20314(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a0 ^ a3 ^ a1 ^ a4,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a0 ^ a3 ^ a1 ^ a4) by (bit_vector);
}

/// Five-way XOR under the permutation (2, 1, 0, 4, 3).
pub proof fn lemma_xor5_perm_21043(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a1 ^ a0 ^ a4 ^ a3,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a1 ^ a0 ^ a4 ^ a3) by (bit_vector);
}

/// Five-way XOR under the permutation (2, 4, 1, 3, 0).
pub proof fn lemma_xor5_perm_24130(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a4 ^ a1 ^ a3 ^ a0,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a2 ^ a4 ^ a1 ^ a3 ^ a0) by (bit_vector);
}

/// Five-way XOR under the permutation (3, 0, 2, 4, 1).
pub proof fn lemma_xor5_perm_30241(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a0 ^ a2 ^ a4 ^ a1,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a0 ^ a2 ^ a4 ^ a1) by (bit_vector);
}

/// Five-way XOR under the permutation (3, 1, 4, 2, 0).
pub proof fn lemma_xor5_perm_31420(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a1 ^ a4 ^ a2 ^ a0,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a1 ^ a4 ^ a2 ^ a0) by (bit_vector);
}

/// Five-way XOR under the permutation (3, 2, 1, 0, 4).
pub proof fn lemma_xor5_perm_32104(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a2 ^ a1 ^ a0 ^ a4,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a3 ^ a2 ^ a1 ^ a0 ^ a4) by (bit_vector);
}

/// Five-way XOR under the permutation (4, 1, 3, 0, 2).
pub proof fn lemma_xor5_perm_41302(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a1 ^ a3 ^ a0 ^ a2,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a1 ^ a3 ^ a0 ^ a2) by (bit_vector);
}

/// Five-way XOR under the permutation (4, 2, 0, 3, 1).
pub proof fn lemma_xor5_perm_42031(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a2 ^ a0 ^ a3 ^ a1,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a2 ^ a0 ^ a3 ^ a1) by (bit_vector);
}

/// Five-way XOR under the permutation (4, 3, 2, 1, 0).
pub proof fn lemma_xor5_perm_43210(a0: u64, a1: u64, a2: u64, a3: u64, a4: u64)
    ensures
        a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a3 ^ a2 ^ a1 ^ a0,
{
    assert(a0 ^ a1 ^ a2 ^ a3 ^ a4 == a4 ^ a3 ^ a2 ^ a1 ^ a0) by (bit_vector);
}

/// Theta's column XOR, taken in the order round `r` reads it, is the
/// specification's `C[x]`.
pub(crate) open spec fn col_order_ok(spec_state: Seq<u64>, inv: Seq<int>, x: int) -> bool {
    spec_state[inv[5 * x]] ^ spec_state[inv[5 * x + 1]] ^ spec_state[inv[5 * x + 2]] ^ spec_state[inv[5
        * x + 3]] ^ spec_state[inv[5 * x + 4]] == theta_c(spec_state, x)
}

/// Round 0's five columns.
pub(crate) proof fn lemma_col_order_0(spec_state: Seq<u64>)
    requires
        wf_state(spec_state),
    ensures
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, round_inv(0), x),
{
    assert forall|x: int| 0 <= x < 5 implies #[trigger] col_order_ok(
        spec_state,
        round_inv(0),
        x,
    ) by {
        if x == 0 {
            lemma_xor5_perm_01234(spec_state[0], spec_state[5], spec_state[10], spec_state[15], spec_state[20]);
        }
        if x == 1 {
            lemma_xor5_perm_01234(spec_state[1], spec_state[6], spec_state[11], spec_state[16], spec_state[21]);
        }
        if x == 2 {
            lemma_xor5_perm_01234(spec_state[2], spec_state[7], spec_state[12], spec_state[17], spec_state[22]);
        }
        if x == 3 {
            lemma_xor5_perm_01234(spec_state[3], spec_state[8], spec_state[13], spec_state[18], spec_state[23]);
        }
        if x == 4 {
            lemma_xor5_perm_01234(spec_state[4], spec_state[9], spec_state[14], spec_state[19], spec_state[24]);
        }
    }
}

/// Round 1's five columns.
pub(crate) proof fn lemma_col_order_1(spec_state: Seq<u64>)
    requires
        wf_state(spec_state),
    ensures
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, round_inv(1), x),
{
    assert forall|x: int| 0 <= x < 5 implies #[trigger] col_order_ok(
        spec_state,
        round_inv(1),
        x,
    ) by {
        if x == 0 {
            lemma_xor5_perm_02413(spec_state[0], spec_state[15], spec_state[5], spec_state[20], spec_state[10]);
        }
        if x == 1 {
            lemma_xor5_perm_13024(spec_state[11], spec_state[1], spec_state[16], spec_state[6], spec_state[21]);
        }
        if x == 2 {
            lemma_xor5_perm_24130(spec_state[22], spec_state[12], spec_state[2], spec_state[17], spec_state[7]);
        }
        if x == 3 {
            lemma_xor5_perm_30241(spec_state[8], spec_state[23], spec_state[13], spec_state[3], spec_state[18]);
        }
        if x == 4 {
            lemma_xor5_perm_41302(spec_state[19], spec_state[9], spec_state[24], spec_state[14], spec_state[4]);
        }
    }
}

/// Round 2's five columns.
pub(crate) proof fn lemma_col_order_2(spec_state: Seq<u64>)
    requires
        wf_state(spec_state),
    ensures
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, round_inv(2), x),
{
    assert forall|x: int| 0 <= x < 5 implies #[trigger] col_order_ok(
        spec_state,
        round_inv(2),
        x,
    ) by {
        if x == 0 {
            lemma_xor5_perm_04321(spec_state[0], spec_state[20], spec_state[15], spec_state[10], spec_state[5]);
        }
        if x == 1 {
            lemma_xor5_perm_32104(spec_state[16], spec_state[11], spec_state[6], spec_state[1], spec_state[21]);
        }
        if x == 2 {
            lemma_xor5_perm_10432(spec_state[7], spec_state[2], spec_state[22], spec_state[17], spec_state[12]);
        }
        if x == 3 {
            lemma_xor5_perm_43210(spec_state[23], spec_state[18], spec_state[13], spec_state[8], spec_state[3]);
        }
        if x == 4 {
            lemma_xor5_perm_21043(spec_state[14], spec_state[9], spec_state[4], spec_state[24], spec_state[19]);
        }
    }
}

/// Round 3's five columns.
pub(crate) proof fn lemma_col_order_3(spec_state: Seq<u64>)
    requires
        wf_state(spec_state),
    ensures
        forall|x: int| 0 <= x < 5 ==> #[trigger] col_order_ok(spec_state, round_inv(3), x),
{
    assert forall|x: int| 0 <= x < 5 implies #[trigger] col_order_ok(
        spec_state,
        round_inv(3),
        x,
    ) by {
        if x == 0 {
            lemma_xor5_perm_03142(spec_state[0], spec_state[10], spec_state[20], spec_state[5], spec_state[15]);
        }
        if x == 1 {
            lemma_xor5_perm_20314(spec_state[6], spec_state[16], spec_state[1], spec_state[11], spec_state[21]);
        }
        if x == 2 {
            lemma_xor5_perm_42031(spec_state[12], spec_state[22], spec_state[7], spec_state[17], spec_state[2]);
        }
        if x == 3 {
            lemma_xor5_perm_14203(spec_state[18], spec_state[3], spec_state[13], spec_state[23], spec_state[8]);
        }
        if x == 4 {
            lemma_xor5_perm_31420(spec_state[24], spec_state[9], spec_state[19], spec_state[4], spec_state[14]);
        }
    }
}

} // verus!
