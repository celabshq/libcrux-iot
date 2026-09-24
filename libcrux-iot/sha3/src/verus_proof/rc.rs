//! The round constants in the implementation's interleaved form.
//!
//! The implementation keeps `RC[ir]` split across two `u32` tables,
//! `RC_INTERLEAVED_0` and `RC_INTERLEAVED_1`, so that the iota step can XOR
//! them straight into the two halves of lane `A[0,0]`. This module states the
//! twenty-four entries and proves each one is the interleaved form of the
//! corresponding FIPS-202 round constant.

use vstd::prelude::*;

use super::lane_bridge::{is_lane, lane_bits_at};
use super::spec::round_constant;

verus! {

/// Even-bit half of `RC[ir]` -- the implementation's `RC_INTERLEAVED_0`.
pub open spec fn rc_interleaved_0(ir: int) -> u32 {
    seq![
        0x00000001u32, 0x00000000u32, 0x00000000u32, 0x00000000u32,
        0x00000001u32, 0x00000001u32, 0x00000001u32, 0x00000001u32,
        0x00000000u32, 0x00000000u32, 0x00000001u32, 0x00000000u32,
        0x00000001u32, 0x00000001u32, 0x00000001u32, 0x00000001u32,
        0x00000000u32, 0x00000000u32, 0x00000000u32, 0x00000000u32,
        0x00000001u32, 0x00000000u32, 0x00000001u32, 0x00000000u32,
    ][ir]
}

/// Odd-bit half of `RC[ir]` -- the implementation's `RC_INTERLEAVED_1`.
pub open spec fn rc_interleaved_1(ir: int) -> u32 {
    seq![
        0x00000000u32, 0x00000089u32, 0x8000008bu32, 0x80008080u32,
        0x0000008bu32, 0x00008000u32, 0x80008088u32, 0x80000082u32,
        0x0000000bu32, 0x0000000au32, 0x00008082u32, 0x00008003u32,
        0x0000808bu32, 0x8000000bu32, 0x8000008au32, 0x80000081u32,
        0x80000081u32, 0x80000008u32, 0x00000083u32, 0x80008003u32,
        0x80008088u32, 0x80000088u32, 0x00008000u32, 0x80008082u32,
    ][ir]
}

/// Each interleaved pair really is the FIPS-202 round constant, split by bit
/// parity. Twenty-four concrete instances, each settled by bit-blasting.
pub proof fn lemma_round_constant(ir: int)
    requires
        0 <= ir < 24,
    ensures
        is_lane(round_constant(ir), rc_interleaved_0(ir), rc_interleaved_1(ir)),
{
    if ir == 0 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000000000001u64,
            0x00000001u32,
            0x00000000u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000000000001u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000000000001u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 1 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000000008082u64,
            0x00000000u32,
            0x00000089u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000000008082u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000000008082u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00000089u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 2 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x800000000000808au64,
            0x00000000u32,
            0x8000008bu32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x800000000000808au64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x800000000000808au64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x8000008bu32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 3 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000080008000u64,
            0x00000000u32,
            0x80008080u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000080008000u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000080008000u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80008080u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 4 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x000000000000808bu64,
            0x00000001u32,
            0x0000008bu32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x000000000000808bu64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x000000000000808bu64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x0000008bu32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 5 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000080000001u64,
            0x00000001u32,
            0x00008000u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000080000001u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000080000001u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00008000u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 6 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000080008081u64,
            0x00000001u32,
            0x80008088u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000080008081u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000080008081u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80008088u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 7 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000008009u64,
            0x00000001u32,
            0x80000082u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000008009u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000008009u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80000082u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 8 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x000000000000008au64,
            0x00000000u32,
            0x0000000bu32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x000000000000008au64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x000000000000008au64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x0000000bu32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 9 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000000000088u64,
            0x00000000u32,
            0x0000000au32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000000000088u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000000000088u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x0000000au32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 10 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000080008009u64,
            0x00000001u32,
            0x00008082u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000080008009u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000080008009u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00008082u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 11 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x000000008000000au64,
            0x00000000u32,
            0x00008003u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x000000008000000au64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x000000008000000au64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00008003u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 12 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x000000008000808bu64,
            0x00000001u32,
            0x0000808bu32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x000000008000808bu64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x000000008000808bu64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x0000808bu32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 13 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x800000000000008bu64,
            0x00000001u32,
            0x8000000bu32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x800000000000008bu64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x800000000000008bu64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x8000000bu32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 14 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000008089u64,
            0x00000001u32,
            0x8000008au32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000008089u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000008089u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x8000008au32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 15 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000008003u64,
            0x00000001u32,
            0x80000081u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000008003u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000008003u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80000081u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 16 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000008002u64,
            0x00000000u32,
            0x80000081u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000008002u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000008002u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80000081u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 17 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000000080u64,
            0x00000000u32,
            0x80000008u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000000080u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000000080u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80000008u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 18 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x000000000000800au64,
            0x00000000u32,
            0x00000083u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x000000000000800au64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x000000000000800au64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00000083u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 19 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x800000008000000au64,
            0x00000000u32,
            0x80008003u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x800000008000000au64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x800000008000000au64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80008003u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 20 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000080008081u64,
            0x00000001u32,
            0x80008088u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000080008081u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000080008081u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80008088u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 21 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000000008080u64,
            0x00000000u32,
            0x80000088u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000000008080u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000000008080u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80000088u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 22 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x0000000080000001u64,
            0x00000001u32,
            0x00008000u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x0000000080000001u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000001u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x0000000080000001u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x00008000u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
    if ir == 23 {
        assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(
            0x8000000080008008u64,
            0x00000000u32,
            0x80008082u32,
            k,
        ) by {
            let t = k as u32;
            assert(((0x8000000080008008u64 >> ((2 * t) as u64)) & 1u64 == 1u64) == ((0x00000000u32 >> t) & 1u32
                == 1u32)) by (bit_vector) requires t < 32;
            assert(((0x8000000080008008u64 >> ((2 * t + 1) as u64)) & 1u64 == 1u64) == ((0x80008082u32 >> t)
                & 1u32 == 1u32)) by (bit_vector) requires t < 32;
        }
    }
}

/// The first twenty-four entries of the implementation's tables are the
/// interleaved constants stated above. Split case by case so that every index
/// into the 255-entry tables is concrete for the solver.
pub(crate) proof fn lemma_rc_table(ir: int)
    requires
        0 <= ir < 24,
    ensures
        crate::keccak::RC_INTERLEAVED_0[ir] == rc_interleaved_0(ir),
        crate::keccak::RC_INTERLEAVED_1[ir] == rc_interleaved_1(ir),
{
    if ir == 0 {
    }
    if ir == 1 {
    }
    if ir == 2 {
    }
    if ir == 3 {
    }
    if ir == 4 {
    }
    if ir == 5 {
    }
    if ir == 6 {
    }
    if ir == 7 {
    }
    if ir == 8 {
    }
    if ir == 9 {
    }
    if ir == 10 {
    }
    if ir == 11 {
    }
    if ir == 12 {
    }
    if ir == 13 {
    }
    if ir == 14 {
    }
    if ir == 15 {
    }
    if ir == 16 {
    }
    if ir == 17 {
    }
    if ir == 18 {
    }
    if ir == 19 {
    }
    if ir == 20 {
    }
    if ir == 21 {
    }
    if ir == 22 {
    }
    if ir == 23 {
    }
}

/// What the iota step needs: the pair the implementation XORs into lane
/// `A[0,0]` is the interleaved form of the FIPS-202 round constant.
pub(crate) proof fn lemma_rc_lane(ir: int)
    requires
        0 <= ir < 24,
    ensures
        is_lane(
            round_constant(ir),
            crate::keccak::RC_INTERLEAVED_0[ir],
            crate::keccak::RC_INTERLEAVED_1[ir],
        ),
{
    lemma_rc_table(ir);
    lemma_round_constant(ir);
}

} // verus!
