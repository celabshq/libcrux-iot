//! The bridge between the implementation's bit-interleaved lane layout and
//! the specification's `u64` lanes.
//!
//! A lane is stored as a pair of 32-bit halves: the even-indexed bits of the
//! `u64` in one, the odd-indexed bits in the other. The lemmas here say how
//! the operations Keccak uses -- XOR, AND, complement and rotation -- act on
//! that representation, which is what lets a proof about the implementation's
//! 32-bit arithmetic be read as a proof about 64-bit lanes.

use vstd::prelude::*;

verus! {

pub open spec fn bit32(x: u32, k: int) -> bool { (x >> (k as u32)) & 1u32 == 1u32 }
pub open spec fn bit64(x: u64, k: int) -> bool { (x >> (k as u64)) & 1u64 == 1u64 }

pub open spec fn rotl32(x: u32, n: u32) -> u32 {
    if n == 0 { x } else { (x << n) | (x >> ((32 - n) as u32)) }
}
pub open spec fn rotl64(x: u64, n: u64) -> u64 {
    if n == 0 { x } else { (x << n) | (x >> ((64 - n) as u64)) }
}

pub proof fn lemma_rotl32_bit_hi(x: u32, n: u32, k: u32)
    requires n < 32, n <= k < 32,
    ensures bit32(rotl32(x, n), k as int) == bit32(x, (k - n) as int),
{
    if n != 0 {
        assert((((x << n) | (x >> ((32 - n) as u32))) >> k) & 1u32 == ((x >> ((k - n) as u32)) & 1u32))
            by (bit_vector) requires 0 < n < 32, n <= k < 32;
    }
}

pub proof fn lemma_rotl32_bit_lo(x: u32, n: u32, k: u32)
    requires n < 32, k < n,
    ensures bit32(rotl32(x, n), k as int) == bit32(x, (k + 32 - n) as int),
{
    assert((((x << n) | (x >> ((32 - n) as u32))) >> k) & 1u32 == ((x >> ((k + 32 - n) as u32)) & 1u32))
        by (bit_vector) requires 0 < n < 32, k < n;
}

pub proof fn lemma_rotl64_bit_hi(x: u64, n: u64, k: u64)
    requires n < 64, n <= k < 64,
    ensures bit64(rotl64(x, n), k as int) == bit64(x, (k - n) as int),
{
    if n != 0 {
        assert((((x << n) | (x >> ((64 - n) as u64))) >> k) & 1u64 == ((x >> ((k - n) as u64)) & 1u64))
            by (bit_vector) requires 0 < n < 64, n <= k < 64;
    }
}

pub proof fn lemma_rotl64_bit_lo(x: u64, n: u64, k: u64)
    requires n < 64, k < n,
    ensures bit64(rotl64(x, n), k as int) == bit64(x, (k + 64 - n) as int),
{
    assert((((x << n) | (x >> ((64 - n) as u64))) >> k) & 1u64 == ((x >> ((k + 64 - n) as u64)) & 1u64))
        by (bit_vector) requires 0 < n < 64, k < n;
}

/// XORing in zero changes nothing.
///
/// Stated as its own lemma rather than asserted at the use site: the bit-vector
/// tactic cannot cope with an operand that reads through an array field, and
/// crashes rather than failing.
pub proof fn lemma_xor_zero(a: u32)
    ensures
        a ^ 0u32 == a,
{
    assert(a ^ 0u32 == a) by (bit_vector);
}

/// Half `z` of a lane rotated left by `off`, in terms of the unrotated halves.
///
/// An even offset rotates each half in place by half the offset; an odd one
/// makes each half read the other, the even half picking up an extra step. The
/// rho offsets run up to 62, so `off / 2 + 1` stays below 32.
pub open spec fn rot_half(even: u32, odd: u32, off: int, z: int) -> u32 {
    if off % 2 == 0 {
        if z == 0 {
            rotl32(even, (off / 2) as u32)
        } else {
            rotl32(odd, (off / 2) as u32)
        }
    } else {
        if z == 0 {
            rotl32(odd, (off / 2 + 1) as u32)
        } else {
            rotl32(even, (off / 2) as u32)
        }
    }
}

/// Rotation across the bridge, for any offset the rho step uses.
pub proof fn lemma_lane_rotl(l: u64, e: u32, o: u32, off: int)
    requires
        is_lane(l, e, o),
        0 <= off < 63,
    ensures
        is_lane(rotl64(l, off as u64), rot_half(e, o, off, 0), rot_half(e, o, off, 1)),
{
    if off % 2 == 0 {
        let n = (off / 2) as u32;
        assert(off == 2 * n);
        lemma_lane_rotl_even(l, e, o, n);
    } else {
        let n = (off / 2) as u32;
        assert(off == 2 * n + 1);
        assert(n < 31);
        lemma_lane_rotl_odd(l, e, o, n);
    }
}

/// `u32::rotate_left` is the shift-and-or form `rotl32` names. vstd carries no
/// specification for it, so this is where the two are tied together.
#[allow(unsafe_code)]
pub assume_specification[ u32::rotate_left ](x: u32, n: u32) -> (r: u32)
    ensures
        n < 32 ==> r == rotl32(x, n),
;

/// Bit `k` of each half agrees with bits `2k` and `2k+1` of the lane.
pub open spec fn lane_bits_at(l: u64, e: u32, o: u32, k: int) -> bool {
    bit64(l, 2 * k) == bit32(e, k) && bit64(l, 2 * k + 1) == bit32(o, k)
}

/// `l` is the lane whose even-indexed bits are `e` and odd-indexed bits are `o`.
pub open spec fn is_lane(l: u64, e: u32, o: u32) -> bool {
    forall|k: int| 0 <= k < 32 ==> #[trigger] lane_bits_at(l, e, o, k)
}

/// Rotating a lane by an even amount rotates each half by half that amount.
pub proof fn lemma_lane_rotl_even(l: u64, e: u32, o: u32, n: u32)
    requires is_lane(l, e, o), n < 32,
    ensures is_lane(rotl64(l, (2 * n) as u64), rotl32(e, n), rotl32(o, n)),
{
    let r = rotl64(l, (2 * n) as u64);
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(r, rotl32(e, n), rotl32(o, n), k) by {
        assert(lane_bits_at(l, e, o, k));
        if k >= n {
            lemma_rotl64_bit_hi(l, (2 * n) as u64, (2 * k) as u64);
            lemma_rotl64_bit_hi(l, (2 * n) as u64, (2 * k + 1) as u64);
            lemma_rotl32_bit_hi(e, n, k as u32);
            lemma_rotl32_bit_hi(o, n, k as u32);
            assert(lane_bits_at(l, e, o, k - n));
        } else {
            lemma_rotl64_bit_lo(l, (2 * n) as u64, (2 * k) as u64);
            lemma_rotl64_bit_lo(l, (2 * n) as u64, (2 * k + 1) as u64);
            lemma_rotl32_bit_lo(e, n, k as u32);
            lemma_rotl32_bit_lo(o, n, k as u32);
            assert(lane_bits_at(l, e, o, k + 32 - n));
        }
    }
}

/// Rotating a lane by an odd amount `2n+1` swaps the halves: the even half of
/// the result is the old odd half rotated by `n+1`, the odd half is the old
/// even half rotated by `n`. `n < 31` covers every offset the implementation
/// uses -- the largest odd rho offset is 61, and theta rotates by 1.
pub proof fn lemma_lane_rotl_odd(l: u64, e: u32, o: u32, n: u32)
    requires is_lane(l, e, o), n < 31,
    ensures is_lane(rotl64(l, (2 * n + 1) as u64), rotl32(o, (n + 1) as u32), rotl32(e, n)),
{
    let r = rotl64(l, (2 * n + 1) as u64);
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(r, rotl32(o, (n + 1) as u32), rotl32(e, n), k) by {
        // Even bit 2k of the result: comes from bit 2(k-n-1)+1 of `l`, i.e. the
        // odd half at k-n-1, which is the odd half rotated by n+1 at k.
        if k >= n + 1 {
            lemma_rotl64_bit_hi(l, (2 * n + 1) as u64, (2 * k) as u64);
            lemma_rotl32_bit_hi(o, (n + 1) as u32, k as u32);
            assert(lane_bits_at(l, e, o, k - n - 1));
        } else {
            lemma_rotl64_bit_lo(l, (2 * n + 1) as u64, (2 * k) as u64);
            lemma_rotl32_bit_lo(o, (n + 1) as u32, k as u32);
            assert(lane_bits_at(l, e, o, k + 31 - n));
        }
        // Odd bit 2k+1 of the result: comes from bit 2(k-n) of `l`.
        if k >= n {
            lemma_rotl64_bit_hi(l, (2 * n + 1) as u64, (2 * k + 1) as u64);
            lemma_rotl32_bit_hi(e, n, k as u32);
            assert(lane_bits_at(l, e, o, k - n));
        } else {
            lemma_rotl64_bit_lo(l, (2 * n + 1) as u64, (2 * k + 1) as u64);
            lemma_rotl32_bit_lo(e, n, k as u32);
            assert(lane_bits_at(l, e, o, k + 32 - n));
        }
    }
}

pub proof fn lemma_xor_bit64(a: u64, b: u64, i: int)
    requires 0 <= i < 64,
    ensures bit64(a ^ b, i) == (bit64(a, i) != bit64(b, i)),
{
    let s = i as u64;
    assert((((a ^ b) >> s) & 1u64 == 1u64) == ((((a >> s) & 1u64 == 1u64) != ((b >> s) & 1u64 == 1u64))))
        by (bit_vector) requires s < 64;
}

pub proof fn lemma_xor_bit32(a: u32, b: u32, i: int)
    requires 0 <= i < 32,
    ensures bit32(a ^ b, i) == (bit32(a, i) != bit32(b, i)),
{
    let s = i as u32;
    assert((((a ^ b) >> s) & 1u32 == 1u32) == ((((a >> s) & 1u32 == 1u32) != ((b >> s) & 1u32 == 1u32))))
        by (bit_vector) requires s < 32;
}

pub proof fn lemma_and_bit64(a: u64, b: u64, i: int)
    requires 0 <= i < 64,
    ensures bit64(a & b, i) == (bit64(a, i) && bit64(b, i)),
{
    let s = i as u64;
    assert((((a & b) >> s) & 1u64 == 1u64) == ((((a >> s) & 1u64 == 1u64) && ((b >> s) & 1u64 == 1u64))))
        by (bit_vector) requires s < 64;
}

pub proof fn lemma_and_bit32(a: u32, b: u32, i: int)
    requires 0 <= i < 32,
    ensures bit32(a & b, i) == (bit32(a, i) && bit32(b, i)),
{
    let s = i as u32;
    assert((((a & b) >> s) & 1u32 == 1u32) == ((((a >> s) & 1u32 == 1u32) && ((b >> s) & 1u32 == 1u32))))
        by (bit_vector) requires s < 32;
}

pub proof fn lemma_not_bit64(a: u64, i: int)
    requires 0 <= i < 64,
    ensures bit64(!a, i) == !bit64(a, i),
{
    let s = i as u64;
    assert((((!a) >> s) & 1u64 == 1u64) == (!((a >> s) & 1u64 == 1u64))) by (bit_vector) requires s < 64;
}

pub proof fn lemma_not_bit32(a: u32, i: int)
    requires 0 <= i < 32,
    ensures bit32(!a, i) == !bit32(a, i),
{
    let s = i as u32;
    assert((((!a) >> s) & 1u32 == 1u32) == (!((a >> s) & 1u32 == 1u32))) by (bit_vector) requires s < 32;
}

/// XOR acts componentwise on the interleaved halves.
pub proof fn lemma_lane_xor(l1: u64, e1: u32, o1: u32, l2: u64, e2: u32, o2: u32)
    requires is_lane(l1, e1, o1), is_lane(l2, e2, o2),
    ensures is_lane(l1 ^ l2, e1 ^ e2, o1 ^ o2),
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(l1 ^ l2, e1 ^ e2, o1 ^ o2, k) by {
        assert(lane_bits_at(l1, e1, o1, k));
        assert(lane_bits_at(l2, e2, o2, k));
        lemma_xor_bit64(l1, l2, 2 * k);
        lemma_xor_bit64(l1, l2, 2 * k + 1);
        lemma_xor_bit32(e1, e2, k);
        lemma_xor_bit32(o1, o2, k);
    }
}

/// AND acts componentwise on the interleaved halves.
pub proof fn lemma_lane_and(l1: u64, e1: u32, o1: u32, l2: u64, e2: u32, o2: u32)
    requires is_lane(l1, e1, o1), is_lane(l2, e2, o2),
    ensures is_lane(l1 & l2, e1 & e2, o1 & o2),
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(l1 & l2, e1 & e2, o1 & o2, k) by {
        assert(lane_bits_at(l1, e1, o1, k));
        assert(lane_bits_at(l2, e2, o2, k));
        lemma_and_bit64(l1, l2, 2 * k);
        lemma_and_bit64(l1, l2, 2 * k + 1);
        lemma_and_bit32(e1, e2, k);
        lemma_and_bit32(o1, o2, k);
    }
}

/// Complement acts componentwise on the interleaved halves.
pub proof fn lemma_lane_not(l: u64, e: u32, o: u32)
    requires is_lane(l, e, o),
    ensures is_lane(!l, !e, !o),
{
    assert forall|k: int| 0 <= k < 32 implies #[trigger] lane_bits_at(!l, !e, !o, k) by {
        assert(lane_bits_at(l, e, o, k));
        lemma_not_bit64(l, 2 * k);
        lemma_not_bit64(l, 2 * k + 1);
        lemma_not_bit32(e, k);
        lemma_not_bit32(o, k);
    }
}


} // verus!
