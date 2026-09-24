//! The Verus proof that this implementation of SHA-3 computes the FIPS-202
//! functions -- the same claim the Lean development under `proofs/` makes,
//! rebuilt on Verus and Z3.
//!
//! The module exists only while Verus runs (`verus_keep_ghost`); everything in
//! it is specification and proof, and none of it is compiled into the library.
//! Run it with `cargo verus focus` from `libcrux-iot/sha3`.
//!
//! # Layering
//!
//! Bottom-up, mirroring the Lean tree:
//!
//! * [`lane_bridge`] relates the implementation's bit-interleaved pair of
//!   32-bit halves to a specification `u64` lane, and proves how the four
//!   operations Keccak uses -- XOR, AND, complement and rotation -- act across
//!   that bridge. Rotation splits into an even case, where each half rotates by
//!   half the amount, and an odd case, where the halves additionally swap.
//! * [`spec`] restates the FIPS-202 permutation over `Seq<u64>`, one step
//!   mapping at a time, in the same shape as `hacspec_sha3::keccak_f`.
//! * [`rc`] states the round constants in their interleaved form and proves
//!   each is the bit-parity split of the FIPS-202 constant.
//! * [`state`] lifts a whole `KeccakState` to a specification state under a
//!   storage layout: which implementation lane holds each specification lane,
//!   and whether its two halves are stored swapped. A freshly loaded state is
//!   in `identity_place`, the 5x5 transpose `T(l) = 5*(l % 5) + (l / 5)`.
//! * [`theta`] is the first step mapping built on those.
//!
//! # What is proved so far
//!
//! * The lane bridge, complete: XOR, AND, complement, and rotation by any
//!   offset the rho step uses. Discharged by Z3's bit-vector theory rather than
//!   by hand, which is why it is a few hundred lines rather than a few thousand.
//! * All twenty-four round constants, each settled by bit-blasting, and their
//!   identification with the implementation's two tables.
//! * **All four rounds of `keccakf1600_4rounds`.** Every one of their
//!   implementation functions -- ninety-two of them: per round, ten theta
//!   column functions, `theta_d`, the theta that sequences them, ten
//!   pi-rho-chi row functions and the two that sequence those -- carries a
//!   postcondition verified from its real body.
//! * [`round_pack::lemma_round_0`] and its three siblings: from a state that
//!   lifts to `spec_state` in round `r`'s layout, the round's four
//!   implementation functions leave a state that lifts to
//!   `spec::round(spec_state, ir)` in round `r+1`'s.
//! * [`four_rounds::lemma_four_rounds`], and `keccakf1600_4rounds` itself:
//!   one whole pass carries the state through all four layouts and back to the
//!   one it started in, and the function says so in its own postcondition.
//! * **`keccakf1600`: the whole Keccak-f[1600] permutation.** Its six passes
//!   are proved by a loop invariant -- after `k` passes the state lifts to `4*k`
//!   rounds of the input -- so the function's postcondition is the real claim:
//!   for every specification state the input lifts to, the output lifts to
//!   `spec::keccak_f` of it.
//!
//! Supporting those: [`prc_bridge::lemma_round_at`] unfolds
//! `iota . chi . pi . rho . theta` at any `(x, y)` on the specification side;
//! [`layout`] holds the four layouts, read off each round's own code, with
//! `lemma_layout_order_four` proving the fourth is the first again -- the
//! property that makes `keccakf1600`'s six passes over `keccakf1600_4rounds`
//! sound; and [`theta_order`] reconciles the order theta XORs a column in
//! (implementation lane order) with the specification's (`A[x,0]`, `A[x,1]`,
//! ...), which coincide only for round 0. Verus does not commute or
//! reassociate `^` on its own, so that reconciliation is sixteen bit-vector
//! queries, one per distinct permutation that arises.
//!
//! The implementation functions carry only data-flow postconditions, never
//! specification-level ones, and the bridge to the specification lives in
//! separate lemmas here. That is deliberate: it keeps proof obligations out of
//! the function bodies, which have to stay plain Rust for the hax extraction
//! that feeds the Lean development.
//!
//! # What is still assumed
//!
//! Everything above the permutation. `keccak` in `crate::keccak` is still
//! `external_body`, and `keccak_fc` there still states the equivalence with the
//! hacspec as an assumption rather than a theorem.
//!
//! # What comes next
//!
//! The byte-to-lane conversions in `crate::state` -- `load_block` and
//! `store_block`, which move between the sponge's byte view and the
//! implementation's interleaved lanes -- and then the sponge itself: absorb,
//! padding, squeeze, and the `keccak` that drives them. `keccak_fc` in
//! `crate::keccak` still states the equivalence with the hacspec as an
//! assumption rather than a theorem; that is what all of this is working
//! towards replacing.

//! # Two things learned, worth keeping for the sponge
//!
//! `proof!` and `proof_decl!` erase in non-verification builds, so ghost
//! snapshots and lemma calls belong inside function bodies where they are
//! needed -- checked against both the normal and the `--cfg hax` build. Nothing
//! about the hax extraction forces proofs out of the code.
//!
//! And a resource-limit failure is worth bisecting rather than raising the
//! limit against. Chaining four rounds looked like it needed a bigger budget;
//! the entire cost turned out to be `spec::round` being unfolded through the
//! recursion in `rounds_from`. Making `round` opaque, and revealing it in the
//! two places that want its body, took the chain from "does not return in half
//! an hour" to seconds. The same move -- opaque fact bundles per composite,
//! revealed where they are proved and where they are consumed -- is what keeps
//! `keccakf1600_4rounds` itself tractable, with twelve atomic terms in its
//! context instead of twelve hundred lane-level facts.

pub mod four_rounds;
pub mod lane_bridge;
pub mod layout;
pub mod prc;
pub mod prc_bridge;
pub mod rc;
pub mod round;
pub mod round_pack;
pub mod spec;
pub mod state;
pub mod theta;
pub mod theta_order;
