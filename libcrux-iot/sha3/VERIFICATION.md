# Formal Verification of `libcrux-iot-sha3`

## Runtime Safety with F*
We prove runtime safety for all code reachable via public APIs, including for the `unbuffered-xof` feature, with the assumption that the implementation of the Keccak permutation itself is free of panics. This is achieved by marking the Keccak permutation entrypoint, the internal function `libcrux_iot_sha3::keccakf1600` as well as all functions in its call-tree with the `hax_lib::opaque` attribute, which exempts them from extraction to F* (but not to Lean). One more exception to panic freedom is the implementation of the `Debug` trait on an internal data structure due to limitations in hax.

Above runtime safety proofs have been merged with PR [#153](https://github.com/celabshq/libcrux-iot/pull/153) and are continuously checked on CI.

## Functional Correctness with Lean
We prove functional equivalence of the Keccak implementation function `libcrux_iot_sha3::keccak::keccak` to the reference implementation at  https://github.com/celabshq/libcrux/tree/8470b57c228f12c81b27eb5abcba298729a72826/specs/sha3 .
Derived from this, we prove functional correctness of the public API functions `shake128`, `shake256`, `sha224_ema`, `sha256_ema`, `sha384_ema` and `sha512_ema` which compute SHA3 and SHAKE family functions in a one-shot way by calling `libcrux_iot_sha3::keccak::keccak` with the correct rate and delimiter constants. We do *not* prove functional correctness of other parts of the public API, such as the incremental APIs or the provided `libcrux-traits` APIs.

The functional correctness proof were merged with PR [#161](https://github.com/celabshq/libcrux-iot/pull/161). For more details on the proofs and how to reproduce them please refer to [`/proofs/aeneas-lean/LibcruxIotSha3/README.md`](https://github.com/celabshq/libcrux-iot/blob/main/libcrux-iot/sha3/proofs/aeneas-lean/LibcruxIotSha3/README.md).
