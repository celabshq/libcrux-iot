# Formal Verification of `libcrux-iot-ml-dsa` 

## WIP: Runtime Safety with F*
We prove runtime safety for the following modules of the implementation.

The portable implementation of the `Operations` trait, which captures the low-level implementation of central arithmetic, sampling and (de-)serialization operations:

    - `libcrux_iot_ml_dsa::simd::traits`
    - `libcrux_iot_ml_dsa::simd::portable`
    
The following high-level modules, which are generic in implementations of the `Operations` trait:

    - `libcrux_iot_ml_dsa::polynomial`
    - `libcrux_iot_ml_dsa::ntt`
    - `libcrux_iot_ml_dsa::encoding::t0`
    - `libcrux_iot_ml_dsa::encoding::t1`
    - `libcrux_iot_ml_dsa::encoding::gamma1`
    - `libcrux_iot_ml_dsa::encoding::error`
    - `libcrux_iot_ml_dsa::encoding::commitment`
    - `libcrux_iot_ml_dsa::encoding::verification_key`
    - `libcrux_iot_ml_dsa::encoding::signing_key`

This does not include the signature (de-)serialization code in `libcrux_iot_ml_dsa::encoding::signature`. An additional limitation is that calls to `libcrux-iot-sha3` functions that are part of the extraction because they appear in the call tree of a function in the modules listed above are marked with `#[hax_lib::opaque]`, thus assuming their pre-conditions are met by the callers in ML-DSA.

The proofs are pending review before they can get merged to the main branch of `libcrux-iot`. Until then, the proofs can be found on branch [jonas/mldsa-runtime-safety](https://github.com/celabshq/libcrux-iot/tree/jonas/mldsa-runtime-safety).

## WIP: Functional Correctness with Lean
We prove functional correctness for the polynomial arithmetic of ML-DSA, impelemented in module `libcrux_iot_ml_dsa::polynomial`.

The proofs show that these implementations are functionally equivalent to their reference implementation at ivalent to their reference implementation at https://github.com/celabshq/libcrux/tree/29b5688824ec92eacdf6930e6c69ed861583e2e4/specs/ml-dsa .

The proofs are pending review before they can get merged to the main branch of `libcrux-iot`. Until then the proofs can be found on branch `proofs`, which contains more details and instructions on reproducing the proofs at [proofs/aeneas-lean/LibcruxIotMlDsa/README.md](https://github.com/cryspen/libcrux-iot/blob/824842159bdcedacd6b266bde7732fae5a79a416/libcrux-iot/ml-dsa/proofs/aeneas-lean/LibcruxIotMlDsa/README.md?plain=1).

