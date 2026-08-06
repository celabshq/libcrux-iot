# Formal Verification of `libcrux-iot-ml-kem` 

## Runtime Safety with F*
We prove runtime safety for all code reachable from the `ind_cca` module, which provides generic implementations of all the KEM operations as well as public and private key validation functions, with the following exceptions:

- For the module `libcrux_iot_ml_kem::hash_functions`, which contains a hash function abstraction over calls into `libcrux_iot_sha3`, only the function signatures are extracted and the functions within it are marked with the `#[hax_lib::opaque]` attribute, thus assuming their pre-conditions are met by the callers in ML-KEM.

Above runtime safety proofs were merged with PR [#125](https://github.com/celabshq/libcrux-iot/pull/125) and [#123](https://github.com/celabshq/libcrux-iot/pull/123) and are continuously checked on CI.

## WIP: Functional Correctness with Lean
We prove functional correctness for the matrix arithmetic core of ML-KEM, implemented in the module `libcrux_iot_ml_kem::matrix`.
Concretely, we have proof for functions 
- `libcrux_iot_ml_kem::matrix::compute_As_plus_e` used in key generation
- `libcrux_iot_ml_kem::matrix::compute_vector_u` used in encapsulatin and decapsulation
- `libcrux_iot_ml_kem::matrix::compute_ring_element_v` used in encapsulation and decapsulation
- `libcrux_iot_ml_kem::matrix::compute_message` used in encapsulation and decapsulation

The proofs show that these implementations are functionally equivalent to their reference implementation at https://github.com/celabshq/libcrux/tree/a4cfb1ebf26431b2ee81f0dc19383158aaf397b7/specs/mlkem .

The proofs are pending review before they can get merged to the main branch of `libcrux-iot`. Until then the proofs can be found on branch `proofs`, which contains more details and instructions on reproducing the proofs at [/proofs/aeneas-lean/LibcruxIotMLKem/README.md](https://github.com/cryspen/libcrux-iot/blob/824842159bdcedacd6b266bde7732fae5a79a416/libcrux-iot/ml-kem/proofs/aeneas-lean/LibcruxIotMlKem/README.md?plain=1).
