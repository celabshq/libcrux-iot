# Formal Verification in `libcrux-iot`

Our verification methodology relies on translating Rust implementation code to different proof assistants using the hax toolchain.

Overall, we follow a two-pronged approach: As a first level of assurance we establish that code cannot produce a runtime panic, a property we call runtime safety. A runtime panic can occur e.g. in debug mode builds when integer arithmetic leads to an over- or underflow, or in debug or release mode builds when an out-of-bounds memory access occurs.
As a second level of assurance, for critical parts of the code, we use hax in conjunction with the aeneas tool to translate Rust code into the Lean proof assistant. There we can perform a full functional correctness proof that proves a given piece of code is functionally equivalent to a much simpler reference implementation, also written in Rust.

## Methodology
### Runtime safety with F\*
We use hax to extract a model of the Rust source code into the F\* language. F\* operates on total functions, so when a program is successfully typechecked by the F\* type system it guarantees that there can be no runtime crashes in the program.
We have different ways of establishing safety of a given function for F\*:
When there is a potentially panicking integer arithmetic operation, we can replace this operation in the Rust source code with the corresponding non-panicking, wrapping operation, i.e. + becomes `wrapping_add` and - becomes `wrapping_sub`. This makes the arithmetic behaviour in debug build match the behaviour of release builds. An alternative to this approach is given by providing annotations that put boundedness pre-conditions on the operands of the potentially panicking operation, meaning that F\* can assume the operation will not panic, as long as the operands are within non-panicking ranges, which becomes a proof obligation for every caller of the code in question.
When there are array or slice accesses, we provide runtime safety annotations in the Rust code that encode pre-conditions on slice or index inputs which prevent out-of-bounds access. As a simple example in the following function, an index greater or equal to 5 would lead to an invalid memory access, so we provide a `hax_lib::requires` annotation that encodes that index must be less than five to avoid a runtime panic. In some cases, it is also necessary to provide post-conditions in a function to satisfy another precondition at a subsequent call-site. For these, we add `hax_lib::ensure` annotations in the Rust code, which also get translated to the F\* type system.

```Rust
#[hax_lib::requires(index < 5)]
fn example(index: usize, array: [u8; 5]) -> u8 {
	array[index]
}
```

### Functional Correctness with Lean and AI-Assisted Verification
We use hax and Aeneas to translate Rust implementation code to Lean, in order to prove functional correctness of critical portions of the implementation.
The mainline `libcrux` repository contains reference implementations of SHA3, ML-KEM and ML-DSA written in a simple, functional programming style in Rust. These reference implementations are used as executable specifcations and should therefore be easy to understand implementations of the FIPS standards without any complicating optimizations and come with extensive test coverage. For functional correctness proofs, these refernce implementations are now translated into Lean as well, again using hax and Aeneas and theorems are stated and proven in Lean which express the functional equivalence of the target functions Lean extraction to its corresponding reference implementation's Lean extraction.
The proofs for these theorems in Lean are generated using LLM assistance and checked for loopholes, such as the use of `sorry` to discharge proof obligations without providing a proof.

## Results
Some of the results summarized here are still work-in-progress and will be marked as such. Please refer to the referenced documents for each algorithm for more details on the results and their status.

### SHA3
We prove runtime safety using F* for all code in this crate, with the exception of the permutation itself.
For the Keccak permutation, we prove in Lean that it is runtime safe and functionally equivalent to an easy to understand reference implementation in Rust. In addition, we prove in Lean, that the top-level APIs for one-shot evaluation of the SHA3 functions SHA3-224, SHA3-256, SHA3-384 & SHA3-512 is are functionally equivalent to an easy to understand reference implementation in Rust. The incremental APIs that are implemented for the SHAKE-128 and SHAKE-256 functions are not part of the Lean proof.

Please refer to `libcrux-iot/sha3/VERIFICATION.md` for more details on the results and their status.

### ML-KEM
We prove runtime safety using F* for all code that is part of the implementation of the top-level module `ind_cca` which implements the high-level functionality of ML-KEM in a generic way, with the following exceptions:
- One function in the sampling module that contains a while loop.
- At the crate boundary, where ML-KEM code calls into SHA3 code, we assume that pre-conditions for SHA3 functions are met by marking the calls with the `hax_lib::opaque` annotation.
 
WIP: Starting with the critical modules implementing field arithmetic, up to NTT, inverse NTT and polynomial operations, we prove functional equivalence to an easy to understand Rust reference implementation using Lean. Crucially, the Lean proofs demonstrate that it is safe to switch to wrapping arithmetic, which simplifies runtime safety proofs.

Please refer to `libcrux-iot/ml-kem/VERIFICATION.md` for more details on the results and their status.

### ML-DSA
WIP: We prove runtime safety using F* for critical parts of the implementation, notably all low-level implementations of arithmetic operations, (de-)serialization, sampling as well as NTT and inverse NTT. In addition, we prove runtime safety for most of the high-level (de-)serialization code, with the exception of the signature (de-)serialization.

WIP: Like for ML-KEM, we use Lean to prove functional correctness of all code up to the polynomial layer.

Please refer to `libcrux-iot/ml-dsa/VERIFICATION.md` for more details on the results and their status.
