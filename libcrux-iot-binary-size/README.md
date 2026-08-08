# Binary Size

This crate collects data about the binary size impact of the different ML-KEM and ML-DSA operations with their different variants and under different optimization configurations.

To perform the measurements, run:
```shell
python3 binary_size_report.py
```

The report is written to `binary-size-report` by default. The contained `summary.md` lists the sizes of the different configurations and the `binary-size-report/bloat` directory contains the `cargo bloat` output.

*Requirements:*
- [cargo-binutils](https://crates.io/crates/cargo-binutils)
- [cargo-bloat](https://crates.io/crates/cargo-bloat)
- `thumbv7em-none-eabihf` rust target
- `llvm-tools-preview` rust toolchain component

## Methodology

To measure the binary size impact of the different variants for the reference board (`nucleo-L4R5ZI`), we build a minimal binary for the `thumbv7em-none-eabihf` (Cortex-M4) target, with no support for logging, panic handling, etc.  
We then run `rust-size` from the `cargo-binutils` project to get the sizes of the different sections for the summary. For more granular size information, we also run `cargo-bloat`.

