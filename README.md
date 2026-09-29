# libcrux-iot
An IoT friendly, formally verified, crypto library based on libcrux.

The `nucleo-l4r5zi` crate is based on the app template found at [https://github.com/knurling-rs/app-template].

## Algorithms
The library provides implementations of the following cryptographic algorithms:

### SHA3
The crate `libcrux-iot-sha3` provides implementations of SHA3 and SHAKE family functions standardized in NIST publication FIPS 202.

The `libcrux-iot-sha3` crate is not yet published on crates.io.

### ML-KEM
The crate `libcrux-iot-ml-kem` provides implementations of the lattice-based ML-KEM key encapsulation mechanism standardized in NIST publication FIPS 203.

The `libcrux-iot-ml-kem` crate is not yet published on crates.io.

### ML-DSA
The crate `libcrux-iot-ml-dsa` provides implementations of the lattice-based ML-DSA digital signature algorithm standardized in NIST publication FIPS 204.

The `libcrux-iot-ml-dsa` crate is not yet published on crates.io.

## Dependencies

#### 1. `flip-link`:

```console
$ cargo install flip-link
```

#### 2. Install the target resp. toolchain

You need the following target toolchains installed, by board:

| Board         | Target toolchain            |
|---------------|-----------------------------|
| nucleo-L4R5ZI | `thumbv7em-none-eabihf`     |

#### 3. `probe-rs`:

``` console
$ # make sure to install v0.2.0 or later
$ cargo install probe-rs --features cli
```

## Running Benchmarks

With the device attached, run
```console
$ cargo rrb mlkem
```
for a crude benchmark of ML-KEM 1024 and 

```console
$ cargo rrb mldsa
```
for a crude benchmark of ML-DSA 87.

Other parameter sets are available behind `mldsa44/65` and
`mlkem512/768` features.

## Formal Verification
The implementations in this crate have received formal verification. For details on what was proven and the methodology employed, please refer to `VERIFICATION.md`.
