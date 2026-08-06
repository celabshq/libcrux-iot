# Libcrux ML-KEM / DSA on RIOT-rs

This setup is based on the app template found at [https://github.com/kaspar030/riot-rs-hello].

## Dependencies

#### 1. `laze`:

```console
$ cargo install laze
```

#### 2. `probe-rs`:

```console
$ cargo install probe-rs-tools
```

## Running Benchmarks

With the device attached, run

```console
$ laze b -b nrf52840dk run
```

for a crude benchmark of ML-KEM 1024 and

```console
$ TBD (not supported yet)
```

for a crude benchmark of ML-DSA 65.
