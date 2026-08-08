use libcrux_iot_testutil::DefmtInfoLogger;
use libcrux_iot_testutil::*;
extern crate alloc;
use alloc::string::String;

#[cfg(feature = "mldsa44")]
use libcrux_iot_ml_dsa::ml_dsa_44 as mldsa;
#[cfg(feature = "mldsa44")]
type MLDSASignature = mldsa::MLDSA44Signature;
#[cfg(feature = "mldsa44")]
type MLDSAKeyPair = mldsa::MLDSA44KeyPair;

#[cfg(feature = "mldsa65")]
use libcrux_iot_ml_dsa::ml_dsa_65 as mldsa;
#[cfg(feature = "mldsa65")]
type MLDSASignature = mldsa::MLDSA65Signature;
#[cfg(feature = "mldsa65")]
type MLDSAKeyPair = mldsa::MLDSA65KeyPair;

#[cfg(feature = "mldsa87")]
use libcrux_iot_ml_dsa::ml_dsa_87 as mldsa;
#[cfg(feature = "mldsa87")]
type MLDSASignature = mldsa::MLDSA87Signature;
#[cfg(feature = "mldsa87")]
type MLDSAKeyPair = mldsa::MLDSA87KeyPair;

#[cfg(not(any(feature = "mldsa44", feature = "mldsa65", feature = "mldsa87")))]
compile_error!("Must select any feature of mldsa44, mldsa65, mldsa87");

struct MLDSABenchState {
    randomness_gen: [u8; 32],
    keypair: MLDSAKeyPair,
    signing_randomness: [u8; 32],
    message: [u8; 1024],
    signature: MLDSASignature,
}

fn bench_keygen<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _pair = mldsa::generate_key_pair(state.randomness_gen);
    Ok(())
}

fn bench_sign<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _signature = mldsa::sign(
        &state.keypair.signing_key,
        &state.message,
        b"",
        state.signing_randomness,
    );
    Ok(())
}

fn bench_verify<L: EventLogger>(_l: &mut L, state: &MLDSABenchState) -> Result<(), String> {
    let _ = mldsa::verify(
        &state.keypair.verification_key,
        &state.message,
        b"",
        &state.signature,
    );

    Ok(())
}

pub fn run_benchmarks<P: platform::Platform>(test_config: TestConfig<P>) {
    // set up the test suite
    let test_cases = [
        TestCase::new("bench_keygen", bench_keygen),
        TestCase::new("bench_sign", bench_sign),
        TestCase::new("bench_verify", bench_verify),
    ];

    let test_suite = TestSuite::new("ML-DSA Benchmark", &test_cases);

    // prepare the state for the benchmarked functions
    let randomness_gen = [1u8; 32];
    let keypair = mldsa::generate_key_pair(randomness_gen);
    let signing_randomness = [4u8; 32];
    let message = [5u8; 1024];
    let signature = mldsa::sign(&keypair.signing_key, &message, b"", signing_randomness).unwrap();

    let state = MLDSABenchState {
        randomness_gen,
        keypair,
        signing_randomness,
        message,
        signature,
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);
}
