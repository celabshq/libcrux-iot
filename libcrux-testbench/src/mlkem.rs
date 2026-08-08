use libcrux_iot_testutil::{DefmtInfoLogger, *};
extern crate alloc;
use alloc::string::String;

struct MlKemBenchState<
    'a,
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
> {
    randomness_gen: [u8; RAND_KEYGEN_LEN],
    public_key: &'a [u8; EK_LEN],
    private_key: &'a [u8; DK_LEN],
    randomness_encaps: [u8; RAND_ENCAPS_LEN],
    ciphertext: [u8; CT_LEN],
}

fn bench_keygen<
    L: EventLogger,
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
    K: libcrux_traits::kem::arrayref::Kem<
        EK_LEN,
        DK_LEN,
        CT_LEN,
        SS_LEN,
        RAND_KEYGEN_LEN,
        RAND_ENCAPS_LEN,
    >,
>(
    _l: &mut L,
    state: &MlKemBenchState<EK_LEN, DK_LEN, CT_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN>,
) -> Result<(), String> {
    let mut dk = [0u8; DK_LEN];
    let mut ek = [0u8; EK_LEN];
    let _pair = core::hint::black_box(K::keygen(
        core::hint::black_box(&mut ek),
        core::hint::black_box(&mut dk),
        core::hint::black_box(&state.randomness_gen),
    ));
    Ok(())
}

fn bench_encaps<
    L: EventLogger,
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
    K: libcrux_traits::kem::arrayref::Kem<
        EK_LEN,
        DK_LEN,
        CT_LEN,
        SS_LEN,
        RAND_KEYGEN_LEN,
        RAND_ENCAPS_LEN,
    >,
>(
    _l: &mut L,
    state: &MlKemBenchState<EK_LEN, DK_LEN, CT_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN>,
) -> Result<(), String> {
    let mut ct = [0u8; CT_LEN];
    let mut ss = [0u8; SS_LEN];
    let _ = core::hint::black_box(K::encaps(
        core::hint::black_box(&mut ct),
        core::hint::black_box(&mut ss),
        core::hint::black_box(&state.public_key),
        core::hint::black_box(&state.randomness_encaps),
    ));
    Ok(())
}

fn bench_decaps<
    L: EventLogger,
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
    K: libcrux_traits::kem::arrayref::Kem<
        EK_LEN,
        DK_LEN,
        CT_LEN,
        SS_LEN,
        RAND_KEYGEN_LEN,
        RAND_ENCAPS_LEN,
    >,
>(
    _l: &mut L,
    state: &MlKemBenchState<EK_LEN, DK_LEN, CT_LEN, RAND_KEYGEN_LEN, RAND_ENCAPS_LEN>,
) -> Result<(), String> {
    let mut ss = [0u8; SS_LEN];
    let _ = core::hint::black_box(K::decaps(
        core::hint::black_box(&mut ss),
        core::hint::black_box(&state.ciphertext),
        core::hint::black_box(&state.private_key),
    ));

    Ok(())
}

pub fn run_benchmarks<
    P: platform::Platform,
    const EK_LEN: usize,
    const DK_LEN: usize,
    const CT_LEN: usize,
    const SS_LEN: usize,
    const RAND_KEYGEN_LEN: usize,
    const RAND_ENCAPS_LEN: usize,
    K: libcrux_traits::kem::arrayref::Kem<
        EK_LEN,
        DK_LEN,
        CT_LEN,
        SS_LEN,
        RAND_KEYGEN_LEN,
        RAND_ENCAPS_LEN,
    >,
>(
    test_config: TestConfig<P>,
    randomness_gen: [u8; RAND_KEYGEN_LEN],
    randomness_encaps: [u8; RAND_ENCAPS_LEN],
) {
    // set up the test suite
    let test_cases = [
        TestCase::new(
            "bench_keygen",
            bench_keygen::<
                DefmtInfoLogger,
                EK_LEN,
                DK_LEN,
                CT_LEN,
                SS_LEN,
                RAND_KEYGEN_LEN,
                RAND_ENCAPS_LEN,
                K,
            >,
        ),
        TestCase::new(
            "bench_encaps",
            bench_encaps::<
                DefmtInfoLogger,
                EK_LEN,
                DK_LEN,
                CT_LEN,
                SS_LEN,
                RAND_KEYGEN_LEN,
                RAND_ENCAPS_LEN,
                K,
            >,
        ),
        TestCase::new(
            "bench_decaps",
            bench_decaps::<
                DefmtInfoLogger,
                EK_LEN,
                DK_LEN,
                CT_LEN,
                SS_LEN,
                RAND_KEYGEN_LEN,
                RAND_ENCAPS_LEN,
                K,
            >,
        ),
    ];

    let test_suite = TestSuite::new("ML-KEM Benchmark", &test_cases);

    // prepare the state for the benchmarked functions
    let mut dk = [0u8; DK_LEN];
    let mut ek = [0u8; EK_LEN];
    let _ = K::keygen(&mut ek, &mut dk, &randomness_gen);
    let mut ct = [0u8; CT_LEN];
    let mut ss = [0u8; SS_LEN];
    let _ = K::encaps(&mut ct, &mut ss, &ek, &randomness_encaps);
    let state = MlKemBenchState {
        randomness_gen,
        public_key: &ek,
        private_key: &dk,
        randomness_encaps,
        ciphertext: ct,
    };

    // run the benchmark
    let mut logger = DefmtInfoLogger;
    let _ = test_suite.benchmark(&mut logger, &test_config, &state);
}
