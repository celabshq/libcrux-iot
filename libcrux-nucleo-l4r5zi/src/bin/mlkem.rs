#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi::{self as board, init::ClockConfig}; // global logger + panicking-behavior + memory layout
use rand_core::RngCore;

extern crate alloc;

/// Macro to simplify cfg gating
#[allow(unused_macros)]
macro_rules! cfg {
    ($feature:literal, $($item:item)*) => {
        $(
            #[cfg(feature = $feature)]
            $item
        )*
    }
}

use embedded_alloc::LlffHeap as Heap;

const SS_LEN: usize = 32;
const RAND_KEYGEN_LEN: usize = libcrux_iot_ml_kem::KEY_GENERATION_SEED_SIZE;
const RAND_ENCAPS_LEN: usize = libcrux_iot_ml_kem::ENCAPS_SEED_SIZE;

cfg! {
    "mlkem512",
    use libcrux_iot_ml_kem::mlkem512::MlKem512 as MlKem;
    const EK_LEN: usize = 800;
    const DK_LEN: usize = 1632;
    const CT_LEN: usize = 768;
}
cfg! {
    "mlkem768",
    use libcrux_iot_ml_kem::mlkem768::MlKem768 as MlKem;
    const EK_LEN: usize = 1184;
    const DK_LEN: usize = 2400;
    const CT_LEN: usize = 1088;
}
cfg! {
    "mlkem1024",
    use libcrux_iot_ml_kem::mlkem1024::MlKem1024 as MlKem;
    const EK_LEN: usize = 1568;
    const DK_LEN: usize = 3168;
    const CT_LEN: usize = 1568;
}

#[global_allocator]
static HEAP: Heap = Heap::empty();

#[cortex_m_rt::entry]
fn main() -> ! {
    use libcrux_iot_testutil::*;
    // Initialize the allocator BEFORE you use it
    board::init::initialize_allocator(&HEAP);

    // Set up the system clock.
    let clock_config = ClockConfig::CycleBenchmark;
    let p = board::init::setup_clock(clock_config);

    // set up the test config
    let test_config = TestConfig {
        platform: platform::CortexM,
        core_freq: clock_config.core_freq(),
        only_names: alloc::vec![],
        early_abort: false,
        benchmark_runs: 5,
    };

    let mut rng = board::init::init_rng(p);
    let mut randomness_gen = [0u8; RAND_KEYGEN_LEN];
    let mut randomness_encaps = [0u8; RAND_ENCAPS_LEN];

    rng.fill_bytes(&mut randomness_gen);
    rng.fill_bytes(&mut randomness_encaps);

    libcrux_testbench::mlkem::run_benchmarks::<
        platform::CortexM,
        EK_LEN,
        DK_LEN,
        CT_LEN,
        SS_LEN,
        RAND_KEYGEN_LEN,
        RAND_ENCAPS_LEN,
        MlKem,
    >(test_config, randomness_gen, randomness_encaps);

    board::exit()
}
