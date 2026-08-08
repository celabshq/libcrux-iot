#![no_main]
#![no_std]

use cortex_m_semihosting::debug;

#[cfg(all(feature = "board", feature = "qemu"))]
compile_error!("features `board` and `qemu` are mutually exclusive");
#[cfg(not(any(feature = "board", feature = "qemu")))]
compile_error!("enable exactly one feature of `board` (default) or `qemu`");

#[cfg(feature = "board")]
use defmt_rtt as _;
#[cfg(feature = "qemu")]
use defmt_semihosting as _;

use embassy_stm32 as _; // memory layout

use panic_probe as _;

#[cfg(feature = "stack")]
pub mod assets;
pub mod cycle_counter;
pub mod init;
#[cfg(feature = "realtime")]
pub mod real_time;
#[cfg(feature = "stack")]
pub mod stack;

#[cfg(feature = "mldsa44")]
pub use libcrux_iot_ml_dsa::ml_dsa_44 as mldsa;
#[cfg(feature = "mldsa65")]
pub use libcrux_iot_ml_dsa::ml_dsa_65 as mldsa;
#[cfg(feature = "mldsa87")]
pub use libcrux_iot_ml_dsa::ml_dsa_87 as mldsa;

#[cfg(feature = "mlkem1024")]
pub use libcrux_iot_ml_kem::mlkem1024 as mlkem;
#[cfg(feature = "mlkem512")]
pub use libcrux_iot_ml_kem::mlkem512 as mlkem;
#[cfg(feature = "mlkem768")]
pub use libcrux_iot_ml_kem::mlkem768 as mlkem;

#[cfg(not(any(feature = "mldsa44", feature = "mldsa65", feature = "mldsa87")))]
compile_error!("Must select any feature of mldsa44, mldsa65, mldsa87");

#[cfg(not(any(feature = "mlkem512", feature = "mlkem768", feature = "mlkem1024")))]
compile_error!("Must select any feature of mlkem512, mlkem768, mlkem1024");


// same panicking *behavior* as `panic-probe` but doesn't print a panic message
// this prevents the panic message being printed *twice* when `defmt::panic` is invoked
#[defmt::panic_handler]
fn panic() -> ! {
    cortex_m::asm::udf()
}

/// Terminates the application and makes a semihosting-capable debug tool exit
/// with status code 0.
pub fn exit() -> ! {
    loop {
        debug::exit(debug::EXIT_SUCCESS);
    }
}

/// Hardfault handler.
///
/// Terminates the application and makes a semihosting-capable debug tool exit
/// with an error. This seems better than the default, which is to spin in a
/// loop.
#[cortex_m_rt::exception]
unsafe fn HardFault(_frame: &cortex_m_rt::ExceptionFrame) -> ! {
    loop {
        debug::exit(debug::EXIT_FAILURE);
    }
}

// defmt-test 0.3.0 has the limitation that this `#[tests]` attribute can only be used
// once within a crate. the module can be in any file but there can only be at most
// one `#[tests]` module in this library crate
#[cfg(test)]
#[defmt_test::tests]
mod unit_tests {
    use defmt::assert;

    #[test]
    fn it_works() {
        assert!(true)
    }
}
