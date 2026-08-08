//! ML-KEM Operations driver
//!
//! This binary just runs the ML-KEM top-level operations, which
//! should be instrumented for cycle measurement.

#![no_main]
#![no_std]

use libcrux_nucleo_l4r5zi as board; // global logger + panicking-behavior + memory layout
use libcrux_nucleo_l4r5zi::mldsa;
use libcrux_nucleo_l4r5zi::assets::mldsa as assets;

extern crate alloc;

use embedded_alloc::LlffHeap as Heap;

#[global_allocator]
static HEAP: Heap = Heap::empty();

extern "C" {
    static _stack_start: u32;
    static _stack_end: u32;
}

#[cortex_m_rt::entry]
fn main() -> ! {
    if core::hint::black_box(mldsa::verify(
        &libcrux_iot_ml_dsa::MLDSAVerificationKey::new(assets::VK),
        &assets::MSG,
        b"",
        &libcrux_iot_ml_dsa::MLDSASignature::new(assets::SIG),
    ))
    .is_ok()
    {
        defmt::trace!("OK");
    } else {
        defmt::trace!("NO");
    }

    let stack_start = core::hint::black_box(&raw const _stack_start);
    let stack_end = core::hint::black_box(&raw const _stack_end);

    core::hint::black_box(board::stack::measure(
        assets::STR_VERIFY,
        core::hint::black_box(stack_start),
        core::hint::black_box(stack_end),
    ));

    board::exit()
}
