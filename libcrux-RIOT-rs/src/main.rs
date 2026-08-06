#![no_main]
#![no_std]
#![feature(type_alias_impl_trait)]
#![feature(used_with_arg)]

use riot_rs::{
    bench::benchmark,
    debug::{exit, log::info},
};

use libcrux_ml_kem::mlkem1024 as mlkem;

const US_PER_TICK: f32 = 0.0125f32;

#[riot_rs::thread(autostart, stacksize = 65535)]
fn main() {
    let randomness_gen = [1u8; libcrux_ml_kem::KEY_GENERATION_SEED_SIZE];

    info!("Generating 1 key pairs");

    let ticks = benchmark(1, || {
        let _ = mlkem::generate_key_pair(randomness_gen);
        // Insert the function to benchmark here.
        // Consider using `core::hint::black_box()` where necessary.
    })
    .unwrap();

    let time_keygen_avg = ticks as f32 * US_PER_TICK;
    info!(
        "Took {=f32} µs to generate key pair on average",
        time_keygen_avg
    );

    let pair = mlkem::generate_key_pair(randomness_gen);
    let randomness_encaps = [2u8; libcrux_ml_kem::ENCAPS_SEED_SIZE];
    info!("Encapsulating 1 times.");

    let ticks = benchmark(1, || {
        let _ = mlkem::encapsulate(pair.public_key(), randomness_encaps);
    })
    .unwrap();

    let time_encaps_avg = ticks as f32 * US_PER_TICK;
    info!("Took {=f32} µs to encapsulate on average", time_encaps_avg);

    let (ct, ss) = mlkem::encapsulate(pair.public_key(), randomness_encaps);

    info!("Decapsulating 1 times.");
    let ticks = benchmark(1, || {
        let _ = mlkem::decapsulate(pair.private_key(), &ct);
    })
    .unwrap();

    let time_decaps_avg = ticks as f32 * US_PER_TICK;
    info!("Took {=f32} µs to decapsulate on average", time_decaps_avg);

    let ss_decaps = mlkem::decapsulate(pair.private_key(), &ct);
    assert_eq!(ss, ss_decaps);

    exit(Ok(()));
}
