// C extraction:
// A couple helper functions and definitions -- this file ends up being bundled in
// libcrux_core.{c,h}, so if you need something that has to be shared across multiple mlkem
// instances / implementations, it can go in here.

use libcrux_secrets::{Classify as _, U8};

/// Pad the `slice` with `0`s at the end.
#[inline(always)]
#[cfg_attr(hax, hax_lib::requires(
    slice.len() <= LEN
))]
pub(crate) fn into_padded_array<const LEN: usize>(slice: &[U8]) -> [U8; LEN] {
    let mut out = [0u8.classify(); LEN];
    out[0..slice.len()].copy_from_slice(slice);
    out
}

#[hax_lib::requires(domain_separator <= u8::MAX - K as u8 && K <= 4)]
#[hax_lib::ensures(|result| result == domain_separator + K as u8)]
#[inline(always)]
pub(crate) fn prf_input_inc<const K: usize>(
    prf_inputs: &mut [[U8; 33]; K],
    mut domain_separator: u8,
) -> u8 {
    #[cfg(hax)]
    let _domain_separator_init = domain_separator;
    #[cfg(hax)]
    let _prf_inputs_init = prf_inputs.clone();

    for i in 0..K {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| domain_separator == _domain_separator_init + i as u8);
        prf_inputs[i][32] = domain_separator.classify();
        domain_separator += 1;
    }
    domain_separator
}

// C extraction:
//
// This is only enabled when extracting.
//
// Without these type abbreviations, the monomorphized definitions end up being inserted at the
// first location that they are used, which might be, e.g., the avx2 impl of mlkem512, resulting in
// the portable impl of mlkem512 including the header for the avx2 impl of mlkem512 to have this
// type definition in scope!
//
// To avoid that, we manually place those definitions in this file, which ends up in a shared
// header.
//
// TODO: use proper constants. They don't work right now ...
#[cfg(eurydice)]
mod extraction_helper {
    type Keypair512 = ([u8; 768], [u8; 800]);
    type Keypair768 = ([u8; 1152], [u8; 1184]);
    type Keypair1024 = ([u8; 1536], [u8; 1568]);
}
