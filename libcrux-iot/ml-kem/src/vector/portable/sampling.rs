use crate::vector::FIELD_MODULUS;

#[hax_lib::requires(a.len() == 24 && out.len() == 16)]
#[hax_lib::ensures(|result| result <= 16 && future(out).len() == 16)]
#[inline(always)]
pub(crate) fn rej_sample(a: &[u8], out: &mut [i16]) -> usize {
    let mut sampled = 0;
    for i in 0..a.len() / 3 {
        #[cfg(hax)]
        hax_lib::loop_invariant!(|i: usize| { out.len() == 16 && sampled <= 2 * i });

        let b1 = a[i * 3 + 0] as i16;
        let b2 = a[i * 3 + 1] as i16;
        let b3 = a[i * 3 + 2] as i16;

        let d1 = ((b2 & 0xF) << 8) | b1;
        let d2 = (b3 << 4) | (b2 >> 4);

        if d1 < FIELD_MODULUS && sampled < 16 {
            out[sampled] = d1;
            sampled += 1
        }
        if d2 < FIELD_MODULUS && sampled < 16 {
            out[sampled] = d2;
            sampled += 1
        }
    }
    sampled
}
