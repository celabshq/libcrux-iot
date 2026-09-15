//! ECDH on P-256 with the curve operations delegated to an [`EcPrimitives`] backend.
//!
//! The functions in this module mirror `crate::p256::dh_initiator` and
//! `crate::p256::dh_responder`, but perform the scalar multiplication through the
//! `embedded-cal` plumbing traits, so that it can be provided by e.g. a hardware
//! accelerator. Everything around the multiplication — private key validation and the
//! constant-time masking of an invalid scalar, and the public key validation on the
//! responder side — is the unmodified verified code from `crate::p256`.
//!
//! [`LibcruxEc`] is an [`EcPrimitives`] implementation backed by this crate's own verified
//! curve operations, mostly useful for testing a backend against a known-good reference.
//! It also works as a fallback where no accelerator is available, but note that it is
//! slower than calling `crate::p256` directly: [`EcPrimitives`] has no "multiply the base
//! point" operation, so the initiator gives up the precomputed tables of `point_mul_g` for
//! the generic `point_mul`, and [`LibcruxEc::point`] and [`LibcruxEc::multiply_scalar_point`]
//! both re-validate the point that the caller has already checked.

// The base point coordinates are the ones `crate::p256` holds in `make_g_x`/`make_g_y`, but
// those are in Montgomery form, an internal representation of that implementation and not
// what `EcPrimitives` expects. `base_point_matches_make_g` below checks the two against each
// other.
use embedded_cal::p256::{P256_GX_BYTES, P256_GY_BYTES};
use embedded_cal::plumbing::ec::{EcPrimitives, P256};
use embedded_cal::ImportError;
// The masking code below is copied verbatim from the extracted `crate::p256`, which needs
// this alias for the `unroll_for!` macro.
use libcrux_macros as krml;

/// Variant of `crate::p256::ecp256dh_i` that delegates the scalar multiplication to `ec`.
///
/// Up to and including `is_sk_valid` this is the verified code; only `point_mul_g` and
/// `point_store` are replaced by [`EcPrimitives`] operations.
// The copied code uses the extraction's naming, which is not snake case.
#[allow(non_snake_case)]
pub(crate) fn ecp256dh_i_ec<EC: EcPrimitives<P256>>(
    ec: &mut EC,
    public_key: &mut [u8],
    private_key: &[u8],
) -> bool {
    const { assert!(EC::HAS_MULTIPLY_SCALAR_POINT) };
    // The verified code sizes this at 16 words because `pk.1` took the 12-word projective
    // output of `point_mul_g`. Here nothing writes to `pk.1`, so only the 4 scalar words of
    // `pk.0` are needed; the two splits below are unchanged.
    let mut tmp: [u64; 4] = [0u64; 4usize];
    let sk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    crate::p256::bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    krml::unroll_for!(4, "i", 0u32, 1u32, {
        let uu____0: u64 = (&oneq)[i as usize];
        let x: u64 = uu____0 ^ is_b_valid & (pk.0[i as usize] ^ uu____0);
        let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
        os.1[i as usize] = x
    });
    let is_sk_valid: u64 = is_b_valid;
    // `pk.0` is the (masked) scalar; hand it and G to the `EcPrimitives` implementation
    // instead of calling `point_mul_g`, and write the resulting affine point out instead of
    // calling `point_store`.
    let mut sk_bytes: [u8; 32] = [0u8; 32usize];
    crate::p256::bn_to_bytes_be4(&mut sk_bytes, pk.0);
    let scalar = ec.import_scalar_bytes(&sk_bytes);
    let g_x = ec.import_scalar_bytes(&P256_GX_BYTES);
    let g_y = ec.import_scalar_bytes(&P256_GY_BYTES);
    let (Ok(scalar), Ok(g_x), Ok(g_y)) = (scalar, g_x, g_y) else {
        return false;
    };
    let g = ec.point(g_x, g_y);
    let p = ec.multiply_scalar_point(&scalar, &g);
    store_point(ec, public_key, &p);
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64
}

/// Variant of `crate::p256::ecp256dh_r` that delegates the scalar multiplication to `ec`.
///
/// Up to and including `is_sk_valid` this is the verified code, except that the public key
/// is validated with `aff_point_load_vartime` rather than `load_point_vartime`: the
/// projective point the latter additionally produces is only an input to `point_mul`, which
/// is what `ec` replaces here. The validation performed is the same.
// The copied code uses the extraction's naming, which is not snake case.
#[allow(non_snake_case)]
pub(crate) fn ecp256dh_r_ec<EC: EcPrimitives<P256>>(
    ec: &mut EC,
    shared_secret: &mut [u8],
    their_pubkey: &[u8],
    private_key: &[u8],
) -> bool {
    const { assert!(EC::HAS_MULTIPLY_SCALAR_POINT) };
    // The verified code sizes this at 16 words because `pk.1` took the 12-word projective
    // point from `load_point_vartime`. `aff_point_load_vartime` writes only the 8 affine
    // words, so 12 suffice; the two splits below are unchanged.
    let mut tmp: [u64; 12] = [0u64; 12usize];
    let sk: (&mut [u64], &mut [u64]) = tmp.split_at_mut(0usize);
    let pk: (&mut [u64], &mut [u64]) = sk.1.split_at_mut(4usize);
    let is_pk_valid: bool = crate::p256::aff_point_load_vartime(pk.1, their_pubkey);
    crate::p256::bn_from_bytes_be4(pk.0, private_key);
    let is_b_valid: u64 = crate::p256::bn_is_lt_order_and_gt_zero_mask4(pk.0);
    let mut oneq: [u64; 4] = [0u64; 4usize];
    (&mut oneq)[0usize] = 1u64;
    (&mut oneq)[1usize] = 0u64;
    (&mut oneq)[2usize] = 0u64;
    (&mut oneq)[3usize] = 0u64;
    krml::unroll_for!(4, "i", 0u32, 1u32, {
        let uu____0: u64 = (&oneq)[i as usize];
        let x: u64 = uu____0 ^ is_b_valid & (pk.0[i as usize] ^ uu____0);
        let os: (&mut [u64], &mut [u64]) = pk.0.split_at_mut(0usize);
        os.1[i as usize] = x
    });
    let is_sk_valid: u64 = is_b_valid;
    if is_pk_valid {
        // Their public key is on the curve, so it is safe to hand its coordinates to
        // `point`, whose contract puts that check on the caller.
        let mut sk_bytes: [u8; 32] = [0u8; 32usize];
        crate::p256::bn_to_bytes_be4(&mut sk_bytes, pk.0);
        let scalar = ec.import_scalar_bytes(&sk_bytes);
        let their_x = ec.import_scalar_bytes(&their_pubkey[0usize..32usize]);
        let their_y = ec.import_scalar_bytes(&their_pubkey[32usize..64usize]);
        let (Ok(scalar), Ok(their_x), Ok(their_y)) = (scalar, their_x, their_y) else {
            return false;
        };
        let q = ec.point(their_x, their_y);
        let ss = ec.multiply_scalar_point(&scalar, &q);
        store_point(ec, shared_secret, &ss);
    };
    is_sk_valid == 0xFFFFFFFFFFFFFFFFu64 && is_pk_valid
}

/// Writes the affine coordinates of `p` to `res` as `x || y`, the layout `point_store` uses.
///
/// # Panics
///
/// Panics if `res` is shorter than 64 bytes, and if `ec` exports a coordinate that is not 32
/// bytes long, as every P-256 backend must.
fn store_point<EC: EcPrimitives<P256>>(ec: &mut EC, res: &mut [u8], p: &EC::Point) {
    let p_x = ec.x_coord(p);
    let p_y = ec.y_coord(p);
    (res[0usize..32usize]).copy_from_slice(ec.export_scalar_bytes(&p_x).as_ref());
    (res[32usize..64usize]).copy_from_slice(ec.export_scalar_bytes(&p_y).as_ref());
}

/**
Compute the public key from the private key, using `ec` for the curve operations.

  This behaves like `crate::p256::dh_initiator`, but delegates the scalar multiplication
  to the given [`EcPrimitives`] implementation, which may be hardware accelerated.

  The function returns `true` if a private key is valid and `false` otherwise. It also
  returns `false` if `ec` rejects one of the scalars it is handed.

  The outparam `public_key`  points to 64 bytes of valid memory, i.e., uint8_t\[64\].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t\[32\].

  The private key is valid:
    • 0 < `private_key` < the order of the curve.

  # Panics

  Panics if `ec` exports a coordinate that is not 32 bytes long, as every P-256 backend
  must. Fails to compile for an `ec` whose [`EcPrimitives::HAS_MULTIPLY_SCALAR_POINT`] is
  `false`.
*/
pub fn dh_initiator_ec<EC: EcPrimitives<P256>>(
    ec: &mut EC,
    public_key: &mut [u8],
    private_key: &[u8],
) -> bool {
    ecp256dh_i_ec(ec, public_key, private_key)
}

/**
Execute the diffie-hellmann key exchange, using `ec` for the curve operations.

  This behaves like `crate::p256::dh_responder`, but delegates the scalar multiplication
  to the given [`EcPrimitives`] implementation, which may be hardware accelerated.

  The function returns `true` for successful creation of an ECDH shared secret and
  `false` otherwise. It also returns `false` if `ec` rejects one of the scalars it is
  handed.

  The outparam `shared_secret` points to 64 bytes of valid memory, i.e., uint8_t\[64\].
  The argument `their_pubkey` points to 64 bytes of valid memory, i.e., uint8_t\[64\].
  The argument `private_key` points to 32 bytes of valid memory, i.e., uint8_t\[32\].

  The function also checks whether `private_key` and `their_pubkey` are valid.

  # Panics

  Panics if `ec` exports a coordinate that is not 32 bytes long, as every P-256 backend
  must. Fails to compile for an `ec` whose [`EcPrimitives::HAS_MULTIPLY_SCALAR_POINT`] is
  `false`.
*/
pub fn dh_responder_ec<EC: EcPrimitives<P256>>(
    ec: &mut EC,
    shared_secret: &mut [u8],
    their_pubkey: &[u8],
    private_key: &[u8],
) -> bool {
    ecp256dh_r_ec(ec, shared_secret, their_pubkey, private_key)
}

/// An [`EcPrimitives`] implementation backed by this crate's verified curve operations.
///
/// Passing this to [`dh_initiator_ec`] / [`dh_responder_ec`] gives the same results as
/// `crate::p256::dh_initiator` / `crate::p256::dh_responder`, just with more conversions in
/// between, and more slowly — see the module documentation. Its purpose is to serve as a
/// reference to test accelerated backends against, and as a fallback for platforms that have
/// no accelerator.
pub struct LibcruxEc;

/// A P-256 field element, in big-endian byte order.
#[derive(Clone)]
pub struct LibcruxScalar([u8; 32]);

/// A P-256 point in affine coordinates, as `x || y` in big-endian byte order.
#[derive(Clone)]
pub struct LibcruxPoint([u8; 64]);

impl EcPrimitives<P256> for LibcruxEc {
    const HAS_MULTIPLY_SCALAR_POINT: bool = true;
    type Scalar = LibcruxScalar;
    type Point = LibcruxPoint;

    /// Performs a scalar × point multiplication on P256.
    ///
    /// The method validates that the point `b` is on the curve, but **does not** validate
    /// the scalar `a`.
    ///
    /// # Panics
    ///
    /// Panics if `b` is not a point on the curve. [`Self::point`] rejects those already; what
    /// remains for this check is the point at infinity, which an earlier multiplication may
    /// have returned.
    fn multiply_scalar_point(&mut self, a: &Self::Scalar, b: &Self::Point) -> Self::Point {
        let mut p = [0u64; 12];
        // The check is free: the projective point is needed either way.
        assert!(
            crate::p256::load_point_vartime(&mut p, &b.0),
            "point is not on the curve"
        );
        let mut scalar = [0u64; 4];
        crate::p256::bn_from_bytes_be4(&mut scalar, &a.0);
        let mut res = [0u64; 12];
        crate::p256::point_mul(&mut res, &scalar, &p);
        let mut out = [0u8; 64];
        crate::p256::point_store(&mut out, &res);
        LibcruxPoint(out)
    }

    fn import_scalar_bytes(&mut self, scalar: &[u8]) -> Result<Self::Scalar, ImportError> {
        scalar
            .try_into()
            .map(LibcruxScalar)
            .map_err(|_| ImportError)
    }

    /// # Panics
    ///
    /// Panics if `x`, `y` is not a point on the curve. Per the [`EcPrimitives::point`]
    /// contract that is the caller's responsibility.
    fn point(&mut self, x: Self::Scalar, y: Self::Scalar) -> Self::Point {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&x.0);
        out[32..].copy_from_slice(&y.0);
        let mut aff = [0u64; 8];
        assert!(
            crate::p256::aff_point_load_vartime(&mut aff, &out),
            "point is not on the curve"
        );
        LibcruxPoint(out)
    }

    fn export_scalar_bytes<'s>(&mut self, scalar: &'s Self::Scalar) -> impl AsRef<[u8]> + use<'s> {
        &scalar.0[..]
    }

    fn x_coord(&mut self, point: &Self::Point) -> Self::Scalar {
        LibcruxScalar(
            point.0[..32]
                .try_into()
                .expect("a 32 byte slice of a 64 byte array"),
        )
    }

    fn y_coord(&mut self, point: &Self::Point) -> Self::Scalar {
        LibcruxScalar(
            point.0[32..]
                .try_into()
                .expect("a 32 byte slice of a 64 byte array"),
        )
    }
}

#[cfg(test)]
mod tests {
    //! Checks the `_ec` functions against their [`crate::p256`] counterparts, using
    //! [`LibcruxEc`] as the backend.

    use super::*;

    /// The order n of the P-256 group, in big-endian byte order.
    const ORDER: [u8; 32] = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x51,
    ];

    /// Private keys to test with: `0` and `n` are invalid, the rest are valid.
    fn private_keys() -> [[u8; 32]; 5] {
        let mut one = [0u8; 32];
        one[31] = 1;
        let mut order_minus_one = ORDER;
        order_minus_one[31] -= 1;
        let mut arbitrary = [0u8; 32];
        for (i, b) in arbitrary.iter_mut().enumerate() {
            *b = (3 * i + 7) as u8;
        }
        [[0u8; 32], one, arbitrary, order_minus_one, ORDER]
    }

    /// `embedded-cal`'s base point constants must match the (Montgomery-form)
    /// `make_g_x`/`make_g_y` that the verified code multiplies by.
    #[test]
    fn base_point_matches_make_g() {
        let mut g_proj = [0u64; 12];
        crate::p256::make_base_point(&mut g_proj);
        let mut g_bytes = [0u8; 64];
        crate::p256::point_store(&mut g_bytes, &g_proj);
        assert_eq!(g_bytes[..32], P256_GX_BYTES);
        assert_eq!(g_bytes[32..], P256_GY_BYTES);
    }

    #[test]
    fn initiator_matches_dh_initiator() {
        for sk in private_keys() {
            let mut expected = [0u8; 64];
            let expected_ok = crate::p256::dh_initiator(&mut expected, &sk);

            let mut got = [0u8; 64];
            let got_ok = dh_initiator_ec(&mut LibcruxEc, &mut got, &sk);

            assert_eq!(expected_ok, got_ok, "validity mismatch for {sk:02x?}");
            assert_eq!(expected, got, "public key mismatch for {sk:02x?}");
        }
    }

    #[test]
    fn responder_matches_dh_responder() {
        // A valid peer public key, plus a point that is not on the curve.
        let mut their_pubkey = [0u8; 64];
        let mut their_sk = [0u8; 32];
        their_sk[31] = 42;
        assert!(crate::p256::dh_initiator(&mut their_pubkey, &their_sk));
        let mut off_curve = their_pubkey;
        off_curve[0] ^= 1;

        for their_pk in [their_pubkey, off_curve, [0u8; 64]] {
            for sk in private_keys() {
                let mut expected = [0u8; 64];
                let expected_ok = crate::p256::dh_responder(&mut expected, &their_pk, &sk);

                let mut got = [0u8; 64];
                let got_ok = dh_responder_ec(&mut LibcruxEc, &mut got, &their_pk, &sk);

                assert_eq!(expected_ok, got_ok, "validity mismatch for {sk:02x?}");
                assert_eq!(expected, got, "shared secret mismatch for {sk:02x?}");
            }
        }
    }

    /// The whole point of the exercise: both sides arrive at the same shared secret.
    #[test]
    fn key_exchange_agrees() {
        let mut initiator_sk = [0u8; 32];
        initiator_sk[31] = 7;
        let mut responder_sk = [0u8; 32];
        responder_sk[31] = 11;

        let mut initiator_pk = [0u8; 64];
        let mut responder_pk = [0u8; 64];
        assert!(dh_initiator_ec(
            &mut LibcruxEc,
            &mut initiator_pk,
            &initiator_sk
        ));
        assert!(dh_initiator_ec(
            &mut LibcruxEc,
            &mut responder_pk,
            &responder_sk
        ));

        let mut ss_a = [0u8; 64];
        let mut ss_b = [0u8; 64];
        assert!(dh_responder_ec(
            &mut LibcruxEc,
            &mut ss_a,
            &responder_pk,
            &initiator_sk
        ));
        assert!(dh_responder_ec(
            &mut LibcruxEc,
            &mut ss_b,
            &initiator_pk,
            &responder_sk
        ));

        assert_eq!(ss_a, ss_b);
    }
}
