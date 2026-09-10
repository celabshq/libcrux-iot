use libcrux_iot_aes::{
    aes_gcm_128::{Key, Nonce, Tag},
    AesGcm128,
};
use libcrux_secrets::{ClassifyRef, ClassifyRefMut, U8};

#[test]
fn test_key_centric_owned() {
    use libcrux_iot_aes::AeadConsts as _;

    let k: Key = [U8(0); AesGcm128::KEY_LEN].into();
    let nonce: Nonce = [U8(0); AesGcm128::NONCE_LEN].into();
    let mut tag: Tag = [U8(0); AesGcm128::TAG_LEN].into();

    let pt = b"the quick brown fox jumps over the lazy dog";
    let mut ct = [0; 43];
    let mut pt_out = [0; 43];

    k.encrypt(&mut ct, &mut tag, &nonce, b"", pt.classify_ref())
        .unwrap();
    k.decrypt(pt_out.classify_ref_mut(), &nonce, b"", &ct, &tag)
        .unwrap();
    assert_eq!(pt, &pt_out);
}

#[test]
fn test_key_centric_refs() {
    use libcrux_iot_aes::{Aead as _, AeadConsts as _};

    let algo = AesGcm128;

    let mut tag_bytes = [0; AesGcm128::TAG_LEN];
    let key = algo
        .new_key((&[0; AesGcm128::KEY_LEN]).classify_ref())
        .unwrap();
    let tag = algo.new_tag_mut(tag_bytes.classify_ref_mut()).unwrap();
    let nonce = algo
        .new_nonce((&[0; AesGcm128::NONCE_LEN]).classify_ref())
        .unwrap();

    let pt = b"the quick brown fox jumps over the lazy dog";
    let mut ct = [0; 43];
    let mut pt_out = [0; 43];

    key.encrypt(&mut ct, tag, nonce, b"", pt.classify_ref())
        .unwrap();
    let tag = algo.new_tag(tag_bytes.classify_ref()).unwrap();
    key.decrypt(pt_out.classify_ref_mut(), nonce, b"", &ct, tag)
        .unwrap();
    assert_eq!(pt, &pt_out);
}
