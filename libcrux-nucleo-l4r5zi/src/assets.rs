pub mod mldsa_assets;
pub mod mlkem_assets;

#[cfg(feature = "mldsa44")]
pub use mldsa_assets::mldsa44 as mldsa;
#[cfg(feature = "mldsa65")]
pub use mldsa_assets::mldsa65 as mldsa;
#[cfg(feature = "mldsa87")]
pub use mldsa_assets::mldsa87 as mldsa;

#[cfg(feature = "mlkem512")]
pub use mlkem_assets::mlkem512 as mlkem;
#[cfg(feature = "mlkem768")]
pub use mlkem_assets::mlkem768 as mlkem;
#[cfg(feature = "mlkem1024")]
pub use mlkem_assets::mlkem1024 as mlkem;
