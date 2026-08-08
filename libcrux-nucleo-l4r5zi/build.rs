use std::env;
use std::fs;
use std::path::PathBuf;

fn main() {
    let out_dir = PathBuf::from(env::var_os("OUT_DIR").unwrap());
    let manifest_dir = PathBuf::from(env::var_os("CARGO_MANIFEST_DIR").unwrap());

    let source = if env::var_os("CARGO_FEATURE_QEMU").is_some() {
        manifest_dir.join("memory-qemu.x")
    } else {
        manifest_dir.join("memory-board.x")
    };

    fs::copy(&source, out_dir.join("memory.x"))
        .unwrap_or_else(|e| panic!("failed to copy {}: {e}", source.display()));

    println!("cargo:rustc-link-search={}", out_dir.display());
    println!("cargo:rerun-if-changed=memory-board.x");
    println!("cargo:rerun-if-changed=memory-qemu.x");
}
