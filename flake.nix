#
#       Disclaimer: This nix environment is provided as-is.
#       None of this is officially supported and use is at your own risk.
#       We do not maintain or support nix environments.
#
{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay.url = "github:oxalica/rust-overlay";
    # Keep this revision in sync with EURYDICE_REV in [libcrux/.docker/c/Dockerfile](https://github.com/cryspen/libcrux/blob/main/.docker/c/Dockerfile),
    # which is what CI uses for the extraction.
    eurydice.url = "github:aeneasverif/eurydice/aaa9fa657fb6f09802edb890252040d94cd93982";
    eurydice.inputs.karamel.inputs.fstar.follows = "fstar-pinned";
    hax.url = "github:hacspec/hax/87ba96831ecfeb7dbb54efcf97036fbc5f25bc71";
    fstar-pinned.url = "github:FStarLang/FStar/v2025.10.06";

    # --- Lean SHA-3 proof toolchain ----------------------------------------
    # Used only by the `lean` devShell. The Lean backend now lives in mainline
    # hax (the old `aeneas-lean` backend was renamed to `lean`), so we build
    # `cargo hax` from cryspen/hax main instead of the private `hax-evit` fork
    # (no more SSH access required to evaluate the shell).
    #
    # aeneas + charon are prebuilt binaries that `cargo hax` now downloads
    # itself: as of 0.4.0 the old root `pins.toml` + `install-aeneas.sh` are
    # gone, replaced by versions embedded from `cli/cargo-hax/defaults.toml`
    # and fetched by `cargo hax tools install` (see the devShell below). The
    # tool versions are pinned workspace-wide in `libcrux-iot/hax.toml`; keep
    # them and the Lean projects' `{lean-toolchain,lakefile.toml}` in sync.
    #
    # cargo-hax v0.4.0 (release). This is the first version that (a) fills the
    # `PartialEq.ne`/`Clone.clone_from` record fields and fixes the `lane`
    # namespace shadowing itself, and (b) sets the `hax_backend_lean` cfg for the
    # Lean backend on its own — so the per-crate `hax_aeneas.py` post-processing
    # drivers are gone: each crate declares a `[scenario.<package>]` in its
    # `hax.toml` and is extracted with `cargo hax extract` (ml-kem via
    # `libcrux-iot/hax_mlkem.py`, which runs the scenario and applies its residual
    # fix-ups).
    hax-main.url = "github:cryspen/hax/f8fe69339b69e48a01b8a6a6bcb2ab5e5c5e424d";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      rust-overlay,
      eurydice,
      hax,
      fstar-pinned,
      ...
    }@inputs:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        charon = eurydice.inputs.charon;
        fstar = fstar-pinned;
        karamel = eurydice.packages.${system}.karamel;

        tools-environment = {
          CHARON_HOME = charon.packages.${system}.charon;
          EURYDICE_HOME = pkgs.runCommand "eurydice-home" { } ''
            mkdir -p $out
            cp -r ${eurydice.packages.${system}.default}/bin/eurydice $out
            cp -r ${eurydice}/include $out
          '';
          FSTAR_HOME = fstar.packages.${system}.default;
          HAX_HOME = hax;
          KRML_HOME = karamel;

          CHARON_REV = charon.rev or "dirty";
          EURYDICE_REV = eurydice.rev or "dirty";
          KRML_REV = karamel.version;
          FSTAR_REV = fstar.rev or "dirty";
          LIBCRUX_REV = self.rev or "dirty";
        };

        rustToolchain = pkgs.rust-bin.stable.latest.default.override {
          extensions = [
            "rust-src"
            "rust-analyzer"
            "llvm-tools-preview"
          ];
          # Targets needed for libcrux-nucleo-l4r5zi (real board + qemu mps2-an386).
          targets = [ "thumbv7em-none-eabihf" ];
        };

        # defmt-print decodes the rzCOBS-framed log stream that
        # libcrux-nucleo-l4r5zi emits over ARM semihosting under qemu.
        # Pinned to the 0.3.x line (defmt 0.3 compatible).
        defmt-print = pkgs.rustPlatform.buildRustPackage rec {
          pname = "defmt-print";
          version = "0.3.13";
          src = pkgs.fetchCrate {
            inherit pname version;
            hash = "sha256-j1qtHKZNMkPkAZg6Vw6bXqZjBBjkgRvLLuS8d3tJBGI=";
          };
          cargoHash = "sha256-BoDlig4uLMBcejI6AOjaoVOQ+DveTV9jn1Q3vC2bY74=";
          doCheck = false;
        };

        # --- Lean toolchain (used by devShells.lean) ------------------------
        # cargo-hax with the `lean` backend, built from the flake-locked
        # `hax-main` rev. (Built from a Nix source tree it reports its commit as
        # "unknown" in `--version`; nothing depends on that any more since the
        # `hax_aeneas.py` drivers, which grepped it, were replaced by hax.toml.)
        haxMain = inputs.hax-main.packages.${system}.default;
      in
      {
        devShells.default = pkgs.mkShell (tools-environment // {
          packages = [
            pkgs.clang_18
            pkgs.llvmPackages_18.clang-tools
            (pkgs.writeShellScriptBin "clang-format-18" ''exec ${pkgs.llvmPackages_18.clang-tools}/bin/clang-format "$@"'')
            pkgs.cmake
            pkgs.ninja
            pkgs.openssl
            pkgs.pkg-config
            pkgs.jq
            pkgs.valgrind
            pkgs.libclang
            pkgs.python3
            pkgs.cargo-bloat
            pkgs.cargo-binutils
            # `qemu-system-arm` for emulating the nucleo-l4r5zi binaries
            # (libcrux-nucleo-l4r5zi/run-qemu.sh). Pulls in all qemu system
            # emulators; if size matters this can be narrowed in the future.
            pkgs.qemu
            pkgs.flip-link
            defmt-print
            rustToolchain
            fstar.packages.${system}.default
            hax.packages.${system}.default
          ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
          LIBCLANG_PATH = "${pkgs.llvmPackages_18.libclang.lib}/lib";
        });

        # Toolchain for the Lean proofs (sha3, ml-kem, ml-dsa). Reproduces the
        # "Reproduction" sections of the
        # libcrux-iot/<crate>/proofs/lean/<Lib>/README.md files.
        #
        #   nix develop .#lean
        #
        # Extraction (Rust -> Lean; scenarios declared in the crates' hax.toml,
        # tools pinned in libcrux-iot/hax.toml):
        #   cd libcrux-iot
        #   cargo hax tools install # once: fetch pinned aeneas + charon
        #   cargo hax extract libcrux-iot-sha3 libcrux-iot-ml-dsa
        #   ./hax_mlkem.py          # = cargo hax extract libcrux-iot-ml-kem + fix-ups
        # Proving:
        #   cd libcrux-iot/<crate>/proofs/lean
        #   lake exe cache get && lake build
        devShells.lean = pkgs.mkShell {
          packages = [
            # Extraction: `cargo hax extract` drives charon + aeneas; both are
            # downloaded on first use by cargo-hax itself, or eagerly by
            # `cargo hax tools install`.
            haxMain # cargo-hax (with the lean backend)
            rustToolchain # `cargo` launcher for `cargo hax` + rust-src
            # charon (the prebuilt binary cargo-hax fetches) drives a
            # pinned rustc via rustup: with rustup on PATH it auto-installs its
            # baked toolchain (currently nightly-2026-06-01 + rustc-dev, ...)
            # and runs charon-driver under it. Without rustup charon aborts.
            pkgs.rustup
            pkgs.python3 # runs libcrux-iot/hax_mlkem.py

            # Landlock sandbox used by leanprover/comparator (sha3/proofs/lean/comparator.sh)
            # to run lean/lake/lean4export while judging the proofs against hax's generated
            # proof obligations. nixpkgs' release is older than the main-branch build
            # comparator asks for; `comparator-landrun-compat.sh` next to the script bridges
            # the difference. comparator and lean4export themselves are Lean projects;
            # build them as that script's header says.
            pkgs.landrun

            # Proving: elan provisions the pinned Lean toolchain (from the
            # lean-toolchain file) and provides `lake`.
            pkgs.elan

            # Common build deps for lake / native crates, and for the
            # `cargo hax tools install` download + extract step.
            pkgs.git
            pkgs.curl
            pkgs.gnutar
            pkgs.gzip
            pkgs.cmake
            pkgs.gmp
            pkgs.pkg-config
          ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
          # cargo-hax caches aeneas/charon under ~/.cargo/bin; make sure
          # `cargo hax extract` can find them on PATH.
          shellHook = ''
            export PATH="''${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
          '';
        };
      }
    );
}
