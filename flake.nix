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
    # aeneas + charon are consumed as the prebuilt binaries pinned by hax in its
    # `pins.toml`; run `install-aeneas` inside `nix develop .#lean` to fetch them
    # (see the devShell below). Keep this revision in sync with
    # `libcrux-iot/sha3/hax_aeneas.py` and the Lean project's
    # `{lean-toolchain,lakefile.toml}`.
    hax-main.url = "github:cryspen/hax/2fedcb2b196f5adea55975d0a023596ec6383ff2";
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
          ];
        };

        # --- Lean toolchain (used by devShells.lean) ------------------------
        # `cargo hax` bakes its commit into the binary at build time (via
        # `env!("HAX_GIT_COMMIT_HASH")`). Built from a Nix source tree (no
        # `.git`) it reports "unknown", so the version check in `hax_aeneas.py`
        # would fail. We wrap it so `cargo hax --version` reports the
        # flake-locked rev — the exact source Nix built — and pass every other
        # invocation straight through. The reported value is taken from the
        # lock, so it cannot drift from what is actually built.
        haxMainPkg = inputs.hax-main.packages.${system}.default;
        haxMainRev = inputs.hax-main.rev;
        # `cargo hax --version` (clap long-version) is what the script greps for
        # `commit=<rev>`; everything else passes through to the real binary.
        haxVersionScript = pkgs.writeShellScript "cargo-hax" ''
          case " $* " in
            *" --version "*)
              echo "hax"
              echo "commit=${haxMainRev}"
              exit 0
              ;;
          esac
          exec ${haxMainPkg}/bin/cargo-hax "$@"
        '';
        haxMain = pkgs.symlinkJoin {
          name = "hax-main-version-wrapped";
          paths = [ haxMainPkg ];
          postBuild = ''
            rm -f $out/bin/cargo-hax
            install -m555 ${haxVersionScript} $out/bin/cargo-hax
          '';
        };

        # `install-aeneas` fetches the prebuilt aeneas + charon binaries pinned
        # by hax (in its `pins.toml`) into ~/.cargo/bin. It is a thin wrapper
        # around the script shipped in the hax source tree, so the aeneas/charon
        # pins stay in lock-step with the `cargo hax` built above.
        installAeneas = pkgs.writeShellScriptBin "install-aeneas" ''
          exec ${inputs.hax-main}/install-aeneas.sh "$@"
        '';
      in
      {
        devShells.default = pkgs.mkShell (
          tools-environment
          // {
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
              pkgs.cargo-nextest
              rustToolchain
              fstar.packages.${system}.default
              hax.packages.${system}.default
            ];
            RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
            LIBCLANG_PATH = "${pkgs.llvmPackages_18.libclang.lib}/lib";
          }
        );

        # Toolchain for the SHA-3 Lean proof. Reproduces the "Reproduction"
        # section of
        # libcrux-iot/sha3/proofs/lean/LibcruxIotSha3/README.md.
        #
        #   nix develop .#lean
        #
        # Extraction (Rust -> Lean):
        #   cd libcrux-iot/sha3
        #   install-aeneas          # once: fetch pinned aeneas + charon
        #   ./hax_aeneas.py
        # Proving:
        #   cd libcrux-iot/sha3/proofs/lean
        #   lake exe cache get && lake build
        devShells.lean = pkgs.mkShell {
          packages = [
            # Extraction: `cargo hax into lean` drives charon + aeneas.
            # cargo-hax is version-wrapped (see the `let` block) so the version
            # check in hax_aeneas.py passes against the flake-locked rev; aeneas
            # and charon are fetched as prebuilt binaries by `install-aeneas`.
            haxMain # cargo-hax (with the lean backend)
            installAeneas # fetches pinned aeneas + charon into ~/.cargo/bin
            rustToolchain # `cargo` launcher for `cargo hax` + rust-src
            # charon (the prebuilt binary fetched by `install-aeneas`) drives a
            # pinned rustc via rustup: with rustup on PATH it auto-installs its
            # baked toolchain (currently nightly-2026-06-01 + rustc-dev, ...)
            # and runs charon-driver under it. Without rustup charon aborts.
            pkgs.rustup
            pkgs.python3 # runs hax_aeneas.py

            # Proving: elan provisions the pinned Lean toolchain (from the
            # lean-toolchain file) and provides `lake`.
            pkgs.elan

            # Common build deps for lake / native crates, and for the
            # `install-aeneas` download + extract step.
            pkgs.git
            pkgs.curl
            pkgs.gnutar
            pkgs.gzip
            pkgs.cmake
            pkgs.gmp
            pkgs.pkg-config
          ];
          RUST_SRC_PATH = "${rustToolchain.outPath}/lib/rustlib/src/rust/library";
          # `install-aeneas` drops aeneas/charon in ~/.cargo/bin; make sure
          # `cargo hax into lean` can find them on PATH.
          shellHook = ''
            export PATH="''${CARGO_HOME:-$HOME/.cargo}/bin:$PATH"
          '';
        };
      }
    );
}
