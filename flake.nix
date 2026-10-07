{
  description = "VeriFast dev environment: native toolchain, OCaml stack and Rust nightly, all from Nix";

  inputs = {
    # Latest stable nixpkgs release
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-26.05";
    # older nixpkgs revision that specifically carries z3 4.8.5
    z3_old.url = "https://github.com/NixOS/nixpkgs/archive/60d98a51638fef1419a0df7a5e2728925dc32d28.tar.gz";
    flake-utils.url = "github:numtide/flake-utils";
    # Dated Rust nightlies (with rustc-dev), which nixpkgs does not carry.
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      z3_old,
      flake-utils,
      rust-overlay,
    }:
    flake-utils.lib.eachSystem [ "x86_64-linux" "aarch64-linux" "aarch64-darwin" ] (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        pkgsZ3 = import z3_old {
          inherit system;
        };

        llvm23 = pkgs.symlinkJoin {
          name = "vf-llvm-clang-23";
          paths = with pkgs.llvmPackages_23; [
            llvm.dev
            llvm.lib
            llvm.out
            clang-unwrapped.dev
            clang-unwrapped.lib
            clang-unwrapped
          ];
        };

        ocamlPackages = pkgs.ocaml-ng.ocamlPackages_4_14;

        # pinned version of z3 from a specific nixpkgs revision, with override needed to get ocaml bindings.
        z3 =
          (pkgsZ3.z3_4_8_5.override {
            ocamlBindings = true;
            inherit (ocamlPackages) ocaml findlib zarith;
          }).overrideAttrs
            (prev: {
              propagatedBuildInputs = (prev.propagatedBuildInputs or [ ]) ++ [ ocamlPackages.num ];
              doCheck = false;
            });

        # Not in nixpkgs. Same version and tarball hash as upstream's vfdeps.
        ppxParser = ocamlPackages.buildDunePackage rec {
          pname = "ppx_parser";
          version = "0.1.0";
          src = pkgs.fetchurl {
            url = "https://github.com/NielsMommen/ppx_parser/archive/refs/tags/${version}.tar.gz";
            sha256 = "42007eb6dfd7c6cdc02a4acae8a4d48626ba06fca4d5590aeeb1420943d0dc79";
          };
          propagatedBuildInputs = with ocamlPackages; [
            ppxlib
            camlp-streams
          ];
        };

        decoder = pkgs.rustPlatform.buildRustPackage {
          pname = "capnpc-ocaml-decoder";
          version = "0.1.0-unstable-2d6606d";
          src = pkgs.fetchFromGitHub {
            owner = "btj";
            repo = "capnpc-ocaml-decoder";
            rev = "2d6606d9b59cd0c88a66729f3f076c10c0c8e0b2";
            hash = "sha256-sZ4mfOm1ynjN+zdbvy4sM8JnAmRmjF9Oja+O8HC8oHw=";
          };
          cargoLock.lockFile = ./nix/capnpc-ocaml-decoder-Cargo.lock;
          nativeBuildInputs = [ pkgs.capnproto ];
          meta.mainProgram = "capnpc-ocaml-decoder";
        };

        buildTools =
          (with pkgs;
          [
            gnumake
            cmake
            pkg-config
            m4
            which
            capnproto
          ])
          ++ [ decoder llvm23 ]
          ++ (with ocamlPackages; [
            ocaml
            dune_3
            findlib
          ]);

        buildLibs =
          [
            ppxParser
            z3.ocaml
            z3.lib
          ]
          ++ (with ocamlPackages; [
            num
            camlp-streams
            capnp
            stdint
            dune-configurator
            zarith
          ]);

        runtimeDeps = [
          (pkgs.rust-bin.fromRustupToolchainFile ./rust-toolchain.toml)
          # coqc for bin/vfrocq; Rocq 9 no longer bundles its stdlib
          (pkgs.coq_9_0.withPackages (ps: [ ps.stdlib ]))
        ];

        ideLibs = [
          ocamlPackages.lablgtk
          pkgsZ3.gtk2
          pkgsZ3.gnome2.gtksourceview
        ];

        devTools =
          with pkgs;
          [
            ninja
            binutils
            coq_9_0 # its setup hook puts iris on COQPATH
            coqPackages_9_0.iris
          ]
          ++ (with ocamlPackages; [
            merlin
            ocaml-lsp
            ocamlformat
          ]);

        testingTools = [
          # examples/helloproc generates its (gitignored) proxy vfmanifest with an OCaml script
          ocamlPackages.ocaml
          # mysh's `ifrocq` probes for coqc with `which`
          pkgs.which
        ];


        vfEnv = {
          VF_LLVM_INSTALL_DIR = "${llvm23}";

          # Cap'n Proto env vars
          VF_VFDEPS_DIR = "${pkgs.capnproto}";
          CAPNP_INC_DIR = "${pkgs.capnproto}/include";
          CAPNP_INCLUDE = "${pkgs.capnproto}/include";
          CAPNP_LIBS = "${pkgs.capnproto}/lib";
          CAPNP_BIN = "${pkgs.capnproto}/bin";

          # read by src/dune:5; bin/verifast then finds the libz3.so copied next to it
          OCAMLOPT_CCLIB_FLAGS = "-Wl,-rpath=$ORIGIN";

          # required for first build on a fresh download
          Z3_DLL_DIR = "${z3.lib}/lib";
        };

        mkVerifast =
          withIde:
          pkgs.stdenv.mkDerivation (
            vfEnv
            // {
              pname = if withIde then "verifast-ide" else "verifast";
              meta.mainProgram = if withIde then "vfide" else "verifast";
              version = self.shortRev or "dirty";
              src = ./.;

              nativeBuildInputs =
                buildTools
                ++ runtimeDeps
                ++ [
                  pkgs.makeWrapper
                  pkgs.rustPlatform.cargoSetupHook
                ];
              buildInputs = buildLibs ++ pkgs.lib.optionals withIde ideLibs;

              cargoRoot = "src/rust_frontend/vf_mir_exporter";
              cargoDeps = pkgs.rustPlatform.importCargoLock {
                lockFile = ./src/rust_frontend/vf_mir_exporter/Cargo.lock;
              };
              dontUseCmakeConfigure = true;

              buildPhase = ''
                make -C src build
                # vfrocq would otherwise build these next to itself on first use, i.e. in the read-only store
                make -C bin/rust/rocq VfMir.vo Annotations.vo Values.vo SymbolicExecution.vo
              '';
              installPhase = ''
                mkdir $out && cp -r bin $out
                for exe in verifast vfrocq ${pkgs.lib.optionalString withIde "vfide"}; do
                  wrapProgram $out/bin/$exe --prefix PATH : ${pkgs.lib.makeBinPath runtimeDeps}
                done
              '';
            }
            // pkgs.lib.optionalAttrs (!withIde) { WITHOUT_LABLGTK = "yes"; }
          );

      in
      {
        packages = {
          default = mkVerifast false;
          verifast-ide = mkVerifast true;
          capnpc-ocaml-decoder = decoder;
          inherit llvm23;
          inherit z3;
          ppx_parser = ppxParser;
        };

        checks.testsuite = pkgs.stdenv.mkDerivation {
          name = "verifast-testsuite";
          src = ./.;
          nativeBuildInputs = [
            self.packages.${system}.default
          ]
          ++ runtimeDeps ++ testingTools;
          cargoDeps = pkgs.rustPlatform.importCargoLock {
            lockFile = ./tests/rust/purely_unsafe/httpd_mt/Cargo.lock;
          };
          postUnpack = ''
            cp -r $cargoDeps/.cargo .
            ln -s $cargoDeps cargo-vendor-dir
          '';
          buildPhase = "mysh -cpus $NIX_BUILD_CORES < testsuite.mysh";
          installPhase = "touch $out";
        };

        devShells.default = pkgs.mkShell (
          vfEnv
          // {
            name = "verifast-dev";
            packages = buildTools ++ buildLibs ++ runtimeDeps ++ ideLibs ++ devTools ++ testingTools;
          }
        );
      }
    );
}
