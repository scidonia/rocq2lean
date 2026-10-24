{
  description = "rocq2lean — carry the automatically translatable fragment of Rocq into Lean 4";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";

    flake-parts.url = "github:hercules-ci/flake-parts";

    treefmt-nix.url = "github:numtide/treefmt-nix";
    treefmt-nix.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    inputs@{ flake-parts, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [
        "x86_64-linux"
        "aarch64-linux"
      ];

      imports = [ inputs.treefmt-nix.flakeModule ];

      perSystem =
        { config, pkgs, ... }:
        let
          # One Rocq, named once. The extractor is an OCaml program that links
          # Rocq's own kernel, so the compiler that builds it must be the one
          # Rocq was built with; `rocq-core` in nixpkgs is an OCaml 4.14 build.
          rocq = pkgs.rocqPackages.rocq-core;
          # `rocq-core` carries the prelude; the standard library is its own
          # package, installed under a versioned directory. Sources import it as
          # `Stdlib.*`, which is why the physical root is `user-contrib`.
          stdlib = pkgs.rocqPackages.stdlib;
          coqVersion = builtins.head (
            builtins.filter (n: (builtins.readDir "${stdlib}/lib/coq").${n} == "directory") (
              builtins.attrNames (builtins.readDir "${stdlib}/lib/coq")
            )
          );
          stdlibRoot = "${stdlib}/lib/coq/${coqVersion}/user-contrib";
          ocaml = pkgs.ocaml-ng.ocamlPackages_4_14;

          shell = pkgs.mkShell {
            name = "rocq2lean";

            packages = [
              pkgs.lean4
              ocaml.ocaml
              ocaml.dune_3
              ocaml.findlib
              rocq
              stdlib
              pkgs.git
              pkgs.jq
              pkgs.coreutils
              config.treefmt.build.wrapper
            ];

            shellHook = ''
              # `rocq-core` installs its findlib packages under `$out/lib`, so
              # the extractor's `(libraries rocq-runtime.*)` resolves from here
              # and nowhere else: no host opam switch leaks in.
              export OCAMLPATH="${rocq}/lib''${OCAMLPATH:+:$OCAMLPATH}"
              # The standard library is found by logical name, so its physical
              # root goes on Rocq's own search path; `ROCQPATH` is read by the
              # same initialisation the extractor runs. Do not add it twice when
              # this shell is re-entered.
              case ":''${ROCQPATH:-}:" in
                *":${stdlibRoot}:"*) ;;
                *) export ROCQPATH="${stdlibRoot}''${ROCQPATH:+:$ROCQPATH}" ;;
              esac
              export ROCQ2LEAN_DEV_SHELL="${rocq}"

              printf 'rocq2lean: %s\n' "$(lean --version)"
              printf 'rocq2lean: %s / ocaml %s\n' "$(${rocq}/bin/rocq --version | head -1)" "$(ocaml -version)"
            '';
          };
        in
        {
          treefmt = {
            projectRootFile = "flake.nix";

            programs = {
              deadnix.enable = true;
              nixfmt.enable = true;
              shellcheck.enable = true;
              shfmt.enable = true;
              statix.enable = true;
              taplo.enable = true;
            };
          };

          devShells.default = shell;

          packages.default = shell;
        };
    };
}
