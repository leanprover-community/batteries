# Cheap packaging — copies pre-built .olean files from .lake/build/
# No rebuild, no lean4-nix. Use with nix build --impure.
{
  description = "batteries — lean-toolchain=leanprover/lean4:v4.29.1, 175 .olean files (pre-built)";

  inputs = {
    nixpkgs.url = "git+file:///mnt/data1/git/github.com/NixOS/nixpkgs.git?ref=master";
  };

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs { inherit system; };
    in {
      packages.${system}.default = pkgs.stdenv.mkDerivation {
        name = "batteries-olean-17d08b05";
        src = builtins.path {
          path = /mnt/data1/time-2026/07-july/15/lean-deps/batteries/.lake/build/lib/lean;
          name = "batteries-olean";
        };
        buildPhase = "true";
        installPhase = "cp -r $src $out";
      };
    };
}
