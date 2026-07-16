{
  description = "batteries — lean-toolchain=leanprover/lean4:v4.29.1, 175 .olean files";

  inputs = {
    nixpkgs.follows = "lean4-nix/nixpkgs";
    flake-parts.url = "github:hercules-ci/flake-parts";
    lean4-nix.url = "github:lenianiva/lean4-nix";
  };

  outputs = inputs @ { nixpkgs, flake-parts, lean4-nix, ... }:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" ];

      perSystem = { system, pkgs, ... }: {
        _module.args.pkgs = import nixpkgs {
          inherit system;
          overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
        };

        packages.default = (pkgs.lean.buildLeanPackage {
          name = "batteries";
          roots = [ "Batteries" ];
          src = pkgs.lib.cleanSource ./.;
        }).modRoot;

        devShells.default = pkgs.mkShell {
          packages = with pkgs.lean; [ lean-all ];
        };
      };
    };
}
