{
  description = "A basic devshell";

  inputs = {
    nixpkgs.url = "nixpkgs";

    nixNeovim = {
      url = "github:D3vZro/NixNeovim";
    };

    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, nixNeovim, lean4-nix, ... }:
  let
    system = "x86_64-linux";
    nvim = nixNeovim.outputs.packages.${system}.lean;

    pkgs = import nixpkgs { 
      inherit system;

      overlays = [ (lean4-nix.readToolchainFile ./lean-toolchain) ];
    };
  in {
    devShells.${system}.default = pkgs.mkShell.override { stdenv = pkgs.clangStdenv; } {
      # Interactive packages
      packages = with pkgs; [
        nvim
        elan
        lean.lean-all
      ];

      # Build dependencies
      inputsFrom = with pkgs; [
      ];
    };
  };
}
