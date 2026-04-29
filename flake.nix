{
  description = "A Lean 4 and Lake development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          # The packages you want in your environment
          buildInputs = with pkgs; [
            lean4
          ];

          # Commands to run when entering the shell
          shellHook = ''
            echo "Lean 4 development environment loaded!"
            echo "------------------------------------"
            lean --version
            lake --version
          '';
        };
      }
    );
}
