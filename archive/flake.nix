{
  description = "Ziku - A programming language with duality-aware design";

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
          buildInputs = with pkgs; [
            # Lean 4 version manager
            elan

            # Scheme backend
            chez

            # Build dependencies
            git
            curl
            cacert
            gnumake
            coreutils

            # Python for build scripts (if needed)
            python3
          ];

        };
      }
    );
}
