{
  description = "Algebraic structures for use with Felix.";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs?ref=23.05";
    utils.url = "github:numtide/flake-utils";
    agda-stdlib = {
      url = "github:jkopanski/agda-stdlib";
      inputs = {
        nixpkgs.follows = "nixpkgs";
      };
    };
    felix = {
      url = "github:jkopanski/felix";
      inputs = {
        nixpkgs.follows = "nixpkgs";
        utils.follows = "utils";
        agda-stdlib.follows = "agda-stdlib";
      };
    };
  };

  outputs = { self, nixpkgs, utils, agda-stdlib, felix }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        standard-library = agda-stdlib.packages.${system}.default;
        felix-lib = felix.packages.${system}.default;
        # felix-boolean-lib = felix-boolean.packages.${system}.default;
        agdaWithStandardLibrary = pkgs.agda.withPackages (p: [
          standard-library
          felix-lib
          # felix-boolean-lib
        ]);

      in {
        devShell = pkgs.mkShell {
          buildInputs = [
            agdaWithStandardLibrary
            pkgs.graphviz
          ];
        };

        packages.default = pkgs.agdaPackages.mkDerivation {
          pname = "felix-algebra";
          version = "0.0.1";
          src = ./.;

          everythingFile = "./src/Everything.agda";

          buildInputs = [
            standard-library
            felix-lib
          ];

          meta = with pkgs.lib; {
            description = "Algebraic structures for use with Felix.";
            homepage = "https://github.com/jkopanski/felix-algebra";
            license = licenses.bsd3;
            # platforms = platforms.unix;
            # maintainers = with maintainers; [ ];
          };
        };
      }
    );
}
