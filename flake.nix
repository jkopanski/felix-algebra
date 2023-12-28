{
  description = "Algebraic structures for use with Felix.";

  inputs = {
    felix.url = "github:conal/felix";
    nixpkgs.follows = "felix/nixpkgs";
    utils.follows = "felix/utils";
    agda-stdlib-src.follows = "felix/agda-stdlib-src";
  };

  outputs = { self, nixpkgs, utils, agda-stdlib-src, felix }:
    utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        standard-library = pkgs.agdaPackages.standard-library.overrideAttrs (final: prev: {
          version = "2.0";
          src = agda-stdlib-src;
        });
        felix-lib = felix.packages.${system}.default;
        agdaWithStandardLibrary = pkgs.agda.withPackages (p: [
          standard-library
          felix-lib
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
