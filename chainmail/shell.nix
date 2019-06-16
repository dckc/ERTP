with import <nixpkgs> {};

let
containers20190502 = idrisPackages.callPackage ./idris-containers.nix {};
in
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [
    (idrisPackages.with-packages (with idrisPackages;
        [ containers20190502 contrib pruviloj ]))
  ];
}
