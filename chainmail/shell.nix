with import <nixpkgs> {};
stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [
    (idrisPackages.with-packages (with idrisPackages;
        [ contrib pruviloj ]))
  ];
}
