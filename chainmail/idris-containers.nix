{ build-idris-package
, fetchFromGitHub
, contrib
, effects
, lib
}:
build-idris-package  {
  name = "containers";
  version = "2019-05-02";

  idrisDeps = [ effects contrib ];

  src = fetchFromGitHub {
    owner = "dckc";
    repo = "idris-containers";
    rev = "2fada25";
    sha256 = "1k8mjv81iia0d56rsjxig84q252raaiv3g1jk2jlz2z4p44lvq3c";
  };

  meta = {
    description = "Various data structures for use in the Idris Language.";
    homepage = https://github.com/jfdm/idris-containers;
    license = lib.licenses.bsd3;
    maintainers = [ lib.maintainers.brainrape ];
  };
}
