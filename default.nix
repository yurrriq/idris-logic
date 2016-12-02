{ pkgs ? import <nixpkgs> {}
, date ? "2016-11-24"
}:
let
  inherit (pkgs) lib gcc fetchFromGitHub haskellPackages idrisPackages;
  inherit (haskellPackages) idris;
  inherit (idrisPackages) build-idris-package with-packages;

  # TODO: patch build-idris-package.nix
  bifunctors = build-idris-package rec {
    name = "${pkg}-${date}";
    pkg = "bifunctors";

    src = fetchFromGitHub {
      owner = "yurrriq";
      repo = "idris-bifunctors";
      rev = "29293c5";
      sha256 = "1nazxmml3mdi13zx3pszgihjsp6g6008s7k969q3jjcvnpn8qrah";
    };

    doCheck = false;

    propagatedBuildInputs = with idrisPackages; [ prelude base effects ];

    meta = with lib; {
      description = "A small bifunctor library for Idris";
      homepage = "https://github.com/yurrriq/idris-bifunctors";
      # license =
      maintainers = with maintainers; [ yurrriq ];
      inherit (idris.meta) platforms;
    };
  };

  logic = build-idris-package rec {
    name = "${pkg}-${date}";
    pkg = "logic";

    src = ./.;

    doCheck = false;

    propagatedBuildInputs = with idrisPackages; [
      prelude base bifunctors
    ] ++ [ gcc ];

    meta = with lib; {
      description = "Coq-inspired propositional logic tools";
      homepage = "https://github.com/yurrriq/idris-logic";
      license = licenses.mit;
      maintainers = with maintainers; [ yurrriq ];
      inherit (idris.meta) platforms;
    };
  };
in
{
  idris = with-packages(with idrisPackages; [
    prelude base bifunctors # logic # contrib pruviloj
  ]);
}
