{ mkDerivation, alex, array, base, containers, directory, filepath
, ghc, happy, hspec, HUnit, mtl, optparse-applicative, QuickCheck
, stdenv
}:
mkDerivation {
  pname = "dl";
  version = "0.0.0.1";
  src = ./.;
  isLibrary = false;
  isExecutable = true;
  executableHaskellDepends = [
    array base containers ghc mtl optparse-applicative
  ];
  executableToolDepends = [ alex happy ];
  testHaskellDepends = [
    array base containers directory filepath ghc hspec HUnit mtl
    optparse-applicative QuickCheck
  ];
  homepage = "zachsully.com";
  description = "A simple dual data language";
  license = stdenv.lib.licenses.bsd3;
}
