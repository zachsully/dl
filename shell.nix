{ nixpkgs ? import <nixpkgs> {}, compiler ? "default", doBenchmark ? false }:

let

  inherit (nixpkgs) pkgs;

  f = { mkDerivation, alex, array, base, containers, directory
      , filepath, ghc, happy, mtl, optparse-applicative, process, stdenv
      }:
      mkDerivation {
        pname = "dl";
        version = "0.0.0.1";
        src = ./.;
        isLibrary = false;
        isExecutable = true;
        executableHaskellDepends = [
          array base containers directory ghc mtl optparse-applicative
          process
        ];
        executableToolDepends = [ alex happy ];
        testHaskellDepends = [
          array base containers directory filepath ghc mtl
          optparse-applicative process
        ];
        homepage = "zachsully.com";
        description = "A simple dual data language";
        license = stdenv.lib.licenses.bsd3;
      };

  haskellPackages = if compiler == "default"
                       then pkgs.haskellPackages
                       else pkgs.haskell.packages.${compiler};

  variant = if doBenchmark then pkgs.haskell.lib.doBenchmark else pkgs.lib.id;

  drv = variant (haskellPackages.callPackage f {});

in

  if pkgs.lib.inNixShell then drv.env else drv
