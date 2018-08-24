{ nixpkgs ? import <nixpkgs> { }, ghc ? nixpkgs.ghc }:

with nixpkgs;

haskell.lib.buildStackProject {
    name = "Ouroboros";
    buildInputs = [ ];
    inherit ghc;
}
