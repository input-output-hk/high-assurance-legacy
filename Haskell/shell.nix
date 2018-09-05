{nixpkgs ? import <nixpkgs> { }, ghc ? nixpkgs.ghc}:

with nixpkgs;

haskell.lib.buildStackProject {
  name = "datastructures";
  buildInputs = [cairo zlib];
  inherit ghc;
}
