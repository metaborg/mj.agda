{
  pkgs ? (import <nixpkgs> {})
}:

let
  # get nixplus
  nixplus = import (pkgs.fetchgit {
    url    = https://gitlab.ewi.tudelft.nl/aj.rouvoet/nixplus.nix.git;
    sha256 = "0zla8sf6k1n0ggb2h416n0x4ganjr3lnrz4mv5blsfyakjhrrxha";
    rev    = "e9d6d27e37e88d318dd5963b1751482c292ce36f";
  });

in nixplus.stdenv.mkDerivation rec {
  version = "1.1.0";
  name    = "mj.agda-${version}";
  src     = ./.;

  buildInputs = with nixplus; [
    git
    agdaPackages.Agda.v2_5_4
  ];
}

