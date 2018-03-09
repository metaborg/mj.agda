{
  pkgs ? (import <nixpkgs> {})
}:

let
  # get nixplus
  nixplus = import (pkgs.fetchgit {
    url    = https://gitlab.ewi.tudelft.nl/aj.rouvoet/nixplus.nix.git;
    sha256 = "1qmln4c0vla5an4vmkf828q7xg8qkbfrlpmhg0kjb064nvnrcr0h";
    rev    = "fda1611c6263774f8e9ca31eab3e1c6ba778d505";
  });

in nixplus.stdenv.mkDerivation rec {
  version = "1.0.0";
  name    = "mj.agda-${version}";
  src     = ./.;

  buildInputs = with nixplus; [
    git
    agdaPackages.Agda.v2_6_0
  ];
}

