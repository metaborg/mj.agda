{
  description = "Middleweight Java Interpreter in Agda";

  outputs = { self, nixpkgs }: {

    inputs.nixpkgs.url = github:NixOS/nixpkgs/unstable;

    defaultPackage.x86_64-linux =
      with import nixpkgs { system = "x86_64-linux"; };
      stdenv.mkDerivation {
        name = "mj.agda";
        src = self;

        buildInputs = [
          agda
        ];

        installPhase = "";

        LANG   = "en_US.utf8";
        LC_ALL = "C";
      };
  };
}
