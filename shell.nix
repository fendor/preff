let
  sources = import ./nix/sources.nix;
  nixpkgs = import sources.nixpkgs {};
in
with nixpkgs;
stdenv.mkDerivation {
  name = "minieff";
  buildInputs = [
    gmp
    zlib
    ncurses
    haskell.compiler.ghc943
    (haskell-language-server.override { supportedGhcVersions = ["943"]; })
    haskellPackages.cabal-install
    haskellPackages.fourmolu
  ];
  src = null;
  shellHook = ''
    export LD_LIBRARY_PATH=${gmp}/lib:${zlib}/lib:${ncurses}/lib
  '';
}
