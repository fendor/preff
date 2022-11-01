let 
  sources = import ./nix/sources.nix;
  nixpkgs = import sources.nixpkgs {};
in
with nixpkgs;
stdenv.mkDerivation {
  name = "safe-mutations";
  buildInputs = [
    gmp
    zlib
    ncurses
    haskell.compiler.ghc942
    haskellPackages.cabal-install
  ];
  src = null;
  shellHook = ''
    export LD_LIBRARY_PATH=${gmp}/lib:${zlib}/lib:${ncurses}/lib
  '';
}
