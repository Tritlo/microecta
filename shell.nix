{ pkgs ? import <nixpkgs> { } }:

let
  # z3-4.15.4's test executable ends with "Error: invalid argument" on
  # aarch64-darwin in this nixpkgs snapshot, after the solver itself builds.
  # The command-line solver is all liquid-fixpoint needs.
  z3 =
    if pkgs.stdenv.isDarwin
    then pkgs.z3.overrideAttrs (_: { doCheck = false; })
    else pkgs.z3;

  # GHC expects a `gcc` executable, but recent macOS installations only ship
  # a compatibility shim. Use the host compiler so it matches the host GHC.
  gcc = pkgs.writeShellScriptBin "gcc" ''
    exec env \
      -u DEVELOPER_DIR \
      -u MACOSX_DEPLOYMENT_TARGET \
      -u NIX_CC \
      -u SDKROOT \
      /usr/bin/clang "$@"
  '';
in
pkgs.mkShell {
  packages = [ z3 ] ++ pkgs.lib.optionals pkgs.stdenv.isDarwin [ gcc ];
}
