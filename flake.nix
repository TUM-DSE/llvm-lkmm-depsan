{
  description = "Custom clang";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };
  outputs = { self, nixpkgs, flake-utils, ...}:
  flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
    in
    {
      packages.default = pkgs.llvmPackages.stdenv.mkDerivation {
        pname = "custom-clang";
        version = "0.1.0";
        src = self;

        nativeBuildInputs = [
          pkgs.cmake
          pkgs.ninja
          pkgs.python3
        ];

        cmakeDir = "../llvm";

        cmakeFlags = [
          "-DLLVM_ENABLE_PROJECTS=clang"
          "-DCMAKE_BUILD_TYPE=Release"
          "-DLLVM_TARGETS_TO_BUILD=Native"
          "-DLLVM_PARALLEL_LINK_JOBS=4"
        ];

        hardeningDisable = [ "all" ];

        dontStrip = true;
      };

      devShells.default = pkgs.llvmPackages.stdenv.mkDerivation {
        name = "custom-clang-devshell";
        src = self;
        nativeBuildInputs = [
          pkgs.cmake
          pkgs.ninja
          pkgs.gdb
          pkgs.python3
          pkgs.llvmPackages_20.clang-tools
        ];
        hardeningDisable = [ "all" ];
      };
    }
  );
}
