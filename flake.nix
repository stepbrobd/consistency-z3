{
  outputs =
    inputs
    @
    { self
    , nixpkgs
    , parts
    , pyp
    , pypbs
    , pypuv
    , ...
    }:
    let lib = builtins // nixpkgs.lib // parts.lib // pypuv.lib; in
    parts.lib.mkFlake { inherit inputs; } {
      systems = import inputs.systems;

      debug = true;
      flake = { inherit lib; };

      perSystem = { pkgs, ... }:
        let
          python = pkgs.python313;
          workspace = lib.workspace.loadWorkspace { workspaceRoot = ./.; };
          pythonPackages = (pkgs.callPackage pyp.build.packages { inherit python; }).overrideScope (
            lib.composeManyExtensions [
              pypbs.overlays.default
              (workspace.mkPyprojectOverlay { sourcePreference = "wheel"; })
              (final: prev: {
                # broken (devshell still works, standalone build fail):
                # uv#4088, possibly a bug in uv2nix
                z3-solver = prev.z3-solver.overrideAttrs (old: {
                  nativeBuildInputs = (old.nativeBuildInputs or [ ]) ++ [ final.cmake ] ++ final.resolveBuildSystem ({ setuptools = [ ]; });
                });
              })
            ]);
        in
        {
          packages.default = pythonPackages.mkVirtualEnv
            (let meta = lib.importTOML ./pyproject.toml; in with meta.project; "${name}-${version}")
            workspace.deps.default;

          devShells.default = pkgs.mkShell {
            packages = with pkgs; [
              cvc5
              deno
              direnv
              nix-direnv
              nixpkgs-fmt
              python
              python.pkgs.venvShellHook
              ruff
              uv
              z3
            ];

            # only affects linux, darwin behavior is untouched
            LD_LIBRARY_PATH = lib.makeLibraryPath (with pkgs; [ stdenv.cc.cc z3 ]);

            UV_PYTHON_DOWNLOADS = "never";
            UV_PYTHON = python.interpreter;

            venvDir = "./.venv";
            preShellHook = "uv venv $venvDir --allow-existing";
            postShellHook = "uv sync";
          };

          devShells.paper = pkgs.mkShell {
            packages = with pkgs;[
              bibtex-tidy
              hayagriva
              tex-fmt
              texliveFull
              typst
              typstyle
            ];
          };

          formatter = pkgs.writeShellScriptBin "formatter" ''
            set -eoux pipefail
            shopt -s globstar
            root="$PWD"
            while [[ ! -f "$root/.git/index" ]]; do
              if [[ "$root" == "/" ]]; then
                exit 1
              fi
              root="$(dirname "$root")"
            done
            pushd "$root" > /dev/null
            ${lib.getExe pkgs.deno} fmt **/*.md **/*.yaml
            ${lib.getExe pkgs.nixpkgs-fmt} .
            ${lib.getExe pkgs.ruff} check --fix --unsafe-fixes --preview .
            ${lib.getExe pkgs.taplo} format pyproject.toml
            ${lib.getExe pkgs.typstyle} -i **/*.typ
            ${lib.getExe pkgs.ty} check --fix --error all .
          '';
        };
    };

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    parts.url = "github:hercules-ci/flake-parts";
    parts.inputs.nixpkgs-lib.follows = "nixpkgs";
    systems.url = "github:nix-systems/default";
    pyp.url = "github:pyproject-nix/pyproject.nix";
    pyp.inputs.nixpkgs.follows = "nixpkgs";
    pypbs.url = "github:pyproject-nix/build-system-pkgs";
    pypbs.inputs.pyproject-nix.follows = "pyp";
    pypbs.inputs.uv2nix.follows = "pypuv";
    pypbs.inputs.nixpkgs.follows = "nixpkgs";
    pypuv.url = "github:pyproject-nix/uv2nix";
    pypuv.inputs.nixpkgs.follows = "nixpkgs";
    pypuv.inputs.pyproject-nix.follows = "pyp";
  };
}
