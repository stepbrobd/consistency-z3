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
      debug = true;

      systems = import inputs.systems;

      perSystem = { pkgs, ... }:
        let
          python = pkgs.python313;
          workspace = lib.workspace.loadWorkspace { workspaceRoot = ./.; };
          pythonPackages = (pkgs.callPackage pyp.build.packages { inherit python; }).overrideScope (
            lib.composeManyExtensions [
              pypbs.overlays.default
              (workspace.mkPyprojectOverlay { sourcePreference = "wheel"; })
            ]);
        in
        {
          packages.default = pythonPackages.mkVirtualEnv "venv" workspace.deps.default;

          devShells.default = pkgs.mkShell {
            packages = with pkgs; [
              cvc5
              direnv
              git
              hayagriva
              nix-direnv
              python
              python.pkgs.venvShellHook
              ruff
              typst
              typstfmt
              uv
              z3
            ];

            UV_PYTHON_DOWNLOADS = "never";
            UV_PYTHON = python.interpreter;

            venvDir = "./.venv";
            preShellHook = ''
              uv sync
              unset PYTHONPATH
            '';
          };

          formatter = pkgs.writeShellScriptBin "formatter" ''
            set -x
            shopt -s globstar
            ${lib.getExe pkgs.nixpkgs-fmt} .
            ${lib.getExe pkgs.mypy} --disable-error-code=import .
            ${lib.getExe pkgs.ruff} check --fix --unsafe-fixes .
            ${lib.getExe pkgs.typstfmt} **/*.typ
          '';
        };

      flake.hydraJobs = { inherit (self) packages devShells; };
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
