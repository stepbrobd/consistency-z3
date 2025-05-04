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
      flake.hydraJobs = { inherit (self) packages devShells; };

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
              bibtex-tidy
              cvc5
              direnv
              git
              hayagriva
              nix-direnv
              python
              python.pkgs.venvShellHook
              ruff
              tex-fmt
              texliveFull
              typst
              typstfmt
              uv
              z3
            ];

            UV_PYTHON_DOWNLOADS = "never";
            UV_PYTHON = python.interpreter;

            venvDir = "./.venv";
            preShellHook = "uv venv $venvDir";
            postShellHook = "uv sync";
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
