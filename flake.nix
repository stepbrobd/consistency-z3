{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5";
    unstable.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default";
    pyproject.url = "github:nix-community/pyproject.nix";
    pyproject.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs @ { self, parts, pyproject, ... }: parts.lib.mkFlake { inherit inputs; } {
    systems = import inputs.systems;

    perSystem = { system, pkgs, unstable, ... }:
      let
        python = pkgs.python311;
      in
      {
        _module.args.unstable = import inputs.unstable { inherit system; };

        packages.default = (python.pkgs.buildPythonPackage (
          (pyproject.lib.project.loadPyproject {
            projectRoot = ./.;
          }).renderers.buildPythonPackage { inherit python; }
        )).overridePythonAttrs (_: {
          doCheck = true;
          nativeCheckInputs = [ python.pkgs.pytestCheckHook ];
          pythonImportsCheck = [ "consistency" ];
        });

        devShells.default = unstable.mkShell {
          packages = with unstable; [
            direnv
            git
            hayagriva
            nix-direnv
            ruff
            typst
            typstfmt
          ];

          venvDir = "./.venv";
          buildInputs = [ python ] ++ (with python.pkgs; [
            venvShellHook
            setuptools
            wheel
          ]);
          postShellHook = ''
            pip --disable-pip-version-check install -e .
          '';
        };

        formatter = unstable.writeShellScriptBin "formatter" ''
          set -x
          shopt -s globstar
          ${unstable.nixpkgs-fmt}/bin/nixpkgs-fmt .
          ${unstable.mypy}/bin/mypy --disable-error-code=import .
          ${unstable.ruff}/bin/ruff check --fix --unsafe-fixes .
          ${unstable.typstfmt}/bin/typstfmt **/*.typ
        '';
      };

    flake.hydraJobs = { inherit (self) packages devShells; };
  };
}
