{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5";
    parts.url = "github:hercules-ci/flake-parts";
    systems.url = "github:nix-systems/default";
    pyproject.url = "github:nix-community/pyproject.nix";
    pyproject.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs = inputs @ { self, nixpkgs, parts, systems, pyproject }: parts.lib.mkFlake { inherit inputs; } {
    systems = import inputs.systems;

    perSystem = { pkgs, ... }:
      let
        python = pkgs.python311;
      in
      {
        packages.default = (python.pkgs.buildPythonPackage (
          (pyproject.lib.project.loadPyproject {
            projectRoot = ./.;
          }).renderers.buildPythonPackage { inherit python; }
        )).overridePythonAttrs (_: {
          doCheck = true;
          nativeCheckInputs = [ python.pkgs.pytestCheckHook ];
          pythonImportsCheck = [ "consistency" ];
        });

        devShells.default = pkgs.mkShell {
          packages = with pkgs; [
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

        formatter = pkgs.writeShellScriptBin "formatter" ''
          set -x
          shopt -s globstar
          ${pkgs.nixpkgs-fmt}/bin/nixpkgs-fmt .
          ${pkgs.mypy}/bin/mypy --disable-error-code=import .
          ${pkgs.ruff}/bin/ruff --fix --unsafe-fixes .
          ${pkgs.typstfmt}/bin/typstfmt **/*.typ
        '';
      };

    flake.hydraJobs = { inherit (self) packages devShells; };
  };
}
