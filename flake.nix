{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/eabe8d3eface69f5bb16c18f8662a702f50c20d5";
    compat.url = "github:edolstra/flake-compat";
    compat.flake = false;
    utils.url = "github:numtide/flake-utils";
    pyproject.url = "github:nix-community/pyproject.nix";
    pyproject.inputs.nixpkgs.follows = "nixpkgs";
  };

  outputs =
    { self
    , nixpkgs
    , compat
    , utils
    , pyproject
    }: utils.lib.eachDefaultSystem
      (system:
      let
        pkgs = import nixpkgs { inherit system; };
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

        apps.default = utils.lib.mkApp { drv = self.packages.${system}.default; };

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
      }) // {
      hydraJobs = {
        inherit (self)
          packages devShells;
      };
    };
}
