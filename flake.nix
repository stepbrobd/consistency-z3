{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    pyproject = {
      url = "github:nix-community/pyproject.nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs =
    { self
    , nixpkgs
    , flake-utils
    , pyproject
    }: flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
      python = pkgs.python311;
      project = pyproject.lib.project.loadPyproject { projectRoot = ./.; };
    in
    {
      formatter = pkgs.writeShellScriptBin "formatter" ''
        set -eoux pipefail
        shopt -s globstar
        ${pkgs.nixpkgs-fmt}/bin/nixpkgs-fmt .
        ${pkgs.ruff}/bin/ruff --fix --unsafe-fixes .
        ${pkgs.typstfmt}/bin/typstfmt **/*.typ
      '';

      packages.default = python.pkgs.buildPythonPackage (
        project.renderers.buildPythonPackage { inherit python; }
      );

      apps.default = flake-utils.lib.mkApp { drv = self.packages.${system}.default; };

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
    });
}
