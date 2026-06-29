{
  artifact ? ./issta2026-paper405.tgz,
  nixpkgs ? fetchTarball {
    url = "https://github.com/nixos/nixpkgs/archive/e73de5be04e0eff4190a1432b946d469c794e7b4.tar.gz";
    sha256 = "sha256-pGvFkM8N0xEkIIXDe5YYfbEAvHrk4IxBrjB/x8OomhE=";
  },
}:

(import "${nixpkgs}/nixos/lib/eval-config.nix" {
  system = "x86_64-linux";

  modules = [
    (
      {
        config,
        lib,
        modulesPath,
        pkgs,
        ...
      }:
      {
        imports = [ "${modulesPath}/profiles/qemu-guest.nix" ];

        documentation.enable = false;

        fileSystems."/" = {
          fsType = "ext4";
          autoResize = true;
          device = "/dev/disk/by-label/nixos";
        };

        boot = {
          growPartition = true;
          kernelPackages = pkgs.linuxPackages_latest;
          kernelParams = [ "console=ttyS0" ];
          loader.grub.device = lib.mkDefault "/dev/vda";
        };

        system.build.qcow2 = import "${modulesPath}/../lib/make-disk-image.nix" {
          inherit lib config pkgs;
          diskSize = "auto";
          format = "qcow2-compressed";
          partitionTableType = "hybrid";
        };

        services.openssh = {
          enable = true;
          settings = {
            PermitRootLogin = "yes";
            PasswordAuthentication = true;
            PermitEmptyPasswords = "yes";
          };
        };

        security.pam.services.sshd.allowNullPassword = true;
        security.sudo.wheelNeedsPassword = false;

        users.mutableUsers = false;
        users.users.root.hashedPassword = "";
        users.users.evaluator = {
          isNormalUser = true;
          createHome = true;
          home = "/home/evaluator";
          extraGroups = [ "wheel" ];
          hashedPassword = "";
        };
        services.getty.autologinUser = "evaluator";

        system.activationScripts.seedEvaluatorHome = {
          deps = [ "users" ];
          text =
            let
              contents = pkgs.runCommand "issta2026-paper405-contents" { } ''
                mkdir -p $out
                tar -xzf ${artifact} -C $out
              '';
            in
            ''
              if [ ! -e /home/evaluator/.seeded ]; then
                mkdir -p /home/evaluator
                cp -a ${contents}/. /home/evaluator/
                touch /home/evaluator/.seeded
                chmod -R u+rwX /home/evaluator
                chown -R evaluator:users /home/evaluator
              fi
            '';
        };

        nix = {
          channel.enable = false;
          nixPath = [ "nixpkgs=${pkgs.path}" ];
          settings = {
            accept-flake-config = true;
            allow-import-from-derivation = true;
            builders-use-substitutes = true;
            fallback = true;
            keep-build-log = true;
            keep-derivations = true;
            keep-env-derivations = true;
            keep-failed = true;
            keep-going = true;
            keep-outputs = true;
            sandbox = true;
            use-xdg-base-directories = true;
            warn-dirty = false;
            trusted-users = [
              "root"
              "@wheel"
            ];
            experimental-features = [
              "auto-allocate-uids"
              "cgroups"
              "flakes"
              "nix-command"
            ];
          };
        };

        programs.tmux.enable = true;

        programs.direnv.enable = true;
        programs.direnv.nix-direnv.enable = true;
        programs.direnv.enableBashIntegration = true;

        environment.systemPackages = with pkgs; [
          vim
          nano
        ];

        system.stateVersion = lib.trivial.release;
      }
    )
  ];
}).config.system.build.qcow2
