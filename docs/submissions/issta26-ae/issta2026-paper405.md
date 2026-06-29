# Artifact evaluation

```sh
qemu-system-x86_64 \
  -machine accel=kvm:tcg \
  -smp "$(nproc)" -m 8192 \
  -drive file=issta2026-paper405.qcow2,if=virtio,format=qcow2 \
  -nic user,model=virtio-net-pci,hostfwd=tcp::2222-:22 \
  -nographic
```

The interactive console will drop evaluator in the `evaluator` home directory
with artifact prepared, `cd` into the directory and follow the `readme.md` inside.

Note that evaluator user have passwordless root, and `tmux` is installed by
default.

The machine also have SSH exposed. You can run the above command detached, and SSH into the environment.

```sh
ssh -p 2222 evaluator@127.0.0.1
ssh -p 2222 root@127.0.0.1
```

## Instructions to build the QEMU image

Ignore the following if you are not one of the project collaborators.

```sh
nix-build issta2026-paper405.nix
qemu-img info result/nixos.qcow2
cp result/nixos.qcow2 issta2026-paper405.qcow2
chmod +w issta2026-paper405.qcow2
qemu-img resize issta2026-paper405.qcow2 50G
```
