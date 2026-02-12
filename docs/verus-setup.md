# Verus Setup
This document records the exact setup flow for this repository.

## Repo layout assumption
This project expects:

1. `VerusCAD` at `/home/bepis/Documents/verifycad/VerusCAD`
2. `verus` checkout at `/home/bepis/Documents/verifycad/verus`

## One-time setup commands
Run these from `VerusCAD`:

```bash
./scripts/setup-verus.sh
```

On this machine, the script uses `nix-shell` and performs:

1. builds Verus tools (`verus`, `cargo-verus`, `vargo`) with `vargo build --release --vstd-no-verify`,
2. downloads Z3 `4.12.5` using `verus/source/tools/get-z3.sh`,
3. patches `verus/source/z3` to use the NixOS dynamic linker,
4. rebuilds with `VERUS_Z3_PATH=verus/source/z3`.

## Verify the first crate
After setup succeeds:

```bash
./scripts/verify-vcad-math.sh
```

This runs:

```bash
cargo verus verify --manifest-path crates/vcad-math/Cargo.toml -p vcad-math
```

with:

1. `PATH` including `verus/source/target-verus/release`,
2. `VERUS_Z3_PATH=verus/source/z3`.

## Troubleshooting
### `rustup: command not found`
Run commands through `nix-shell` (as done by the scripts), or install rustup manually.

### `Could not resolve host: index.crates.io`
The environment cannot reach crates.io, so `vargo` and dependencies cannot be built.
Resolve DNS/network access, then rerun `./scripts/setup-verus.sh`.

### `cargo: no such command: verus`
`cargo-verus` is not yet built or not in `PATH`.
Run `./scripts/setup-verus.sh` and then `./scripts/verify-vcad-math.sh`.

### `The verifier expects z3 version "4.12.5"`
Use `VERUS_Z3_PATH=/home/bepis/Documents/verifycad/verus/source/z3`.
The setup script installs and patches this exact binary.
