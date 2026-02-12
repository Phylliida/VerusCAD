# Scripts
Helper scripts for local Verus workflows.

1. `setup-verus.sh`: bootstraps Verus tools, downloads Z3 4.12.5, patches it for NixOS, and builds `verus`/`cargo-verus`.
2. `verify-vcad-math.sh`: verifies `vcad-math` with `cargo verus` using the local patched Z3.

Both scripts assume this repo layout:
1. `VerusCAD` at `../VerusCAD` (current repo),
2. Verus checkout at `../verus`.

Set `VERUS_ROOT` to override the Verus checkout location.
