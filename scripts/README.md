# Scripts
Helper scripts for local Verus workflows.

1. `setup-verus.sh`: bootstraps Verus tools, downloads Z3 4.12.5, patches it for NixOS, and builds `verus`/`cargo-verus`.
2. `verify-vcad-math.sh`: verifies `vcad-math` with `cargo verus` using the local patched Z3.
3. `verify-vcad-math-fast.sh`: fast dev loop for `vcad-math` using focused verification.
   - default: `./scripts/verify-vcad-math-fast.sh`
     verifies `quaternion_assoc_cases`.
   - module: `./scripts/verify-vcad-math-fast.sh quaternion`
   - function: `./scripts/verify-vcad-math-fast.sh quaternion lemma_assoc_basis_any`
4. `verify-vcad-geometry.sh`: full `vcad-geometry` verification with `verus-proofs`.
5. `verify-vcad-geometry-fast.sh`: fast dev loop for `vcad-geometry` using focused verification.
   - default: `./scripts/verify-vcad-geometry-fast.sh`
     verifies `runtime_orientation_predicates_refinement`.
   - module: `./scripts/verify-vcad-geometry-fast.sh runtime_sidedness_refinement`
   - function: `./scripts/verify-vcad-geometry-fast.sh runtime_sidedness_refinement runtime_segment_crosses_plane_from_opposite_sides`
6. `check-vcad-topology-trust-surface.sh`: scans `crates/vcad-topology/src` for forbidden trust markers (`assume_specification`, `external_fn_specification`, `uninterpreted`, `admit(`, `assume(`, and `#[verifier::external_body]`).
7. `verify-vcad-topology.sh`: full `vcad-topology` verification with `verus-proofs` (runs trust-surface scan first).
   - execution path:
     prefers `nix-shell -p rustup`; if unavailable (for example Nix daemon socket is blocked), automatically falls back to direct `cargo verus` with a temporary local `rustup` shim wired to `VERUS_TOOLCHAIN` under `$RUSTUP_HOME`/`$HOME/.rustup`.
8. `verify-vcad-topology-fast.sh`: fast dev loop for `vcad-topology` using focused verification (runs trust-surface scan first).
   - execution path:
     same automatic `nix-shell` -> direct `cargo verus` fallback behavior as `verify-vcad-topology.sh`.
   - default: `./scripts/verify-vcad-topology-fast.sh`
     verifies `runtime_halfedge_mesh_refinement`.
   - module: `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
   - function: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_index_bounds`
9. `verify-vcad-topology-matrix.sh`: one-command replay of the full topology matrix.
   - runs in order: trust-surface guard, `verify-vcad-topology-fast.sh`,
     `verify-vcad-topology.sh`, and cargo tests for baseline, `geometry-checks`,
     and `geometry-checks,verus-proofs`.
   - no separate fallback logic in this script; topology verifier fallback behavior is inherited from `verify-vcad-topology-fast.sh` / `verify-vcad-topology.sh`.
10. `verify-vad-topology.sh`: compatibility alias that forwards to `verify-vcad-topology.sh`.
11. `check-vcad-operators-trust-surface.sh`: scans `crates/vcad-operators/src` for forbidden trust markers (`assume_specification`, `external_fn_specification`, `uninterpreted`, `admit(`, `assume(`, `#[verifier::external_body]`, and `#[verifier::external_type_specification]`).
12. `verify-vcad-operators.sh`: full `vcad-operators` verification with `verus-proofs` (runs trust-surface scan first).
   - execution path:
     prefers `nix-shell -p rustup`; if unavailable, automatically falls back to direct `cargo verus`
     with a temporary local `rustup` shim wired to `VERUS_TOOLCHAIN` under `$RUSTUP_HOME`/`$HOME/.rustup`.
13. `verify-vcad-operators-fast.sh`: fast dev loop for `vcad-operators` using focused verification (runs trust-surface scan first).
   - execution path:
     same automatic `nix-shell` -> direct `cargo verus` fallback behavior as `verify-vcad-operators.sh`.
   - default: `./scripts/verify-vcad-operators-fast.sh`
     verifies `vcad-operators` with `verus-proofs` and no module filter.
   - module: `./scripts/verify-vcad-operators-fast.sh <module>`
   - function: `./scripts/verify-vcad-operators-fast.sh <module> <function_pattern>`
14. `test-vcad-geometry-verus-proofs.sh`: stable cargo test wrapper for `vcad-geometry` with `verus-proofs`.
   - clears `RUSTFLAGS`/`CARGO_ENCODED_RUSTFLAGS` to avoid accidental `verus_keep_ghost` leakage.
   - normalizes `TMPDIR` to `/tmp` when the current value is missing/unwritable.
   - default: `./scripts/test-vcad-geometry-verus-proofs.sh`
   - passthrough args: `./scripts/test-vcad-geometry-verus-proofs.sh -- --nocapture`
15. `run-codex-task.sh`: lightweight client that POSTs to the looper service (`http://127.0.0.1:3456/run` by default).
   - sends a `zulip_message` to looper; looper handles Zulip DM + VS Code restart/new Codex panel
   - message source file: `scripts/run-codex-task.message.txt`
   - default: `./scripts/run-codex-task.sh`
   - update message text: edit `scripts/run-codex-task.message.txt` before running
   - override endpoint: `LOOPER_URL=http://host:3456/run ./scripts/run-codex-task.sh`
   - optional auth: `LOOPER_API_TOKEN=... ./scripts/run-codex-task.sh`
   - optional VS Code passthrough env: `VSCODE_PASSWORD_STORE`, `VSCODE_STARTUP_DELAY_SECONDS`, `VSCODE_SIDEBAR_DELAY_SECONDS`, `VSCODE_NEW_TASK_DELAY_SECONDS`, `PROMPT_SEND_DELAY_SECONDS`

These scripts assume this repo layout:
1. `VerusCAD` at `../VerusCAD` (current repo),
2. Verus checkout at `../verus`.

Set `VERUS_ROOT` to override the Verus checkout location.

Rust/Verus scripts in this folder source `scripts/lib/sanitize-rust-env.sh` before
running toolchains. The sanitizer:
1. clears `RUSTFLAGS` and `CARGO_ENCODED_RUSTFLAGS` to prevent accidental
   `verus_keep_ghost` leakage into stable `cargo` flows (avoids `E0554`),
2. repairs `TMPDIR` to `/tmp` when the current value is missing or unwritable,
   which avoids transient `couldn't create a temp dir` failures.
