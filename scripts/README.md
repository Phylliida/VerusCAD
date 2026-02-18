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
8. `verify-vcad-topology-fast.sh`: fast dev loop for `vcad-topology` using focused verification (runs trust-surface scan first).
   - default: `./scripts/verify-vcad-topology-fast.sh`
     verifies `runtime_halfedge_mesh_refinement`.
   - module: `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
   - function: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_index_bounds`
9. `verify-vad-topology.sh`: compatibility alias that forwards to `verify-vcad-topology.sh`.
10. `run-codex-task.sh`: lightweight client that POSTs to the looper service (`http://127.0.0.1:3456/run` by default).
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
