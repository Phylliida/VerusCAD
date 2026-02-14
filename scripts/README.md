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
6. `verify-vcad-topology.sh`: full `vcad-topology` verification with `verus-proofs`.
7. `verify-vcad-topology-fast.sh`: fast dev loop for `vcad-topology` using focused verification.
   - default: `./scripts/verify-vcad-topology-fast.sh`
     verifies `runtime_halfedge_mesh_refinement`.
   - module: `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
   - function: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_index_bounds`
8. `verify-vad-topology.sh`: compatibility alias that forwards to `verify-vcad-topology.sh`.

These scripts assume this repo layout:
1. `VerusCAD` at `../VerusCAD` (current repo),
2. Verus checkout at `../verus`.

Set `VERUS_ROOT` to override the Verus checkout location.
