# vcad-math Verification TODO
Goal: reduce `vcad-math` trust boundaries to a strict zero-trust model while keeping full-crate verification green.

## Current Snapshot (2026-02-17)
- [x] `./scripts/verify-vcad-math.sh` succeeds.
- [x] `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.
- [x] `rg -n "#\\[verifier::external_body\\]" crates/vcad-math/src` returns no matches.
- [x] The previous `RuntimeScalar::signum_i8` trusted bridge has been removed from `crates/vcad-math/src`.
- [ ] Strict zero-trust is not complete yet (see remaining trust surface below).

## Remaining Trust Surface in `vcad-math`

### 1) Refinement bridge style (`external_type_specification`)
The refinement modules still use `#[verifier::external_type_specification]` wrappers:
- `src/runtime_bigint_witness_refinement.rs`
- `src/runtime_orientation_refinement.rs`
- `src/runtime_orientation3_refinement.rs`
- `src/runtime_point2_refinement.rs`
- `src/runtime_point3_refinement.rs`
- `src/runtime_point4_refinement.rs`
- `src/runtime_quaternion_refinement.rs`
- `src/runtime_scalar_refinement.rs`
- `src/runtime_vec2_refinement.rs`
- `src/runtime_vec3_refinement.rs`
- `src/runtime_vec4_refinement.rs`

### 2) cfg-split runtime implementations
Runtime files have separate code paths:
- `#[cfg(not(verus_keep_ghost))]`: executable backend over `rug` types.
- `#[cfg(verus_keep_ghost)]`: verified witness/model path used by Verus proofs.

`cargo verus verify` validates the `verus_keep_ghost` path. Strict zero-trust requires either
(1) one unified implementation path, or
(2) an explicit proved refinement relation that closes the gap between the cfg-split runtime path and the verified model path.

## Zero-Trust Completion Plan

### Phase A: Lock the current baseline
- [x] Keep full crate gate green: `./scripts/verify-vcad-math.sh`.
- [x] Keep no-assumption/no-external-body scans green in `crates/vcad-math/src`.
- [ ] Add these scans to CI (or script-level gate) so regressions fail fast.

### Phase B: Shrink refinement bridge trust
- [ ] Decide whether to keep `external_type_specification` wrappers as an accepted boundary or eliminate them.
- [ ] If eliminating: migrate runtime/refinement boundary toward verifiable native type ownership + explicit representation invariants.
- [ ] If keeping: document precise soundness argument and keep wrappers thin, explicit, and audited.

### Phase C: Close cfg-split gap
- [ ] Define target architecture for runtime/verus unification.
- [ ] Either unify runtime code paths or prove equivalence obligations between `not(verus_keep_ghost)` and `verus_keep_ghost` behavior at API boundaries.
- [ ] Re-run `vcad-math` + downstream gates (`vcad-geometry`, `vcad-topology`) after each boundary reduction.

## Workspace Note
`vcad-math` no longer carries `external_body` in `src/`, but the workspace is not globally zero-trust yet. For example, `vcad-topology` still has `external_body` in `src/runtime_halfedge_mesh_refinement.rs`.

## Verification Commands
- `./scripts/verify-vcad-math.sh`
- `rg -n "assume_specification\\[" crates/vcad-math/src`
- `rg -n "#\\[verifier::external_body\\]" crates/vcad-math/src`
- `rg -n "external_type_specification" crates/vcad-math/src`
