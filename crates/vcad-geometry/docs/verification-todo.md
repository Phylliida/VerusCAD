# vcad-geometry Verification TODO
Goal: remove trusted proof boundaries so all `vcad-geometry` runtime behavior is justified by explicit specs + proofs.

## Baseline Snapshot (2026-02-13)
- [x] `vcad-geometry` verifies with `verus-proofs` enabled (`87 verified, 0 errors`).
- [x] Trusted refinement assumptions removed (`assume_specification[...]` no longer present in `src/`).
- [x] Sign wrapper APIs have explicit proof contracts.

## Recommended Work Order
- [x] 1) Orientation runtime boundary.
- [x] 2) Collinearity/coplanarity boundary.
- [x] 3) Sidedness boundary.
- [x] 4) Convex polygon boundary.
- [x] 5) Final de-trusting and verification gate.

## A. Orientation Runtime Boundary
File: `src/runtime_orientation_predicates_refinement.rs`
- [x] Replace `assume_specification[ orientation_predicates::orient2d_value ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient3d_value ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient2d_class ]` with proved refinement.
- [x] Replace `assume_specification[ orientation_predicates::orient3d_class ]` with proved refinement.

File: `src/orientation_predicates.rs`
- [x] Add/verify spec+proof bridge for `orient2d_sign` (exact sign relation to `orient2d_spec`).
- [x] Add/verify spec+proof bridge for `orient3d_sign` (exact sign relation to `orient3d_spec`).

## B. Collinearity/Coplanarity Runtime Boundary
File: `src/runtime_collinearity_coplanarity_refinement.rs`
- [x] Replace `assume_specification[ collinearity_coplanarity::collinear2d ]` with proved refinement.
- [x] Replace `assume_specification[ collinearity_coplanarity::collinear3d ]` with proved refinement.
- [x] Replace `assume_specification[ collinearity_coplanarity::coplanar ]` with proved refinement.

## C. Sidedness Runtime Boundary
File: `src/runtime_sidedness_refinement.rs`
- [x] Replace `assume_specification[ sidedness::point_above_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::point_below_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::point_on_plane ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_crosses_plane_strict ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_plane_intersection_parameter_strict ]` with proved refinement.
- [x] Replace `assume_specification[ sidedness::segment_plane_intersection_point_strict ]` with proved refinement.

## D. Convex Polygon Runtime Boundary
File: `src/runtime_convex_polygon_refinement.rs`
- [x] Replace `assume_specification[ convex_polygon::point_in_convex_polygon_2d ]` with proved refinement.
- [x] Replace `assume_specification[ convex_polygon::point_strictly_in_convex_polygon_2d ]` with proved refinement.

## E. Completion Gates
- [x] `rg -n "assume_specification\\[" crates/vcad-geometry/src` shows no trusted assumptions for `vcad-geometry` runtime behavior.
- [x] Full crate verification succeeds:
  - `cargo verus verify --manifest-path crates/vcad-geometry/Cargo.toml -p vcad-geometry --features verus-proofs -- --triggers-mode silent`
- [x] Keep/extend runtime unit tests for representative geometric cases while proofs are being migrated.

## F. Proof Quality Hardening
- [x] Remove termination waivers from `vcad-geometry` proof code:
  - `rg -n "exec_allows_no_decreases_clause" crates/vcad-geometry/src` returns no matches.
  - Loop termination is justified with explicit `decreases` clauses in convex polygon proofs.
- [x] Reduce witness-proof duplication and make quantifier instantiation explicit:
  - Reuse helper lemmas for existential witness construction in sidedness refinements.
  - Keep explicit `#[trigger]` terms on witness point-parameter predicates.
