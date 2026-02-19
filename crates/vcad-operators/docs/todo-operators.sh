#!/usr/bin/env bash
# Prints the Phase 6 burndown checklist for vcad-operators.

cat <<'TODO'
# vcad-operators Phase 6 Formal Verification Burndown
Purpose: implement and fully verify Euler operators in `vcad-operators` so
valid mesh state is preserved by each operation and by operation sequences.

Roadmap alignment:
1. MVE / split-edge
2. MEF / split-face
3. KEMR / merge-face (inverse of MEF)
4. KEV / join-edge (inverse of MVE)
5. optional MFKRH for higher-genus support
6. geometric preservation lemmas
7. composition and Euler-formula preservation

------------------------------------------------------------------------------
## Exit Condition (Phase 6 done)
- [ ] All required operators (MVE, MEF, KEMR, KEV) have:
  - runtime implementation,
  - precise precondition and postcondition specs,
  - soundness/completeness bridge to executable checks,
  - fully verified "valid in -> valid out" theorem.
- [ ] Geometric obligations are proven:
  - MVE preserves affected-face coplanarity,
  - MEF preserves result-face convexity under explicit preconditions,
  - MEF precondition checker is proven correct.
- [ ] Composition theorems are proven:
  - finite sequence of valid ops preserves validity,
  - per-op and sequence-level Euler characteristic preservation.
- [ ] Trust-surface checks pass with zero forbidden markers for
  `crates/vcad-operators/src`.
- [ ] Full crate verification passes via `./scripts/verify-vcad-operators.sh`.

------------------------------------------------------------------------------
## P6.0 Crate and Model Foundation
- [ ] Define module layout:
  - `src/euler_ops/mod.rs`
  - `src/euler_ops/types.rs`
  - `src/euler_ops/preconditions.rs`
  - `src/euler_ops/mve.rs`
  - `src/euler_ops/mef.rs`
  - `src/euler_ops/kemr.rs`
  - `src/euler_ops/kev.rs`
  - `src/euler_ops/composition.rs`
  - `src/runtime_operator_refinement.rs`
- [ ] Define operation result/error surface:
  - explicit failure enums per operator,
  - no implicit panic paths on invalid input.
- [ ] Define proof-facing mesh model view reused from `vcad-topology`.
- [ ] Define a single canonical validity predicate for operator specs:
  - `mesh_valid_phase6_input_spec`
  - `mesh_valid_phase6_output_spec`
  (likely aliases/extensions of `vcad-topology` validity + Phase 5 geometry gate).

------------------------------------------------------------------------------
## P6.1 Shared Preconditions and Local Rewrite Specs
- [ ] Formalize reusable predicates:
  - edge/half-edge existence and endpoint distinctness,
  - face membership and boundary order relation,
  - "same face" relation for two vertices,
  - split positions/barycentric constraints for inserted points.
- [ ] Implement runtime precondition checkers for each predicate.
- [ ] Prove runtime precondition checkers are equivalent to spec predicates.
- [ ] Define local delta-spec templates:
  - `delta_vertices`, `delta_edges`, `delta_faces`,
  - incidence rewiring contracts (next/prev/twin/vertex/face).
- [ ] Add helper lemmas for untouched-region frame properties:
  - all unaffected indices preserve prior adjacency and geometry.

------------------------------------------------------------------------------
## P6.2 MVE (Make Vertex-Edge / Split Edge)
- [ ] Runtime implementation:
  - split one edge into two edges by inserting one vertex,
  - update twin/next/prev/edge endpoints coherently.
- [ ] Spec:
  - precise local transformation relation,
  - cardinality deltas (`ΔV=+1`, `ΔE=+1`, `ΔF=0`).
- [ ] Proof:
  - if input mesh valid and preconditions hold, output mesh valid.
- [ ] Geometry proof:
  - inserted point on original edge segment,
  - affected faces remain coplanar.
- [ ] Inverse linkage prep:
  - expose witness data needed by KEV proof.

------------------------------------------------------------------------------
## P6.3 MEF (Make Edge-Face / Split Face)
- [ ] Runtime implementation:
  - add connecting edge between two vertices on same face,
  - split one face cycle into two valid face cycles.
- [ ] Spec:
  - local face-cycle partition with edge insertion,
  - cardinality deltas (`ΔV=0`, `ΔE=+1`, `ΔF=+1`).
- [ ] Preconditions:
  - vertices are distinct and on same face boundary,
  - proposed split diagonal is internal to the face,
  - resulting cycles have length >= 3.
- [ ] Proof:
  - valid in -> valid out.
- [ ] Geometry proof:
  - both result faces remain convex (under explicit convex-splittable input).
- [ ] Precondition checker proof:
  - runtime checker accepts iff spec preconditions hold.

------------------------------------------------------------------------------
## P6.4 KEMR (Kill Edge-Make Ring / Merge Faces)
- [ ] Runtime implementation:
  - remove a face-separating edge and merge two incident faces.
- [ ] Spec:
  - inverse-local relation to MEF where preconditions match,
  - cardinality deltas (`ΔV=0`, `ΔE=-1`, `ΔF=-1`).
- [ ] Proof:
  - valid in -> valid out.
- [ ] Inverse theorem:
  - `kemr(mef(m,...),...)` returns mesh equivalent to `m`
    under explicit witness mapping and canonical indexing relation.

------------------------------------------------------------------------------
## P6.5 KEV (Kill Edge-Vertex / Join Edge)
- [ ] Runtime implementation:
  - collapse a degree-2 inserted vertex back into one edge.
- [ ] Spec:
  - inverse-local relation to MVE,
  - cardinality deltas (`ΔV=-1`, `ΔE=-1`, `ΔF=0`).
- [ ] Preconditions:
  - target vertex has exactly two incident edges in the required pattern,
  - collapse does not violate manifold constraints.
- [ ] Proof:
  - valid in -> valid out.
- [ ] Inverse theorem:
  - `kev(mve(m,...),...)` returns mesh equivalent to `m`
    under explicit witness mapping and canonical indexing relation.

------------------------------------------------------------------------------
## P6.6 Optional MFKRH (Handle/Hole Operator)
- [ ] Decide scope for initial completion:
  - either defer with explicit non-goal note, or implement with proofs.
- [ ] If included:
  - define topology and geometry preconditions,
  - prove validity preservation and Euler-delta relation for handled topology.

------------------------------------------------------------------------------
## P6.7 Global Geometry Preservation Through Operators
- [ ] Prove MVE preserves coplanarity of all affected faces.
- [ ] Prove MEF preserves convexity of both result faces given preconditions.
- [ ] Prove non-affected faces keep prior Phase 5 geometric invariants.
- [ ] Prove geometry checks compose with topology checks into one Phase 6 gate.

------------------------------------------------------------------------------
## P6.8 Composition and Algebraic Laws
- [ ] Define `apply_ops` spec and runtime executor over operation sequences.
- [ ] Prove induction theorem:
  - if `mesh0` valid and every step satisfies preconditions,
    then `mesh_n` valid.
- [ ] Prove per-op Euler-delta lemmas:
  - MVE: `(+1) - (+1) + 0 = 0`
  - MEF: `0 - (+1) + (+1) = 0`
  - KEMR: `0 - (-1) + (-1) = 0` (equivalently `0 + 1 - 1 = 0`)
  - KEV: `(-1) - (-1) + 0 = 0` (equivalently `-1 + 1 + 0 = 0`)
- [ ] Prove sequence-level Euler preservation from per-op lemmas.
- [ ] Prove MEF/KEMR and MVE/KEV inverse-pair roundtrip laws
  (up to explicit mesh-equivalence relation).

------------------------------------------------------------------------------
## P6.9 Refinement and Trust-Surface Burn-Down
- [x] Add `scripts/check-vcad-operators-trust-surface.sh`.
- [ ] Forbid and continuously scan for:
  - `assume_specification[...]`
  - `external_fn_specification`
  - `uninterpreted`
  - `admit(`
  - `assume(`
  - `#[verifier::external_body]` (except documented, temporary, whitelisted shim)
- [ ] Require every temporary trust marker to have:
  - owner,
  - blocking issue reference,
  - removal date target.
- [ ] Exit with zero trust markers for production Phase 6 completion.

------------------------------------------------------------------------------
## P6.10 Test and Counterexample Matrix
- [ ] Positive regression fixtures:
  - tetrahedron-derived edits,
  - cube-derived edits,
  - prism-derived edits.
- [ ] Negative regressions per operator:
  - invalid edge index,
  - vertices not on same face (MEF),
  - split creating non-convex subface (MEF),
  - collapse breaking manifold cycle (KEV),
  - merge over invalid adjacency (KEMR).
- [ ] Sequence regressions:
  - random small valid-op sequences preserve validity,
  - inverse-pair roundtrip tests preserve canonicalized mesh equivalence.
- [ ] Feature matrix:
  - default
  - `geometry-checks`
  - `verus-proofs`
  - `geometry-checks,verus-proofs`

------------------------------------------------------------------------------
## P6.11 Verification Scripts and CI Gates
- [x] Keep `./scripts/verify-vcad-operators.sh` as full proof gate.
- [x] Add fast loop script:
  - `./scripts/verify-vcad-operators-fast.sh [module] [function]`.
- [ ] Add matrix script:
  - `./scripts/verify-vcad-operators-matrix.sh`
    (trust-surface scan, fast verify, full verify, cargo test matrix).
- [ ] Integrate into root verification docs and CI task runner.

------------------------------------------------------------------------------
## Suggested Iteration Order (Concrete)
- [ ] Iteration 1: shared specs + MVE end-to-end validity proof.
- [ ] Iteration 2: KEV + MVE/KEV inverse theorem.
- [ ] Iteration 3: MEF end-to-end validity + convexity preservation.
- [ ] Iteration 4: KEMR + MEF/KEMR inverse theorem.
- [ ] Iteration 5: sequence composition + Euler preservation.
- [ ] Iteration 6: trust-surface cleanup + matrix hardening + docs freeze.

------------------------------------------------------------------------------
## Commands (Definition of Done per Iteration)
- [ ] `./scripts/verify-vcad-operators.sh`
- [ ] `cargo test -p vcad-operators`
- [ ] `cargo test -p vcad-operators --features geometry-checks`
- [ ] `cargo test -p vcad-operators --features verus-proofs`
- [ ] `cargo test -p vcad-operators --features "geometry-checks,verus-proofs"`

TODO
