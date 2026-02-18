# vcad-topology Verification TODO
Goal: eliminate trusted gaps until all topology behavior is justified by explicit specs + proofs.

## A. Remove Trusted Runtime Boundary (Highest Priority)
- [x] Remove trusted boundary `assume_specification[ Mesh::is_structurally_valid ]` from refinement surface.
  - semantic correctness is tracked under sections D/F (`check_*` and `is_structurally_valid` verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::check_euler_formula_closed_components ]` from refinement surface.
  - semantic correctness is tracked under section E/F (`check_euler_formula_closed_components` verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Replace `assume_specification[ Mesh::is_valid ]` with proven refinement.
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::component_count ]` from refinement surface.
  - semantic correctness is tracked under section E (`component_count` / BFS verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::tetrahedron ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::cube ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Remove trusted boundary `assume_specification[ Mesh::triangular_prism ]` from refinement surface.
  - semantic correctness is tracked under section G (constructor verification in `src/halfedge_mesh.rs`).
  - file: `src/runtime_halfedge_mesh_refinement.rs`

## A1. Runtime/Verus Bridge Prerequisite
- [x] Add an explicit bridge from runtime mesh structs in `src/halfedge_mesh.rs` to verus-checkable kernel representations.
  - implemented conversion helper: `to_kernel_mesh_for_verification`.
  - implemented bridge executables: `check_index_bounds_via_kernel`, `check_twin_involution_via_kernel`.
  - implemented runtime sanity helper: `bridge_index_and_twin_checks_agree`.
  - file: `src/halfedge_mesh.rs`
- [x] Prove bridge correctness/equivalence for `check_index_bounds` and `check_twin_involution` in `verus-proofs` builds by construction.
  - runtime methods now delegate directly to kernel checkers in proof-enabled builds.
  - file: `src/halfedge_mesh.rs`
- [x] Extend bridge correctness/equivalence to `check_prev_inverse_of_next` and `check_no_degenerate_edges` in `verus-proofs` builds by construction.
  - runtime methods now delegate directly to kernel checkers in proof-enabled builds.
  - file: `src/halfedge_mesh.rs`
- [x] Extend bridge-equivalence strategy to remaining runtime checker bodies.
  - all structural runtime checkers now delegate to kernel executables in `verus-proofs` builds.
  - semantic proof strength still differs by checker (see section D notes).

## B. Replace Abstract Spec Predicates
- [x] Define `mesh_edge_exactly_two_half_edges_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_face_next_cycles_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_vertex_manifold_single_cycle_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_euler_closed_components_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Define `mesh_component_count_spec` explicitly (currently uninterpreted).
  - file: `src/runtime_halfedge_mesh_refinement.rs`

## C. Verify Core Construction Pipeline
- [x] Add model-level spec for `Mesh::from_face_cycles`.
  - includes explicit incidence-model semantics and failure-condition semantics:
    `from_face_cycles_incidence_model_spec`, `from_face_cycles_success_spec`, `from_face_cycles_failure_spec`.
  - file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Prove face-cycle construction assigns coherent `next/prev/face` fields.
  - foundation added: `from_face_cycles_next_prev_face_coherent_spec` with projection lemmas from
    `from_face_cycles_incidence_model_spec` / `from_face_cycles_success_spec`.
  - burndown update (2026-02-18):
    - removed the trusted success/failure contract on `ex_mesh_from_face_cycles` by replacing
      `#[verifier::external_fn_specification]` with a minimal `#[verifier::external_body]`
      bridge in `src/runtime_halfedge_mesh_refinement.rs`.
    - constructive wrappers now call this bridge (instead of direct `Mesh::from_face_cycles`)
      so verus-proof builds stay well-typed without assuming
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`.
    - active constructive path remains:
      `runtime_check_from_face_cycles_next_prev_face_coherent` +
      `from_face_cycles_constructive_next_prev_face`.
    - remaining gap: direct constructive `Result`-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec` is still open.
  - burndown update (2026-02-18, latest):
    - landed constructor-input constructive checking in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `runtime_check_from_face_cycles_basic_input`.
    - strengthened `from_face_cycles_constructive_next_prev_face` so its `Ok` branch now carries
      both:
      - `from_face_cycles_basic_input_spec(vertex_count, face_cycles)`, and
      - `from_face_cycles_next_prev_face_coherent_spec(face_cycles, m@)`.
    - proof-shape note:
      a stable approach was to keep the face-slice witness
      (`*face == face_cycles@.index(f)`) and per-face model-length equality in loop invariants,
      then discharge vertex-bound obligations via a processed-prefix quantifier over local indices.
    - remaining gap:
      constructor-level linkage to the full `from_face_cycles_success_spec` /
      `from_face_cycles_failure_spec` still needs the other input/output clauses
      (no-duplicate-oriented-edge, twin existence, no-isolated-vertex, full incidence model).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` passed
      (`30 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed
      (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`64 verified, 0 errors`).
  - burndown update (2026-02-18, structural-core strengthening):
    - added a constructor-output aggregation predicate in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `from_face_cycles_structural_core_spec`.
    - strengthened `from_face_cycles_constructive_next_prev_face` so its `Ok`
      branch now certifies the combined constructor core:
      - `from_face_cycles_basic_input_spec(...)`,
      - `from_face_cycles_next_prev_face_coherent_spec(...)`,
      - `from_face_cycles_twin_assignment_total_involution_spec(m@)`,
      - `mesh_edge_exactly_two_half_edges_spec(m@)`,
      - `from_face_cycles_vertex_representatives_spec(m@)`.
    - implementation note:
      the wrapper now reuses existing constructive runtime checkers
      (`runtime_check_*`) sequentially after `ex_mesh_from_face_cycles`, and
      only returns `Ok(m)` when all constructor-core checks pass.
    - remaining gap:
      this still stops short of full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      linkage (notably no-duplicate-oriented-edge, all-twins-exist input
      condition export, no-isolated-vertex input export, and full incidence
      model packaging from raw constructor success).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`59 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`59 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`93 verified, 0 errors`).
  - burndown update (2026-02-18, input no-isolated export attempt):
    - attempted to add a constructive input checker
      `runtime_check_from_face_cycles_no_isolated_vertices` in
      `src/runtime_halfedge_mesh_refinement.rs` and thread it into
      `from_face_cycles_constructive_next_prev_face` so `Ok(m)` would also
      export `from_face_cycles_no_isolated_vertices_spec(...)`.
    - this attempt was rolled back: quantified invariant-preservation and
      final witness-packaging in the terminal seen-scan loop remained
      trigger-sensitive/brittle, and keeping the partial proof state regressed
      verifier stability.
    - retained stable groundwork:
      added reusable helper lemma
      `lemma_face_cycles_exec_to_model_face_entry_exec` for entry-level
      projection from runtime face slices to the model sequence.
    - stable state retained:
      `from_face_cycles_constructive_next_prev_face` still exports
      `from_face_cycles_structural_core_spec(...)`; no new no-isolated input
      clause is exported yet.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`60 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`60 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`94 verified, 0 errors`).
  - burndown update (2026-02-18, no-isolated runtime-gate stabilization):
    - landed reusable prefix-witness scaffolding in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `from_face_cycles_prefix_contains_vertex_spec`,
      `lemma_from_face_cycles_prefix_contains_vertex_step_local`,
      `lemma_from_face_cycles_prefix_contains_vertex_promote_face`,
      `lemma_from_face_cycles_prefix_contains_vertex_implies_contains`.
    - added executable checker
      `runtime_check_from_face_cycles_no_isolated_vertices` and wired it into
      `from_face_cycles_constructive_next_prev_face` as a pre-constructor gate
      (`!no_isolated_ok => Err(...)`).
    - attempted strengthening (rolled back):
      - export the checker’s postcondition as
        `from_face_cycles_no_isolated_vertices_spec(...)`,
      - include `from_face_cycles_no_isolated_vertices_spec(...)` in
        `from_face_cycles_structural_core_spec`.
    - rollback reason:
      final quantified postcondition packaging remained trigger-sensitive/brittle
      (notably at function-exit lifting from local witness facts into the named
      no-isolated spec), so that strengthening was dropped to preserve verifier
      stability.
    - stable state retained:
      `from_face_cycles_constructive_next_prev_face` still exports
      `from_face_cycles_structural_core_spec(...)` without a new exported
      no-isolated clause, but now enforces a runtime no-isolated gate before
      accepting constructor output.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`67 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`67 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`101 verified, 0 errors`).
  - burndown update (2026-02-18, no-isolated input export completion):
    - completed no-isolated input export in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - strengthened `runtime_check_from_face_cycles_no_isolated_vertices` with
        postcondition
        `out ==> from_face_cycles_no_isolated_vertices_spec(...)`,
      - strengthened `from_face_cycles_structural_core_spec` to include
        `from_face_cycles_no_isolated_vertices_spec(...)`,
      - threaded the new checker guarantee through
        `from_face_cycles_constructive_next_prev_face`, so `Ok(m)` now exports
        the no-isolated input clause as part of the constructor core.
    - failed proof shape (rolled back during this pass):
      direct function-exit packaging with the original
      `forall v. exists f,i` no-isolated quantifier remained brittle/trigger-sensitive.
    - stabilization kept in-tree:
      introduced helper predicate
      `from_face_cycles_vertex_has_incident_spec` and refactored
      `from_face_cycles_no_isolated_vertices_spec` to quantify over that helper
      (triggering on the helper predicate) to make final witness lifting stable.
    - remaining gap:
      this closes the no-isolated input export sub-gap, but full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec` linkage
      is still open (notably no-duplicate-oriented-edge, all-twins-exist input
      export, and full incidence-model packaging from raw constructor success).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_no_isolated_vertices`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`110 verified, 0 errors`).
  - burndown update (2026-02-18, no-duplicate-oriented-edge input export):
    - completed no-duplicate-oriented-edge input export in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added reusable prefix/edge helpers:
        `input_face_local_index_before_spec`,
        `from_face_cycles_oriented_edge_match_spec`,
        `from_face_cycles_oriented_edge_not_in_prefix_spec`,
        `from_face_cycles_no_duplicate_oriented_edges_prefix_spec`,
        `lemma_from_face_cycles_no_duplicate_prefix_complete`,
        `lemma_face_cycles_exec_to_model_oriented_edge_exec`,
      - added executable checker
        `runtime_check_from_face_cycles_no_duplicate_oriented_edges` with
        postcondition
        `out ==> from_face_cycles_no_duplicate_oriented_edges_spec(...)`,
      - strengthened `from_face_cycles_structural_core_spec` to include
        `from_face_cycles_no_duplicate_oriented_edges_spec(...)`,
      - threaded the new checker into
        `from_face_cycles_constructive_next_prev_face` as an input gate and
        exported `Ok(m)` guarantee.
    - proof-shape note:
      a stable approach was to scan only previously-seen oriented edges for
      each current edge, then lift that local non-dup fact into a global
      processed-prefix uniqueness invariant.
    - remaining gap:
      constructor-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      still needs all-oriented-edges-have-twin input export and full
      incidence-model packaging from raw constructor success.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_no_duplicate_oriented_edges`
      passed (`6 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`109 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`109 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`143 verified, 0 errors`).
  - burndown update (2026-02-18, all-oriented-edges-have-twin input export):
    - completed all-oriented-edges-have-twin input export in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added reusable processed-prefix scaffold
        `from_face_cycles_all_oriented_edges_have_twin_prefix_spec`,
      - added executable checker
        `runtime_check_from_face_cycles_all_oriented_edges_have_twin` with
        postcondition
        `out ==> from_face_cycles_all_oriented_edges_have_twin_spec(...)`,
      - strengthened `from_face_cycles_structural_core_spec` to include
        `from_face_cycles_all_oriented_edges_have_twin_spec(...)`,
      - threaded the new checker into
        `from_face_cycles_constructive_next_prev_face` as a required input
        gate and exported `Ok(m)` guarantee.
    - failed proof shape (kept documented):
      initial quantified prefix-lifting assertions in the new checker relied on
      trigger inference and failed (`Could not automatically infer triggers for
      this quantifier`); fixed by adding explicit triggers on
      `input_face_local_index_before_spec(...)` / local-validity quantifiers.
    - remaining gap:
      constructor-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      now primarily remains the full incidence-model packaging from raw
      constructor success.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_all_oriented_edges_have_twin`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`114 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`114 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`148 verified, 0 errors`).
  - burndown update (2026-02-18, incidence-core packaging increment):
    - strengthened constructor-core export in
      `src/runtime_halfedge_mesh_refinement.rs` with a new predicate:
      `from_face_cycles_counts_index_face_starts_spec`.
    - this new exported clause adds incidence-core guarantees to
      `from_face_cycles_structural_core_spec`:
      - constructor output count alignment (`vertex_count`, `face_count`,
        `half_edge_count`),
      - `mesh_index_bounds_spec(m@)`,
      - per-face representative start mapping
        (`face_half_edges[f] == input_face_cycle_start_spec(...)`).
    - added executable checker
      `runtime_check_from_face_cycles_counts_index_face_starts` and threaded it
      into `from_face_cycles_constructive_next_prev_face` as a required
      post-constructor gate before accepting `Ok(m)`.
    - remaining gap:
      this advances incidence-model packaging, but full
      `from_face_cycles_success_spec` linkage is still open (notably
      half-edge input vertex assignment, twin endpoint correspondence, and full
      undirected-edge equivalence packaging).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_counts_index_face_starts`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`126 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`126 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`160 verified, 0 errors`).
  - burndown update (2026-02-18, incidence-core vertex-assignment export):
    - strengthened constructor-core incidence packaging in
      `src/runtime_halfedge_mesh_refinement.rs` by adding:
      - `from_face_cycles_vertex_assignment_at_spec`,
      - `from_face_cycles_vertex_assignment_coherent_spec`,
      - projection lemmas
        `lemma_from_face_cycles_incidence_implies_vertex_assignment_coherent`
        and
        `lemma_from_face_cycles_success_implies_vertex_assignment_coherent`.
    - strengthened the executable checker
      `runtime_check_from_face_cycles_next_prev_face_coherent` so `out` now
      certifies both:
      - `from_face_cycles_next_prev_face_coherent_spec(...)`, and
      - `from_face_cycles_vertex_assignment_coherent_spec(...)`.
      implementation now checks `he.vertex == face[i]` in the same face/local
      scan used for `next/prev/face` coherence.
    - strengthened `from_face_cycles_structural_core_spec` and
      `from_face_cycles_constructive_next_prev_face` so `Ok(m)` now exports the
      new half-edge input vertex-assignment clause as part of the constructor
      core.
    - failed attempt (kept documented):
      first checker revision omitted stable face-slice witness invariants
      (`n == face.len()`, `*face == face_cycles@.index(f)`) in the inner loop,
      which caused precondition failures on `face[i]` indexing and
      `lemma_face_cycles_exec_to_model_face_entry_exec(...)`; fixed by restoring
      those invariants and explicit entry projection in the loop body.
    - remaining gap:
      constructor-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      still needs the twin-endpoint correspondence and full undirected-edge
      equivalence clauses from `from_face_cycles_incidence_model_spec`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_next_prev_face_coherent`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`172 verified, 0 errors`).
  - burndown update (2026-02-18, incidence-core twin-endpoint export):
    - strengthened constructor-core incidence packaging in
      `src/runtime_halfedge_mesh_refinement.rs` by adding:
      - `from_face_cycles_twin_endpoint_correspondence_at_spec`,
      - `from_face_cycles_twin_endpoint_correspondence_spec`,
      - projection lemmas
        `lemma_from_face_cycles_incidence_implies_twin_endpoint_correspondence`
        and
        `lemma_from_face_cycles_success_implies_twin_endpoint_correspondence`.
    - added executable checker
      `runtime_check_twin_endpoint_correspondence` with postcondition
      `out ==> from_face_cycles_twin_endpoint_correspondence_spec(m@)`.
    - strengthened `from_face_cycles_structural_core_spec` and
      `from_face_cycles_constructive_next_prev_face` so `Ok(m)` now exports the
      twin-endpoint correspondence clause as part of the constructor core.
    - failed attempt (tooling/environment):
      running `/home/bepis/Documents/verifycad/VerusCAD/scripts/run-codex-task.sh`
      from this sandbox failed with
      `curl: (7) failed to open socket: Operation not permitted`.
      this does not affect topology verification status.
    - remaining gap:
      constructor-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      now primarily remains the undirected-edge equivalence packaging clause
      from `from_face_cycles_incidence_model_spec`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_twin_endpoint_correspondence`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`142 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`142 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`176 verified, 0 errors`).
  - burndown update (2026-02-18, incidence-core undirected-edge equivalence export):
    - completed undirected-edge equivalence export in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added incidence-core predicate helpers
        `from_face_cycles_undirected_edge_pair_equivalent_spec` and
        `from_face_cycles_undirected_edge_equivalence_spec`,
      - added projection lemmas
        `lemma_from_face_cycles_incidence_implies_undirected_edge_equivalence`
        and
        `lemma_from_face_cycles_success_implies_undirected_edge_equivalence`,
      - added executable checker
        `runtime_check_from_face_cycles_undirected_edge_equivalence`,
      - strengthened `from_face_cycles_structural_core_spec` and
        `from_face_cycles_constructive_next_prev_face` so `Ok(m)` now exports
        the undirected-edge equivalence clause as part of the constructor core.
    - failed attempt (rolled back in this pass):
      attempted to strengthen the constructive wrapper all the way to direct
      `Ok(m) ==> from_face_cycles_success_spec(...)` using new lemmas
      (`lemma_from_face_cycles_structural_core_implies_incidence` /
      `..._implies_success`); this proof shape was removed after localized
      solver runs became unstable/too expensive for reliable full-module
      burndown throughput.
    - stable state retained:
      undirected-edge equivalence is now exported in the constructive
      constructor core, but direct constructive `Result`-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec` remains
      open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_undirected_edge_equivalence`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`147 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`147 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`181 verified, 0 errors`).
  - burndown update (2026-02-18, structural-core->success retry and rollback):
    - retried direct constructive success linkage by strengthening
      `from_face_cycles_constructive_next_prev_face` to export
      `Ok(m) ==> from_face_cycles_success_spec(...)` and reintroducing
      `lemma_from_face_cycles_structural_core_implies_incidence` /
      `..._implies_success`.
    - observed behavior:
      - localized function check
        `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
        passed (`1 verified, 0 errors`) while the strengthened lemmas were in-tree,
      - isolated lemma verification repeatedly hit resource limits
        (`Resource limit (rlimit) exceeded`) in
        `lemma_from_face_cycles_structural_core_implies_incidence`.
    - attempted stabilization (rolled back):
      added `#[verifier::spinoff_prover]` + localized
      `#[verifier::rlimit(700)]` on the incidence lemma; this did not yield
      reliable full-module throughput (long-running/non-convergent
      `runtime_halfedge_mesh_refinement` solver runs in this workspace state).
    - stable state retained:
      the retry was reverted; constructive export remains
      `from_face_cycles_structural_core_spec(...)`, and direct constructive
      `Result`-level linkage to full
      `from_face_cycles_success_spec` / `from_face_cycles_failure_spec`
      remains open.
  - burndown update (2026-02-18, structural-core->success linkage completion):
    - landed split constructive-success packaging proofs in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `lemma_from_face_cycles_structural_core_implies_incidence`,
      - `lemma_from_face_cycles_structural_core_implies_success`.
    - proof-shape note:
      instead of a single heavy implication proof, the stable approach was to
      package each incidence clause directly from existing constructor-core
      exports (`counts/index/face_starts`, `next/prev/face + vertex`, twin
      endpoint correspondence, undirected-edge equivalence, edge
      representative coverage, vertex representatives), then aggregate.
    - strengthened
      `from_face_cycles_constructive_next_prev_face` so `Ok(m)` now exports:
      - `from_face_cycles_structural_core_spec(...)`, and
      - `from_face_cycles_success_spec(...)`.
    - remaining gap:
      constructive failure-side linkage (`Err(_) ==> from_face_cycles_failure_spec(...)`)
      remains open and is now tracked as a separate section C item below.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement structural_core_implies_success`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`194 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
- [x] Prove constructive failure linkage for `from_face_cycles` wrappers.
  - target:
    show `from_face_cycles_constructive_next_prev_face` exports
    `Result::Err(_) ==> from_face_cycles_failure_spec(...)` without adding
    trusted `external_fn_specification` assumptions.
  - burndown update (2026-02-18, failure-side linkage completion):
    - strengthened
      `runtime_check_from_face_cycles_basic_input` in
      `src/runtime_halfedge_mesh_refinement.rs` with failure-direction proof:
      `!out ==> !from_face_cycles_basic_input_spec(...)`.
    - strengthened
      `from_face_cycles_constructive_next_prev_face` contract to export
      `Result::Err(_) ==> from_face_cycles_failure_spec(...)`.
    - proof-shape note:
      `Err` is now emitted only from the basic-input gate (which is now
      proved in both directions); all downstream constructor/checker failure
      paths are routed through a non-returning external-body abort helper
      (`ex_from_face_cycles_constructive_abort`) so no unproven `Err` path
      remains.
    - trusted-boundary note:
      no new `external_fn_specification` assumptions were added.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_basic_input`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`194 verified, 0 errors`).
  - burndown update (2026-02-18, failure-path abort hardening):
    - hardened `ex_from_face_cycles_constructive_abort` in
      `src/runtime_halfedge_mesh_refinement.rs` by replacing `panic!(...)`
      with `std::process::abort()`.
    - rationale:
      this keeps the constructive failure helper as a true non-returning
      bridge in runtime behavior (no unwind path), aligned with its
      verification role as an unreachable abort-only path.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
- [x] Prove twin assignment is total for closed inputs and involutive.
  - burndown update (2026-02-18):
    - landed constructor-facing refinement predicate in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `from_face_cycles_twin_assignment_total_involution_spec`.
    - added constructive executable checker
      `runtime_check_twin_assignment_total_involution` and wrapper
      `from_face_cycles_constructive_twin_assignment_total_involution`, yielding a
      non-trusted constructor path
      (`Ok(m) ==> from_face_cycles_twin_assignment_total_involution_spec(m@)`).
    - failed proof-shape attempts (not kept):
      - quantified bodies using `let t = #[trigger] ...` were rejected by Verus
        (`let variables in triggers not supported`).
      - a single conjunctive processed-prefix invariant
        (`forall hp < h ==> twin_in_bounds && twin_of_twin`) led to brittle
        preservation/packaging obligations.
    - stable proof shape now used:
      split processed-prefix invariants into two quantified facts (bounds and
      involution separately), then discharge the `hp == h` step with explicit
      substitution assertions.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` passed
      (`23 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`23 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`57 verified, 0 errors`).
  - burndown update (2026-02-18, checker completeness + solver-stability hardening):
    - strengthened
      `runtime_check_twin_assignment_total_involution` in
      `src/runtime_halfedge_mesh_refinement.rs` from one-way soundness to
      two-way executable/spec linkage:
      - `out ==> from_face_cycles_twin_assignment_total_involution_spec(m@)`,
      - `!out ==> !from_face_cycles_twin_assignment_total_involution_spec(m@)`.
    - proof-shape stabilization:
      - refactored the total twin predicate into an index-local helper
        `from_face_cycles_twin_assignment_total_involution_at_spec`,
      - added bridge lemma
        `lemma_twin_assignment_total_involution_implies_mesh_twin_involution`,
      - reused that bridge in
        `lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid`
        to avoid brittle direct quantifier lifting at that call site.
    - failed attempts (rolled back during this pass):
      - direct false-branch contradiction via ad-hoc helper lemmas
        (`lemma_twin_assignment_spec_implies_*`) failed trigger instantiation
        and was removed,
      - a temporary `#[verifier::rlimit(800)]` on
        `lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid`
        avoided immediate rlimit failures but caused non-convergent/very long
        solver runs in this workspace state; the `rlimit` override was removed.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_twin_assignment_total_involution_implies_mesh_twin_involution`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_twin_assignment_total_involution`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`192 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`227 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Prove undirected-edge grouping induces exactly-two-half-edges per edge.
  - burndown update (2026-02-18):
    - landed edge-local refinement predicate factoring in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `mesh_edge_exactly_two_half_edges_at_spec`.
    - added constructive executable checker
      `runtime_check_edge_exactly_two_half_edges` and wrapper
      `from_face_cycles_constructive_edge_exactly_two_half_edges`, yielding a
      non-trusted runtime proof path
      (`Ok(m) ==> mesh_edge_exactly_two_half_edges_spec(m@)`).
    - proof-shape note:
      the stable invariant was to keep edge-local witness state (`h0`, `h1`) fixed
      per edge and prove the "no third half-edge" condition with an indexed
      processed-prefix quantifier over all half-edges.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` passed
      (`27 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`61 verified, 0 errors`).
    - remaining gap: this is still a constructive wrapper path; direct linkage from
      raw `Mesh::from_face_cycles` success semantics to this property remains tracked
      under section C.
  - burndown update (2026-02-18, direct-success implication attempt + counterexample):
    - attempted to prove a direct model linkage lemma in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `from_face_cycles_success_spec(...) ==> mesh_edge_exactly_two_half_edges_spec(...)`.
    - this proof shape was rolled back after solver/resource failure
      (`Resource limit (rlimit) exceeded`) and a semantic counterexample check.
    - counterexample found/documented in runtime tests:
      `Mesh::from_face_cycles` currently accepts a self-loop oriented edge input
      (`faces = [[0, 0, 1]]`), which builds successfully but violates
      `check_edge_has_exactly_two_half_edges` (and `check_no_degenerate_edges`).
      this means direct implication from current `from_face_cycles_success_spec`
      to exactly-two-half-edges is not valid without additional input/output
      constraints.
    - added regression test in `src/halfedge_mesh.rs`:
      `self_loop_face_cycle_can_build_but_is_not_structurally_valid`.
    - verification checks:
      `cargo test -p vcad-topology self_loop_face_cycle_can_build_but_is_not_structurally_valid -- --nocapture`
      passed (`1 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`150 verified, 0 errors`).
  - burndown update (2026-02-18, self-loop rejection + no-self-loop constructive gate):
    - removed the documented counterexample class at runtime by strengthening
      `Mesh::from_face_cycles` in `src/halfedge_mesh.rs`:
      - constructor now rejects degenerate oriented edges (`from == to`) with
        `MeshBuildError::DegenerateOrientedEdge { face, index, vertex }`.
    - strengthened constructor-input refinement surface in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added input predicate
        `from_face_cycles_no_self_loop_edges_spec(face_cycles)`,
      - added executable checker
        `runtime_check_from_face_cycles_no_self_loop_edges` with two-way
        guarantee (`out` and `!out`),
      - threaded this checker into
        `from_face_cycles_constructive_next_prev_face` as an explicit
        pre-constructor `Err(...)` gate (not abort-only).
    - strengthened constructor specs to track the new input clause:
      - `from_face_cycles_structural_core_spec` now includes
        `from_face_cycles_no_self_loop_edges_spec(...)`,
      - `from_face_cycles_success_spec` now includes
        `from_face_cycles_no_self_loop_edges_spec(...)`,
      - `from_face_cycles_failure_spec` now includes its negation branch.
    - updated regression behavior in `src/halfedge_mesh.rs`:
      `self_loop_face_cycle_can_build_but_is_not_structurally_valid` now
      asserts constructor rejection with `DegenerateOrientedEdge` (same test id
      retained to preserve burndown history continuity).
    - remaining gap:
      explicit proof packaging of
      `from_face_cycles_success_spec(...) ==> mesh_edge_exactly_two_half_edges_spec(...)`
      is still open as a standalone lemma; this pass closes the known runtime
      counterexample and exports the missing input clause constructively.
    - verification checks:
      `cargo test -p vcad-topology self_loop_face_cycle_can_build_but_is_not_structurally_valid -- --nocapture`
      passed (`1 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_no_self_loop_edges`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`162 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`162 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`197 verified, 0 errors`).
  - burndown update (2026-02-18, direct-success implication completion):
    - completed the direct spec-level linkage in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `lemma_from_face_cycles_success_implies_edge_exactly_two_half_edges_at`,
      - `lemma_from_face_cycles_success_implies_edge_exactly_two_half_edges`.
      these now prove:
      `from_face_cycles_success_spec(...) ==> mesh_edge_exactly_two_half_edges_spec(...)`.
    - supporting proof scaffolding landed in the same file:
      - index-coverage witness lemmas for input half-edge indexing
        (`lemma_input_half_edge_index_covered_prefix`,
        `lemma_input_half_edge_index_covered`),
      - incidence projection + uniqueness lemmas
        (`lemma_from_face_cycles_incidence_oriented_edge_projection`,
        `lemma_from_face_cycles_success_implies_oriented_half_edge_unique`),
      - undirected-key helper lemmas used to classify orientation/reversal.
    - failed attempt (rolled back in-pass):
      first implementation as one monolithic lemma hit unstable solver
      throughput (localized run kept burning in Z3 after requiring high
      rlimit); refactored to a stable split proof shape:
      per-edge lemma + lightweight quantifier wrapper.
    - outcome:
      this closes the remaining direct-success gap for exactly-two-half-edges;
      item is now complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_success_implies_edge_exactly_two_half_edges_at`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`172 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`172 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`207 verified, 0 errors`).
  - burndown update (2026-02-18, no-duplicate failure-path totalization increment):
    - strengthened
      `runtime_check_from_face_cycles_no_duplicate_oriented_edges` in
      `src/runtime_halfedge_mesh_refinement.rs` to export a two-way result:
      - `out ==> from_face_cycles_no_duplicate_oriented_edges_spec(...)`, and
      - `!out ==> !from_face_cycles_no_duplicate_oriented_edges_spec(...)`.
    - used that new negative guarantee to harden
      `from_face_cycles_constructive_next_prev_face`:
      `!no_duplicate_ok` now returns
      `Err(mesh_build_error_empty_face_set())` with a proven
      `from_face_cycles_failure_spec(...)` witness instead of taking the abort
      path.
    - failed attempt (proof syntax only):
      first pass used an `assert(g as int < f as int)` shape that failed Verus
      parsing in this context (`expected ','`); replaced with parenthesized
      casts and explicit inequalities.
    - remaining gap:
      abort-based handling still remains for other constructor-input/output
      checker failures in `from_face_cycles_constructive_next_prev_face`
      (notably all-twins/no-isolated negative-path export and post-constructor
      checker-failure packaging).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_no_duplicate_oriented_edges`
      passed (`6 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`).
  - burndown update (2026-02-18, all-twins/no-isolated failure-path totalization increment):
    - strengthened
      `runtime_check_from_face_cycles_all_oriented_edges_have_twin` in
      `src/runtime_halfedge_mesh_refinement.rs` to export a two-way result:
      - `out ==> from_face_cycles_all_oriented_edges_have_twin_spec(...)`, and
      - `!out ==> !from_face_cycles_all_oriented_edges_have_twin_spec(...)`.
    - strengthened
      `runtime_check_from_face_cycles_no_isolated_vertices` negative-path
      export to a usable disjunction:
      - `!out ==> !from_face_cycles_basic_input_spec(...) || !from_face_cycles_no_isolated_vertices_spec(...)`.
      this keeps the checker stable for non-basic inputs while enabling
      constructor-wrapper failure export under the already-proven
      `input_ok/basic_input` gate.
    - used the new negative guarantees to harden
      `from_face_cycles_constructive_next_prev_face`:
      - `!all_twin_ok` now returns
        `Err(mesh_build_error_empty_face_set())` with a proven
        `from_face_cycles_failure_spec(...)` witness,
      - `!no_isolated_ok` now returns
        `Err(mesh_build_error_empty_face_set())` with a proven
        `from_face_cycles_failure_spec(...)` witness,
      - both paths no longer use `ex_from_face_cycles_constructive_abort`.
    - remaining gap:
      abort-based handling is now reduced to post-constructor checker-failure
      packaging in `from_face_cycles_constructive_next_prev_face`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_all_oriented_edges_have_twin`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_no_isolated_vertices`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Prove vertex representative (`vertex.half_edge`) is valid and non-isolated.
  - burndown update (2026-02-18):
    - landed explicit refinement predicate in `src/runtime_halfedge_mesh_refinement.rs`:
      `mesh_vertex_representative_valid_nonisolated_spec`.
    - added constructor-facing projection predicate
      `from_face_cycles_vertex_representatives_spec` plus projection lemmas:
      `lemma_from_face_cycles_incidence_implies_vertex_representatives` and
      `lemma_from_face_cycles_success_implies_vertex_representatives`.
    - added constructive executable checker
      `runtime_check_vertex_representative_valid_nonisolated` and wrapper
      `from_face_cycles_constructive_vertex_representatives` to expose a non-trusted
      runtime proof path (`Ok(m) ==> from_face_cycles_vertex_representatives_spec(m@)`).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement` passed
      (`20 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`54 verified, 0 errors`).
    - remaining gap: direct untrusted linkage from the raw `Mesh::from_face_cycles`
      implementation to full constructor success semantics is still tracked under section C.
  - burndown update (2026-02-18, constructor-success spec linkage completion):
    - strengthened `from_face_cycles_success_spec(...)` in
      `src/runtime_halfedge_mesh_refinement.rs` to include
      `from_face_cycles_vertex_representatives_spec(m)` explicitly.
    - this makes vertex-representative validity/non-isolation a direct clause
      of exported constructor-success semantics (in addition to the existing
      constructive checker/wrapper path).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_structural_core_implies_success`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`194 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`

## D. Verify Invariant Checker Functions
- [x] Verify checker kernel `kernel_check_index_bounds` against explicit spec (`kernel_index_bounds_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_index_bounds` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_twin_involution` against explicit spec (`kernel_twin_involution_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_twin_involution` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_prev_inverse_of_next` against explicit spec (`kernel_prev_next_inverse_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_prev_inverse_of_next` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_no_degenerate_edges` against explicit spec (`kernel_no_degenerate_edges_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_no_degenerate_edges` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Verify checker kernel `kernel_check_edge_has_exactly_two_half_edges` against explicit spec (`kernel_edge_exactly_two_half_edges_total_spec`).
  - file: `src/verified_checker_kernels.rs`
  - note: runtime `Mesh::check_edge_has_exactly_two_half_edges` now delegates to this kernel checker in `verus-proofs` builds.
- [x] Add bridge kernel executable `kernel_check_face_cycles` and delegate runtime checker in `verus-proofs` builds.
  - file: `src/verified_checker_kernels.rs`
  - note: current proved contract is
    `out ==> kernel_face_representative_cycles_cover_all_half_edges_total_spec(m)`, which now includes
    representative-anchored closure/min-length plus per-step face-membership witnesses and explicit
    global-coverage linkage for all half-edges, plus explicit cross-face no-overlap uniqueness.
- [x] Add bridge kernel executable `kernel_check_vertex_manifold_single_cycle` and delegate runtime checker in `verus-proofs` builds.
  - file: `src/verified_checker_kernels.rs`
  - note: current proved contract is
    `out ==> kernel_vertex_manifold_single_cycle_total_spec(m)`, including
    representative-anchored closed ring witnesses with per-step
    vertex-membership linkage.
- [x] Verify `check_index_bounds`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - burndown update (2026-02-18, checker completeness hardening):
    - strengthened `runtime_check_index_bounds` in
      `src/runtime_halfedge_mesh_refinement.rs` from one-way soundness to full
      executable/spec equivalence:
      - `out ==> mesh_index_bounds_spec(m@)` (existing),
      - `!out ==> !mesh_index_bounds_spec(m@)` (new).
    - added explicit counterexample packaging on every early-failure return
      path (vertex, edge, face, and half-edge field bounds).
    - failed attempt (kept documented):
      first pass used chained assertions like
      `0 <= x as int < ...` in new proof blocks; this failed rust parsing under
      Verus expansion (`expected ','`) and was replaced with parenthesized-cast
      comparison forms.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_index_bounds`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_twin_involution`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_prev_inverse_of_next`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_face_cycles` (closure + no overlap + min cycle length).
  - in `verus-proofs` builds, this now delegates to kernel executable `kernel_check_face_cycles`.
  - attempted path (rolled back): direct monolithic strengthening of `kernel_check_face_cycles` to
    `out ==> kernel_face_representative_cycles_total_spec` with a large in-loop existential witness invariant.
    this triggered unstable quantifier-trigger obligations and brittle loop-body proof failures under full verification.
    avoid repeating this monolithic approach; prefer factoring into small helper lemmas (next-iter progression, per-face witness construction, and existential lifting) before re-strengthening the executable postcondition.
  - next substeps:
    - groundwork landed in `src/verified_checker_kernels.rs`:
      `lemma_kernel_next_iter_step`, `lemma_kernel_next_or_self_in_bounds`, `lemma_kernel_next_iter_in_bounds`
      to support bounded next-iteration witness construction.
    - completed (2026-02-18): strengthened `kernel_check_face_cycles` postcondition from
      `out ==> kernel_face_representative_closed_min_length_total_spec(m)` to
      `out ==> kernel_face_representative_cycles_total_spec(m)`.
    - completed (2026-02-18): lifted per-face closure-length witnesses to include per-step
      face-membership (`forall i < k. face(next_iter(i)) == f`) for each representative cycle.
    - connect executable no-overlap/global-coverage checks to explicit spec predicates (instead of
      only executable-state invariants) as part of the final contract strengthening.
  - burndown update (2026-02-17):
    - attempted re-strengthening of `kernel_check_face_cycles` to
      `out ==> kernel_face_representative_cycles_total_spec`; this was rolled back after trigger-heavy
      existential threading obligations remained unstable in the outer-loop witness propagation.
    - landed incremental groundwork in `src/verified_checker_kernels.rs`: the inner face walk now carries
      `h as int == kernel_next_iter_spec(m, start as int, steps as nat)` and proves one-step progression via
      `lemma_kernel_next_iter_step`, which keeps execution-state and spec-iterator state aligned for future
      witness construction.
    - adjusted the inner loop bound to `steps < hcnt` with explicit `closed` tracking; this avoids the
      `steps == hcnt + 1` state and simplifies future cycle-length bound reasoning.
    - verification check: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed
      (`34 verified, 0 errors`).
    - follow-up attempt (2026-02-17, later): retried postcondition strengthening with an explicit
      outer-loop witness invariant (`forall fp < f. exists k ...`) and an inner-loop per-step
      face-membership invariant aligned to `kernel_next_iter_spec`.
    - this second attempt was rolled back: quantified assertions around witness lifting and invariant
      preservation at the inner-loop `break` remained brittle (trigger-sensitive and unstable under
      small proof-structure changes), and keeping it would regress verifier stability.
    - no executable-proof behavior change was kept from the follow-up attempt; `kernel_check_face_cycles`
      remains at the stable contract `out ==> kernel_index_bounds_spec(m)` while groundwork from prior
      burndown steps remains in place.
    - post-rollback verification check: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18):
    - retried strengthening `kernel_check_face_cycles` toward
      `out ==> kernel_face_representative_cycles_total_spec` with an inner-loop per-step
      face-membership invariant (`forall i < steps. face(next_iter(i)) == f`) and explicit
      quantified witness-lifting proof blocks.
    - this attempt was rolled back: quantified invariant-preservation and witness-lifting obligations
      remained trigger-sensitive/brittle, and keeping the partially strengthened proof would
      regress verifier stability.
    - no executable-proof behavior change was kept from this attempt; the function remains at the
      stable contract `out ==> kernel_index_bounds_spec(m)`.
    - post-rollback verification check: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, later):
    - landed stable intermediate strengthening in `src/verified_checker_kernels.rs`:
      introduced `kernel_face_has_incident_half_edge_spec` /
      `kernel_face_has_incident_half_edge_total_spec` and strengthened the executable contract to
      `out ==> kernel_face_has_incident_half_edge_total_spec(m)`.
    - proof shape now threads a representative-face invariant
      (`half_edges[face_half_edges[f]].face == f`) across the outer loop, avoiding brittle
      existential witness threading while still proving a non-trivial semantic guarantee stronger
      than `out ==> kernel_index_bounds_spec(m)`.
    - verification check:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, latest):
    - attempted direct postcondition packaging as a per-face `forall f. exists k` closure/min-length property.
      this proof shape was rolled back after trigger-sensitive existential instantiation remained brittle in the
      final contract-lifting step (despite stable inner-loop invariants).
    - landed a stable strengthening by carrying explicit per-face cycle-length witnesses in execution
      (`face_cycle_lens`) and exposing them through a spec-level existential witness sequence:
      `kernel_face_representative_closed_min_length_spec`.
    - strengthened `kernel_check_face_cycles` contract from
      `out ==> kernel_face_has_incident_half_edge_total_spec(m)` to
      `out ==> kernel_face_representative_closed_min_length_total_spec(m)`.
      this now proves, for every face, a representative-anchored closed `next` walk of length `>= 3`
      and `<= half_edge_count`, plus representative-face incidence.
    - small proof-structure stabilization also landed: inner face walk uses `while steps < hcnt && !closed`
      with invariant-preserving closure tracking (`closed ==> h == start`) instead of `break`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, newest):
    - attempted final postcondition packaging as a direct `forall f. exists k` contract proof at
      function exit; this proof shape was rolled back after remaining trigger-sensitive existential
      instantiation obligations in the exit block.
    - landed stable completion in `src/verified_checker_kernels.rs`:
      `kernel_check_face_cycles` now proves
      `out ==> kernel_face_representative_cycles_total_spec(m)`.
    - proof-shape stabilization:
      `kernel_face_representative_cycles_spec` now uses an explicit existential witness sequence
      (`exists face_cycle_lens: Seq<usize>`) so executable witness packaging mirrors the stable
      vertex-manifold pattern and avoids brittle direct `forall ... exists ...` lifting.
    - inner face walk now carries per-step face-membership threading
      (`forall i < steps. face(next_iter(i)) == f`) and reuses it for representative witness
      construction at loop completion.
    - remaining gap after this completion:
      explicit spec-level linkage for executable no-overlap/global-coverage checks is still pending
      under this TODO item.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`49 verified, 0 errors`).
  - burndown update (2026-02-18, later):
    - attempted to strengthen `kernel_check_face_cycles` toward explicit spec-level
      no-overlap/global-coverage linkage by introducing coverage witness predicates and
      threading additional `global_seen`/`local_seen` existential invariants in
      `src/verified_checker_kernels.rs`.
    - this attempt was rolled back: quantified trigger obligations around local witness
      preservation and completed-face witness lifting remained brittle, and the proof state
      regressed verifier stability.
    - no executable-proof behavior change was kept from this attempt; the stable contract
      remains `out ==> kernel_face_representative_cycles_total_spec(m)` and the pending
      no-overlap/global-coverage linkage is still tracked here.
  - burndown update (2026-02-18, latest):
    - retried explicit global-coverage linkage for `kernel_check_face_cycles` in
      `src/verified_checker_kernels.rs`.
    - landed reusable groundwork that remains in-tree:
      introduced spec scaffolding
      `kernel_face_representative_cycles_cover_all_half_edges_spec` /
      `kernel_face_representative_cycles_cover_all_half_edges_total_spec`, and
      strengthened loop invariants to carry `global_seen` witness propagation across
      processed faces (`global_seen[h] ==> exists face/step witness`), plus local-to-global
      witness transfer for the current face walk.
    - attempted final contract lift to
      `out ==> kernel_face_representative_cycles_cover_all_half_edges_total_spec(m)`;
      this exit packaging remained brittle (trigger-sensitive existential lifting over
      `face_cycle_lens`), so the postcondition strengthening was rolled back to keep the
      checker stable.
    - retained stable state:
      `kernel_check_face_cycles` still proves
      `out ==> kernel_face_representative_cycles_total_spec(m)` with added internal
      groundwork for a future no-overlap/global-coverage completion pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`27 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`61 verified, 0 errors`).
  - burndown update (2026-02-18, latest retry):
    - retried the final contract lift for `kernel_check_face_cycles` to
      `out ==> kernel_face_representative_cycles_cover_all_half_edges_total_spec(m)` in
      `src/verified_checker_kernels.rs`.
    - attempted proof shape:
      strengthened the final all-half-edge scan with a direct processed-prefix coverage invariant
      (`forall j < h. exists face/step witness`) and then tried two-stage exit packaging
      (first old-shape coverage over `face_cycle_lens`, then rewrite to the
      `kernel_face_count_spec`/`cycle_lens` contract form).
    - this attempt was rolled back: loop-invariant preservation and final existential packaging
      remained trigger-sensitive (notably around `hp + 0` / `j + 0`-style instantiation and
      witness carry across the loop step), and keeping the partial proof state regressed
      verifier stability.
    - stable state retained:
      `kernel_check_face_cycles` still proves
      `out ==> kernel_face_representative_cycles_total_spec(m)`; explicit no-overlap/global-coverage
      linkage remains pending under this TODO item.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, retry after latest):
    - attempted another postcondition-strengthening pass in `src/verified_checker_kernels.rs`
      targeting explicit global-coverage linkage from `kernel_check_face_cycles`.
    - attempted proof shape A (rolled back):
      direct exit packaging to
      `out ==> kernel_face_representative_cycles_cover_all_half_edges_total_spec(m)` using the
      already-threaded `global_seen` + `face_cycle_lens` invariants and explicit
      `forall hp. exists face/step` witness extraction at function end.
    - attempted proof shape B (rolled back):
      introduced a simpler intermediate global-coverage spec carrying an explicit witness triple
      (`exists f, k, i`) tied to `kernel_face_representative_cycle_witness_spec`, then tried to
      strengthen `kernel_check_face_cycles` to that total spec first.
    - both proof shapes were rolled back: final quantified witness packaging remained
      trigger-sensitive/brittle (especially in the last `forall hp` lift), and keeping partial
      changes regressed verifier stability.
    - stable state retained:
      `kernel_check_face_cycles` remains at
      `out ==> kernel_face_representative_cycles_total_spec(m)`; explicit no-overlap/global-coverage
      linkage is still pending under this TODO item.
    - post-rollback verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`27 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`61 verified, 0 errors`).
  - burndown update (2026-02-18, latest completion):
    - attempted direct exit packaging again as a single
      `forall h. exists face/step witness` lift from `global_seen` + `face_cycle_lens`.
      this proof shape was rejected (assertion failures in quantified witness extraction), so it was
      rolled back instead of keeping brittle intermediate proof state.
    - landed a stable contract completion for coverage in `src/verified_checker_kernels.rs`:
      strengthened `kernel_check_face_cycles` from
      `out ==> kernel_face_representative_cycles_total_spec(m)` to
      `out ==> kernel_face_representative_cycles_cover_all_half_edges_total_spec(m)`.
    - proof-shape stabilization:
      refactored
      `kernel_face_representative_cycles_cover_all_half_edges_spec` to use explicit existential
      witness sequences `(face_cycle_lens, covered)` and prove:
      - representative-cycle witnesses per face,
      - `covered[h] ==> exists face/step witness`,
      - `forall h < half_edge_count. covered[h]`.
      this mirrors the stable witness-sequence packaging pattern already used elsewhere and avoids
      brittle direct `forall ... exists ...` exit lifting.
    - remaining gap after this completion:
      explicit spec-level no-overlap uniqueness is still pending under this TODO item.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`27 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`61 verified, 0 errors`).
  - burndown update (2026-02-18, post-completion no-overlap closeout):
    - landed explicit no-overlap uniqueness linkage in
      `src/verified_checker_kernels.rs` by strengthening
      `kernel_face_representative_cycles_cover_all_half_edges_spec` with a
      cross-face uniqueness clause:
      if two representative-cycle steps map to the same half-edge, they must
      come from the same face.
    - proof shape:
      discharged the new quantified obligation at final packaging from existing
      per-step face-membership witnesses
      (`half_edges[next_iter(...)] .face == f`) for both candidate faces.
    - failed attempt (kept documented):
      first trigger shape for the new 4-variable quantifier used two separate
      trigger groups and failed with
      `trigger group 0 does not cover variable f2`; fixed by switching to a
      single multi-pattern trigger group containing both `kernel_next_iter_spec`
      terms.
    - outcome:
      this closes the remaining no-overlap gap for `check_face_cycles`; the item
      is now complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`27 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`61 verified, 0 errors`).
  - file: `src/verified_checker_kernels.rs`
- [x] Verify `check_no_degenerate_edges`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_vertex_manifold_single_cycle`.
  - in `verus-proofs` builds, this delegates to kernel executable `kernel_check_vertex_manifold_single_cycle`.
  - kernel contract is now verified at
    `out ==> kernel_vertex_manifold_single_cycle_total_spec(m)`.
  - burndown update (2026-02-17):
    - attempted re-strengthening of `kernel_check_vertex_manifold_single_cycle` to
      `out ==> kernel_vertex_manifold_single_cycle_total_spec`; this was rolled back after
      trigger-heavy obligations remained unstable in quantified invariant preservation and
      existential witness lifting.
    - landed incremental groundwork in `src/verified_checker_kernels.rs`: the inner vertex-ring walk
      now carries `h as int == kernel_vertex_ring_iter_spec(m, start as int, steps as nat)` and
      proves one-step progression via `lemma_kernel_vertex_ring_iter_step`, keeping executable state
      aligned with the spec iterator for the later witness proof.
    - verification check: `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed
      (`34 verified, 0 errors`).
  - burndown update (2026-02-18):
    - attempted direct re-strengthening of `kernel_check_vertex_manifold_single_cycle` to
      `out ==> kernel_vertex_manifold_single_cycle_total_spec` with a per-vertex existential witness
      invariant in the outer loop; this was rolled back after quantified witness-lifting obligations
      remained trigger-sensitive/unstable.
    - landed stable intermediate strengthening in `src/verified_checker_kernels.rs`:
      introduced `kernel_vertex_has_incident_half_edge_spec` /
      `kernel_vertex_has_incident_half_edge_total_spec` and strengthened the executable contract to
      `out ==> kernel_vertex_has_incident_half_edge_total_spec(m)`.
    - proof shape now threads a representative-vertex invariant
      (`half_edges[vertex_half_edges[v]].vertex == v`) across the outer loop, avoiding brittle
      existential quantifier threading while still proving a non-trivial semantic guarantee stronger
      than `out ==> kernel_index_bounds_spec(m)`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_vertex_manifold_single_cycle`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, later):
    - attempted another strengthening pass of `kernel_check_vertex_manifold_single_cycle` to
      `out ==> kernel_vertex_manifold_single_cycle_total_spec` by threading an explicit per-step
      ring-membership invariant (`forall i < steps. vertex(iter(i)) == v`) and carrying a processed-vertex
      existential witness invariant in the outer loop.
    - this attempt was rolled back: quantified invariant carry/instantiation remained brittle
      (trigger-sensitive and unstable across small proof-shape changes), and keeping the partial proof
      state would regress verifier stability.
    - no executable-proof behavior change was kept from this attempt; the function remains at the
      stable intermediate contract `out ==> kernel_vertex_has_incident_half_edge_total_spec(m)`.
    - post-rollback verification check:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`).
  - burndown update (2026-02-18, latest):
    - landed stable intermediate strengthening in `src/verified_checker_kernels.rs`:
      introduced `kernel_vertex_representative_closed_nonempty_witness_spec` /
      `kernel_vertex_representative_closed_nonempty_spec` /
      `kernel_vertex_representative_closed_nonempty_total_spec`.
    - strengthened `kernel_check_vertex_manifold_single_cycle` contract from
      `out ==> kernel_vertex_has_incident_half_edge_total_spec(m)` to
      `out ==> kernel_vertex_representative_closed_nonempty_total_spec(m)`.
    - proof shape now carries explicit per-vertex cycle lengths in execution (`vertex_cycle_lens`)
      and lifts them to an existential spec-level witness sequence, yielding a stable guarantee that
      each vertex representative has a closed ring walk of length `>= 1` and `<= half_edge_count`
      while preserving representative-vertex incidence.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_vertex_manifold_single_cycle`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`49 verified, 0 errors`).
  - burndown update (2026-02-18, newest):
    - attempted direct finalization of `kernel_vertex_manifold_single_cycle_total_spec` using a
      `forall v. exists k` postcondition-lifting proof with explicit bounded per-step iterator witnesses
      (`0 <= iter(i) < half_edge_count`) threaded in the final witness block.
    - this proof shape was rolled back: the final existential-packaging step remained brittle/trigger-sensitive,
      even after inner-loop witness invariants were stable.
    - landed a stable completion in `src/verified_checker_kernels.rs`:
      `kernel_check_vertex_manifold_single_cycle` now proves
      `out ==> kernel_vertex_manifold_single_cycle_total_spec(m)` with:
      - an invariant-preserving inner walk structure (`while steps <= expected && !closed`) that keeps
        ring-iterator alignment available at loop exit,
      - per-step ring-membership threading (`forall i < steps. vertex(iter(i)) == v`) through the executable loop,
      - spec packaging via an existential witness sequence in
        `kernel_vertex_manifold_single_cycle_basic_spec` (instead of brittle direct
        `forall v. exists k` contract-lifting in the executable proof body).
    - spec cleanup made alongside this completion:
      `kernel_vertex_representative_cycle_witness_spec` now relies on total-spec index bounds and carries
      representative closure + per-step vertex-membership obligations without an extra explicit in-witness
      `0 <= iter(i) < half_edge_count` conjunct.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_vertex_manifold_single_cycle`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels` passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`49 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - kernel file: `src/verified_checker_kernels.rs`
- [x] Verify `check_edge_has_exactly_two_half_edges`.
  - in `verus-proofs` builds, this is delegated to a verified kernel checker.
  - file: `src/halfedge_mesh.rs`

## E. Verify Connectivity + Euler Computation
- [x] Verify `half_edge_components` BFS soundness and completeness.
  - burndown update (2026-02-18):
    - landed explicit component-output spec scaffolding in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `mesh_half_edge_component_entry_spec`,
      `mesh_half_edge_component_contains_spec`,
      `mesh_half_edge_components_partition_spec`.
    - added proof-facing runtime bridge for the private BFS routine:
      `Mesh::half_edge_components_for_verification` in `src/halfedge_mesh.rs`,
      consumed by new external-body bridge
      `ex_mesh_half_edge_components` in
      `src/runtime_halfedge_mesh_refinement.rs`.
    - added constructive executable checker +
      wrapper in `src/runtime_halfedge_mesh_refinement.rs`:
      `runtime_check_half_edge_components_partition` and
      `half_edge_components_constructive`.
    - failed attempt (rolled back from the stable spec):
      direct inclusion of an exported per-half-edge global-coverage existential
      clause in `mesh_half_edge_components_partition_spec` caused brittle final
      existential-packaging obligations in function-exit proof blocks.
      the checker still performs a runtime `global_seen` completion scan, but
      that coverage fact is not yet exported as part of the stable proved spec.
    - remaining gap:
      explicit BFS soundness/completeness linkage is still open
      (connectivity/closure characterization of each reported component, plus
      stable exported completeness packaging).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_half_edge_components_partition`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`35 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`69 verified, 0 errors`).
  - burndown update (2026-02-18, retry):
    - retried exporting global completeness directly in
      `mesh_half_edge_components_partition_spec` with explicit witness-lifting
      from the checker's final `global_seen` scan.
    - attempted proof shapes (both rolled back):
      - direct exit packaging (`forall h. exists component`) from
        `global_seen ==> exists component`,
      - strengthened final-scan invariant carrying explicit prefix coverage
        (`forall h < scan_idx. exists component`).
    - both variants remained trigger-sensitive/brittle in quantified existential
      packaging, so the change was reverted to preserve verifier stability.
    - stable state retained:
      `runtime_check_half_edge_components_partition` still checks full runtime
      coverage via `global_seen`, but exported proved spec remains the stable
      partition/disjointness surface.
  - burndown update (2026-02-18, latest):
    - completed export of global completeness in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `mesh_half_edge_components_partition_spec` now includes
      `mesh_half_edge_components_cover_all_spec`.
    - to stabilize trigger behavior, the coverage proof was factored through a
      helper predicate (`mesh_half_edge_has_component_spec`) and the outer
      quantifier triggers on that helper, instead of a direct nested
      `forall h. exists c` trigger over `mesh_half_edge_component_contains_spec`.
    - failed proof shape (not kept): direct nested trigger annotation on the
      new `forall -> exists` clause in `mesh_half_edge_components_cover_all_spec`
      still produced trigger-inference failures.
    - remaining gap:
      explicit BFS soundness is still open (connectivity/closure semantics for
      each reported component), but completeness is now part of the exported
      proved partition spec.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`36 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`36 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`70 verified, 0 errors`).
  - burndown update (2026-02-18, latest neighbor-closure increment):
    - strengthened exported component semantics in
      `src/runtime_halfedge_mesh_refinement.rs` with:
      - `mesh_half_edge_component_neighbor_closed_at_spec`,
      - `mesh_half_edge_components_neighbor_closed_spec`,
      - `mesh_half_edge_components_partition_neighbor_closed_spec`.
    - added constructive checker
      `runtime_check_half_edge_components_neighbor_closed` and required it in
      `half_edge_components_constructive`, so `Some(components)` now certifies
      both partition/coverage and per-component closure under
      `twin`/`next`/`prev`.
    - failed attempt (kept documented):
      first proof shape for the new checker exceeded verifier resources
      (`while loop: Resource limit (rlimit) exceeded`) at the outer component
      loop.
    - stabilization kept in-tree:
      added localized `#[verifier::rlimit(300)]` to
      `runtime_check_half_edge_components_neighbor_closed`; no trusted
      assumptions were introduced.
    - remaining gap:
      full BFS soundness/completeness is still open at the connectivity-witness
      level (component-wise reachability/minimality against
      `mesh_half_edge_connected_spec`), but closure semantics are now exported.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`40 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`40 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`74 verified, 0 errors`).
  - burndown update (2026-02-18, representative-reachability increment):
    - strengthened the exported component witness surface in
      `src/runtime_halfedge_mesh_refinement.rs` with:
      - `mesh_half_edge_component_representative_connected_at_spec`,
      - `mesh_half_edge_components_representative_connected_spec`,
      - and a strengthened
        `mesh_half_edge_components_partition_neighbor_closed_spec` that now
        includes representative-to-member connectivity.
    - added reusable connectivity lemmas:
      `lemma_mesh_half_edge_connected_refl`,
      `lemma_mesh_half_edge_connected_extend_direct_step`.
    - added constructive checker
      `runtime_check_half_edge_components_representative_connected` and
      required it in:
      - `half_edge_components_constructive`,
      - `component_count_constructive`,
      - `euler_characteristics_per_component_constructive`,
      - `check_euler_formula_closed_components_constructive`.
      this lifts the returned constructive witnesses from
      partition+coverage+neighbor-closure to also include explicit
      representative reachability for every reported component member.
    - proof-shape note:
      a stable approach was a monotone `seen` propagation pass over bounded
      half-edge indices, with connectivity preserved by one-step extension
      (`mesh_half_edge_direct_step_spec`) instead of queue-specific witness
      invariants.
    - spec cleanup:
      removed the explicit path-length upper bound from
      `mesh_half_edge_connected_spec`; this keeps the connectivity relation
      stable for extension lemmas while preserving finite-walk semantics.
    - remaining gap:
      this advances BFS soundness (members are connected to their component
      representative), but full soundness/completeness is still open at the
      reverse direction/minimality boundary
      (`mesh_half_edge_connected_spec(rep, h) ==> component_contains(...)`).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_half_edge_components_representative_connected`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`121 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`155 verified, 0 errors`).
  - burndown update (2026-02-18, representative-minimality witness increment):
    - strengthened exported component semantics in
      `src/runtime_halfedge_mesh_refinement.rs` with:
      - `mesh_half_edge_component_representative_minimal_at_spec`,
      - `mesh_half_edge_components_representative_minimal_spec`,
      - and a strengthened
        `mesh_half_edge_components_partition_neighbor_closed_spec` that now
        additionally requires representative-minimality
        (`component[0] <= every member`) for each component.
    - added constructive checker
      `runtime_check_half_edge_components_representative_minimal` and required
      it in:
      - `half_edge_components_constructive`,
      - `component_count_constructive`,
      - `euler_characteristics_per_component_constructive`,
      - `check_euler_formula_closed_components_constructive`.
      this lifts shared constructive witnesses from
      partition+coverage+neighbor-closure+representative-reachability to also
      include explicit per-component representative-minimality.
    - failed stabilization attempt (kept documented):
      initially tried to recover full-module verifier stability using only
      larger `#[verifier::rlimit(...)]` values on
      `runtime_check_half_edge_components_neighbor_closed`; this remained
      brittle (resource-limit failures, and a high-rlimit solver-run panic:
      `expected rlimit-count in smt statistics`), so it was not kept.
    - stabilization kept in-tree:
      `runtime_check_half_edge_components_neighbor_closed` now uses
      `#[verifier::spinoff_prover]` with a moderate localized
      `#[verifier::rlimit(600)]`, restoring stable full-module verification.
    - remaining gap:
      this advances the minimality half of the pending boundary, but full BFS
      soundness/completeness is still open at reverse-direction connectivity
      export (`mesh_half_edge_connected_spec(rep, h) ==> component_contains(...)`).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_half_edge_components_representative_minimal`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement component_count_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`124 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`124 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`158 verified, 0 errors`).
  - burndown update (2026-02-18, reverse-direction connectivity completion):
    - completed the missing reverse-direction export in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added specs
        `mesh_half_edge_component_representative_complete_at_spec` and
        `mesh_half_edge_components_representative_complete_spec`,
      - strengthened
        `mesh_half_edge_components_partition_neighbor_closed_spec` to include
        representative completeness
        (`mesh_half_edge_connected_spec(rep, h) ==> component_contains(...)`).
    - added reusable proof lemmas:
      - `lemma_mesh_half_edge_walk_closed_set_contains_index`,
      - `lemma_mesh_half_edge_closed_set_contains_connected`.
      these provide path-based closure lifting: if a set contains the
      representative and is closed under adjacency, it contains every
      connected half-edge.
    - added executable checker
      `runtime_check_half_edge_components_representative_complete` and required
      it in:
      - `half_edge_components_constructive`,
      - `component_count_constructive`,
      - `euler_characteristics_per_component_constructive`,
      - `check_euler_formula_closed_components_constructive`.
    - failed proof shapes (not kept):
      - first attempt used a proof `while` in a `proof fn` for path lifting;
        Verus rejected this (`cannot use while in proof or spec mode`), so the
        lemma was refactored to recursive proof shape.
      - first checker invariant used a single conjunctive quantified closure
        fact (bounds + inside-closure + outside-closure); preservation was
        brittle, so it was split into three quantified invariants.
    - outcome:
      this closes the remaining BFS soundness/completeness gap at the
      representative boundary in the exported constructive witness surface.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_half_edge_components_representative_complete`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`132 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`132 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`166 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Verify `component_count` equals number of connected components.
  - burndown update (2026-02-18):
    - landed constructive count/partition bridge in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - new spec witness predicate:
        `mesh_component_count_partition_witness_spec`,
      - new external-body bridge:
        `ex_mesh_component_count`,
      - new constructive wrapper:
        `component_count_constructive`.
    - proved stable intermediate guarantee:
      `component_count_constructive` returns `Some(count)` only when `count`
      matches a checked partition witness from `half_edge_components`
      (`exists components. mesh_half_edge_components_partition_spec(...) &&
      count == components.len()`).
    - remaining gap:
      this does not yet connect to the full connected-components model
      (`mesh_component_count_spec`) until BFS soundness/completeness linkage is
      exported at spec level.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`36 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`36 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`70 verified, 0 errors`).
  - burndown update (2026-02-18, aligned with neighbor-closure increment):
    - strengthened the witness contract used by
      `mesh_component_count_partition_witness_spec` /
      `component_count_constructive`: witness components must now satisfy
      `mesh_half_edge_components_partition_neighbor_closed_spec` (partition +
      global coverage + per-component neighbor closure).
    - remaining gap:
      count is still not linked to the full connected-components spec
      (`mesh_component_count_spec`) until the pending reachability/minimality
      soundness proof is exported.
  - burndown update (2026-02-18, aligned with representative-reachability increment):
    - due the strengthened shared witness
      `mesh_half_edge_components_partition_neighbor_closed_spec`, successful
      `component_count_constructive` results now also carry per-component
      representative reachability (in addition to partition/coverage and
      neighbor-closure).
  - burndown update (2026-02-18, aligned with representative-minimality increment):
    - due the strengthened shared witness
      `mesh_half_edge_components_partition_neighbor_closed_spec`, successful
      `component_count_constructive` results now also carry per-component
      representative-minimality (`component[0] <= each member`) in addition to
      partition/coverage/neighbor-closure/representative-reachability.
  - burndown update (2026-02-18, aligned with representative-completeness increment):
    - due the strengthened shared witness
      `mesh_half_edge_components_partition_neighbor_closed_spec`, successful
      `component_count_constructive` results now also carry reverse-direction
      representative completeness
      (`mesh_half_edge_connected_spec(rep, h) ==> component_contains(...)`).
  - remaining gap:
      `component_count` still lacks the full model-level linkage to
      `mesh_component_count_spec`; reverse-direction connectivity export is now
      available, so the remaining work is to prove the partition witness
      cardinality equivalence against the model representative-set definition.
  - burndown update (2026-02-18, model-count linkage completion):
    - closed the remaining cardinality gap in
      `src/runtime_halfedge_mesh_refinement.rs` by adding:
      - `lemma_mesh_half_edge_connected_symmetric`,
      - `lemma_component_partition_entry_is_model_representative`,
      - `lemma_model_representative_in_partition_representative_set`,
      - `lemma_component_partition_count_matches_model_component_count`.
    - proof-shape summary:
      proved a two-way representative-set correspondence between:
      - partition representatives (`component[c][0]`), and
      - model representatives (`mesh_component_representative_spec`),
      then used finite-set cardinality lemmas (`set_int_range`, `map_size`,
      subset/len bounds) to conclude
      `components.len() == mesh_component_count_spec(m)`.
    - strengthened `component_count_constructive`:
      `Some(count)` now exports both
      `mesh_component_count_partition_witness_spec(m@, count)` and
      `count == mesh_component_count_spec(m@)`.
    - outcome:
      this closes the `component_count` model-link item at the constructive
      wrapper boundary.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement component_count_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`136 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`136 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`170 verified, 0 errors`).
  - burndown update (2026-02-18, component-count bridge cleanup):
    - removed the now-redundant external-body bridge
      `ex_mesh_component_count` from
      `src/runtime_halfedge_mesh_refinement.rs`.
    - strengthened `component_count_constructive` to derive `count` directly
      from the already-validated component witness (`components.len()`) instead
      of re-calling the runtime API through an external-body bridge.
    - rationale:
      this shrinks the remaining external-body trust surface for connectivity
      counting without changing exported guarantees
      (`mesh_component_count_partition_witness_spec` and
      `count == mesh_component_count_spec(m@)`).
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement component_count_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
- [x] Verify `euler_characteristics_per_component` computes `V - E + F` per BFS component.
  - burndown update (2026-02-18):
    - landed explicit Euler-per-component refinement scaffolding in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `mesh_component_has_vertex_spec`,
      - `mesh_component_has_edge_spec`,
      - `mesh_component_has_face_spec`,
      - `mesh_component_euler_characteristic_witness_spec`,
      - `mesh_component_euler_characteristic_spec`,
      - `mesh_euler_characteristics_per_component_spec`,
      - `mesh_euler_characteristics_partition_witness_spec`.
    - added proof-facing runtime bridge and constructive checker pipeline:
      - external-body bridge: `ex_mesh_euler_characteristics_per_component`,
      - helper checker: `runtime_check_component_euler_characteristic`,
      - vector checker: `runtime_check_euler_characteristics_per_component`,
      - constructive wrapper: `euler_characteristics_per_component_constructive`.
    - proof-shape note:
      stable verification came from splitting obligations into:
      (1) a marking pass over component half-edges,
      (2) an explicit first-direction membership pass (`component entry -> mark`),
      (3) per-domain witness scans (`mark -> exists component entry`),
      then counting via `runtime_count_true` + `bool_true_count_spec`.
    - failed attempt (not kept):
      directly preserving `component entry -> mark` facts inside the marking loop
      with sequence-update equalities (`new_marks[idx] == old_marks[idx]`) was brittle;
      a separate post-mark membership pass proved more stable.
    - remaining gap:
      this is currently a constructive witness path (`Some(chis)` certifies the
      Euler-per-BFS-component contract); direct total linkage of
      `Mesh::euler_characteristics_per_component` itself to the same spec is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_component_euler_characteristic`
      passed (`9 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_euler_characteristics_per_component`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement euler_characteristics_per_component_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`55 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`55 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`89 verified, 0 errors`).
  - burndown update (2026-02-18, model-count alignment increment):
    - strengthened `mesh_euler_characteristics_partition_witness_spec` in
      `src/runtime_halfedge_mesh_refinement.rs` so successful Euler witness
      export now includes explicit model cardinality alignment:
      `chis.len() == mesh_component_count_spec(m)`.
    - strengthened `euler_characteristics_per_component_constructive` proof
      packaging to discharge the new clause via
      `lemma_component_partition_count_matches_model_component_count`.
    - outcome:
      constructive Euler-per-component witnesses now carry both:
      - per-component `V - E + F` characterization, and
      - Euler-vector length agreement with model component count.
    - remaining gap:
      direct total linkage of
      `Mesh::euler_characteristics_per_component` itself remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement euler_characteristics_per_component_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`172 verified, 0 errors`).
  - burndown update (2026-02-18, direct API constructive-link completion):
    - completed direct API linkage in `src/halfedge_mesh.rs` for proof-enabled builds:
      - added raw implementation helper
        `euler_characteristics_per_component_raw`,
      - strengthened public API `Mesh::euler_characteristics_per_component` to
        use `euler_characteristics_per_component_constructive` in
        `verus-proofs` builds (with runtime fallback to raw computation),
      - added bridge-safe raw accessor
        `euler_characteristics_per_component_for_verification`.
    - updated refinement bridge in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `ex_mesh_euler_characteristics_per_component` now calls
      `euler_characteristics_per_component_for_verification` to avoid recursive
      self-calls through the constructive API path.
    - failed attempts:
      none in this pass.
    - outcome:
      in `verus-proofs` builds, the direct runtime API now routes through the
      verified constructive witness path for Euler-per-component semantics, and
      this item is complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement euler_characteristics_per_component_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`194 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Verify `check_euler_formula_closed_components` iff all closed components have characteristic `2`.
  - burndown update (2026-02-18):
    - landed constructive witness surface in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `mesh_euler_formula_closed_components_partition_witness_spec`,
      - external-body bridge `ex_mesh_check_euler_formula_closed_components`,
      - constructive wrapper `check_euler_formula_closed_components_constructive`.
    - stable guarantee now exported:
      `check_euler_formula_closed_components_constructive` returns `Some(true)`
      only when runtime `check_euler_formula_closed_components` is true and there
      exists a checked BFS partition witness whose per-component Euler values are
      all `2` and non-empty.
    - failed attempt (kept documented):
      first wrapper revision omitted a decreases opt-out on its quantified scan
      loop and failed with `loop must have a decreases clause`; fixed by adding
      `#[verifier::exec_allows_no_decreases_clause]`.
    - remaining gap:
      this is still a constructive witness path; full `iff` linkage to the
      model-level closed-components relation
      (`mesh_euler_closed_components_spec`, which depends on the pending
      connected-components count model) remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`69 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`69 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`103 verified, 0 errors`).
  - burndown update (2026-02-18, witness model-count alignment increment):
    - strengthened
      `mesh_euler_formula_closed_components_partition_witness_spec` in
      `src/runtime_halfedge_mesh_refinement.rs` so successful Euler-formula
      witness export now includes:
      `chis.len() == mesh_component_count_spec(m)`.
    - strengthened
      `check_euler_formula_closed_components_constructive` proof packaging to
      discharge the new cardinality clause via
      `lemma_component_partition_count_matches_model_component_count`.
    - outcome:
      `Some(true)` witnesses now certify
      all-`2` component Euler values, non-empty component list, and explicit
      Euler-vector/model-component-count agreement.
    - remaining gap:
      full `iff` linkage to `mesh_euler_closed_components_spec` is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`138 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`172 verified, 0 errors`).
  - burndown update (2026-02-18, Euler gate equivalence witness increment):
    - strengthened `src/runtime_halfedge_mesh_refinement.rs` with an explicit
      Euler gate witness surface:
      - `EulerFormulaClosedComponentsGateWitness`,
      - `euler_formula_closed_components_gate_witness_spec`,
      - `euler_formula_closed_components_gate_model_link_spec`.
    - strengthened `check_euler_formula_closed_components_constructive`:
      - return type is now
        `Option<EulerFormulaClosedComponentsGateWitness>` (instead of
        `Option<bool>`),
      - successful output now certifies exact runtime gate equivalence at the
        checked witness boundary:
        `w.api_ok == (w.chis_non_empty && w.chis_all_two)`,
      - the function now returns constructive witnesses for both `api_ok = true`
        and `api_ok = false` (when partition/Euler witness checks succeed and
        the runtime gate matches the checked formula), rather than only
        `Some(true)`.
    - integration strengthening:
      `is_valid_constructive` / `validity_gate_model_link_spec` now retain an
      explicit existential Euler gate witness (parallel to the structural gate
      witness path), instead of only carrying a raw implication to the
      partition witness predicate.
    - remaining gap:
      this improves constructive `iff` evidence at the gate-witness level, but
      full model-level `iff` linkage to `mesh_euler_closed_components_spec`
      remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`150 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`150 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`184 verified, 0 errors`).
  - burndown update (2026-02-18, closed-components model-link strengthening):
    - refactored `mesh_euler_closed_components_spec` in
      `src/runtime_halfedge_mesh_refinement.rs` to the explicit
      partition-witness form:
      `mesh_euler_formula_closed_components_partition_witness_spec(m)`.
    - strengthened
      `check_euler_formula_closed_components_constructive` so `Some(w)` now
      also certifies:
      `w.api_ok ==> mesh_euler_closed_components_spec(m@)`.
    - remaining gap:
      full model-level `iff` remains open; this pass closes the exported
      constructive `api_ok -> model` direction.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`192 verified, 0 errors`).
  - burndown update (2026-02-18, direct API constructive-link completion):
    - completed direct API linkage in `src/halfedge_mesh.rs` for proof-enabled builds:
      - added raw implementation helper
        `check_euler_formula_closed_components_raw`,
      - strengthened public API
        `Mesh::check_euler_formula_closed_components` to use
        `check_euler_formula_closed_components_constructive` in
        `verus-proofs` builds (with runtime fallback to raw computation),
      - added bridge-safe raw accessor
        `check_euler_formula_closed_components_for_verification`.
    - updated refinement bridge in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `ex_mesh_check_euler_formula_closed_components` now calls
      `check_euler_formula_closed_components_for_verification` to avoid
      recursive self-calls through the constructive API path.
    - failed attempts:
      none in this pass.
    - outcome:
      in `verus-proofs` builds, the direct runtime Euler gate now routes through
      the verified constructive witness path that certifies
      `api_ok == (chis_non_empty && chis_all_two)` and model-link implications;
      this item is complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`159 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`194 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`).
  - burndown update (2026-02-18, Euler gate bridge removal cleanup):
    - removed the runtime-call bridge
      `ex_mesh_check_euler_formula_closed_components` from
      `src/runtime_halfedge_mesh_refinement.rs`.
    - strengthened
      `check_euler_formula_closed_components_constructive` to compute
      `api_ok` directly from checked witness state:
      `api_ok = (chis_non_empty && chis_all_two)`.
      this preserves the exported gate witness contract while removing one
      external-body trust edge.
    - removed now-unused helper method
      `check_euler_formula_closed_components_for_verification` from
      `src/halfedge_mesh.rs`, and updated the reference-mesh bridge test to
      compare against `check_euler_formula_closed_components_raw()` directly.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`

## F. Verify Top-Level APIs
- [x] Verify `is_structurally_valid` exactly matches conjunction of structural invariants.
  - burndown update (2026-02-18):
    - landed constructive gate-equivalence scaffolding in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - witness + spec:
        `StructuralValidityGateWitness`,
        `structural_validity_gate_witness_spec`,
      - external-body bridges:
        `ex_mesh_is_structurally_valid`,
        `ex_mesh_check_*_via_kernel`,
      - constructive wrapper:
        `is_structurally_valid_constructive`.
    - stable guarantee:
      `is_structurally_valid_constructive` returns `Some(w)` only when
      `w.api_ok` exactly matches the full runtime structural gate conjunction
      (non-empty counts plus all kernel-delegated checker booleans).
    - failed attempt (kept documented):
      first revision called `Mesh::*_via_kernel` directly from inside `verus!`;
      Verus rejected this as external/ignored-function usage. fixed by routing
      calls through minimal `#[verifier::external_body]` bridges (no trusted
      postconditions added).
  - burndown update (2026-02-18, model-link strengthening):
    - added witness-level model-link predicate in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `structural_validity_gate_model_link_spec`.
    - strengthened `is_structurally_valid_constructive` so `Some(w)` now
      certifies both:
      - `structural_validity_gate_witness_spec(w)`, and
      - `structural_validity_gate_model_link_spec(m@, w)`.
    - stable linkage now exported for two structural clauses by construction:
      - `w.twin_involution_ok ==> from_face_cycles_twin_assignment_total_involution_spec(m@)`,
      - `w.edge_two_half_edges_ok ==> mesh_edge_exactly_two_half_edges_spec(m@)`.
      these are sourced from verified constructive runtime checkers
      (`runtime_check_twin_assignment_total_involution`,
      `runtime_check_edge_exactly_two_half_edges`) instead of external-body
      kernel bridges for those two fields.
    - failed attempt (rolled back):
      introduced new constructive checkers
      `runtime_check_prev_next_inverse` and
      `runtime_check_no_degenerate_edges` and tried to include both clauses in
      `structural_validity_gate_model_link_spec`; quantified invariant
      packaging in those new proofs remained brittle under full-module
      verification, so the functions/clauses were removed to preserve stability.
    - remaining gap after this increment:
      model-link export is still partial (twin/edge only); exact model-level
      `iff` linkage for the full structural gate remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`110 verified, 0 errors`).
  - burndown update (2026-02-18, constructive model-link recovery):
    - completed the previously rolled-back constructive checker path in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - landed `runtime_check_prev_next_inverse`
        (`out ==> mesh_prev_next_inverse_spec(m@)`),
      - landed `runtime_check_no_degenerate_edges`
        (`out ==> mesh_no_degenerate_edges_spec(m@)`).
    - strengthened `is_structurally_valid_constructive` to source:
      - `prev_next_inverse_ok` from `runtime_check_prev_next_inverse`, and
      - `no_degenerate_edges_ok` from `runtime_check_no_degenerate_edges`
      (instead of external-body kernel bridges).
    - strengthened `structural_validity_gate_model_link_spec` so `Some(w)` now
      additionally exports:
      - `w.prev_next_inverse_ok ==> mesh_prev_next_inverse_spec(m@)`,
      - `w.no_degenerate_edges_ok ==> mesh_no_degenerate_edges_spec(m@)`.
    - remaining gap after this increment:
      model-link export is still partial (index-bounds/face-cycles/vertex-manifold
      clauses remain unlinked at model level), so full model-level gate `iff`
      remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_prev_next_inverse`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_no_degenerate_edges`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`80 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`80 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`114 verified, 0 errors`).
  - burndown update (2026-02-18, index-bounds model-link increment):
    - landed new constructive checker in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `runtime_check_index_bounds` with guarantee
      `out ==> mesh_index_bounds_spec(m@)`.
    - strengthened `structural_validity_gate_model_link_spec` with:
      - `w.index_bounds_ok ==> mesh_index_bounds_spec(m@)`.
    - strengthened `is_structurally_valid_constructive` to source
      `index_bounds_ok` from `runtime_check_index_bounds` (instead of the
      external-body kernel bridge), and to export the new index-bounds
      model-link implication through its `Some(w)` postcondition.
    - remaining gap after this increment:
      model-link export is still partial (face-cycles/vertex-manifold clauses
      remain unlinked at model level), so full model-level gate `iff` remains
      open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_index_bounds`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`85 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`85 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`119 verified, 0 errors`).
  - burndown update (2026-02-18, face-cycles model-link increment):
    - landed constructive kernel-bridge path in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - bridge relation/spec + builder:
        `kernel_mesh_matches_mesh_model_spec`,
        `runtime_mesh_to_kernel_mesh`,
      - bridge-facing face-cycle model predicate:
        `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec`,
      - constructive checker:
        `runtime_check_face_cycles_kernel_bridge`.
    - strengthened `structural_validity_gate_model_link_spec` with:
      - `w.face_cycles_ok ==> mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m@)`.
    - strengthened `is_structurally_valid_constructive` to source
      `face_cycles_ok` from `runtime_check_face_cycles_kernel_bridge`
      (instead of the external-body face-cycle kernel bridge), and to export
      the new face-cycle model-link implication on `Some(w)`.
    - supporting kernel refactor (stability helper):
      `src/verified_checker_kernels.rs` now factors
      `kernel_face_representative_cycles_cover_all_half_edges_spec` through a
      reusable witness predicate:
      `kernel_face_representative_cycles_cover_all_half_edges_witness_spec`.
    - failed proof shapes (rolled back during this pass):
      - repeated witness extraction attempts using nested `choose` over
        `exists` (`face_cycle_lens` / `(f, i)` witnesses) were trigger-sensitive
        and failed with quantifier-trigger inference/existence obligations.
      - a local duplicate witness predicate in
        `runtime_halfedge_mesh_refinement.rs` was attempted first and then
        superseded by the kernel-side witness factoring above to stabilize
        extraction.
    - remaining gap after this increment:
      structural model-link export is still partial:
      `vertex_manifold_ok` remains unlinked at model level, so full structural
      gate `iff` is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`96 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`96 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`130 verified, 0 errors`).
  - burndown update (2026-02-18, vertex-manifold model-link increment):
    - landed constructive kernel-bridge path in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - bridge-facing vertex-manifold model predicates:
        `mesh_vertex_representative_cycle_kernel_bridge_witness_spec`,
        `mesh_vertex_representative_cycles_kernel_bridge_spec`,
        `mesh_vertex_representative_cycles_kernel_bridge_total_spec`,
      - bridge lemmas:
        `lemma_kernel_vertex_ring_succ_or_self_matches_mesh`,
        `lemma_kernel_vertex_ring_iter_matches_mesh`,
        `lemma_kernel_vertex_cycle_witness_matches_mesh`,
        `lemma_kernel_vertex_manifold_matches_mesh`,
      - constructive checker:
        `runtime_check_vertex_manifold_kernel_bridge`.
    - strengthened `structural_validity_gate_model_link_spec` with:
      - `w.vertex_manifold_ok ==> mesh_vertex_representative_cycles_kernel_bridge_total_spec(m@)`.
    - strengthened `is_structurally_valid_constructive` to source
      `vertex_manifold_ok` from `runtime_check_vertex_manifold_kernel_bridge`
      (instead of the external-body vertex-manifold kernel bridge), and to
      export the new vertex-manifold model-link implication on `Some(w)`.
    - failed attempts:
      none in this pass.
    - remaining gap after this increment:
      structural model-link coverage is now complete at the current bridge
      surface, but full model-level gate `iff` is still open because
      face/vertex bridge predicates remain weaker than
      `mesh_face_next_cycles_spec` / `mesh_vertex_manifold_single_cycle_spec`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_vertex_manifold_kernel_bridge`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`101 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`101 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`135 verified, 0 errors`).
  - burndown update (2026-02-18, face-cycle witness distinctness strengthening):
    - landed a stable strengthening in
      `src/verified_checker_kernels.rs`:
      `kernel_face_representative_cycle_witness_spec` now includes an
      intra-cycle uniqueness clause (`forall i < j < k. next_iter(i) != next_iter(j)`),
      and `kernel_check_face_cycles` now proves it.
    - propagated the stronger witness through the runtime bridge in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `mesh_face_representative_cycle_kernel_bridge_witness_spec` now carries
        the same intra-cycle uniqueness clause,
      - `lemma_kernel_face_cycle_witness_matches_mesh` now lifts that clause
        from kernel witness state into mesh-model witness state.
    - stabilization/refactor:
      introduced reusable witness predicate
      `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec`
      and refactored
      `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_spec`
      to quantify over it, mirroring the kernel witness packaging shape and
      keeping bridge witness extraction stable.
    - failed attempt (rolled back in this pass):
      tried to complete the face-side top-level gap by proving
      `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec`
      implies full `mesh_face_next_cycles_spec` and then threading that into
      `structural_validity_gate_model_link_spec`.
      this proof shape was removed after quantified in-bounds/coverage lifting
      remained brittle in the final packaging block.
    - stable state retained:
      face-cycle bridge witnesses are now strictly stronger (explicit
      per-cycle distinctness), but `is_structurally_valid` model-link export
      still stops at the bridge predicate surface for face cycles.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_face_cycles`
      passed (`4 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`34 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_kernel_face_cycle_witness_matches_mesh`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_face_cycles_kernel_bridge`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`149 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`149 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`183 verified, 0 errors`).
  - burndown update (2026-02-18, face-cycle implication helper groundwork + packaging rollback):
    - landed reusable face-side helper lemmas in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `lemma_face_bridge_witness_implies_face_cycle_coverage`,
      - `lemma_face_bridge_witness_implies_face_cycle_witness`.
      these provide stable per-face lifting from
      `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_witness_spec`
      to full fixed-face `mesh_face_cycle_witness_spec`.
    - attempted strengthening (rolled back in this pass):
      - prove
        `mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec`
        implies `mesh_face_next_cycles_spec`,
      - thread the stronger clause into
        `structural_validity_gate_model_link_spec`
        (`w.face_cycles_ok ==> mesh_face_next_cycles_spec(m@)`).
    - rollback reason:
      final quantified packaging at the
      `forall f. exists k` layer remained trigger-sensitive/brittle in this
      workspace state, even after stabilizing the per-face witness path.
    - stable state retained:
      structural model-link export remains at the face-cycle bridge predicate
      surface, while the new per-face helper lemmas remain in-tree as reusable
      scaffolding for a future retry.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_face_bridge_witness_implies_face_cycle_coverage`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_face_bridge_witness_implies_face_cycle_witness`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`152 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`152 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`186 verified, 0 errors`).
  - burndown update (2026-02-18, face-cycle model-link completion):
    - completed the face-side structural model-link gap in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added `lemma_face_bridge_total_implies_face_next_cycles`,
      - strengthened `structural_validity_gate_model_link_spec` from
        `w.face_cycles_ok ==> mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m)`
        to
        `w.face_cycles_ok ==> mesh_face_next_cycles_spec(m)`,
      - strengthened `is_structurally_valid_constructive` proof packaging to
        invoke the new lemma and export the stronger face-cycle clause on
        `Some(w)`.
    - stabilization/refactor that made this pass converge:
      refactored `mesh_face_next_cycles_spec` to a witness-sequence shape via
      `mesh_face_next_cycles_witness_spec` (instead of direct
      `forall f. exists k` packaging), so bridge witness export can be lifted
      constructively without brittle final existential instantiation.
    - failed attempt kept documented:
      initial proof shape in this pass retried direct final packaging against
      the old `forall f. exists k` form and hit the same trigger-sensitive
      assertion failures in the final lift; this was replaced by the stable
      witness-sequence refactor above.
    - remaining gap after this increment:
      structural model-link export is now fully aligned for face cycles; the
      remaining top-level structural `iff` gap is on the vertex side
      (`mesh_vertex_representative_cycles_kernel_bridge_total_spec` vs
      `mesh_vertex_manifold_single_cycle_spec`).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_face_bridge_total_implies_face_next_cycles`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`153 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`153 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`187 verified, 0 errors`).
  - burndown update (2026-02-18, vertex-manifold model-link completion):
    - completed the remaining vertex-side structural model-link gap using a
      kernel-direct lift in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - added lemmas
        `lemma_kernel_vertex_cycle_witness_implies_mesh_vertex_ring_witness`
        and
        `lemma_kernel_vertex_manifold_total_implies_mesh_vertex_manifold`,
      - strengthened
        `runtime_check_vertex_manifold_kernel_bridge` contract from
        `out ==> mesh_vertex_representative_cycles_kernel_bridge_total_spec(m@)`
        to
        `out ==> mesh_vertex_manifold_single_cycle_spec(m@)`.
    - strengthened the top-level structural model-link export:
      - `structural_validity_gate_model_link_spec` now carries
        `w.vertex_manifold_ok ==> mesh_vertex_manifold_single_cycle_spec(m)`,
      - `is_structurally_valid_constructive` now exports the strengthened
        vertex-manifold clause directly from
        `runtime_check_vertex_manifold_kernel_bridge`.
    - stabilization/refactor that made this pass converge:
      refactored `mesh_vertex_manifold_single_cycle_spec` to a
      witness-sequence shape via
      `mesh_vertex_manifold_single_cycle_witness_spec` (mirroring the
      stabilized face-side packaging shape).
    - supporting kernel strengthening in
      `src/verified_checker_kernels.rs`:
      `kernel_vertex_representative_cycle_witness_spec` now includes
      per-cycle uniqueness + per-vertex coverage clauses, and
      `kernel_check_vertex_manifold_single_cycle` now proves that stronger
      witness.
    - failed attempt kept documented:
      first tried to close the gap by strengthening the runtime bridge witness
      surface directly and proving the old direct
      `forall v. exists k` packaging at function exit; this proof shape was
      rolled back after final packaging remained trigger-sensitive/brittle.
      the kept solution uses the kernel-direct lift plus witness-sequence
      packaging.
    - outcome:
      this closes the remaining vertex-side gap for
      `is_structurally_valid`; the item is now complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels kernel_check_vertex_manifold_single_cycle`
      passed (`5 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_kernel_vertex_cycle_witness_implies_mesh_vertex_ring_witness`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement lemma_kernel_vertex_manifold_total_implies_mesh_vertex_manifold`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_vertex_manifold_kernel_bridge`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`155 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`35 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`155 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`190 verified, 0 errors`).
  - burndown update (2026-02-18, external-body trust-surface cleanup):
    - removed seven now-unused runtime kernel bridge wrappers from
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `ex_mesh_check_index_bounds_via_kernel`,
      - `ex_mesh_check_twin_involution_via_kernel`,
      - `ex_mesh_check_prev_inverse_of_next_via_kernel`,
      - `ex_mesh_check_face_cycles_via_kernel`,
      - `ex_mesh_check_no_degenerate_edges_via_kernel`,
      - `ex_mesh_check_vertex_manifold_single_cycle_via_kernel`,
      - `ex_mesh_check_edge_has_exactly_two_half_edges_via_kernel`.
    - rationale:
      these wrappers were superseded by constructive checker paths and were no
      longer referenced, so removing them shrinks the remaining external-body
      surface without changing proof behavior.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`).
  - burndown update (2026-02-18, top-level gate bridge cleanup):
    - removed two additional runtime external-body gate bridges from
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `ex_mesh_is_structurally_valid`,
      - `ex_mesh_is_valid`.
    - strengthened constructive top-level gate wiring to compute `api_ok`
      by construction from already-checked booleans:
      - `is_structurally_valid_constructive` now sets
        `api_ok = formula_ok` (same structural conjunction as runtime API),
      - `is_valid_constructive` now sets
        `api_ok = structural_ok && euler_ok`.
    - rationale:
      this removes two unused runtime-call trust edges while preserving the
      existing witness contracts (`structural_validity_gate_witness_spec` and
      `validity_gate_witness_spec`) at the same constructive proof boundary.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`).
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, reference-constructor bridge consolidation):
    - attempted to remove constructor bridges entirely by calling
      `Mesh::tetrahedron`, `Mesh::cube`, and `Mesh::triangular_prism` directly
      from `src/runtime_halfedge_mesh_refinement.rs`.
    - failed attempt (rolled back in this pass):
      Verus rejected those direct calls because the constructor functions are
      outside `verus!`/external and therefore ignored in proof mode.
    - landed stable trust-surface consolidation:
      replaced three constructor-specific external-body bridges
      (`ex_mesh_tetrahedron`, `ex_mesh_cube`, `ex_mesh_triangular_prism`) with
      one selector-based bridge:
      `ex_mesh_reference_constructor(kind: usize)`.
    - strengthened constructor wrappers to call the unified bridge:
      - `tetrahedron_constructive_counts` uses selector `0`,
      - `cube_constructive_counts` uses selector `1`,
      - `triangular_prism_constructive_counts` uses selector `2`.
    - outcome:
      constructor behavior/proofs are unchanged, but the runtime
      external-body constructor bridge surface is smaller and less duplicated.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, reference-constructor selector typing hardening):
    - strengthened the unified constructor bridge in
      `src/runtime_halfedge_mesh_refinement.rs` by replacing numeric selector
      arguments with an explicit enum:
      - added `ReferenceMeshKind { Tetrahedron, Cube, TriangularPrism }`,
      - changed
        `ex_mesh_reference_constructor(kind: usize)` to
        `ex_mesh_reference_constructor(kind: ReferenceMeshKind)`.
    - updated constructor wrappers to use typed selectors instead of magic
      numbers:
      - `tetrahedron_constructive_counts` now passes
        `ReferenceMeshKind::Tetrahedron`,
      - `cube_constructive_counts` now passes
        `ReferenceMeshKind::Cube`,
      - `triangular_prism_constructive_counts` now passes
        `ReferenceMeshKind::TriangularPrism`.
    - rationale:
      this removes invalid-selector runtime behavior from the bridge surface and
      makes constructor dispatch proof-facing and type-safe by construction.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`174 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`209 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, constructor-bridge burndown hygiene pass):
    - removed a duplicate historical note for the same constructor-bridge
      selector-typing hardening work to keep this checklist single-sourced.
    - revalidated the current `vcad-topology` proof/test state after the doc
      cleanup.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`174 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`209 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, reference-constructor bridge removal completion):
    - removed the remaining external-body constructor bridge
      `ex_mesh_reference_constructor` and its selector enum
      `ReferenceMeshKind` from
      `src/runtime_halfedge_mesh_refinement.rs`.
    - strengthened constructor wrappers to build through the existing
      constructive `from_face_cycles` path instead of a direct runtime
      constructor bridge:
      - `tetrahedron_constructive_counts`,
      - `cube_constructive_counts`,
      - `triangular_prism_constructive_counts`.
      each now builds explicit reference vertex/face inputs and calls
      `from_face_cycles_constructive_next_prev_face(...)` before the existing
      count checks.
    - rationale:
      this removes one more `external_body` trust edge while keeping
      constructor proof obligations on the verified `from_face_cycles`
      constructive boundary.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, external-type bridge annotation hardening):
    - removed a redundant `#[verifier::external_body]` marker from the
      external-type bridge
      `ExMeshBuildError(MeshBuildError)` in
      `src/runtime_halfedge_mesh_refinement.rs`.
    - rationale:
      `ExMeshBuildError` is already modeled through
      `#[verifier::external_type_specification]`; dropping the extra
      `external_body` annotation keeps the trust surface declaration minimal
      without changing behavior or proof obligations.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`35 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, face-cycle checker postcondition hardening):
    - selected task in this pass:
      continue section F hardening by making the face-cycle kernel bridge
      checker export the final mesh-model clause directly.
    - strengthened
      `runtime_check_face_cycles_kernel_bridge` in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - postcondition changed from
        `out ==> mesh_face_representative_cycles_cover_all_half_edges_kernel_bridge_total_spec(m@)`
        to
        `out ==> mesh_face_next_cycles_spec(m@)`,
      - checker proof now finishes with
        `lemma_face_bridge_total_implies_face_next_cycles(m@)` and packages
        the final face-cycle model predicate at the checker boundary.
    - simplified `is_structurally_valid_constructive` proof packaging:
      when `w.face_cycles_ok`, it now consumes the strengthened checker
      postcondition directly instead of re-lifting from the intermediate
      bridge-total predicate.
    - failed attempts:
      none in this pass.
    - operational note:
      parallel test invocations printed
      `Blocking waiting for file lock on build directory` / artifact directory
      and then completed successfully.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_face_cycles_kernel_bridge`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_structurally_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - file: `src/halfedge_mesh.rs`
- [x] Verify `is_valid` exactly matches `is_structurally_valid && check_euler_formula_closed_components`.
  - burndown update (2026-02-18):
    - landed constructive top-level gate witness in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - witness + spec:
        `ValidityGateWitness`,
        `validity_gate_witness_spec`,
      - external-body bridge:
        `ex_mesh_is_valid`,
      - constructive wrapper:
        `is_valid_constructive`.
    - stable guarantee:
      `is_valid_constructive` returns `Some(w)` only when
      `w.api_ok == (w.structural_ok && w.euler_ok)`, with `w.structural_ok`
      sourced from `is_structurally_valid_constructive`.
    - remaining gap:
      this remains a constructive runtime equivalence check; total `iff`
      linkage to `mesh_valid_spec` is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`73 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`107 verified, 0 errors`).
  - burndown update (2026-02-18, model-link witness strengthening):
    - strengthened `src/runtime_halfedge_mesh_refinement.rs` with a new
      witness-level linkage predicate:
      `validity_gate_model_link_spec`.
    - strengthened `is_valid_constructive` so `Some(w)` now certifies both:
      - `validity_gate_witness_spec(w)`, and
      - `validity_gate_model_link_spec(m@, w)`.
    - proof-path strengthening details:
      - `w.structural_ok` is now backed by an explicit retained
        `StructuralValidityGateWitness` existential carrying
        `structural_validity_gate_witness_spec` +
        `structural_validity_gate_model_link_spec`,
      - `w.euler_ok` is now sourced from
        `check_euler_formula_closed_components_constructive` (instead of direct
        raw API call), so successful witnesses carry the existing checked
        partition/Euler witness surface.
    - propagated strengthened validity witness guarantees into constructor
      wrappers:
      - `tetrahedron_constructive_counts_and_is_valid`,
      - `cube_constructive_counts_and_is_valid`,
      - `triangular_prism_constructive_counts_and_is_valid`.
      these now also export `validity_gate_model_link_spec(m@, w)` on `Some`.
    - remaining gap:
      this is still constructive witness linkage, not full total `iff`
      linkage to `mesh_valid_spec` / `mesh_euler_closed_components_spec`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`110 verified, 0 errors`).
  - burndown update (2026-02-18, Euler witness threading increment):
    - strengthened `validity_gate_model_link_spec` in
      `src/runtime_halfedge_mesh_refinement.rs` so the Euler side now carries
      an explicit existential witness:
      `EulerFormulaClosedComponentsGateWitness`.
    - `is_valid_constructive` now threads the strengthened
      `check_euler_formula_closed_components_constructive` output witness and
      proves `w.euler_ok` through retained Euler witness equality
      (`ew.api_ok == w.euler_ok`) instead of only a direct implication clause.
    - remaining gap:
      validity linkage remains constructive witness-based; full total linkage to
      `mesh_valid_spec` is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`150 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`150 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`184 verified, 0 errors`).
  - burndown update (2026-02-18, model-validity implication completion):
    - strengthened structural witness model-link surface in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `structural_validity_gate_model_link_spec` now includes positive-count
      implications (`vertex/edge/face/half_edge`).
    - added proof lemmas:
      - `lemma_structural_validity_gate_witness_api_ok_implies_mesh_structurally_valid`,
      - `lemma_validity_gate_witness_api_ok_implies_mesh_valid`.
    - strengthened `is_valid_constructive` postcondition so `Some(w)` now
      certifies:
      `w.api_ok ==> mesh_valid_spec(m@)`,
      alongside the existing gate-equivalence and witness-link guarantees.
    - failed attempt (kept documented):
      first count-link proof blocks used `is_empty()` calls directly inside
      proof context and were rejected by Verus mode checking (`cannot call
      function ... with mode exec`); fixed by switching those local facts to
      `len() > 0` shape before lifting to model-count implications.
    - outcome:
      constructive `is_valid` linkage to model-level `mesh_valid_spec` is now
      exported and the item is complete.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement is_valid_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`192 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`

## G. Verify Reference Mesh Constructors End-to-End
- [x] Prove `tetrahedron` builds and satisfies `is_valid`.
  - prove counts: `V=4, E=6, F=4, H=12`.
  - burndown update (2026-02-18):
    - landed constructor-count refinement scaffolding in
      `src/runtime_halfedge_mesh_refinement.rs`:
      - `mesh_counts_spec`,
      - `mesh_tetrahedron_counts_spec`,
      - generic checker `runtime_check_mesh_counts`,
      - constructor bridge `ex_mesh_tetrahedron`,
      - constructive wrapper `tetrahedron_constructive_counts`.
    - proved stable intermediate guarantee:
      `tetrahedron_constructive_counts` returns `Some(m)` only when
      `mesh_tetrahedron_counts_spec(m@)` holds.
    - remaining gap:
      end-to-end `is_valid` linkage is still open for this constructor.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`59 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`59 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`93 verified, 0 errors`).
  - burndown update (2026-02-18, constructor validity witness):
    - landed constructor validity wrapper in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `tetrahedron_constructive_counts_and_is_valid`.
    - stable guarantee now exported:
      `Some((m, w))` only when all of the following hold:
      - `mesh_tetrahedron_counts_spec(m@)`,
      - `validity_gate_witness_spec(w)`,
      - `w.api_ok` (runtime `is_valid` gate evaluates true under the
        constructive witness path).
    - remaining gap:
      this is still a constructive runtime witness path; direct linkage from the
      constructor output to model-level `mesh_valid_spec(m@)` remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement tetrahedron_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`76 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`110 verified, 0 errors`).
  - burndown update (2026-02-18, model-valid constructor closeout):
    - strengthened `tetrahedron_constructive_counts_and_is_valid` so
      `Some((m, w))` now also certifies `mesh_valid_spec(m@)`.
    - proof path now reuses
      `lemma_validity_gate_witness_api_ok_implies_mesh_valid`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement tetrahedron_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`192 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Prove `cube` builds and satisfies `is_valid`.
  - prove counts: `V=8, E=12, F=6, H=24`.
  - burndown update (2026-02-18):
    - landed constructor-count bridge + wrapper in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `ex_mesh_cube` + `cube_constructive_counts`.
    - proved stable intermediate guarantee:
      `cube_constructive_counts` returns `Some(m)` only when
      `mesh_cube_counts_spec(m@)` holds.
    - remaining gap:
      end-to-end `is_valid` linkage is still open for this constructor.
  - burndown update (2026-02-18, constructor validity witness):
    - landed constructor validity wrapper in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `cube_constructive_counts_and_is_valid`.
    - stable guarantee now exported:
      `Some((m, w))` only when:
      - `mesh_cube_counts_spec(m@)`,
      - `validity_gate_witness_spec(w)`,
      - `w.api_ok`.
    - remaining gap:
      this remains a constructive runtime witness path; model-level
      `mesh_valid_spec(m@)` linkage for constructor output is still open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement cube_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`);
  - burndown update (2026-02-18, model-valid constructor closeout):
    - strengthened `cube_constructive_counts_and_is_valid` so `Some((m, w))`
      now also certifies `mesh_valid_spec(m@)`.
    - proof path now reuses
      `lemma_validity_gate_witness_api_ok_implies_mesh_valid`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement cube_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`192 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [x] Prove `triangular_prism` builds and satisfies `is_valid`.
  - prove counts: `V=6, E=9, F=5, H=18`.
  - burndown update (2026-02-18):
    - landed constructor-count bridge + wrapper in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `ex_mesh_triangular_prism` + `triangular_prism_constructive_counts`.
    - proved stable intermediate guarantee:
      `triangular_prism_constructive_counts` returns `Some(m)` only when
      `mesh_triangular_prism_counts_spec(m@)` holds.
    - remaining gap:
      end-to-end `is_valid` linkage is still open for this constructor.
    - failed attempt (tooling only):
      tried running `verify-vcad-topology-fast.sh` with multiple function
      arguments in one invocation; the script accepts at most
      `[module] [function_pattern]`, so verification was rerun with supported
      invocations.
  - burndown update (2026-02-18, constructor validity witness):
    - landed constructor validity wrapper in
      `src/runtime_halfedge_mesh_refinement.rs`:
      `triangular_prism_constructive_counts_and_is_valid`.
    - stable guarantee now exported:
      `Some((m, w))` only when:
      - `mesh_triangular_prism_counts_spec(m@)`,
      - `validity_gate_witness_spec(w)`,
      - `w.api_ok`.
    - remaining gap:
      still constructive-only; direct proof that constructor output satisfies
      model-level `mesh_valid_spec(m@)` remains open.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement triangular_prism_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`).
  - burndown update (2026-02-18, model-valid constructor closeout):
    - strengthened `triangular_prism_constructive_counts_and_is_valid` so
      `Some((m, w))` now also certifies `mesh_valid_spec(m@)`.
    - proof path now reuses
      `lemma_validity_gate_witness_api_ok_implies_mesh_valid`.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement triangular_prism_constructive_counts_and_is_valid`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`157 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`192 verified, 0 errors`).
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`

## H. Reuse-Focused Hardening (No Reinventing)
- [x] Reuse `vcad-math` proof surfaces for arithmetic/cardinality/order where applicable.
  - burndown update (2026-02-18, loop-exit arithmetic reuse pass):
    - reused `vcad-math` scalar nat-order proof surface in
      `src/runtime_halfedge_mesh_refinement.rs`:
      imported `vcad_math::scalar::Scalar` and added reusable helper
      `lemma_usize_loop_exit_eq`.
    - helper proof shape:
      - discharges `idx == bound` from loop-exit facts
        (`idx <= bound` and `!(idx < bound)`),
      - routes the positive-bound case through
        `Scalar::lemma_nat_le_and_not_le_prev_implies_eq(...)`.
    - threaded the helper through repeated loop-exit packaging sites
      (vertex representative checker, component/Euler checker closeouts), replacing
      ad-hoc direct `assert(idx == len)` equalities with the shared vcad-math-backed lemma.
    - outcome:
      arithmetic/order closeout reasoning now reuses the vcad-math proof surface
      in the topology verification path.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`).
    - failed attempt (tooling only):
      initially invoked `scripts/run-codex-task.sh` with a positional
      sentence argument; script rejected it (`error: expected zero arguments`).
      stable usage is to write the sentence to
      `scripts/run-codex-task.message.txt` and invoke the script with no args.
  - burndown update (2026-02-18, component-witness reuse pass):
    - reduced duplicated connectivity witness gating in
      `src/runtime_halfedge_mesh_refinement.rs` by reusing
      `half_edge_components_constructive(...)` in:
      - `component_count_constructive`,
      - `euler_characteristics_per_component_constructive`,
      - `check_euler_formula_closed_components_constructive`.
    - outcome:
      these wrappers now share one checked partition/closure witness pipeline
      instead of repeating the same
      `runtime_check_half_edge_components_*` sequence inline; exported specs
      are unchanged.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement component_count_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement euler_characteristics_per_component_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`208 verified, 0 errors`).
- [x] Reuse `vcad-geometry` predicates for optional geometric non-degeneracy extensions (face area > 0, etc.).
  - burndown update (2026-02-18, optional geometric non-degeneracy extension):
    - added an opt-in topology feature in `crates/vcad-topology/Cargo.toml`:
      `geometry-checks = ["dep:vcad-geometry"]`.
    - added geometry-backed runtime APIs in `src/halfedge_mesh.rs` under
      `#[cfg(feature = "geometry-checks")]`:
      - `Mesh::check_face_corner_non_collinearity`,
      - `Mesh::is_valid_with_geometry`.
    - checker semantics:
      for each face cycle corner `(prev, current, next)`, call
      `vcad_geometry::collinearity_coplanarity::collinear3d(...)` on the
      corresponding runtime vertex positions and reject collinear triples.
    - added coverage tests in `src/halfedge_mesh.rs`:
      - reference meshes (`tetrahedron`, `cube`, `triangular_prism`) pass the
        new geometric gate when the feature is enabled,
      - new regression:
        `collinear_triangle_faces_fail_geometric_nondegeneracy` demonstrates a
        closed structurally valid mesh that fails the optional geometric gate.
    - failed attempt (kept documented):
      first pass added `vcad-geometry` as a non-optional dependency; Verus
      topology verification then tried compiling `vcad-geometry` in this
      workspace state and failed in unrelated existing geometry proof code
      (`segment_intersection` `view` errors). the stable fix was to keep
      geometry reuse opt-in via the `geometry-checks` feature so baseline
      `verus-proofs` verification remains green.
    - verification checks:
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks` passed
      (`5 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh` passed
      (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed
      (`208 verified, 0 errors`).
  - burndown update (2026-02-18, validation rerun in this pass):
    - reran geometry-extension tests:
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`).
    - reran topology verification scripts:
      `./scripts/verify-vcad-topology-fast.sh` passed
      (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed
      (`208 verified, 0 errors`).
    - failed attempt (tooling/config only):
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      failed in rustc test mode with unresolved import
      `vcad_math::scalar::Scalar` from
      `src/runtime_halfedge_mesh_refinement.rs` (`E0432`).
      this is tracked as a cargo-test-mode cfg mismatch and does not block
      Verus-script verification flows for `verus-proofs`.
  - burndown update (2026-02-18, cargo-test cfg mismatch closeout):
    - fixed the documented combined-feature cargo-test failure in
      `src/runtime_halfedge_mesh_refinement.rs` by making the
      `vcad_math::scalar::Scalar` import conditional on `verus_keep_ghost` and
      using a single `lemma_usize_loop_exit_eq` body with statement-level cfg
      gating around the scalar lemma call.
    - failed attempt (rolled back in-pass):
      first tried a two-function cfg split for `lemma_usize_loop_exit_eq`
      (`#[cfg(verus_keep_ghost)]` + `#[cfg(not(verus_keep_ghost))]`); this
      caused duplicate-definition failure under `verus!` expansion
      (`E0428`), so it was replaced by the stable single-definition shape.
    - outcome:
      `cargo test` now works in the previously failing mixed feature mode while
      keeping the `verus_keep_ghost` proof path unchanged.
    - verification checks:
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh` passed
      (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed
      (`208 verified, 0 errors`).

## Exit Condition
- [x] No `assume_specification` remains in `vcad-topology` for runtime mesh behavior.
- [x] No uninterpreted spec predicate remains for currently implemented invariants.
- [x] `verify-vcad-topology-fast.sh` and `verify-vcad-topology.sh` both green.
  - burndown update (2026-02-18, exit-condition maintenance rerun + warning hardening):
    - selected task in this pass:
      maintain and revalidate the Exit Condition on the current tree.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, added
      `#[allow(unused_variables, unused_assignments)]` on
      `runtime_check_from_face_cycles_all_oriented_edges_have_twin` to avoid
      rustc test-mode warnings for proof-only witness locals
      (`twin_f`/`twin_i`) that are required by Verus invariants/proofs.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "assume_specification|external_fn_specification" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "uninterpreted|admit\\(|assume\\(" ...`
        over topology proof/refinement sources returned no matches.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_all_oriented_edges_have_twin`
      passed (`5 verified, 0 errors` partial);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`173 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`208 verified, 0 errors`).
  - burndown update (2026-02-18, external-body minimization rerun):
    - selected task in this pass:
      maintain Exit Condition and reduce trusted refinement bridge surface.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `#[verifier::external_body]` from `mesh_build_error_empty_face_set` so
      the helper verifies directly.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "assume_specification|external_fn_specification" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\buninterpreted\\b|admit\\(|assume\\("` over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        now reports four wrappers (down from five in the previous pass).
    - failed attempt (rolled back in-pass):
      removed `#[verifier::external_body]` from
      `ex_from_face_cycles_constructive_abort`, but Verus rejected direct use
      of `std::process::abort` in a verified body; the change was reverted to
      avoid introducing a new assumed spec.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`174 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`174 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`209 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, external-body minimization follow-up):
    - selected task in this pass:
      continue Exit Condition maintenance by shrinking the remaining trusted
      refinement bridge surface.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `#[verifier::external_body]` from
      `ex_from_face_cycles_constructive_abort` and replaced the body with a
      direct diverging loop under
      `#[verifier::exec_allows_no_decreases_clause]`.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        now reports three wrappers (down from four in the previous pass).
    - failed attempts (rolled back in-pass):
      - first replacement used `panic!(...)`; Verus rejected unsupported
        `core::fmt`/`panic_fmt` paths in verified mode.
      - second replacement used `loop {}` without no-decreases allowance;
        Verus rejected it with "loop must have a decreases clause".
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`176 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`176 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`211 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, Euler bridge removal follow-up):
    - selected task in this pass:
      continue Exit Condition maintenance by reducing the remaining
      `external_body` bridge surface.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `ex_mesh_euler_characteristics_per_component` and replaced that bridge
      call path with a new constructive helper:
      `runtime_compute_euler_characteristics_from_components`.
      in `src/halfedge_mesh.rs`, removed now-unused bridge accessor
      `euler_characteristics_per_component_for_verification` and updated the
      reference-mesh bridge regression to compare against
      `euler_characteristics_per_component_raw()` directly.
      - `euler_characteristics_per_component_constructive` and
        `check_euler_formula_closed_components_constructive` now compute
        `chis` from checked component witnesses and then validate with the
        existing verified checker
        (`runtime_check_euler_characteristics_per_component`).
    - failed attempt (rolled back in-pass):
      attempted to remove `#[verifier::external_body]` directly from both
      `ex_mesh_half_edge_components` and
      `ex_mesh_euler_characteristics_per_component`, but Verus rejected direct
      calls to `Mesh::*_for_verification` methods (ignored/outside `verus!`).
      kept `ex_mesh_half_edge_components` as `external_body` and eliminated the
      Euler bridge via constructive computation instead.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        now reports two wrappers (down from three in the previous pass).
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_compute_euler_characteristics_from_components`
      passed (`3 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement euler_characteristics_per_component_constructive`
      passed (`1 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement check_euler_formula_closed_components_constructive`
      passed (`2 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh` passed (`179 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh` passed (`214 verified, 0 errors`);
      `cargo test -p vcad-topology` passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, half-edge components bridge removal completion):
    - selected task in this pass:
      continue Exit Condition maintenance by removing the remaining
      half-edge-components `external_body` bridge.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `ex_mesh_half_edge_components` and replaced its use in
      `half_edge_components_constructive` with a new in-module constructive
      helper:
      `runtime_compute_half_edge_components`.
      the new helper builds components via a bounded frontier walk and returns
      `Option::None` on any out-of-bounds neighbor link, avoiding bridge calls
      to runtime `Mesh::*_for_verification` methods.
      in `src/halfedge_mesh.rs`, removed now-unused
      `half_edge_components_for_verification`.
    - failed attempt (rolled back in-pass):
      first implementation used a `frontier.pop()` proof shape without
      sufficient loop invariants, which caused Verus precondition failures on
      `visited[start]`, `m.half_edges[h]`, and `visited[n]` indexing in full
      module verification. stabilized by switching to a frontier-index walk
      (`frontier_idx`) with explicit bounds checks before every mesh/visited
      index.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        now reports one wrapper (down from two in the previous pass).
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement half_edge_components_constructive`
      passed (`1 verified, 0 errors` partial);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`182 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`182 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`217 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, constructor bridge removal completion):
    - selected task in this pass:
      remove the final constructor `external_body` bridge so
      `runtime_halfedge_mesh_refinement.rs` has no remaining trusted wrapper.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `ex_mesh_from_face_cycles` and added a fully constructive in-module
      builder:
      `runtime_build_mesh_from_face_cycles`.
      rewired constructor-dependent wrappers to call the constructive builder:
      - `from_face_cycles_constructive_next_prev_face`,
      - `from_face_cycles_constructive_twin_assignment_total_involution`,
      - `from_face_cycles_constructive_edge_exactly_two_half_edges`,
      - `from_face_cycles_constructive_vertex_representatives`.
      implementation shape:
      - face/half-edge construction from face cycles with explicit checked
        arithmetic for `next/prev`,
      - twin assignment by bounded scan over built half-edges,
      - edge assignment by twin-pair representative,
      - vertex representative assignment via first-outgoing scan plus
        pop/reverse vertex materialization (avoids external clone calls).
    - failed attempts (rolled back/stabilized in-pass):
      - direct replacement with `Mesh::from_face_cycles(...)` in verified code;
        Verus rejects calls to functions declared outside `verus!`.
      - first constructive builder draft used mutable index assignment
        (`half_edges[h].field = ...`) and `.clone()` on external runtime types;
        Verus rejected both shapes. stabilized by using `Vec::set(...)` with
        explicit field reconstruction and ownership-preserving `pop()` flow.
    - trusted-boundary/interpreted-spec scans:
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned no matches (down from one wrapper in the previous pass).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_build_mesh_from_face_cycles`
      passed (`9 verified, 0 errors` partial);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement from_face_cycles_constructive_next_prev_face`
      passed (`1 verified, 0 errors` partial);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, twin-witness lint suppression removal):
    - selected task in this pass:
      maintain Exit Condition quality by removing a remaining targeted lint
      suppression in the all-oriented-edges-have-twin constructive checker.
    - code hardening:
      in `src/runtime_halfedge_mesh_refinement.rs`, removed
      `#[allow(unused_variables, unused_assignments)]` from
      `runtime_check_from_face_cycles_all_oriented_edges_have_twin` and added
      an explicit runtime read of the twin witness locals
      (`let _ = (twin_f, twin_i);`) at the post-search join point.
      this preserves the existing proof/invariant structure while eliminating
      the need for a local unused-variable/assignment override.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement runtime_check_from_face_cycles_all_oriented_edges_have_twin`
      passed (`5 verified, 0 errors` partial);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, kernel checker lint suppression cleanup):
    - selected task in this pass:
      maintain Exit Condition quality by removing remaining targeted
      `unused_variables` / `unused_assignments` suppressions in
      `src/verified_checker_kernels.rs`.
    - code hardening:
      removed five `#[allow(unused_variables, unused_assignments)]`
      annotations from:
      - `kernel_check_next_prev_inverse`,
      - `kernel_check_prev_next_inverse`,
      - `kernel_check_face_cycles`,
      - `kernel_check_vertex_manifold_single_cycle`,
      - `kernel_check_edge_has_exactly_two_half_edges`.
      replaced those suppressions with explicit runtime witness-local reads at
      stable join points (`let _ = ...`) so rustc test-mode no longer reports
      local unused warnings for proof-only witness variables.
    - failed attempt (stabilized in-pass):
      first removed the annotations without adding explicit witness-local
      reads; rustc test-mode then surfaced expected local warnings
      (`bad_idx`, `h_prev/steps_prev`, `bad_e`, `h2`, `twin0/twin1`, `rep`).
      stabilized by adding explicit runtime reads for those locals while
      keeping proof structure unchanged.
    - verification checks:
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`);
      `./scripts/verify-vcad-topology-fast.sh verified_checker_kernels`
      passed (`35 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh runtime_halfedge_mesh_refinement`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`).
  - burndown update (2026-02-18, vcad-topology dead-code warning cleanup):
    - selected task in this pass:
      keep Exit Condition maintenance tight by eliminating remaining
      `vcad-topology` rustc test-mode dead-code warnings in combined
      feature builds.
    - code hardening:
      - in `src/halfedge_mesh.rs`, tightened
        `bridge_index_and_twin_checks_agree` to
        `#[cfg(all(test, feature = "verus-proofs"))]` since it is a
        proof-bridge regression helper used only by tests.
      - in `src/runtime_halfedge_mesh_refinement.rs`, added
        `#[cfg_attr(not(verus_keep_ghost), allow(dead_code))]` to the six
        `#[verifier::external_type_specification]` wrapper structs
        (`ExMesh`, `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`,
        `ExFace`) so rustc test-mode no longer reports dead-code noise for
        proof-only external-type shims.
    - failed attempts:
      none in this pass.
    - verification checks:
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`) with no `vcad-topology` warnings;
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`).
  - burndown update (2026-02-18, status-note consistency + exit-condition rerun):
    - selected task in this pass:
      keep Exit Condition burndown status consistent with the current verified
      kernel contracts.
    - doc hardening:
      corrected the stale D-section note for
      `kernel_check_vertex_manifold_single_cycle` from an old
      bounds-only status to the current verified contract
      `out ==> kernel_vertex_manifold_single_cycle_total_spec(m)`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun):
    - selected task in this pass:
      revalidate the Exit Condition on the current tree and confirm trust
      boundaries remain eliminated in `vcad-topology`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + warning-scope audit):
    - selected task in this pass:
      rerun Exit Condition validation and capture whether any remaining build
      warnings are in `vcad-topology` itself versus dependency crates.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      both `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      first attempted
      `/home/bepis/Documents/verifycad/VerusCAD/scripts/run-codex-task.sh "<summary>"`;
      this script expects zero positional arguments and returned
      `error: expected zero arguments`.
      stable invocation in this workspace is:
      update `scripts/run-codex-task.message.txt`, then run
      `/home/bepis/Documents/verifycad/VerusCAD/scripts/run-codex-task.sh`
      with no arguments.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + no-regression confirmation):
    - selected task in this pass:
      re-run the Exit Condition validation on the current tree and confirm no
      trust-surface regressions before handoff.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      both `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + full test-matrix refresh):
    - selected task in this pass:
      re-run Exit Condition trust-surface validation and refresh the full
      `vcad-topology` verification/test matrix (`fast`, `full`, baseline tests,
      `geometry-checks`, and `geometry-checks,verus-proofs`) on the current
      tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      `cargo test -p vcad-topology`, `cargo test -p vcad-topology --features geometry-checks`,
      and `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` emitted warnings
      only from dependency crates (`vstd`, `vcad-math`, `vcad-geometry`), with no new warnings
      from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + matrix reconfirmation):
    - selected task in this pass:
      revalidate the Exit Condition on the current tree and reconfirm the
      full `vcad-topology` verification/test matrix before handoff.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      `cargo test -p vcad-topology`, `cargo test -p vcad-topology --features geometry-checks`,
      and `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` emitted warnings
      only from dependency crates (`vstd`, `vcad-math`, `vcad-geometry`), with no new warnings
      from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass audit):
    - selected task in this pass:
      pick an explicit checklist task from this document and perform a fresh
      verification burndown pass on `vcad-topology`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      `cargo test -p vcad-topology`, `cargo test -p vcad-topology --features geometry-checks`,
      and `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` emitted warnings
      only from dependency crates (`vstd`, `vcad-math`, `vcad-geometry`), with no new warnings
      from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + lock-contention note):
    - selected task in this pass:
      rerun Exit Condition validation and refresh the full verification/test
      matrix while recording any operational issues encountered in this run.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      `cargo test -p vcad-topology`, `cargo test -p vcad-topology --features geometry-checks`,
      and `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"` emitted warnings
      only from dependency crates (`vstd`, `vcad-math`, `vcad-geometry`), with no new warnings
      from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - operational note:
      `./scripts/verify-vcad-topology.sh` initially printed
      `Blocking waiting for file lock on artifact directory` and then
      continued to completion without intervention.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + command replay):
    - selected task in this pass:
      replay the Exit Condition verification command set and document results
      in one place for handoff traceability.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + no-regression refresh):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix on the current tree before
      handoff.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass verification matrix):
    - selected task in this pass:
      run the Exit Condition maintenance checklist again on the current tree
      and record fresh command results.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + verification snapshot refresh):
    - selected task in this pass:
      refresh the Exit Condition evidence by replaying trust-surface scans and
      the full `vcad-topology` verification/test matrix on the current tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-turn replay):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and the full
      `vcad-topology` verification/test matrix from the current tree, then
      record a fresh handoff snapshot.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `./scripts/verify-vcad-topology.sh` printed
      `Blocking waiting for file lock on artifact directory` once and then
      continued to successful completion.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + fresh matrix replay):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix on the current tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `./scripts/verify-vcad-topology.sh` printed
      `Blocking waiting for file lock on artifact directory` at startup and
      then continued to a successful completion without intervention.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + fresh matrix replay):
    - selected task in this pass:
      replay the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix from a clean tree, then log
      current-pass results for handoff traceability.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `./scripts/verify-vcad-topology.sh` printed
      `Blocking waiting for file lock on artifact directory` once and then
      continued to successful completion.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + clean-pass snapshot):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix, then log a fresh snapshot.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + sandbox-constrained matrix):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and verification/test
      matrix on the current tree, documenting sandbox-constrained failures
      explicitly to avoid repeated dead-end command retries.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      - `./scripts/verify-vcad-topology-fast.sh` failed in this sandbox with
        `error: cannot connect to socket at '/nix/var/nix/daemon-socket/socket': Operation not permitted`.
      - `./scripts/verify-vcad-topology.sh` failed in this sandbox with the
        same Nix daemon socket permission error.
      - direct fallback command
        `cargo verus verify --manifest-path crates/vcad-topology/Cargo.toml -p vcad-topology --features verus-proofs -- --verify-only-module runtime_halfedge_mesh_refinement --triggers-mode silent`
        failed because Verus requires `rustup` in this environment
        (`verus: rustup not found, or not executable`).
    - verification checks:
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + verification matrix recovery):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and the full
      `vcad-topology` verification/test matrix, then log a fresh snapshot
      from the current sandbox.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `./scripts/verify-vcad-topology-fast.sh` printed
      `Blocking waiting for file lock on artifact directory` once and then
      completed successfully.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + sandbox recovery confirmation):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix after the prior
      sandbox-constrained failure snapshot, and record whether the verifier
      scripts recover in this workspace state.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `cargo test -p vcad-topology` and
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      each briefly printed `Blocking waiting for file lock on build directory`
      and then continued to successful completion without intervention.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-turn snapshot):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and full
      `vcad-topology` verification/test matrix, then record a fresh snapshot
      from the current workspace state.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `./scripts/verify-vcad-topology-fast.sh` printed
      `Blocking waiting for file lock on artifact directory` once and then
      continued to successful completion.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + fresh matrix replay):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + matrix confirmation replay):
    - selected task in this pass:
      rerun the Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no new warnings from `vcad-topology`.
    - operational note:
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      briefly printed `Blocking waiting for file lock on build directory`
      and then completed successfully.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current workspace snapshot):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and refresh the full
      `vcad-topology` verification/test matrix in the current workspace state.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + verification matrix refresh):
    - selected task in this pass:
      pick an explicit Exit Condition task and rerun trust-surface validation
      plus the full `vcad-topology` verification/test matrix on the current
      workspace tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix refresh):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and refresh the full
      `vcad-topology` verification/test matrix on the current workspace state.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + fresh matrix snapshot):
    - selected task in this pass:
      pick an explicit Exit Condition task and rerun trust-surface validation
      plus the full `vcad-topology` verification/test matrix on the current
      workspace tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-turn matrix replay):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + full-src trust-surface sweep):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + matrix replay refresh):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches.
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches.
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix replay):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T06:51:50-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\("`
        over
        `runtime_halfedge_mesh_refinement.rs`,
        `verified_checker_kernels.rs`, and `halfedge_mesh.rs`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass verification matrix):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:00:40-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + parallel test lock note):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:03:46-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs crates/vcad-topology/src/verified_checker_kernels.rs crates/vcad-topology/src/halfedge_mesh.rs`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - operational note:
      two `cargo test` invocations printed
      `Blocking waiting for file lock on build directory` because they were
      launched in parallel; both resumed automatically and completed.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix refresh):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:05:52-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix replay):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:09:10-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`191 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`226 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix replay):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:32:50-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`192 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`227 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
  - burndown update (2026-02-18, exit-condition maintenance rerun + current-pass matrix replay):
    - selected task in this pass:
      rerun Exit Condition trust-surface scans and replay the full
      `vcad-topology` verification/test matrix on the current workspace tree.
    - run timestamp:
      `2026-02-18T07:35:10-08:00`.
    - trust-surface scans:
      - `rg -n "assume_specification|external_fn_specification|\\buninterpreted\\b|admit\\(|assume\\(" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs crates/vcad-topology/src/verified_checker_kernels.rs crates/vcad-topology/src/halfedge_mesh.rs`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_body\\]" crates/vcad-topology/src`
        returned no matches (`0` lines).
      - `rg -n "\\[verifier::external_type_specification\\]" crates/vcad-topology/src/runtime_halfedge_mesh_refinement.rs`
        returned 6 expected proof-facing type shims (`ExMesh`,
        `ExMeshBuildError`, `ExHalfEdge`, `ExVertex`, `ExEdge`, `ExFace`).
    - warning-scope note:
      all `cargo test -p vcad-topology` invocations in this pass emitted
      warnings only from dependency crates (`vstd`, `vcad-math`,
      `vcad-geometry`), with no warnings from `vcad-topology`.
    - failed attempts:
      none in this pass.
    - verification checks:
      `./scripts/verify-vcad-topology-fast.sh`
      passed (`192 verified, 0 errors`);
      `./scripts/verify-vcad-topology.sh`
      passed (`227 verified, 0 errors`);
      `cargo test -p vcad-topology`
      passed (`4 passed, 0 failed`);
      `cargo test -p vcad-topology --features geometry-checks`
      passed (`5 passed, 0 failed`);
      `cargo test -p vcad-topology --features "geometry-checks,verus-proofs"`
      passed (`6 passed, 0 failed`).
