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
- [ ] Prove face-cycle construction assigns coherent `next/prev/face` fields.
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
  - file: `src/halfedge_mesh.rs`
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
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [ ] Prove undirected-edge grouping induces exactly-two-half-edges per edge.
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
  - file: `src/halfedge_mesh.rs`
  - refinement file: `src/runtime_halfedge_mesh_refinement.rs`
- [ ] Prove vertex representative (`vertex.half_edge`) is valid and non-isolated.
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
    `out ==> kernel_face_representative_cycles_total_spec(m)`, which now includes
    representative-anchored closure/min-length plus per-step face-membership witnesses.
    explicit no-overlap/global-coverage spec linkage is still pending.
- [x] Add bridge kernel executable `kernel_check_vertex_manifold_single_cycle` and delegate runtime checker in `verus-proofs` builds.
  - file: `src/verified_checker_kernels.rs`
  - note: current proved contract is bounds-soundness (`out ==> kernel_index_bounds_spec`); full vertex-manifold semantic contract is pending.
- [x] Verify `check_index_bounds`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_twin_involution`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [x] Verify `check_prev_inverse_of_next`.
  - in `verus-proofs` builds, this is delegated to verified kernel checker.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_face_cycles` (closure + no overlap + min cycle length).
  - in `verus-proofs` builds, this now delegates to kernel executable `kernel_check_face_cycles`.
  - semantic contract strengthening in kernel proof is still pending.
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
- [ ] Verify `half_edge_components` BFS soundness and completeness.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `component_count` equals number of connected components.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `euler_characteristics_per_component` computes `V - E + F` per BFS component.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `check_euler_formula_closed_components` iff all closed components have characteristic `2`.
  - file: `src/halfedge_mesh.rs`

## F. Verify Top-Level APIs
- [ ] Verify `is_structurally_valid` exactly matches conjunction of structural invariants.
  - file: `src/halfedge_mesh.rs`
- [ ] Verify `is_valid` exactly matches `is_structurally_valid && check_euler_formula_closed_components`.
  - file: `src/halfedge_mesh.rs`

## G. Verify Reference Mesh Constructors End-to-End
- [ ] Prove `tetrahedron` builds and satisfies `is_valid`.
  - prove counts: `V=4, E=6, F=4, H=12`.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove `cube` builds and satisfies `is_valid`.
  - prove counts: `V=8, E=12, F=6, H=24`.
  - file: `src/halfedge_mesh.rs`
- [ ] Prove `triangular_prism` builds and satisfies `is_valid`.
  - prove counts: `V=6, E=9, F=5, H=18`.
  - file: `src/halfedge_mesh.rs`

## H. Reuse-Focused Hardening (No Reinventing)
- [ ] Reuse `vcad-math` proof surfaces for arithmetic/cardinality/order where applicable.
- [ ] Reuse `vcad-geometry` predicates for optional geometric non-degeneracy extensions (face area > 0, etc.).

## Exit Condition
- [x] No `assume_specification` remains in `vcad-topology` for runtime mesh behavior.
- [x] No uninterpreted spec predicate remains for currently implemented invariants.
- [x] `verify-vcad-topology-fast.sh` and `verify-vcad-topology.sh` both green.
