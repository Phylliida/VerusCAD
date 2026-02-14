# vcad-math Verification TODO
Goal: remove trusted runtime proof boundaries so `vcad-math` runtime behavior is justified by explicit specs + proofs.


## Baseline Snapshot (2026-02-13)
- [x] Full crate verifies: `./scripts/verify-vcad-math.sh`.
- [x] No runtime assumptions remain (`assume_specification[...]`).
- [x] Trust surface reduced to zero runtime assumptions in `crates/vcad-math/src`.
- [x] Current assumption count: `0`.
- [ ] Residual trusted `external_body` bridges are eliminated.

## Current Status Snapshot (2026-02-14)
- [x] `./scripts/verify-vcad-math.sh` succeeds on this branch.
- [x] `./scripts/verify-vcad-geometry.sh` succeeds on this branch (`108 verified, 0 errors`).
- [x] `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.
- [ ] `rg -n "#\\[verifier::external_body\\]" crates/vcad-math/src` still reports one item:
  - `crates/vcad-math/src/runtime_scalar.rs` (`RuntimeScalar::signum_i8`).

### What Is Done
- Runtime orientation paths now branch on semantic sign enum (`RuntimeSign`) instead of raw `i8`.
- Geometry verus callsites that previously extracted raw sign in proof paths have been migrated to semantic sign where practical (`collinear3d`, `segment_intersection::scalar_sign`).
- Runtime/proof consistency lemmas for sign are in place (`signum_i8_proof`, `lemma_signum_i8_matches_proof`) and continue to verify.
- Geometry runtime helpers/tests no longer call `RuntimeScalar::signum_i8` directly; they use semantic wrappers (`RuntimeSign` / orientation classes).

### Remaining Direct `signum_i8` Surface
- Trusted source:
  - `crates/vcad-math/src/runtime_scalar.rs` (`#[verifier::external_body]` implementation).
- Remaining direct callsite:
  - `crates/vcad-math/src/runtime_scalar.rs` (`RuntimeScalar::sign` calls `signum_i8` under `verus_keep_ghost`).

### Core Blocker (still unchanged)
- Under `#[cfg(verus_keep_ghost)]`, `RuntimeScalar` has no exec-visible numeric witness.
- Verus forbids deriving exec values by branching on spec-only expressions (`self@...`) and forbids calling proof fns from exec fns.
- Therefore `RuntimeScalar::sign()` currently still depends on trusted `signum_i8()`.

## Final external_body Burn-Down (signum_i8)
- [x] Introduce semantic sign API: `RuntimeSign` (`Negative/Zero/Positive`) + `RuntimeScalar::sign()`.
- [x] Migrate orientation runtime paths to semantic sign branching (`runtime_orientation.rs`, `runtime_orientation3.rs`).
- [x] Add proof-only bridge: `RuntimeScalar::signum_i8_proof`.
- [ ] Migrate verus-mode callers from exec sign extraction to proof-mode sign extraction.
- [x] `crates/vcad-geometry/src/orientation_predicates.rs` (verus sign APIs now derive from orientation class wrappers).
- [x] `crates/vcad-geometry/src/collinearity_coplanarity.rs` (verus `collinear3d` now threads `signum_i8_proof` alongside exec sign).
- [x] `crates/vcad-geometry/src/segment_intersection.rs` (verus `scalar_sign` now threads `signum_i8_proof` alongside exec sign).
- [x] Migrate verus geometry sign extraction to semantic `RuntimeSign` where possible (`collinear3d`, `scalar_sign`).
- [x] `crates/vcad-math/src/runtime_scalar.rs::recip` now proves runtime/proof sign agreement (`s == signum_i8_proof()`).
- [x] `crates/vcad-math/src/runtime_orientation.rs` and `runtime_orientation3.rs` now prove runtime/proof sign agreement (`s == signum_i8_proof()`).
- [ ] Remaining trusted sign bridge consumers in verus paths: `runtime_scalar.rs` (`sign`, `recip`), `runtime_orientation.rs`, `runtime_orientation3.rs`, and geometry helpers using `RuntimeScalar::sign()`.
- [ ] Remove the final `#[verifier::external_body]` on `RuntimeScalar::signum_i8`.
- [ ] Re-run full gates across `vcad-math`, `vcad-geometry`, `vcad-topology`.

## Full Remaining Work Plan (Final De-Trusting)
Goal: eliminate `RuntimeScalar::signum_i8` `external_body` without introducing new assumptions.

### Phase 1: Representation Decision (required before coding)
- [x] Choose exec witness strategy for `RuntimeScalar` in `verus_keep_ghost` mode.
- [x] Confirm witness can support exact sign/zero extraction in exec code.
- [x] Confirm witness update cost for `add/sub/mul/neg/normalize/recip` is acceptable.

Decision (2026-02-14):
- We need an exact exec witness (numerator/denominator over unbounded integers). A sign-only cache is not sufficient for `add/sub`.
- Bounded integer witnesses (`i64`/`i128`) are rejected for now because they change exact rational semantics.
- Implementation path: introduce a verified arbitrary-precision integer/rational witness layer in `vcad-math`, then wire `RuntimeScalar` (verus cfg) to that witness.

Notes:
- A sign-only witness is insufficient: operations like `add` need enough exec data to recompute next witness.
- Any bounded primitive witness (`i64/i128`) changes semantics unless overflow is fully ruled out.
- Preferred direction is an exact exec witness compatible with current exact rational semantics.
- A direct type-invariant + cached-sign experiment was attempted and reverted:
  - `#[verifier::type_invariant]` is incompatible with the current `RuntimeScalar` integration style (`external_type_specification` path and non-verus datatype declaration).

### Phase 2: Implement Witness-Carrying Scalar (verus mode)
- [x] Add prerequisite verified bigint witness module(s) for exact exec arithmetic.
- [x] Extend `RuntimeScalar` (verus cfg) with exec-visible witness fields.
- [ ] Add and prove representation invariant linking witness to `self@ : ScalarModel`.
- [ ] Update constructors (`from_int`, etc.) to initialize witness + model consistently.
  - [x] `RuntimeScalar::from_int` now initializes concrete exec witnesses:
    - `sign_witness` from runtime integer sign
    - `num_abs_witness` from runtime absolute value (`RuntimeBigNatWitness::from_u64`)
    - `den_witness = 1`
  - [x] `RuntimeScalar::{add,sub,mul}` no longer route through `from_model`; they now construct explicit witness-bearing outputs directly.
    - `sign_witness` is propagated by deterministic sign-combinator helpers.
    - `den_witness` now uses witness multiplication helper (`mul_limbwise_small_total`) in `add/sub/mul`.
    - `num_abs_witness` now uses witness arithmetic in `mul` and same-sign `add/sub` paths (`mul_limbwise_small_total` + `add_limbwise_small_total`).
    - Mixed-sign `add/sub` now uses multi-limb compare/sub witness helpers (`cmp_limbwise_small_total`, `sub_limbwise_small_total`) after scaled magnitude construction.
    - Scaling helpers are now multi-limb implementations (carry/borrow propagation with canonical trim).
  - [x] `RuntimeScalar::{neg,normalize,recip}` now build outputs directly (no `from_model` call in those methods).
    - Uses `RuntimeBigNatWitness::copy_small_total` for witness carry-through/swaps.
    - For `recip`, witness numerator/denominator are swapped (`den`, `|num|`) on nonzero path.
  - [x] No remaining `RuntimeScalar` constructors/operations route through placeholder `from_model` (helper remains but is unused).

Completed scaffold:
- `crates/vcad-math/src/runtime_bigint_witness.rs` introduced `RuntimeBigNatWitness`.
- Verus-side scaffold includes:
  - exact limb-value spec (`limbs_value_spec`)
  - base-power helper + append-value law (`pow_base_spec`, `lemma_limbs_value_push`)
  - canonical limb predicate (`canonical_limbs_spec`)
  - representation predicate (`wf_spec`)
  - verified constructors (`zero`, `from_u32`, `from_two_limbs`)
  - first verified limb-wise add step (`add_limbwise_small`, for `<=1` limb inputs with carry split)
- Runtime side includes basic exact arithmetic wrappers (`add`, `mul`) over `rug::Integer`.
- `RuntimeBigNatWitness::from_u64` is now available in both runtime and verus modes (wf guarantee in verus mode).
- `RuntimeBigNatWitness` now also exposes total small-limb witness arithmetic helpers in verus mode:
  - `add_limbwise_small_total` (now full multi-limb carry addition + canonical trim)
  - `mul_limbwise_small_total` (now full schoolbook multi-limb multiplication + canonical trim)
  - `cmp_limbwise_small_total` (now full multi-limb compare via trimmed length + high-to-low limb scan)
  - `sub_limbwise_small_total` (now full multi-limb borrow subtraction for `self >= rhs`)
  - `copy_small_total` (now full multi-limb copy with canonical trailing-zero trim)
- `RuntimeScalar` (verus cfg) now carries explicit witness slots (`sign_witness`, `num_abs_witness`, `den_witness`) as scaffolding; model-consistency proofs are still pending.

### Phase 3: Rebuild Scalar Operations Over Witness
- [x] Re-implement `add/sub/mul/neg/normalize/recip` to update witness in exec mode.
- [x] Re-prove each method’s ensures against `ScalarModel` specs.
- [x] Keep assumption count at `0` and avoid new `external_body` additions.

### Phase 4: Delete Trusted Sign Bridge
- [ ] Implement `RuntimeScalar::sign()` directly from witness (no call to trusted signum).
- [ ] Replace `signum_i8` implementation with non-trusted code or remove API if no longer needed.
- [ ] Remove `#[verifier::external_body]` from `RuntimeScalar::signum_i8`.

### Phase 5: Caller Cleanup and Hardening
- [x] Remove residual raw runtime `signum_i8` callsites in geometry runtime helpers.
- [x] Keep semantic API boundary (`RuntimeSign`, orientation classes) as canonical surface.
- [x] Re-run proof consistency checks where sign relations are asserted.

### Phase 6: Final Gates
- [x] `./scripts/verify-vcad-math.sh`
- [x] `./scripts/verify-vcad-geometry.sh`
- [ ] `./scripts/verify-vcad-topology.sh` (currently has unrelated pre-existing issues to clear separately)
- [ ] Confirm:
  - `rg -n "#\\[verifier::external_body\\]" crates/vcad-math/src` returns no matches.
  - `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.

## Burn-Down Inventory
- direct `signum_i8` callsites (current):
  `crates/vcad-math/src/runtime_scalar.rs` (`sign`, trusted source)
- semantic sign (`RuntimeSign`) callsites in verus paths (dependent on trusted bridge via `RuntimeScalar::sign()`):
  `crates/vcad-math/src/runtime_orientation.rs`
  `crates/vcad-math/src/runtime_orientation3.rs`
  `crates/vcad-math/src/runtime_scalar.rs` (`recip`)
  `crates/vcad-geometry/src/collinearity_coplanarity.rs`
  `crates/vcad-geometry/src/segment_intersection.rs`
- `recip` caller files:
  `crates/vcad-math/src/runtime_quaternion.rs`
  `crates/vcad-geometry/src/sidedness.rs`
  `crates/vcad-geometry/src/segment_intersection.rs`

## Known Verus Constraints (exec/spec boundary)
- Implement signum via proof fn and call it from exec: not allowed.
- Return non-`()` value from `proof { ... }` expression: not allowed.
- Use `choose` in exec mode: not allowed.
- Branch on `self@.signum()` in an exec function: blocked (`int`/`nat` are ghost-only in exec contexts).

## Assumption Inventory (Current)
- [x] `src/runtime_scalar_refinement.rs` (`0`)
- [x] `src/runtime_vec2_refinement.rs` (`0`)
- [x] `src/runtime_point2_refinement.rs` (`0`)
- [x] `src/runtime_orientation_refinement.rs` (`0`)
- [x] `src/runtime_vec3_refinement.rs` (`0`)
- [x] `src/runtime_point3_refinement.rs` (`0`)
- [x] `src/runtime_orientation3_refinement.rs` (`0`)
- [x] `src/runtime_vec4_refinement.rs` (`0`)
- [x] `src/runtime_point4_refinement.rs` (`0`)
- [x] `src/runtime_quaternion_refinement.rs` (`0`)

## Recommended Work Order
- [x] 1) Orientation wrappers (2D/3D): low count, good pattern warm-up.
- [x] 2) Vec/Point 2D runtime boundary.
- [x] 3) Vec/Point 3D runtime boundary.
- [x] 4) Vec/Point 4D runtime boundary.
- [x] 5) Quaternion runtime boundary.
- [x] 6) Scalar runtime boundary (likely hardest due backend/runtime representation).
- [ ] 7) Final de-trusting + verification gate (remove remaining `external_body` items).

## A. runtime_orientation_refinement.rs (0)
- [x] `runtime_orientation::orient2d`
- [x] `runtime_orientation::scale_point_from_origin`
- [x] `runtime_orientation::orientation`

## B. runtime_orientation3_refinement.rs (0)
- [x] `runtime_orientation3::orient3d`
- [x] `runtime_orientation3::scale_point_from_origin3`
- [x] `runtime_orientation3::orientation3`

## C. runtime_vec2_refinement.rs (0)
- [x] `RuntimeVec2::new`
- [x] `RuntimeVec2::from_ints`
- [x] `RuntimeVec2::zero`
- [x] `RuntimeVec2::add`
- [x] `RuntimeVec2::sub`
- [x] `RuntimeVec2::neg`
- [x] `RuntimeVec2::scale`
- [x] `RuntimeVec2::dot`
- [x] `RuntimeVec2::cross`
- [x] `RuntimeVec2::norm2`

## D. runtime_point2_refinement.rs (0)
- [x] `RuntimePoint2::new`
- [x] `RuntimePoint2::from_ints`
- [x] `RuntimePoint2::add_vec`
- [x] `RuntimePoint2::sub`
- [x] `RuntimePoint2::dist2`

## E. runtime_vec3_refinement.rs (0)
- [x] `RuntimeVec3::new`
- [x] `RuntimeVec3::from_ints`
- [x] `RuntimeVec3::zero`
- [x] `RuntimeVec3::add`
- [x] `RuntimeVec3::sub`
- [x] `RuntimeVec3::neg`
- [x] `RuntimeVec3::scale`
- [x] `RuntimeVec3::dot`
- [x] `RuntimeVec3::cross`
- [x] `RuntimeVec3::norm2`

## F. runtime_point3_refinement.rs (0)
- [x] `RuntimePoint3::new`
- [x] `RuntimePoint3::from_ints`
- [x] `RuntimePoint3::add_vec`
- [x] `RuntimePoint3::sub`
- [x] `RuntimePoint3::dist2`

## G. runtime_vec4_refinement.rs (0)
- [x] `RuntimeVec4::new`
- [x] `RuntimeVec4::from_ints`
- [x] `RuntimeVec4::zero`
- [x] `RuntimeVec4::add`
- [x] `RuntimeVec4::sub`
- [x] `RuntimeVec4::neg`
- [x] `RuntimeVec4::scale`
- [x] `RuntimeVec4::dot`
- [x] `RuntimeVec4::norm2`

## H. runtime_point4_refinement.rs (0)
- [x] `RuntimePoint4::new`
- [x] `RuntimePoint4::from_ints`
- [x] `RuntimePoint4::add_vec`
- [x] `RuntimePoint4::sub`
- [x] `RuntimePoint4::dist2`

## I. runtime_quaternion_refinement.rs (0)
- [x] `RuntimeQuaternion::new`
- [x] `RuntimeQuaternion::from_ints`
- [x] `RuntimeQuaternion::zero`
- [x] `RuntimeQuaternion::one`
- [x] `RuntimeQuaternion::add`
- [x] `RuntimeQuaternion::sub`
- [x] `RuntimeQuaternion::neg`
- [x] `RuntimeQuaternion::scale`
- [x] `RuntimeQuaternion::mul`
- [x] `RuntimeQuaternion::conjugate`
- [x] `RuntimeQuaternion::norm2`
- [x] `RuntimeQuaternion::inverse`
- [x] `RuntimeQuaternion::rotate_vec3`

## J. runtime_scalar_refinement.rs (0 assumptions)
- [x] `RuntimeScalar::from_int`
- [x] `RuntimeScalar::from_fraction` (runtime-only under `#[cfg(not(verus_keep_ghost))]`)
- [x] `RuntimeScalar::add`
- [x] `RuntimeScalar::sub`
- [x] `RuntimeScalar::mul`
- [x] Model witness: `Scalar::reciprocal_constructive` (constructive reciprocal for nonzero model scalars)
- [x] `RuntimeScalar::recip`
- [x] `RuntimeScalar::neg`
- [x] `RuntimeScalar::normalize`
- [ ] `RuntimeScalar::signum_i8` (still `external_body`)

## Residual Trusted Items
- [ ] `src/runtime_scalar.rs`: `RuntimeScalar::signum_i8` (`#[verifier::external_body]`)

## Current Blocker
- `RuntimeScalar` under `#[cfg(verus_keep_ghost)]` stores only ghost model state.
- Verus currently disallows branching in exec code on spec-only values (e.g., `self@.signum()`), so removing the final `signum_i8` `external_body` requires a deeper representation refactor for the verus path.

## Completion Gates
- [x] `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.
- [x] `./scripts/verify-vcad-math.sh` succeeds after each milestone.
- [x] Proof quality pass: no unnecessary trigger warnings in newly touched modules.
