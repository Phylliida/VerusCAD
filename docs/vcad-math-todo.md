# vcad-math Proof TODO
Focused list of proof work and migration closure notes for `vcad-math`.

This list assumes the current baseline (orientation classification, scale, norm2, dist2, signum) is already verified.

## Agent Execution Loop (Requested 2026-02-12)
- [x] Sync this TODO to reality before each implementation pass:
  - add any missing required work items discovered during code/proof audits.
  - do not mark items complete unless they are verified in current rational branch.
- [x] Execute all unchecked TODO items in priority order within `vcad-math`.
- [x] After finishing all TODO items, run an anti-cheating audit:
  - identify lemmas that prove weaker/irrelevant properties than their contracts suggest.
  - strengthen/fix contracts and proofs accordingly.
- [x] Keep work strictly scoped to `vcad-math` until the list is exhausted.

## Rational Re-Port Backlog (Reality Audit 2026-02-12)
Derived from diff against:
`crates/vcad-math/backups/2026-02-12-rational-migration-pause/pre-rational-head/src/`

### Scalar
- [x] Reintroduce core scalar law lemmas (rational semantics; structural where valid):
  - `lemma_add_commutative`
  - `lemma_add_associative`
  - `lemma_add_zero_identity`
  - `lemma_add_inverse`
  - `lemma_sub_is_add_neg`
  - `lemma_mul_associative`
  - `lemma_mul_one_identity`
  - `lemma_mul_zero`
  - `lemma_mul_distributes_over_add`
  - `lemma_signum_mul`
- [x] Reintroduce scalar cancellation/order lemmas under rational semantics:
  - [x] Define/order-stabilize scalar comparison contract for rationals (`le_spec`/`lt_spec` or equivalent) so monotonicity lemmas have a canonical target.
  - `lemma_add_left_cancel` (+ strong variant, done)
  - `lemma_add_right_cancel` (+ strong variant, done)
  - `lemma_le_add_monotone` (+ strong variant, done)
  - `lemma_le_mul_monotone_nonnegative` (+ strong variant, done)
  - `lemma_mul_zero_implies_factor_zero` (done)

### Vec2
- [x] Reintroduce vector additive/negation laws:
  - `lemma_eq_from_component_ints` (or rational-equivalent bridge: done via `Vec2::eqv_spec` + `lemma_eqv_from_components`)
  - `lemma_add_commutative`
  - `lemma_add_associative`
  - `lemma_add_zero_identity`
  - `lemma_add_inverse`
  - `lemma_neg_involution`
  - `lemma_sub_is_add_neg`
- [x] Reintroduce scaling laws:
  - `lemma_scale_zero`
  - `lemma_scale_one_identity`
  - `lemma_scale_associative`
  - `lemma_scale_distributes_over_vec_add`
  - `lemma_scale_distributes_over_scalar_add`
  - `lemma_scale_neg_vector`
  - `lemma_scale_neg_scalar`
- [x] Reintroduce dot/cross algebraic laws:
  - `lemma_dot_symmetric` (done)
  - `lemma_dot_linear_left` (done)
  - `lemma_dot_linear_right` (done)
  - `lemma_dot_scale_extract_left` (done)
  - `lemma_cross_linear_left` (done)
  - `lemma_cross_linear_right` (done)
  - `lemma_cross_scale_extract_left` (done)
  - `lemma_cross_scale_extract_right` (done)
  - `lemma_cross_self_zero` (non-signum form, done)
- [x] Reintroduce norm laws:
  - `lemma_norm2_nonnegative` (done)
  - `lemma_norm2_zero_iff_zero` (done)
  - `lemma_norm2_scale` (done)

### Point2
- [x] Reintroduce point/vector cancellation + action laws:
  - `lemma_add_vec_zero_identity` (done)
  - `lemma_add_vec_associative` (done)
  - `lemma_sub_then_add_cancel` (done)
  - `lemma_add_then_sub_cancel` (done)
  - `lemma_add_vec_unique` (done)
- [x] Reintroduce distance laws:
  - `lemma_dist2_is_sub_norm2` (done)
  - `lemma_dist2_symmetric` (done)
  - `lemma_dist2_nonnegative` (done)
  - `lemma_dist2_self_zero` (done, semantic-equality form)
  - `lemma_dist2_zero_iff_equal_points` (done)
  - `lemma_dist2_translation_invariant` (done)
  - `lemma_sub_translation_invariant` (done)
- [x] Reintroduce point equality bridge equivalent to prior `lemma_eq_from_component_ints` (done via `Point2::eqv_spec` + `lemma_eqv_from_components`).

### Orientation
- [x] Reintroduce determinant/value lemmas missing after migration:
  - `lemma_orient2d_collinear` (done)
  - `lemma_orient2d_unit_ccw` (done)
  - `lemma_orient2d_translation_invariant` (done)
  - `lemma_orient2d_scale_from_origin` (done)
- [x] Reintroduce full orientation enum/class laws:
  - `lemma_orientation_spec_exclusive` (done)
  - `lemma_orientation_spec_translation_invariant` (done)
  - `lemma_orientation_spec_scale_nonzero_preserves` (done)
  - `lemma_orientation_spec_scale_nonzero_preserves_strong` (done)
  - `lemma_orientation_spec_scale_zero_collinear` (done)
  - `lemma_orientation_spec_scale_zero_collinear_strong` (done)
- [x] Reintroduce canonical permutation lemmas by legacy names:
  - `lemma_orient2d_cyclic_invariant` (alias/wrapper over `lemma_orient2d_cyclic_eqv`)
  - `lemma_orient2d_permutation_table` (classical sign/same-or-neg form)

## 2026-02-12 Rational Migration Pause
- [x] Choose active baseline for next edits:
  - `crates/vcad-math/backups/2026-02-12-rational-migration-pause/pre-rational-head/src/` (full integer-proof baseline),
  - or `crates/vcad-math/backups/2026-02-12-rational-migration-pause/current-in-progress/src/` (partial rational rewrite, selected).
- [x] Keep both snapshots immutable; only copy out of backup directories when restoring files.
- [x] Bring the active rational branch back to green verification (`./scripts/verify-vcad-math.sh`).
- [x] Reintroduce the full theorem surface on top of the rational branch.
- [x] Rebuild `Scalar` law surface for rational arithmetic with explicit semantic-equality contracts (`as_real`/`eqv_spec`) where structural equality is no longer canonical.
  - [x] Rational scalar core is re-established (`num/den` model, `add/sub/mul/neg`, signum cases, denominator-product lemmas).
  - [x] Added first semantic-equivalence seed lemmas (`eqv_spec` reflexive/symmetric).
  - [x] Added second-wave semantic-equivalence helpers:
    - `lemma_eqv_transitive`
    - `lemma_eqv_neg_congruence`
  - [x] Added arithmetic semantic-congruence helpers:
    - `lemma_eqv_add_congruence_left/right`
    - `lemma_eqv_add_congruence`
    - `lemma_eqv_mul_congruence_left/right`
    - `lemma_eqv_mul_congruence`
    - `lemma_eqv_sub_congruence`
    - `lemma_eqv_sub_chain`
    - `lemma_eqv_mul_distributive_left`
    - `lemma_eqv_sub_cancel_right`
  - [x] Added negation bridge helpers for rational algebra:
    - `lemma_mul_neg_right`
    - `lemma_sub_neg_both`
  - [x] Added zero-numerator arithmetic helpers needed for geometric degeneracy proofs:
    - `lemma_mul_left_zero_num`
    - `lemma_mul_right_zero_num`
    - `lemma_sub_both_zero_num`
  - [x] Reintroduce strong arithmetic semantic lemmas (add/mul/sub over semantic equality, cancellation/order laws).
- [x] Re-add vector/point/orientation theorem layers that were temporarily dropped during migration:
  - `Vec2`: bilinearity, symmetry/antisymmetry, scaling laws, norm laws,
  - `Point2`: cancellation/translation/dist2 laws,
  - `orientation`: permutation, translation, and scale behavior theorems.
  - [x] First recovered vector theorem: `Vec2::lemma_cross_self_zero_signum`.
  - [x] Recovered orientation degeneracy theorems for repeated points:
    - `lemma_orient2d_degenerate_repeated_points`
    - `lemma_orientation_spec_degenerate_repeated_points`
  - [x] Recovered orientation swap antisymmetry/core collinearity lemmas:
    - `lemma_orient2d_swap_antisymmetric`
    - `lemma_orient2d_swap_antisymmetric_num`
    - `lemma_is_collinear_swap`
    - `lemma_orientation_spec_swap_collinear`
  - [x] Recovered full orientation swap classifier laws:
    - `lemma_is_ccw_swap_to_cw`
    - `lemma_is_cw_swap_to_ccw`
    - `lemma_orientation_spec_swap`
  - [x] Added vector semantic-congruence bridge:
    - `Vec2::lemma_cross_eqv_congruence`
    - `Vec2::lemma_cross_neg_right`
    - `Vec2::lemma_cross_add_self_right_eqv`
  - [x] Added point subtraction bridge helpers:
    - `Point2::lemma_sub_antisymmetric`
    - `Point2::lemma_sub_chain_eqv`
  - [x] Recover cyclic/permutation semantic-equality determinant law under rationals:
    - `lemma_orient2d_cyclic_eqv(a,b,c): orient2d_spec(a,b,c).eqv_spec(orient2d_spec(b,c,a))`
    - done via reusable scalar/vector congruence + subtraction chain/cancel lemmas (no one-shot orientation polynomial).
  - [x] Added full orientation permutation determinant table on rational semantics:
    - `lemma_orient2d_permutation_table_eqv`
    - even permutations are `eqv` to `orient2d_spec(a,b,c)` and odd permutations are `eqv` to its negation.
- [x] Decide normalization strategy for rational representation:
  - temporary non-normalized representation + semantic equality,
  - then canonical normalization proofs (gcd/sign placement/uniqueness).
  - decision: keep non-normalized runtime representation for now; treat `eqv_spec` as the semantic contract until roadmap normalization milestones land.
- [x] Update crate docs to state exact migration status and which theorem set is currently guaranteed.

## P0: Core algebra and order
- [x] Prove additive cancellation:
  - `a + c == b + c ==> a == b`
- [x] Prove multiplicative zero law and zero-divisor direction:
  - `a * 0 == 0`, `0 * a == 0`
  - `a * b == 0 ==> a == 0 || b == 0`
- [x] Prove order compatibility with addition:
  - `a <= b ==> a + c <= b + c`
- [x] Prove multiplication order behavior for nonnegative scalars:
  - `0 <= c && a <= b ==> a*c <= b*c`
- [x] Prove signum interaction lemmas:
  - `signum(-a) == -signum(a)`
  - `signum(a*b)` behavior by sign cases

## P0: Vector-space completeness
- [x] Prove negation involution:
  - `-(-v) == v`
- [x] Prove additive inverse for vectors:
  - `v + (-v) == 0`, `(-v) + v == 0`
- [x] Prove scale with negation consistency:
  - `(-v) * k == -(v*k)`
  - `v * (-k) == -(v*k)`
- [x] Prove dot linearity in right argument (left is already present).
- [x] Prove cross linearity in right argument (left is already present).
- [x] Prove scale extraction rules:
  - `dot(v*k, w) == k * dot(v,w)`
  - `cross(v*k, w) == k * cross(v,w)`

## P0: Norm and distance strengthening
- [x] Prove `dist2(p, p) == 0`.
- [x] Prove `norm2(v) == 0 <==> v == 0`.
- [x] Prove `dist2(p, q) == 0 <==> p == q`.
- [x] Prove `dist2` equivalence with translated difference form:
  - `dist2(p, q) == norm2(p - q)` as a dedicated named lemma.
- [x] Prove scale effect on norm:
  - `norm2(v*k) == k*k*norm2(v)`.

## P1: Orientation and determinant structure
- [x] Prove full 6-permutation orientation table:
  - each permutation maps to same or negated determinant.
- [x] Prove orientation class exclusivity as an enum-level lemma:
  - exactly one of `Ccw | Cw | Collinear`.
- [x] Prove orientation translation invariance through `orientation_spec` directly (not only via determinant value).
- [x] Prove orientation behavior under uniform scaling:
  - positive scale preserves class,
  - negative scale also preserves class (uniform scaling in 2D has positive determinant `k^2`),
  - zero scale yields `Collinear`.

## P1: Affine point action laws
- [x] Prove point translation identity:
  - `p + 0 == p`.
- [x] Prove translation associativity:
  - `(p + u) + v == p + (u + v)`.
- [x] Prove subtraction/addition uniqueness:
  - `p + u == p + v ==> u == v`.

## P1: Contract-strengthening pass (anti-cheating hardening)
- [x] Strengthen vector algebra lemma contracts from component equalities to full structural equalities:
  - `lemma_neg_involution`: `v.neg_spec().neg_spec() == v`
  - `lemma_add_inverse`: `v + (-v) == 0` and `(-v) + v == 0` as `Vec2` equality
  - `lemma_scale_neg_vector`: `(-v) * k == -(v*k)` as `Vec2` equality
  - `lemma_scale_neg_scalar`: `v * (-k) == -(v*k)` as `Vec2` equality
- [x] Strengthen scalar algebra contracts to abstract `Scalar` equality where practical (not only `.as_int()` projections):
  - commutativity / associativity / distributivity / identities
  - cancellation lemmas
- [x] Add strengthened (non-implication) variants for cancellation/monotonicity lemmas using `requires`:
  - keep implication-style helpers if needed for proof ergonomics, but expose strongest canonical statements
- [x] Reduce representation leakage in proof bodies:
  - avoid proving via `.value` unless unavoidable
  - prefer proofs over abstract API (`add_spec`, `mul_spec`, `neg_spec`, etc.)
- [x] Add an audit checkpoint for rational migration:
  - no public law lemma depends on integer backing details
  - all public contracts remain valid after swapping `Scalar` internals
  - checkpoint: strengthened public law contracts now target structural equality (not projection equality), and representation-specific reasoning is confined to implementation/proof-bridge internals

## P1: Major-hole closure follow-up
- [x] Strengthen key geometric law lemmas from `.as_int()` equality to full `Scalar` equality:
  - dot/cross symmetry and linearity
  - scale extraction (`dot`, `cross`)
  - `dist2` symmetry/translation invariance
  - `orient2d` swap/cyclic/translation/permutation identities
- [x] Add strongest `requires`-style variants for orientation scaling lemmas:
  - `lemma_orientation_spec_scale_nonzero_preserves_strong`
  - `lemma_orientation_spec_scale_zero_collinear_strong`
  - keep implication-style wrappers for ergonomic use
- [x] Internalize representation bridge usage:
  - scalar equality bridge remains available for proof plumbing but is crate-internal (`pub(crate)`), not part of public law surface
- [x] Refactor crate layout so proofs are split across files:
  - `src/scalar.rs`
  - `src/vec2.rs`
  - `src/point2.rs`
  - `src/orientation.rs`
  - root `src/lib.rs` now just wires modules/exports

## Status
`P0-P3` tracked `vcad-math` proof/runtime TODO items are complete and green-verified on the rational branch.
`P4` (higher-dimensional + quaternion expansion) is now tracked as active planned work.

Anti-cheating follow-up notes:
- legacy compatibility wrappers restored where needed (`lemma_ccw_swap_to_cw`, `lemma_eq_from_component_ints` in `Vec2`/`Point2`) using rational semantic equality.
- contradiction-style branch in orientation collinearity swap proof was removed in favor of direct arithmetic implication proof.

Long-horizon milestones (canonical rational normalization, exec/spec dual-mode APIs, proof regression harness) now live in `docs/vcad-math-roadmap.md`.

## P2 Carryover (2026-02-12)
- [x] Add canonical sign-placement theorem surface for normalized rationals (`canonical_sign_spec`, `lemma_normalized_zero_has_unit_denom`, `lemma_normalized_implies_canonical_sign`).
- [x] Add explicit runtime normalization API and refinement regression wrapper (`RuntimeScalar::normalize`, `runtime_normalize_is_eqv_identity`).
- [x] Complete model-side constructive normalization algorithm/proof for arbitrary rationals (equivalent fully verified construction):
  - `Scalar::normalize_bounded`
  - `Scalar::normalize_constructive`
- [x] Add direct gcd-oriented normalization theorem surface:
  - `Scalar::gcd_one_spec`
  - `Scalar::lemma_normalized_implies_gcd_one`

## P3 Runtime/Refinement Expansion (Vec2, Point2, Orientation)
- [x] Add `RuntimeVec2` runtime type:
  - backing fields: runtime scalars for `x` and `y`
  - constructors mirroring `Vec2` model API
- [x] Add `RuntimeVec2` refinement layer (`runtime_vec2_refinement.rs`):
  - `View` mapping to model `Vec2`
  - contracts for `add`, `sub`, `neg`, `scale`, `dot`, `cross`, `norm2`
  - trusted boundary clearly isolated (same style as runtime scalar boundary)
- [x] Add runtime regression wrappers for `RuntimeVec2`:
  - add commutativity / associativity (model recovery)
  - `sub == add(neg)` composition
  - `dot` symmetry and `cross` antisymmetry recovery
- [x] Add `RuntimePoint2` runtime type:
  - backing fields: runtime scalars for `x` and `y`
  - constructors + affine ops (`add_vec`, `sub`)
- [x] Add `RuntimePoint2` refinement layer (`runtime_point2_refinement.rs`):
  - `View` mapping to model `Point2`
  - contracts for `add_vec`, `sub`, `dist2`
- [x] Add runtime regression wrappers for `RuntimePoint2`:
  - subtraction/addition cancellation recovery
  - translation invariance recovery
  - `dist2(p, q) == norm2(p - q)` recovery
- [x] Add runtime orientation API over runtime points:
  - `orient2d`
  - orientation classification enum compatible with model classification
- [x] Add runtime orientation refinement layer (`runtime_orientation_refinement.rs`):
  - contract linking runtime `orient2d` to model `orient2d_spec`
  - contract linking runtime classifier to model `orientation_spec`
- [x] Add runtime orientation regression wrappers:
  - swap/cyclic/permutation behavior recovery
  - translation invariance recovery
  - uniform-scale behavior recovery

## P4 Higher-Dimensional + Quaternion Expansion
- [x] Create dedicated TODO document for `Vec3/Point3`, `Vec4/Point4`, and `Quaternion`:
  - `docs/vcad-math-higher-dim-todo.md`
- [x] Execute `P4.1 Vec3` checklist from `docs/vcad-math-higher-dim-todo.md`.
  - progress: complete model theorem surface + expanded runtime regression wrappers (`dot/cross` bilinearity, scale extraction, norm laws).
- [x] Execute `P4.2 Point3 + orientation3d` checklist from `docs/vcad-math-higher-dim-todo.md`.
  - progress: `Point3` affine/metric theorem surface is complete (including `dist2` nonnegative/self-zero/zero-iff); `orientation3d` theorem surface is complete for current scope (swap-sign behavior, repeated-point degeneracy, and sign-aware zero/nonzero uniform scaling).
- [x] Execute `P4.3 Vec4/Point4` checklist from `docs/vcad-math-higher-dim-todo.md`.
  - progress: complete for current scope (Vec4 vector-space/dot/norm theorem surface + Point4 affine/metric theorem surface, with matching runtime regression wrappers).
- [ ] Execute `P4.4 Quaternion` checklist from `docs/vcad-math-higher-dim-todo.md`.
  - progress: model API now includes partial `inverse_spec`; ring-law coverage now includes additive/multiplicative identities, left/right distributivity, non-commutativity witness, explicit basis-product table lemmas (`i^2=j^2=k^2=-1` plus cyclic/anti-cyclic products), associativity linear-closure lemmas (`assoc_instance_spec` with add/scale closure across left/middle/right operands), and full multiplication associativity (`lemma_mul_associative`). The associativity proof now uses basis-sign helper infrastructure (`basis_spec`, `signed_basis_spec`, basis sign/index table specs, signed-basis multiply helper lemmas, quaternion scale-one/scale-associative), finite-case basis coverage (`lemma_basis_assoc_indices` + 64 concrete cases), and decomposition/congruence transport (`basis_decompose_spec`, `lemma_basis_decompose_eqv`, `lemma_assoc_eqv_*`). Conjugate linearity/congruence helpers, real-scalar multiplication bridges (`q*real(s)`/`real(s)*q`), and a quaternion norm scale law (`lemma_norm2_scale`) are now in place; norm multiplicativity remains pending.
- [ ] Execute `P4.5 Runtime + refinement rollout` checklist from `docs/vcad-math-higher-dim-todo.md`.
  - progress: all planned runtime families and refinement modules now exist; wrapper theorem coverage has been expanded through quaternion add-associativity/add-zero, multiplication associativity, inverse-identity, distributivity recovery, and quaternion `norm2` scale behavior recovery, but broader regression-law coverage is still pending.
- [ ] Execute `P4.6 Anti-cheating + quality gates` checklist from `docs/vcad-math-higher-dim-todo.md`.
