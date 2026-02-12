# vcad-math Proof TODO
Focused list of proof work still needed in `vcad-math`.

This list assumes the current baseline (orientation classification, scale, norm2, dist2, signum) is already verified.

## Agent Execution Loop (Requested 2026-02-12)
- [ ] Sync this TODO to reality before each implementation pass:
  - add any missing required work items discovered during code/proof audits.
  - do not mark items complete unless they are verified in current rational branch.
- [ ] Execute all unchecked TODO items in priority order within `vcad-math`.
- [ ] After finishing all TODO items, run an anti-cheating audit:
  - identify lemmas that prove weaker/irrelevant properties than their contracts suggest.
  - strengthen/fix contracts and proofs accordingly.
- [ ] Keep work strictly scoped to `vcad-math` until the list is exhausted.

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
- [ ] Reintroduce scalar cancellation/order lemmas under rational semantics:
  - [ ] Define/order-stabilize scalar comparison contract for rationals (`le_spec`/`lt_spec` or equivalent) so monotonicity lemmas have a canonical target.
  - `lemma_add_left_cancel` (+ strong variant, done)
  - `lemma_add_right_cancel` (+ strong variant, done)
  - `lemma_le_add_monotone` (+ strong variant)
  - `lemma_le_mul_monotone_nonnegative` (+ strong variant)
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
- [ ] Reintroduce dot/cross algebraic laws:
  - `lemma_dot_symmetric` (done)
  - `lemma_dot_linear_left` (done)
  - `lemma_dot_linear_right` (done)
  - `lemma_dot_scale_extract_left` (done)
  - `lemma_cross_linear_left`
  - `lemma_cross_linear_right`
  - `lemma_cross_scale_extract_left` (done)
  - `lemma_cross_scale_extract_right` (done)
  - `lemma_cross_self_zero` (non-signum form, done)
- [ ] Reintroduce norm laws:
  - `lemma_norm2_nonnegative`
  - `lemma_norm2_zero_iff_zero`
  - `lemma_norm2_scale`

### Point2
- [x] Reintroduce point/vector cancellation + action laws:
  - `lemma_add_vec_zero_identity` (done)
  - `lemma_add_vec_associative` (done)
  - `lemma_sub_then_add_cancel` (done)
  - `lemma_add_then_sub_cancel` (done)
  - `lemma_add_vec_unique` (done)
- [ ] Reintroduce distance laws:
  - `lemma_dist2_is_sub_norm2` (done)
  - `lemma_dist2_symmetric`
  - `lemma_dist2_nonnegative`
  - `lemma_dist2_self_zero` (done, semantic-equality form)
  - `lemma_dist2_zero_iff_equal_points`
  - `lemma_dist2_translation_invariant`
  - `lemma_sub_translation_invariant`
- [x] Reintroduce point equality bridge equivalent to prior `lemma_eq_from_component_ints` (done via `Point2::eqv_spec` + `lemma_eqv_from_components`).

### Orientation
- [ ] Reintroduce determinant/value lemmas missing after migration:
  - `lemma_orient2d_collinear` (done)
  - `lemma_orient2d_unit_ccw`
  - `lemma_orient2d_translation_invariant`
  - `lemma_orient2d_scale_from_origin`
- [ ] Reintroduce full orientation enum/class laws:
  - `lemma_orientation_spec_exclusive` (done)
  - `lemma_orientation_spec_translation_invariant`
  - `lemma_orientation_spec_scale_nonzero_preserves`
  - `lemma_orientation_spec_scale_nonzero_preserves_strong`
  - `lemma_orientation_spec_scale_zero_collinear`
  - `lemma_orientation_spec_scale_zero_collinear_strong`
- [x] Reintroduce canonical permutation lemmas by legacy names:
  - `lemma_orient2d_cyclic_invariant` (alias/wrapper over `lemma_orient2d_cyclic_eqv`)
  - `lemma_orient2d_permutation_table` (classical sign/same-or-neg form)

## 2026-02-12 Rational Migration Pause
- [x] Choose active baseline for next edits:
  - `crates/vcad-math/backups/2026-02-12-rational-migration-pause/pre-rational-head/src/` (full integer-proof baseline),
  - or `crates/vcad-math/backups/2026-02-12-rational-migration-pause/current-in-progress/src/` (partial rational rewrite, selected).
- [ ] Keep both snapshots immutable; only copy out of backup directories when restoring files.
- [x] Bring the active rational branch back to green verification (`./scripts/verify-vcad-math.sh`).
- [ ] Reintroduce the full theorem surface on top of the rational branch.
- [ ] Rebuild `Scalar` law surface for rational arithmetic with explicit semantic-equality contracts (`as_real`/`eqv_spec`) where structural equality is no longer canonical.
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
  - [ ] Reintroduce strong arithmetic semantic lemmas (add/mul/sub over semantic equality, cancellation/order laws).
- [ ] Re-add vector/point/orientation theorem layers that were temporarily dropped during migration:
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
- [ ] Decide normalization strategy for rational representation:
  - temporary non-normalized representation + semantic equality,
  - then canonical normalization proofs (gcd/sign placement/uniqueness).
- [ ] Update crate docs to state exact migration status and which theorem set is currently guaranteed.

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
Core first-wave proof lemmas, contract-strengthening pass, and major-hole follow-up are complete.

Long-horizon architecture milestones (rational migration, exec/spec dual-mode APIs, proof regression harness) now live in `docs/vcad-math-roadmap.md`.
