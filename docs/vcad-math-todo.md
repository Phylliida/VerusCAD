# vcad-math Proof TODO
Focused list of proof work still needed in `vcad-math`.

This list assumes the current baseline (orientation classification, scale, norm2, dist2, signum) is already verified.

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
