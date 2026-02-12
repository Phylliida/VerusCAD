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

## Status
All currently scoped proof lemmas in this TODO are complete.

Long-horizon architecture milestones (rational migration, exec/spec dual-mode APIs, proof regression harness) now live in `docs/vcad-math-roadmap.md`.
