# vcad-math Roadmap
Long-horizon milestones for `vcad-math` beyond the current proof-lemma TODO.

## P2: Rational scalar migration
- [ ] Replace integer-backed `Scalar` with normalized rational representation.
- [ ] Prove representation invariants:
  - denominator positivity,
  - gcd normalization,
  - canonical sign placement.
- [ ] Prove normalization uniqueness:
  - equal rationals normalize to identical representation.
- [ ] Reprove all arithmetic closure and lemma compatibility over rationals.
- [ ] Preserve `Vec2/Point2/orientation` API contracts across migration.

## P2: API mode hardening
- [ ] Introduce paired `exec` operations with `ensures` to existing spec/proof operations.
- [ ] Keep current proof lemmas as theorems over spec model; add thin exec correctness wrappers.
- [ ] Add a small set of regression proofs/tests to catch accidental weakening of guarantees.
