# vcad-math Roadmap
Long-horizon milestones for `vcad-math` beyond the current proof-lemma TODO.

## P2: Rational scalar hardening
- [x] Replace integer-backed `Scalar` with rational representation and keep theorem surface green.
- [x] Reprove `Vec2/Point2/orientation` law surface on rational semantics (`eqv_spec`).
- [ ] Add canonical normalization model and proofs:
  - denominator positivity as a maintained invariant (beyond constructor facts),
  - gcd normalization,
  - canonical sign placement.
- [ ] Prove normalization uniqueness:
  - equal rationals normalize to identical representation.
- [ ] Add normalized-structural bridge theorem(s):
  - in normalized form, semantic equality implies structural equality.

## P2: API mode hardening
- [ ] Introduce paired `exec` operations with `ensures` to existing spec/proof operations.
- [ ] Keep current proof lemmas as theorems over spec model; add thin exec correctness wrappers.
- [ ] Add a small set of regression proofs/tests to catch accidental weakening of guarantees.
