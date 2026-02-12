# vcad-math Roadmap
Long-horizon milestones for `vcad-math` beyond the current proof-lemma TODO.

## P2: Rational scalar hardening
- [x] Replace integer-backed `Scalar` with rational representation and keep theorem surface green.
- [x] Reprove `Vec2/Point2/orientation` law surface on rational semantics (`eqv_spec`).
- [x] Add canonical normalization model and proofs:
  - [x] model-level normalization predicate (`Scalar::normalized_spec`) as minimal denominator in each semantic-equivalence class.
  - [x] seed existence theorem (`Scalar::lemma_from_int_is_normalized`).
  - [x] constructive normalization algorithm/proof for arbitrary rationals:
    - `Scalar::normalize_bounded`
    - `Scalar::normalize_constructive`
  - [x] canonical sign placement theorem surface:
    - `Scalar::canonical_sign_spec`
    - `Scalar::lemma_normalized_zero_has_unit_denom`
    - `Scalar::lemma_normalized_implies_canonical_sign`
- [x] Prove normalization uniqueness (for the model-level normalization predicate):
  - `Scalar::lemma_normalized_eqv_implies_equal_denom`.
- [x] Add normalized-structural bridge theorem(s):
  - `Scalar::lemma_normalized_eqv_implies_equal`.
- [x] Add a direct gcd-oriented normalization proof strategy:
  - `Scalar::gcd_one_spec`
  - `Scalar::lemma_normalized_implies_gcd_one`

## P2: API mode hardening
- [x] Establish scalar unification execution plan (`docs/scalar-unification-todo.md`) and explicit proof-model naming (`ScalarModel` alias).
- [x] Replace interim runtime helpers with `RuntimeScalar` backed by `rug::Rational`.
- [x] Introduce paired `exec` operations with `ensures` to existing spec/proof operations.
  - covered in `src/runtime_scalar_refinement.rs` for `from_int/from_fraction/add/sub/mul/neg/normalize`.
- [x] Keep current proof lemmas as theorems over spec model; add thin exec correctness wrappers.
  - runtime wrappers currently rely on trusted `assume_specification` at the `rug` boundary.
- [x] Add a small set of regression proofs/tests to catch accidental weakening of guarantees.
  - added verified regression wrappers in `src/runtime_scalar_refinement.rs`:
    - `runtime_add_pair_commutative`
    - `runtime_mul_pair_commutative`
    - `runtime_sub_matches_add_neg`
    - `runtime_normalize_is_eqv_identity`

## P3: Runtime geometry rollout
- [x] Add executable `Vec2` backend (`RuntimeVec2`) based on `RuntimeScalar`.
- [x] Add refinement/view contracts for `RuntimeVec2`:
  - constructor(s), `add`, `sub`, `neg`, `scale`
  - `dot`, `cross`, `norm2`
  - model mapping to `Vec2` via `view`
- [x] Add executable `Point2` backend (`RuntimePoint2`) based on `RuntimeScalar`.
- [x] Add refinement/view contracts for `RuntimePoint2`:
  - constructor(s), `add_vec`, `sub`
  - `dist2`
  - model mapping to `Point2` via `view`
- [x] Add executable orientation entrypoints over runtime points:
  - `orient2d`
  - `orientation` classification (`Ccw/Cw/Collinear`)
- [x] Add runtime-orientation refinement contracts linking to:
  - `orient2d_spec`
  - `orientation_spec`
- [x] Add regression wrappers proving runtime composition recovers key model laws:
  - orientation swap/cyclic behavior
  - translation invariance
  - scale behavior (nonzero and zero-scale cases)

## P4: Higher-dimensional math + rotations
- [x] Create dedicated planning checklist for higher-dimensional expansion:
  - `docs/vcad-math-higher-dim-todo.md`
- [ ] Implement `Vec3` / `Point3` theorem surface and runtime/refinement pairing.
- [ ] Implement `orientation3d` theorem surface (signed-volume/coplanarity classification + invariance laws).
- [ ] Implement `Vec4` / `Point4` theorem surface and runtime/refinement pairing.
- [ ] Implement quaternion theorem surface:
  - algebra laws,
  - conjugate/norm/inverse laws,
  - rotation-facing law surface for 3D vectors.
- [ ] Add runtime regression wrappers for all new 3D/4D/quaternion APIs.
- [ ] Run anti-cheating pass and contract-strengthening pass across all new proof modules.
