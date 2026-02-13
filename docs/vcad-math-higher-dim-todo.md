# vcad-math Higher-Dimensional TODO
Planned proof/runtime backlog for:
1. `Vec3` / `Point3`
2. `Vec4` / `Point4`
3. `Quaternion`

This backlog follows the same pattern used for 2D:
1. clean spec/model API,
2. executable runtime API,
3. refinement contracts (`view` + `ensures`),
4. regression wrappers that recover model laws from runtime composition.

## P4.1 Vec3 (model + proofs)
- [x] Add `src/vec3.rs` model API:
  - `from_ints_spec`, `zero_spec`, `eqv_spec`
  - `add_spec`, `neg_spec`, `sub_spec`, `scale_spec`
  - `dot_spec`, `cross_spec`, `norm2_spec`
- [x] Prove vector-space laws for `Vec3`:
  - add commutativity/associativity
  - zero identity + additive inverse
  - `sub == add(neg)`
  - scale identity/zero/associativity/distributivity
  - negation involution + neg/scale interaction
  - progress: complete (including neg-scale interaction lemmas).
- [x] Prove 3D dot/cross law surface:
  - dot symmetry + bilinearity
  - cross antisymmetry + bilinearity
  - cross self-zero
  - scale extraction for dot/cross
  - progress: complete (`dot`/`cross` bilinearity + left/right scale extraction are implemented).
- [x] Prove norm laws for `Vec3`:
  - `norm2_nonnegative`
  - `norm2_zero_iff_zero`
  - `norm2_scale`
  - progress: complete (`norm2_nonnegative`, `norm2_zero_iff_zero`, `norm2_scale`, `norm2_neg_invariant`).

## P4.2 Point3 + orientation3d (model + proofs)
- [x] Add `src/point3.rs` model API:
  - `from_ints_spec`, `eqv_spec`
  - `add_vec_spec`, `sub_spec`, `dist2_spec`
- [x] Prove affine/metric laws for `Point3`:
  - point add/sub cancellation
  - translation associativity/identity
  - `dist2` symmetry/nonnegative/self-zero/zero-iff-equality
  - `dist2 == norm2(p - q)` bridge
  - translation invariance of subtraction and distance
  - progress: complete (including `dist2` nonnegative/self-zero/zero-iff-equality).
- [x] Add `src/orientation3.rs` model API:
  - signed volume / scalar triple product predicate for tetrahedron orientation
  - classification (`Positive | Negative | Coplanar`) or equivalent sign-based predicates
- [x] Prove orientation3d law surface:
  - class exclusivity/exhaustiveness
  - permutation/sign behavior
  - translation invariance
  - uniform-scale behavior
  - degeneracy lemmas for repeated/coplanar points
  - progress: complete for this surface (class exclusivity/exhaustiveness, translation invariance, swap-sign behavior (`c`/`d`), repeated-point degeneracy, and sign-aware uniform scaling for both zero and nonzero factors).

## P4.3 Vec4 / Point4 (model + proofs)
- [x] Add `src/vec4.rs` model API:
  - `from_ints_spec`, `zero_spec`, `eqv_spec`
  - `add_spec`, `neg_spec`, `sub_spec`, `scale_spec`
  - `dot_spec`, `norm2_spec`
- [x] Prove vector-space + dot/norm law surface for `Vec4`:
  - same additive/scale law family as `Vec2/Vec3`
  - dot symmetry + bilinearity
  - norm nonnegative/zero-iff-zero/scale
  - progress: complete for this surface (additive/scale law family, dot bilinearity/scale extraction/congruence, and norm nonnegative/zero-iff-zero/scale/neg-invariance).
- [x] Add `src/point4.rs` model API:
  - `from_ints_spec`, `eqv_spec`
  - `add_vec_spec`, `sub_spec`, `dist2_spec`
- [x] Prove affine/metric laws for `Point4`:
  - cancellation/translation laws
  - distance law family (`dist2` properties + `dist2 == norm2(p-q)`)
  - progress: complete for this surface (cancellation/translation + distance symmetry/nonnegative/self-zero/zero-iff-equality and `dist2 == norm2(p-q)` bridge).

## P4.4 Quaternion (model + proofs)
- [x] Add `src/quaternion.rs` model API:
  - constructor(s), `zero_spec`, `one_spec`, `eqv_spec`
  - `add_spec`, `neg_spec`, `sub_spec`, `mul_spec`
  - `conjugate_spec`, `norm2_spec`, `inverse_spec` (partial with nonzero precondition)
  - progress: complete for this API surface (including partial `inverse_spec` with positivity precondition on `norm2`).
- [x] Prove quaternion ring-like laws:
  - add commutativity/associativity
  - additive identity/inverse
  - multiplication associativity
  - multiplicative identity
  - left/right distributivity
  - explicit non-commutativity witness lemma for multiplication
  - progress: add commutativity/associativity, additive identity/inverse, multiplicative identity, left/right distributivity, and a non-commutativity witness are implemented; multiplication associativity is now implemented (`lemma_mul_associative`). This was completed by adding basis-sign helper infrastructure (`basis_spec`, `signed_basis_spec`, table sign/index specs, signed-basis multiply helpers, quaternion scale-one/scale-associative), proving basis-associativity for all basis triples via finite-case coverage (`lemma_basis_assoc_indices` + 64 concrete cases), and then lifting through decomposition (`basis_decompose_spec` / `lemma_basis_decompose_eqv`) and congruence transport lemmas.
- [x] Prove conjugation/norm/inverse laws:
  - conjugate involution
  - `q * conjugate(q)` and `conjugate(q) * q` are real-valued and equal to `norm2(q)`
  - `norm2(q) >= 0`, `norm2(q) == 0 <==> q == 0`
  - `norm2(q1*q2) == norm2(q1) * norm2(q2)`
  - inverse correctness for nonzero `q` (`q * inv(q) == 1`, `inv(q) * q == 1`)
  - progress: conjugate involution, conjugate-product characterization (`q*conj(q)` and `conj(q)*q` real-valued and equal to `norm2(q)` up to semantic equality), norm conjugate-invariance, norm nonnegative, norm zero-iff-zero, norm scale law (`norm2(q*k) = (k*k)*norm2(q)` up to semantic equality), norm multiplicativity (`norm2(q1*q2) = norm2(q1)*norm2(q2)` up to semantic equality), and inverse correctness (`q*inv(q)` and `inv(q)*q`) are implemented. Supporting helper lemmas for conjugate linearity/congruence, conjugate anti-homomorphism (`conj(a*b) = conj(b)*conj(a)` up to semantic equality), and real-scalar multiplication (`q*real(s)` / `real(s)*q`) are also in place.
- [x] Add rotation-facing API (if using quaternions for 3D rotations):
  - `rotate_vec3_spec(v, q)` with unit-quaternion precondition
  - proof that rotation preserves vector norm
  - proof that composition matches quaternion multiplication order
  - progress: rotation-facing spec/model layer is implemented via `unit_spec`, `pure_vec3_spec`, `vector_part_spec`, `rotate_quat_spec`, and `rotate_vec3_spec`, with model proofs `lemma_rotate_vec3_norm_preserves` and `lemma_rotate_vec3_composition`.

## P4.5 Runtime + refinement rollout
- [x] Add runtime types:
  - `RuntimeVec3`, `RuntimePoint3`, `RuntimeOrientation3`
  - `RuntimeVec4`, `RuntimePoint4`
  - `RuntimeQuaternion`
- [x] Add refinement modules:
  - `runtime_vec3_refinement.rs`, `runtime_point3_refinement.rs`, `runtime_orientation3_refinement.rs`
  - `runtime_vec4_refinement.rs`, `runtime_point4_refinement.rs`
  - `runtime_quaternion_refinement.rs`
- [x] Add `View` mappings and contracts (`assume_specification` initially at backend boundary) for all runtime APIs.
- [ ] Add regression wrappers proving runtime composition recovers key model laws for each new type.
  - progress: initial regression wrappers are implemented for all newly added runtime families; `RuntimeVec4/RuntimePoint4` now include cancellation/linearity/metric wrappers, `orientation3` wrappers include swap/zero-nonzero scale/repeated-point behavior, and `RuntimeQuaternion` wrappers now include add commutativity/associativity, add-zero identity, sub-via-add-neg, additive inverse, multiplicative identity, multiplication associativity, left/right distributivity, non-commutativity witness, norm laws (including `norm2` scale and multiplicativity behavior), rotation wrappers (`rotate_vec3` norm preservation and composition), conjugate anti-homomorphism recovery, real-scalar multiplication recovery (`q*real(s)` and `real(s)*q` vs `scale`), conjugate-product recovery, and inverse-identity recovery via runtime `inverse()`.

## P4.6 Anti-cheating + quality gates
- [ ] Anti-cheating pass on all new lemmas:
  - strengthen weak implication contracts into strongest `requires`-style forms where applicable
  - avoid representation leaks in public law contracts
  - ensure contracts target abstract semantic equality where canonical representation is not guaranteed
  - progress: quaternion inverse-related contracts were tightened to semantic nonzero form (`!norm2.eqv_spec(0)`) instead of representation-level `.num` checks, and the prior weak implication norm-positivity lemma was strengthened to a requires-style semantic statement (`0 < norm2` under nonzero norm). Runtime refinement contracts were also hardened to semantic zero/nonzero checks for scalar reciprocal and orientation scale wrappers (2D/3D), with local proof bridges to legacy `.num`-based model lemmas. Model orientation scale law contracts (`orientation` and `orientation3`, weak + strong forms) now also use semantic zero/nonzero preconditions/antecedents instead of direct `k.num` exposure.
- [ ] P4.6 backlog: shrink trusted runtime boundary surface.
  - inventory remaining `assume_specification[...]` usage by module and prioritize high-risk arithmetic/orientation/quaternion boundaries first.
  - replace selected trusted contracts with proved refinement wrappers where practical, and keep explicit rationale for remaining trusted assumptions.
- [ ] P4.6 backlog: convert remaining implication-style public lemma contracts to strong `requires` forms (or thin wrapper + strong core pattern).
  - progress: initial scalar targets are completed (`lemma_le_add_monotone`, `lemma_le_mul_monotone_nonnegative`, `lemma_add_right_cancel`, `lemma_add_left_cancel` now use strong `requires` contracts). Orientation wrapper lemmas were also hardened (`lemma_orient2d_collinear`, `lemma_orientation_spec_scale_nonzero_preserves`, `lemma_orientation_spec_scale_zero_collinear`, `lemma_orientation3_spec_scale_nonzero_behavior`, `lemma_orientation3_spec_scale_zero_coplanar` now use strong preconditions instead of outer implication antecedents).
- [ ] P4.6 backlog: eliminate remaining representation leaks from public law contracts.
  - constrain `.num`/`.den` reasoning to proof-local bridges only.
  - progress: orientation 2D class/swap law contracts were hardened to semantic signum forms (no `.num` exposure), and representation-oriented bridge lemmas in `Scalar`/`Vec2`/`Point2`/`Point3`/`Point4` (notably `*_num`/denominator/signum-iff bridge helpers) are now crate-internal (`pub(crate)`), reducing public API leakage while preserving proof-local usage.
- [ ] P4.6 backlog: remove contradiction-endings where a direct semantic conclusion is available.
  - progress: initial target in the non-commutativity witness proof path (`src/quaternion.rs`) is completed; continue scanning for remaining contradiction-endings that can be replaced by direct semantic negation arguments.
- [ ] Keep theorem naming consistent with existing `vcad-math` style (`lemma_*` law surface).
- [ ] Ensure `./scripts/verify-vcad-math.sh` remains green after each sub-phase.

## Requested Checklist Alignment (2026-02-13)
Status check against requested geometry primitives/helper-expression milestones.

- [x] `Point2`, `Point3`, `Vec2`, `Vec3` are defined over rational `Scalar`, with points/vectors as distinct types.
- [x] Vector ops (`add/sub/scale`) and core linearity-family proofs are present for `Vec2` and `Vec3`.
- [x] Dot-product bilinearity + commutativity are present (`Vec2`/`Vec3`).
- [x] 3D cross anti-commutativity is present (`Vec3::lemma_cross_antisymmetric`).
- [x] Add explicit 3D cross-orthogonality law(s), e.g. `a.dot(a.cross(b)) == 0` (semantic-equality form).
  - implemented: `Vec3::lemma_dot_cross_left_orthogonal(a, b)` (`a.dot_spec(a.cross_spec(b)).eqv_spec(0)`).
- [x] Add explicit 2D signed-area polynomial helper spec
  - target form: `(bx-ax)(cy-ay) - (by-ay)(cx-ax)`
  - plus bridge lemma showing equivalence with `orient2d_spec`.
- [x] Add explicit 3D signed-volume polynomial helper spec (fully expanded 3x3 determinant over edge vectors)
  - no matrix type, direct polynomial expression
  - plus bridge lemma showing equivalence with `orient3d_spec`.
- [x] 2D antisymmetry under swaps is covered at orient-level (full permutation/sign table).
- [x] Extend 3D antisymmetry from current `c<->d` swap to any transposition (or provide full permutation/sign table).
  - implemented: orient-level transposition antisymmetry is now covered for all six swaps (`ab/ac/ad/bc/bd/cd`) via `lemma_orient3d_swap_*_eqv_neg`, and the explicit signed-volume helper has matching coverage via `lemma_signed_volume3_poly_swap_*_eqv_neg`.
- [x] Introduce explicit linear-dependence predicates for edge vectors and prove:
  - signed-area `== 0` iff edge vectors are linearly dependent (collinear characterization)
  - signed-volume `== 0` iff edge vectors are linearly dependent (coplanar characterization)
  - implemented: `vec2_linear_dependent_spec` / `edge_vectors2_linear_dependent_spec` + `lemma_signed_area2_zero_iff_edge_vectors_linear_dependent` and `lemma_is_collinear_iff_edge_vectors_linear_dependent`; `vec3_linear_dependent_spec` / `edge_vectors3_linear_dependent_spec` + `lemma_signed_volume3_zero_iff_edge_vectors_linear_dependent` and `lemma_is_coplanar_iff_edge_vectors_linear_dependent`.
