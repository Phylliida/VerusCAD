# vcad-math
Lowest-level verified math crate for VerusCAD.

`vcad-math` contains the exact arithmetic model, geometric model layers, quaternion algebra/rotation model, executable runtime counterparts, and refinement contracts that connect runtime behavior to model specs.

This crate intentionally has no dependency on higher CAD/topology concepts.

## Public Module Surface
Exported through `src/lib.rs`.

Model/proof modules:
1. `scalar` (`Scalar`, `ScalarModel`)
2. `vec2`, `point2`, `orientation`
3. `vec3`, `point3`, `orientation3`
4. `vec4`, `point4`
5. `quaternion`

Runtime executable modules:
1. `runtime_scalar`
2. `runtime_vec2`, `runtime_point2`, `runtime_orientation`
3. `runtime_vec3`, `runtime_point3`, `runtime_orientation3`
4. `runtime_vec4`, `runtime_point4`
5. `runtime_quaternion`

Internal-only support modules:
1. `runtime_*_refinement` files (proof contracts + regression wrappers)
2. `quaternion_assoc_cases` (finite-case associativity support)

## Available Features
Feature groups implemented in the current tree.

1. Exact rational scalar model (`Scalar`)
   - Rational representation: `num: int`, `den: nat` with effective denominator `den + 1`
   - Arithmetic specs/exec: `add`, `sub`, `mul`, `neg`, comparisons/sign
   - Law surface: commutativity, associativity, identities, inverse/distributivity, cancellation, monotonicity
   - Semantic equality (`eqv_spec`) laws and congruence helpers
   - Signum law surface (`signum` cases, multiplication behavior, negation behavior)
   - Normalization/model canonicalization surface:
     - `normalized_spec`, canonical sign, normalized uniqueness/equality bridges
     - constructive normalization (`normalize_bounded`, `normalize_constructive`)
     - gcd-oriented bridge (`gcd_one_spec`, `lemma_normalized_implies_gcd_one`)

2. 2D geometry model (`Vec2`, `Point2`, `orientation`)
   - `Vec2`: add/sub/neg/scale, dot/cross, norm
   - Proven law families: vector-space laws, dot/cross bilinearity and symmetry/antisymmetry, norm laws
   - `Point2`: affine/metric laws (`add_vec/sub`, distance laws, translation invariance)
   - Orientation/classification:
     - `orient2d_spec`, `orientation_spec`, class exclusivity/exhaustiveness
     - explicit signed-area polynomial helper (`signed_area2_poly_spec`) with bridge to `orient2d_spec`
     - swap/cyclic/permutation behavior, translation invariance, zero/nonzero scale behavior, degeneracy lemmas
     - explicit edge-linear-dependence predicates:
       - `vec2_linear_dependent_spec`
       - `edge_vectors2_linear_dependent_spec`
       - zero-characterization lemmas (`signed-area == 0` iff edge vectors are dependent)

3. 3D geometry model (`Vec3`, `Point3`, `orientation3`)
   - `Vec3`: add/sub/neg/scale, dot/cross, norm
   - Proven law families: vector-space laws, dot/cross bilinearity/symmetry/antisymmetry, norm laws
   - Triple-product helpers: orthogonality/cyclic/swap lemmas for dot-cross expressions
   - `Point3`: affine/metric laws (`add_vec/sub`, distance laws, translation invariance)
   - Orientation3/classification:
     - `orient3d_spec`, `orientation3_spec`, class exclusivity/exhaustiveness
     - explicit signed-volume helpers:
       - `signed_volume3_det_expanded_spec`
       - `signed_volume3_poly_spec`
       - bridges to `orient3d_spec`
     - transposition/permutation sign behavior, including all transpositions (`ab/ac/ad/bc/bd/cd`)
     - translation invariance, zero/nonzero scale behavior, degeneracy lemmas
     - explicit edge-linear-dependence predicates:
       - `vec3_linear_dependent_spec`
       - `edge_vectors3_linear_dependent_spec`
       - zero-characterization lemmas (`signed-volume == 0` iff edge vectors are dependent)

4. 4D geometry model (`Vec4`, `Point4`)
   - `Vec4`: add/sub/neg/scale, dot, norm and theorem surface matching lower-dimensional style
   - `Point4`: affine/metric laws and `dist2 == norm2(p - q)` bridge

5. Quaternion model (`Quaternion`)
   - Core operations: add/sub/neg/scale/mul, conjugate, norm2, inverse (partial), rotation-facing APIs
   - Basis + finite-case infrastructure for multiplication associativity
   - Law families:
     - additive laws, multiplicative identity, distributivity, associativity
     - non-commutativity witness
     - conjugation laws (involution, reverse-over-mul)
     - norm laws (nonnegative, zero-iff-zero, scale behavior, multiplicativity)
     - inverse identities for nonzero quaternions
     - rotation-facing laws (`rotate_vec3_spec` norm preservation and composition)

6. Executable runtime APIs
   - `RuntimeScalar` on `rug::Rational`: arithmetic, reciprocal, normalize, signum
   - Runtime geometry families:
     - 2D: `RuntimeVec2`, `RuntimePoint2`, `RuntimeOrientation`
     - 3D: `RuntimeVec3`, `RuntimePoint3`, `RuntimeOrientation3`
     - 4D: `RuntimeVec4`, `RuntimePoint4`
     - quaternion: `RuntimeQuaternion` including `inverse` and `rotate_vec3`

7. Refinement contracts and runtime regression wrappers
   - `View` mappings from runtime types to model types
   - `assume_specification` contracts at external backend boundaries
   - Verified wrapper suites that recover model laws from runtime composition for:
     - scalar
     - vec2/point2/orientation2
     - vec3/point3/orientation3
     - vec4/point4
     - quaternion (algebra, conjugation, norm/inverse, rotation)

## Verification Workflow
Use a staged loop:
1. Fast focused verification:
   - `./scripts/verify-vcad-math-fast.sh`
   - `./scripts/verify-vcad-math-fast.sh orientation3`
   - `./scripts/verify-vcad-math-fast.sh quaternion`
2. Full crate gate:
   - `./scripts/verify-vcad-math.sh`

Latest full run in this workspace: `750 verified, 0 errors`.

## Related Docs
1. `crates/vcad-math/docs/verification-todo.md`
2. `docs/vcad-math-todo.md`
3. `docs/vcad-math-higher-dim-todo.md`
4. `docs/vcad-math-roadmap.md`
5. `docs/scalar-unification-todo.md`
