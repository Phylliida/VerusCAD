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
- [ ] Prove orientation3d law surface:
  - class exclusivity/exhaustiveness
  - permutation/sign behavior
  - translation invariance
  - uniform-scale behavior
  - degeneracy lemmas for repeated/coplanar points
  - progress: class exclusivity/exhaustiveness, translation invariance, swap-sign behavior (`c`/`d`), repeated-point degeneracy, and zero-scale coplanarity are implemented; full uniform-scale (nonzero) theorem surface is still pending.

## P4.3 Vec4 / Point4 (model + proofs)
- [x] Add `src/vec4.rs` model API:
  - `from_ints_spec`, `zero_spec`, `eqv_spec`
  - `add_spec`, `neg_spec`, `sub_spec`, `scale_spec`
  - `dot_spec`, `norm2_spec`
- [ ] Prove vector-space + dot/norm law surface for `Vec4`:
  - same additive/scale law family as `Vec2/Vec3`
  - dot symmetry + bilinearity
  - norm nonnegative/zero-iff-zero/scale
  - progress: `add` commutativity/associativity, `dot` symmetry, and `norm2_eqv_congruence` are implemented; the remaining law surface is pending.
- [x] Add `src/point4.rs` model API:
  - `from_ints_spec`, `eqv_spec`
  - `add_vec_spec`, `sub_spec`, `dist2_spec`
- [ ] Prove affine/metric laws for `Point4`:
  - cancellation/translation laws
  - distance law family (`dist2` properties + `dist2 == norm2(p-q)`)
  - progress: `dist2 == norm2(p-q)` bridge is implemented; remaining affine/metric laws are pending.

## P4.4 Quaternion (model + proofs)
- [ ] Add `src/quaternion.rs` model API:
  - constructor(s), `zero_spec`, `one_spec`, `eqv_spec`
  - `add_spec`, `neg_spec`, `sub_spec`, `mul_spec`
  - `conjugate_spec`, `norm2_spec`, `inverse_spec` (partial with nonzero precondition)
  - progress: all listed APIs except `inverse_spec` are implemented.
- [ ] Prove quaternion ring-like laws:
  - add commutativity/associativity
  - additive identity/inverse
  - multiplication associativity
  - multiplicative identity
  - left/right distributivity
  - explicit non-commutativity witness lemma for multiplication
  - progress: add commutativity/associativity + additive inverse are implemented.
- [ ] Prove conjugation/norm/inverse laws:
  - conjugate involution
  - `q * conjugate(q)` and `conjugate(q) * q` are real-valued and equal to `norm2(q)`
  - `norm2(q) >= 0`, `norm2(q) == 0 <==> q == 0`
  - `norm2(q1*q2) == norm2(q1) * norm2(q2)`
  - inverse correctness for nonzero `q` (`q * inv(q) == 1`, `inv(q) * q == 1`)
  - progress: conjugate involution is implemented.
- [ ] Add rotation-facing API (if using quaternions for 3D rotations):
  - `rotate_vec3_spec(v, q)` with unit-quaternion precondition
  - proof that rotation preserves vector norm
  - proof that composition matches quaternion multiplication order

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
  - progress: initial regression wrappers are implemented for all newly added runtime families; orientation3 wrappers now include swap, zero-scale coplanarity, and repeated-point degeneracy, but full theorem coverage still needs expansion.

## P4.6 Anti-cheating + quality gates
- [ ] Anti-cheating pass on all new lemmas:
  - strengthen weak implication contracts into strongest `requires`-style forms where applicable
  - avoid representation leaks in public law contracts
  - ensure contracts target abstract semantic equality where canonical representation is not guaranteed
- [ ] Keep theorem naming consistent with existing `vcad-math` style (`lemma_*` law surface).
- [ ] Ensure `./scripts/verify-vcad-math.sh` remains green after each sub-phase.
