# vcad-math Verification TODO
Goal: remove trusted runtime proof boundaries so `vcad-math` runtime behavior is justified by explicit specs + proofs.

## Baseline Snapshot (2026-02-13)
- [x] Full crate verifies: `./scripts/verify-vcad-math.sh`.
- [x] No runtime assumptions remain (`assume_specification[...]`).
- [x] Trust surface reduced to zero runtime assumptions in `crates/vcad-math/src`.
- [x] Current assumption count: `0`.
- [ ] Residual trusted `external_body` bridges are eliminated.

## Assumption Inventory (Current)
- [x] `src/runtime_scalar_refinement.rs` (`0`)
- [x] `src/runtime_vec2_refinement.rs` (`0`)
- [x] `src/runtime_point2_refinement.rs` (`0`)
- [x] `src/runtime_orientation_refinement.rs` (`0`)
- [x] `src/runtime_vec3_refinement.rs` (`0`)
- [x] `src/runtime_point3_refinement.rs` (`0`)
- [x] `src/runtime_orientation3_refinement.rs` (`0`)
- [x] `src/runtime_vec4_refinement.rs` (`0`)
- [x] `src/runtime_point4_refinement.rs` (`0`)
- [x] `src/runtime_quaternion_refinement.rs` (`0`)

## Recommended Work Order
- [x] 1) Orientation wrappers (2D/3D): low count, good pattern warm-up.
- [x] 2) Vec/Point 2D runtime boundary.
- [x] 3) Vec/Point 3D runtime boundary.
- [x] 4) Vec/Point 4D runtime boundary.
- [x] 5) Quaternion runtime boundary.
- [x] 6) Scalar runtime boundary (likely hardest due backend/runtime representation).
- [ ] 7) Final de-trusting + verification gate (remove remaining `external_body` items).

## A. runtime_orientation_refinement.rs (0)
- [x] `runtime_orientation::orient2d`
- [x] `runtime_orientation::scale_point_from_origin`
- [x] `runtime_orientation::orientation`

## B. runtime_orientation3_refinement.rs (0)
- [x] `runtime_orientation3::orient3d`
- [x] `runtime_orientation3::scale_point_from_origin3`
- [x] `runtime_orientation3::orientation3`

## C. runtime_vec2_refinement.rs (0)
- [x] `RuntimeVec2::new`
- [x] `RuntimeVec2::from_ints`
- [x] `RuntimeVec2::zero`
- [x] `RuntimeVec2::add`
- [x] `RuntimeVec2::sub`
- [x] `RuntimeVec2::neg`
- [x] `RuntimeVec2::scale`
- [x] `RuntimeVec2::dot`
- [x] `RuntimeVec2::cross`
- [x] `RuntimeVec2::norm2`

## D. runtime_point2_refinement.rs (0)
- [x] `RuntimePoint2::new`
- [x] `RuntimePoint2::from_ints`
- [x] `RuntimePoint2::add_vec`
- [x] `RuntimePoint2::sub`
- [x] `RuntimePoint2::dist2`

## E. runtime_vec3_refinement.rs (0)
- [x] `RuntimeVec3::new`
- [x] `RuntimeVec3::from_ints`
- [x] `RuntimeVec3::zero`
- [x] `RuntimeVec3::add`
- [x] `RuntimeVec3::sub`
- [x] `RuntimeVec3::neg`
- [x] `RuntimeVec3::scale`
- [x] `RuntimeVec3::dot`
- [x] `RuntimeVec3::cross`
- [x] `RuntimeVec3::norm2`

## F. runtime_point3_refinement.rs (0)
- [x] `RuntimePoint3::new`
- [x] `RuntimePoint3::from_ints`
- [x] `RuntimePoint3::add_vec`
- [x] `RuntimePoint3::sub`
- [x] `RuntimePoint3::dist2`

## G. runtime_vec4_refinement.rs (0)
- [x] `RuntimeVec4::new`
- [x] `RuntimeVec4::from_ints`
- [x] `RuntimeVec4::zero`
- [x] `RuntimeVec4::add`
- [x] `RuntimeVec4::sub`
- [x] `RuntimeVec4::neg`
- [x] `RuntimeVec4::scale`
- [x] `RuntimeVec4::dot`
- [x] `RuntimeVec4::norm2`

## H. runtime_point4_refinement.rs (0)
- [x] `RuntimePoint4::new`
- [x] `RuntimePoint4::from_ints`
- [x] `RuntimePoint4::add_vec`
- [x] `RuntimePoint4::sub`
- [x] `RuntimePoint4::dist2`

## I. runtime_quaternion_refinement.rs (0)
- [x] `RuntimeQuaternion::new`
- [x] `RuntimeQuaternion::from_ints`
- [x] `RuntimeQuaternion::zero`
- [x] `RuntimeQuaternion::one`
- [x] `RuntimeQuaternion::add`
- [x] `RuntimeQuaternion::sub`
- [x] `RuntimeQuaternion::neg`
- [x] `RuntimeQuaternion::scale`
- [x] `RuntimeQuaternion::mul`
- [x] `RuntimeQuaternion::conjugate`
- [x] `RuntimeQuaternion::norm2`
- [x] `RuntimeQuaternion::inverse`
- [x] `RuntimeQuaternion::rotate_vec3`

## J. runtime_scalar_refinement.rs (0 assumptions)
- [x] `RuntimeScalar::from_int`
- [x] `RuntimeScalar::from_fraction` (minimal ghost contract)
- [x] `RuntimeScalar::add`
- [x] `RuntimeScalar::sub`
- [x] `RuntimeScalar::mul`
- [ ] `RuntimeScalar::recip` (still `external_body`)
- [x] `RuntimeScalar::neg`
- [x] `RuntimeScalar::normalize`
- [ ] `RuntimeScalar::signum_i8` (still `external_body`)

## Residual Trusted Items
- [ ] `src/runtime_scalar.rs`: `RuntimeScalar::recip` (`#[verifier::external_body]`)
- [ ] `src/runtime_scalar.rs`: `RuntimeScalar::signum_i8` (`#[verifier::external_body]`)
- [ ] `src/runtime_scalar_refinement.rs`: `ExRugInteger` (`#[verifier::external_body]`)

## Completion Gates
- [x] `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.
- [x] `./scripts/verify-vcad-math.sh` succeeds after each milestone.
- [x] Proof quality pass: no unnecessary trigger warnings in newly touched modules.
