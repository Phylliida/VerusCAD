# vcad-math Verification TODO
Goal: remove trusted runtime proof boundaries so `vcad-math` runtime behavior is justified by explicit specs + proofs.

## Baseline Snapshot (2026-02-13)
- [x] Full crate verifies: `./scripts/verify-vcad-math.sh`.
- [ ] Trusted runtime assumptions remain (`assume_specification[...]`).
- [ ] Trust surface reduced to zero runtime assumptions in `crates/vcad-math/src`.
- [x] Current assumption count: `70`.

## Assumption Inventory (Current)
- [ ] `src/runtime_scalar_refinement.rs` (`9`)
- [ ] `src/runtime_vec2_refinement.rs` (`10`)
- [ ] `src/runtime_point2_refinement.rs` (`5`)
- [ ] `src/runtime_orientation_refinement.rs` (`2`)
- [ ] `src/runtime_vec3_refinement.rs` (`10`)
- [ ] `src/runtime_point3_refinement.rs` (`5`)
- [ ] `src/runtime_orientation3_refinement.rs` (`2`)
- [ ] `src/runtime_vec4_refinement.rs` (`9`)
- [ ] `src/runtime_point4_refinement.rs` (`5`)
- [ ] `src/runtime_quaternion_refinement.rs` (`13`)

## Recommended Work Order
- [ ] 1) Orientation wrappers (2D/3D): low count, good pattern warm-up.
- [ ] 2) Vec/Point 2D runtime boundary.
- [ ] 3) Vec/Point 3D runtime boundary.
- [ ] 4) Vec/Point 4D runtime boundary.
- [ ] 5) Quaternion runtime boundary.
- [ ] 6) Scalar runtime boundary (likely hardest due backend/runtime representation).
- [ ] 7) Final de-trusting + verification gate.

## A. runtime_orientation_refinement.rs (2)
- [x] `runtime_orientation::orient2d`
- [ ] `runtime_orientation::scale_point_from_origin`
- [ ] `runtime_orientation::orientation`

## B. runtime_orientation3_refinement.rs (2)
- [x] `runtime_orientation3::orient3d`
- [ ] `runtime_orientation3::scale_point_from_origin3`
- [ ] `runtime_orientation3::orientation3`

## C. runtime_vec2_refinement.rs (10)
- [ ] `RuntimeVec2::new`
- [ ] `RuntimeVec2::from_ints`
- [ ] `RuntimeVec2::zero`
- [ ] `RuntimeVec2::add`
- [ ] `RuntimeVec2::sub`
- [ ] `RuntimeVec2::neg`
- [ ] `RuntimeVec2::scale`
- [ ] `RuntimeVec2::dot`
- [ ] `RuntimeVec2::cross`
- [ ] `RuntimeVec2::norm2`

## D. runtime_point2_refinement.rs (5)
- [ ] `RuntimePoint2::new`
- [ ] `RuntimePoint2::from_ints`
- [ ] `RuntimePoint2::add_vec`
- [ ] `RuntimePoint2::sub`
- [ ] `RuntimePoint2::dist2`

## E. runtime_vec3_refinement.rs (10)
- [ ] `RuntimeVec3::new`
- [ ] `RuntimeVec3::from_ints`
- [ ] `RuntimeVec3::zero`
- [ ] `RuntimeVec3::add`
- [ ] `RuntimeVec3::sub`
- [ ] `RuntimeVec3::neg`
- [ ] `RuntimeVec3::scale`
- [ ] `RuntimeVec3::dot`
- [ ] `RuntimeVec3::cross`
- [ ] `RuntimeVec3::norm2`

## F. runtime_point3_refinement.rs (5)
- [ ] `RuntimePoint3::new`
- [ ] `RuntimePoint3::from_ints`
- [ ] `RuntimePoint3::add_vec`
- [ ] `RuntimePoint3::sub`
- [ ] `RuntimePoint3::dist2`

## G. runtime_vec4_refinement.rs (9)
- [ ] `RuntimeVec4::new`
- [ ] `RuntimeVec4::from_ints`
- [ ] `RuntimeVec4::zero`
- [ ] `RuntimeVec4::add`
- [ ] `RuntimeVec4::sub`
- [ ] `RuntimeVec4::neg`
- [ ] `RuntimeVec4::scale`
- [ ] `RuntimeVec4::dot`
- [ ] `RuntimeVec4::norm2`

## H. runtime_point4_refinement.rs (5)
- [ ] `RuntimePoint4::new`
- [ ] `RuntimePoint4::from_ints`
- [ ] `RuntimePoint4::add_vec`
- [ ] `RuntimePoint4::sub`
- [ ] `RuntimePoint4::dist2`

## I. runtime_quaternion_refinement.rs (13)
- [ ] `RuntimeQuaternion::new`
- [ ] `RuntimeQuaternion::from_ints`
- [ ] `RuntimeQuaternion::zero`
- [ ] `RuntimeQuaternion::one`
- [ ] `RuntimeQuaternion::add`
- [ ] `RuntimeQuaternion::sub`
- [ ] `RuntimeQuaternion::neg`
- [ ] `RuntimeQuaternion::scale`
- [ ] `RuntimeQuaternion::mul`
- [ ] `RuntimeQuaternion::conjugate`
- [ ] `RuntimeQuaternion::norm2`
- [ ] `RuntimeQuaternion::inverse`
- [ ] `RuntimeQuaternion::rotate_vec3`

## J. runtime_scalar_refinement.rs (9)
- [ ] `RuntimeScalar::from_int`
- [ ] `RuntimeScalar::from_fraction`
- [ ] `RuntimeScalar::add`
- [ ] `RuntimeScalar::sub`
- [ ] `RuntimeScalar::mul`
- [ ] `RuntimeScalar::recip`
- [ ] `RuntimeScalar::neg`
- [ ] `RuntimeScalar::normalize`
- [ ] `RuntimeScalar::signum_i8`

## Completion Gates
- [ ] `rg -n "assume_specification\\[" crates/vcad-math/src` returns no matches.
- [ ] `./scripts/verify-vcad-math.sh` succeeds after each milestone.
- [ ] Proof quality pass: no unnecessary trigger warnings in newly touched modules.
