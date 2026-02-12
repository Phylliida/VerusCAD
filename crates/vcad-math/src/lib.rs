pub mod scalar;
pub use scalar::{Scalar, ScalarModel};

pub mod runtime_scalar;
pub use runtime_scalar::RuntimeScalar;
mod runtime_scalar_refinement;

pub mod runtime_vec2;
pub use runtime_vec2::RuntimeVec2;
mod runtime_vec2_refinement;

pub mod runtime_point2;
pub use runtime_point2::RuntimePoint2;
mod runtime_point2_refinement;

pub mod runtime_orientation;
pub use runtime_orientation::RuntimeOrientation;
mod runtime_orientation_refinement;

pub mod runtime_vec3;
pub use runtime_vec3::RuntimeVec3;
mod runtime_vec3_refinement;

pub mod runtime_point3;
pub use runtime_point3::RuntimePoint3;
mod runtime_point3_refinement;

pub mod runtime_orientation3;
pub use runtime_orientation3::RuntimeOrientation3;
mod runtime_orientation3_refinement;

pub mod runtime_vec4;
pub use runtime_vec4::RuntimeVec4;
mod runtime_vec4_refinement;

pub mod runtime_point4;
pub use runtime_point4::RuntimePoint4;
mod runtime_point4_refinement;

pub mod runtime_quaternion;
pub use runtime_quaternion::RuntimeQuaternion;
mod runtime_quaternion_refinement;

pub mod vec2;
pub use vec2::Vec2;

pub mod point2;
pub use point2::*;

pub mod orientation;
pub use orientation::*;

pub mod vec3;
pub use vec3::Vec3;

pub mod point3;
pub use point3::Point3;

pub mod orientation3;
pub use orientation3::*;

pub mod vec4;
pub use vec4::Vec4;

pub mod point4;
pub use point4::Point4;

pub mod quaternion;
pub use quaternion::Quaternion;
mod quaternion_assoc_cases;
