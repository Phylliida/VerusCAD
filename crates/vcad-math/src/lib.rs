pub mod scalar;
pub use scalar::{Scalar, ScalarModel};

pub mod runtime_scalar;
pub use runtime_scalar::RuntimeScalar;
mod runtime_scalar_refinement;

pub mod vec2;
pub use vec2::Vec2;

pub mod point2;
pub use point2::*;

pub mod orientation;
pub use orientation::*;
