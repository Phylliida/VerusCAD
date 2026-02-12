use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;

/// Runtime 2D point backed by runtime scalars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint2 {
    x: RuntimeScalar,
    y: RuntimeScalar,
}

impl RuntimePoint2 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar) -> Self {
        Self { x, y }
    }

    pub fn from_ints(x: i64, y: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
        }
    }

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    pub fn add_vec(&self, v: &RuntimeVec2) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
        }
    }

    pub fn sub(&self, rhs: &Self) -> RuntimeVec2 {
        RuntimeVec2::new(self.x.sub(&rhs.x), self.y.sub(&rhs.y))
    }

    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}
