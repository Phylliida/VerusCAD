use crate::runtime_scalar::RuntimeScalar;

/// Runtime 2D vector backed by runtime scalars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec2 {
    x: RuntimeScalar,
    y: RuntimeScalar,
}

impl RuntimeVec2 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar) -> Self {
        Self { x, y }
    }

    pub fn from_ints(x: i64, y: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
        }
    }

    pub fn zero() -> Self {
        Self::from_ints(0, 0)
    }

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
        }
    }

    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
        }
    }

    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        xx.add(&yy)
    }

    pub fn cross(&self, rhs: &Self) -> RuntimeScalar {
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        xy.sub(&yx)
    }

    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}
