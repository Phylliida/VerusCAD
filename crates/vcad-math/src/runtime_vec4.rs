use crate::runtime_scalar::RuntimeScalar;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec4 {
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
    w: RuntimeScalar,
}

impl RuntimeVec4 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar, w: RuntimeScalar) -> Self {
        Self { x, y, z, w }
    }

    pub fn from_ints(x: i64, y: i64, z: i64, w: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
            w: RuntimeScalar::from_int(w),
        }
    }

    pub fn zero() -> Self {
        Self::from_ints(0, 0, 0, 0)
    }

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    pub fn z(&self) -> &RuntimeScalar {
        &self.z
    }

    pub fn w(&self) -> &RuntimeScalar {
        &self.w
    }

    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
            w: self.w.add(&rhs.w),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
            w: self.w.sub(&rhs.w),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
            w: self.w.neg(),
        }
    }

    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
            w: self.w.mul(k),
        }
    }

    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let ww = self.w.mul(&rhs.w);
        xx.add(&yy).add(&zz).add(&ww)
    }

    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}
