use crate::runtime_scalar::RuntimeScalar;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec3 {
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
}

impl RuntimeVec3 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> Self {
        Self { x, y, z }
    }

    pub fn from_ints(x: i64, y: i64, z: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
        }
    }

    pub fn zero() -> Self {
        Self::from_ints(0, 0, 0)
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

    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let xy = xx.add(&yy);
        xy.add(&zz)
    }

    pub fn cross(&self, rhs: &Self) -> Self {
        let yz = self.y.mul(&rhs.z);
        let zy = self.z.mul(&rhs.y);
        let zx = self.z.mul(&rhs.x);
        let xz = self.x.mul(&rhs.z);
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        Self {
            x: yz.sub(&zy),
            y: zx.sub(&xz),
            z: xy.sub(&yx),
        }
    }

    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}
