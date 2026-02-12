use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint3 {
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
}

impl RuntimePoint3 {
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

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    pub fn z(&self) -> &RuntimeScalar {
        &self.z
    }

    pub fn add_vec(&self, v: &RuntimeVec3) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
            z: self.z.add(v.z()),
        }
    }

    pub fn sub(&self, rhs: &Self) -> RuntimeVec3 {
        RuntimeVec3::new(self.x.sub(&rhs.x), self.y.sub(&rhs.y), self.z.sub(&rhs.z))
    }

    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}
