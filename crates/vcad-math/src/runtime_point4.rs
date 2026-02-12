use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec4::RuntimeVec4;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint4 {
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
    w: RuntimeScalar,
}

impl RuntimePoint4 {
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

    pub fn add_vec(&self, v: &RuntimeVec4) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
            z: self.z.add(v.z()),
            w: self.w.add(v.w()),
        }
    }

    pub fn sub(&self, rhs: &Self) -> RuntimeVec4 {
        RuntimeVec4::new(
            self.x.sub(&rhs.x),
            self.y.sub(&rhs.y),
            self.z.sub(&rhs.z),
            self.w.sub(&rhs.w),
        )
    }

    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}
