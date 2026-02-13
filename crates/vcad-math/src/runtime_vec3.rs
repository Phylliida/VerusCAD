use crate::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec3 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
    pub z: RuntimeScalar,
}

impl RuntimeVec3 {
    #[cfg(not(verus_keep_ghost))]
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> Self {
        Self { x, y, z }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn from_ints(x: i64, y: i64, z: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let xy = xx.add(&yy);
        xy.add(&zz)
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeVec3 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Vec3 { x: x@, y: y@, z: z@ }),
    {
        RuntimeVec3 { x, y, z }
    }

    pub fn from_ints(x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out@ == Vec3::from_ints_spec(x as int, y as int, z as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let sz = RuntimeScalar::from_int(z);
        let out = Self::new(sx, sy, sz);
        proof {
            assert(out@ == Vec3 { x: sx@, y: sy@, z: sz@ });
            assert(sx@ == Scalar::from_int_spec(x as int));
            assert(sy@ == Scalar::from_int_spec(y as int));
            assert(sz@ == Scalar::from_int_spec(z as int));
            assert(out@ == Vec3::from_ints_spec(x as int, y as int, z as int));
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out@ == Vec3::zero_spec(),
    {
        let out = Self::from_ints(0, 0, 0);
        proof {
            assert(out@ == Vec3::from_ints_spec(0, 0, 0));
            assert(Vec3::zero_spec() == Vec3::from_ints_spec(0, 0, 0));
        }
        out
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.add_spec(rhs@),
    {
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let z = self.z.add(&rhs.z);
        let out = Self { x, y, z };
        proof {
            assert(
                out@ == Vec3 {
                    x: self@.x.add_spec(rhs@.x),
                    y: self@.y.add_spec(rhs@.y),
                    z: self@.z.add_spec(rhs@.z),
                }
            );
            assert(out@ == self@.add_spec(rhs@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let out = Self { x, y, z };
        proof {
            assert(
                out@ == Vec3 {
                    x: self@.x.sub_spec(rhs@.x),
                    y: self@.y.sub_spec(rhs@.y),
                    z: self@.z.sub_spec(rhs@.z),
                }
            );
            assert(out@ == self@.sub_spec(rhs@));
        }
        out
    }

    pub fn neg(&self) -> (out: Self)
        ensures
            out@ == self@.neg_spec(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        let z = self.z.neg();
        let out = Self { x, y, z };
        proof {
            assert(
                out@ == Vec3 {
                    x: self@.x.neg_spec(),
                    y: self@.y.neg_spec(),
                    z: self@.z.neg_spec(),
                }
            );
            assert(out@ == self@.neg_spec());
        }
        out
    }

    pub fn scale(&self, k: &RuntimeScalar) -> (out: Self)
        ensures
            out@ == self@.scale_spec(k@),
    {
        let x = self.x.mul(k);
        let y = self.y.mul(k);
        let z = self.z.mul(k);
        let out = Self { x, y, z };
        proof {
            assert(
                out@ == Vec3 {
                    x: self@.x.mul_spec(k@),
                    y: self@.y.mul_spec(k@),
                    z: self@.z.mul_spec(k@),
                }
            );
            assert(out@ == self@.scale_spec(k@));
        }
        out
    }

    pub fn dot(&self, rhs: &Self) -> (out: RuntimeScalar)
        ensures
            out@ == self@.dot_spec(rhs@),
    {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let xy = xx.add(&yy);
        let out = xy.add(&zz);
        proof {
            assert(xx@ == self@.x.mul_spec(rhs@.x));
            assert(yy@ == self@.y.mul_spec(rhs@.y));
            assert(zz@ == self@.z.mul_spec(rhs@.z));
            assert(xy@ == xx@.add_spec(yy@));
            assert(out@ == xy@.add_spec(zz@));
            assert(out@ == self@.dot_spec(rhs@));
        }
        out
    }

    pub fn cross(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.cross_spec(rhs@),
    {
        let yz = self.y.mul(&rhs.z);
        let zy = self.z.mul(&rhs.y);
        let zx = self.z.mul(&rhs.x);
        let xz = self.x.mul(&rhs.z);
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        let out = Self {
            x: yz.sub(&zy),
            y: zx.sub(&xz),
            z: xy.sub(&yx),
        };
        proof {
            assert(yz@ == self@.y.mul_spec(rhs@.z));
            assert(zy@ == self@.z.mul_spec(rhs@.y));
            assert(zx@ == self@.z.mul_spec(rhs@.x));
            assert(xz@ == self@.x.mul_spec(rhs@.z));
            assert(xy@ == self@.x.mul_spec(rhs@.y));
            assert(yx@ == self@.y.mul_spec(rhs@.x));
            assert(out@.x == yz@.sub_spec(zy@));
            assert(out@.y == zx@.sub_spec(xz@));
            assert(out@.z == xy@.sub_spec(yx@));
            assert(out@ == self@.cross_spec(rhs@));
        }
        out
    }

    pub fn norm2(&self) -> (out: RuntimeScalar)
        ensures
            out@ == self@.norm2_spec(),
    {
        let out = self.dot(self);
        proof {
            assert(out@ == self@.dot_spec(self@));
            assert(self@.norm2_spec() == self@.dot_spec(self@));
            assert(out@ == self@.norm2_spec());
        }
        out
    }
}
}
