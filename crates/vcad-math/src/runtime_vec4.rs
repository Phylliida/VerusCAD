use crate::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec4 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
    pub z: RuntimeScalar,
    pub w: RuntimeScalar,
}

impl RuntimeVec4 {
    #[cfg(not(verus_keep_ghost))]
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar, w: RuntimeScalar) -> Self {
        Self { x, y, z, w }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn from_ints(x: i64, y: i64, z: i64, w: i64) -> Self {
        Self {
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
            w: RuntimeScalar::from_int(w),
        }
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
            w: self.w.add(&rhs.w),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
            w: self.w.sub(&rhs.w),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
            w: self.w.neg(),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
            w: self.w.mul(k),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let ww = self.w.mul(&rhs.w);
        xx.add(&yy).add(&zz).add(&ww)
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeVec4 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar, w: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Vec4 { x: x@, y: y@, z: z@, w: w@ }),
    {
        RuntimeVec4 { x, y, z, w }
    }

    pub fn from_ints(x: i64, y: i64, z: i64, w: i64) -> (out: Self)
        ensures
            out@ == Vec4::from_ints_spec(x as int, y as int, z as int, w as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let sz = RuntimeScalar::from_int(z);
        let sw = RuntimeScalar::from_int(w);
        let out = Self::new(sx, sy, sz, sw);
        proof {
            assert(out@ == Vec4 { x: sx@, y: sy@, z: sz@, w: sw@ });
            assert(sx@ == Scalar::from_int_spec(x as int));
            assert(sy@ == Scalar::from_int_spec(y as int));
            assert(sz@ == Scalar::from_int_spec(z as int));
            assert(sw@ == Scalar::from_int_spec(w as int));
            assert(out@ == Vec4::from_ints_spec(x as int, y as int, z as int, w as int));
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out@ == Vec4::zero_spec(),
    {
        let out = Self::from_ints(0, 0, 0, 0);
        proof {
            assert(out@ == Vec4::from_ints_spec(0, 0, 0, 0));
            assert(Vec4::zero_spec() == Vec4::from_ints_spec(0, 0, 0, 0));
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
        let w = self.w.add(&rhs.w);
        let out = Self { x, y, z, w };
        proof {
            assert(
                out@ == Vec4 {
                    x: self@.x.add_spec(rhs@.x),
                    y: self@.y.add_spec(rhs@.y),
                    z: self@.z.add_spec(rhs@.z),
                    w: self@.w.add_spec(rhs@.w),
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
        let w = self.w.sub(&rhs.w);
        let out = Self { x, y, z, w };
        proof {
            assert(
                out@ == Vec4 {
                    x: self@.x.sub_spec(rhs@.x),
                    y: self@.y.sub_spec(rhs@.y),
                    z: self@.z.sub_spec(rhs@.z),
                    w: self@.w.sub_spec(rhs@.w),
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
        let w = self.w.neg();
        let out = Self { x, y, z, w };
        proof {
            assert(
                out@ == Vec4 {
                    x: self@.x.neg_spec(),
                    y: self@.y.neg_spec(),
                    z: self@.z.neg_spec(),
                    w: self@.w.neg_spec(),
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
        let w = self.w.mul(k);
        let out = Self { x, y, z, w };
        proof {
            assert(
                out@ == Vec4 {
                    x: self@.x.mul_spec(k@),
                    y: self@.y.mul_spec(k@),
                    z: self@.z.mul_spec(k@),
                    w: self@.w.mul_spec(k@),
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
        let ww = self.w.mul(&rhs.w);
        let xy = xx.add(&yy);
        let xyz = xy.add(&zz);
        let out = xyz.add(&ww);
        proof {
            assert(xx@ == self@.x.mul_spec(rhs@.x));
            assert(yy@ == self@.y.mul_spec(rhs@.y));
            assert(zz@ == self@.z.mul_spec(rhs@.z));
            assert(ww@ == self@.w.mul_spec(rhs@.w));
            assert(xy@ == xx@.add_spec(yy@));
            assert(xyz@ == xy@.add_spec(zz@));
            assert(out@ == xyz@.add_spec(ww@));
            assert(out@ == self@.dot_spec(rhs@));
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
