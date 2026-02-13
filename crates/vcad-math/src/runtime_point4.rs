use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec4::RuntimeVec4;
#[cfg(verus_keep_ghost)]
use crate::point4::{dist2_spec, Point4};
#[cfg(verus_keep_ghost)]
use crate::vec4::Vec4;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint4 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
    pub z: RuntimeScalar,
    pub w: RuntimeScalar,
}

impl RuntimePoint4 {
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
    pub fn add_vec(&self, v: &RuntimeVec4) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
            z: self.z.add(v.z()),
            w: self.w.add(v.w()),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> RuntimeVec4 {
        RuntimeVec4::new(
            self.x.sub(&rhs.x),
            self.y.sub(&rhs.y),
            self.z.sub(&rhs.z),
            self.w.sub(&rhs.w),
        )
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimePoint4 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar, w: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Point4 { x: x@, y: y@, z: z@, w: w@ }),
    {
        RuntimePoint4 { x, y, z, w }
    }

    pub fn from_ints(x: i64, y: i64, z: i64, w: i64) -> (out: Self)
        ensures
            out@ == Point4::from_ints_spec(x as int, y as int, z as int, w as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let sz = RuntimeScalar::from_int(z);
        let sw = RuntimeScalar::from_int(w);
        let out = Self::new(sx, sy, sz, sw);
        proof {
            assert(out@ == Point4 { x: sx@, y: sy@, z: sz@, w: sw@ });
            assert(out@ == Point4::from_ints_spec(x as int, y as int, z as int, w as int));
        }
        out
    }

    pub fn add_vec(&self, v: &RuntimeVec4) -> (out: Self)
        ensures
            out@ == self@.add_vec_spec(v@),
    {
        let x = self.x.add(&v.x);
        let y = self.y.add(&v.y);
        let z = self.z.add(&v.z);
        let w = self.w.add(&v.w);
        let out = Self { x, y, z, w };
        proof {
            assert(
                out@ == Point4 {
                    x: self@.x.add_spec(v@.x),
                    y: self@.y.add_spec(v@.y),
                    z: self@.z.add_spec(v@.z),
                    w: self@.w.add_spec(v@.w),
                }
            );
            assert(out@ == self@.add_vec_spec(v@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: RuntimeVec4)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let w = self.w.sub(&rhs.w);
        let out = RuntimeVec4::new(x, y, z, w);
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

    pub fn dist2(&self, rhs: &Self) -> (out: RuntimeScalar)
        ensures
            out@ == dist2_spec(self@, rhs@),
    {
        let d = self.sub(rhs);
        let out = d.norm2();
        proof {
            assert(d@ == self@.sub_spec(rhs@));
            assert(out@ == d@.norm2_spec());
            assert(dist2_spec(self@, rhs@) == self@.sub_spec(rhs@).norm2_spec());
            assert(out@ == dist2_spec(self@, rhs@));
        }
        out
    }
}
}
