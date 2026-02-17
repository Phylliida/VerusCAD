use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use crate::point3::{dist2_spec, Point3};
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint3 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
    pub z: RuntimeScalar,
}

impl RuntimePoint3 {
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
    pub fn add_vec(&self, v: &RuntimeVec3) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
            z: self.z.add(v.z()),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> RuntimeVec3 {
        RuntimeVec3::new(self.x.sub(&rhs.x), self.y.sub(&rhs.y), self.z.sub(&rhs.z))
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimePoint3 {
    pub open spec fn witness_wf_spec(&self) -> bool {
        &&& self.x.witness_wf_spec()
        &&& self.y.witness_wf_spec()
        &&& self.z.witness_wf_spec()
    }

    pub fn new(x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Point3 { x: x@, y: y@, z: z@ }),
    {
        RuntimePoint3 { x, y, z }
    }

    pub fn from_ints(x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out@ == Point3::from_ints_spec(x as int, y as int, z as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let sz = RuntimeScalar::from_int(z);
        let out = Self::new(sx, sy, sz);
        proof {
            assert(out@ == Point3 { x: sx@, y: sy@, z: sz@ });
            assert(out@ == Point3::from_ints_spec(x as int, y as int, z as int));
        }
        out
    }

    pub fn add_vec(&self, v: &RuntimeVec3) -> (out: Self)
        ensures
            out@ == self@.add_vec_spec(v@),
    {
        let x = self.x.add(&v.x);
        let y = self.y.add(&v.y);
        let z = self.z.add(&v.z);
        let out = Self { x, y, z };
        proof {
            assert(
                out@ == Point3 {
                    x: self@.x.add_spec(v@.x),
                    y: self@.y.add_spec(v@.y),
                    z: self@.z.add_spec(v@.z),
                }
            );
            assert(out@ == self@.add_vec_spec(v@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: RuntimeVec3)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let out = RuntimeVec3::new(x, y, z);
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
