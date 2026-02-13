use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;
#[cfg(verus_keep_ghost)]
use crate::point2::{dist2_spec, Point2};
#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

/// Runtime 2D point backed by runtime scalars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimePoint2 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
}

impl RuntimePoint2 {
    #[cfg(not(verus_keep_ghost))]
    pub fn new(x: RuntimeScalar, y: RuntimeScalar) -> Self {
        Self { x, y }
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn add_vec(&self, v: &RuntimeVec2) -> Self {
        Self {
            x: self.x.add(v.x()),
            y: self.y.add(v.y()),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> RuntimeVec2 {
        RuntimeVec2::new(self.x.sub(&rhs.x), self.y.sub(&rhs.y))
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dist2(&self, rhs: &Self) -> RuntimeScalar {
        self.sub(rhs).norm2()
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimePoint2 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Point2 { x: x@, y: y@ }),
    {
        RuntimePoint2 { x, y }
    }

    pub fn from_ints(x: i64, y: i64) -> (out: Self)
        ensures
            out@ == Point2::from_ints_spec(x as int, y as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let out = Self::new(sx, sy);
        proof {
            assert(out@ == Point2 { x: sx@, y: sy@ });
            assert(out@ == Point2::from_ints_spec(x as int, y as int));
        }
        out
    }

    pub fn add_vec(&self, v: &RuntimeVec2) -> (out: Self)
        ensures
            out@ == self@.add_vec_spec(v@),
    {
        let x = self.x.add(&v.x);
        let y = self.y.add(&v.y);
        let out = Self { x, y };
        proof {
            assert(out@ == Point2 { x: self@.x.add_spec(v@.x), y: self@.y.add_spec(v@.y) });
            assert(out@ == self@.add_vec_spec(v@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: RuntimeVec2)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let out = RuntimeVec2::new(x, y);
        proof {
            assert(out@ == Vec2 { x: self@.x.sub_spec(rhs@.x), y: self@.y.sub_spec(rhs@.y) });
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
