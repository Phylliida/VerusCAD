use crate::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::vec2::Vec2;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

/// Runtime 2D vector backed by runtime scalars.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeVec2 {
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
}

impl RuntimeVec2 {
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

    #[cfg(not(verus_keep_ghost))]
    pub fn zero() -> Self {
        Self::from_ints(0, 0)
    }

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn neg(&self) -> Self {
        Self {
            x: self.x.neg(),
            y: self.y.neg(),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            x: self.x.mul(k),
            y: self.y.mul(k),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn dot(&self, rhs: &Self) -> RuntimeScalar {
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        xx.add(&yy)
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn cross(&self, rhs: &Self) -> RuntimeScalar {
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        xy.sub(&yx)
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn norm2(&self) -> RuntimeScalar {
        self.dot(self)
    }
}

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeVec2 {
    pub fn new(x: RuntimeScalar, y: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Vec2 { x: x@, y: y@ }),
    {
        RuntimeVec2 { x, y }
    }

    pub fn from_ints(x: i64, y: i64) -> (out: Self)
        ensures
            out@ == Vec2::from_ints_spec(x as int, y as int),
    {
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let out = Self::new(sx, sy);
        proof {
            assert(out@ == Vec2 { x: sx@, y: sy@ });
            assert(sx@ == Scalar::from_int_spec(x as int));
            assert(sy@ == Scalar::from_int_spec(y as int));
            assert(out@ == Vec2::from_ints_spec(x as int, y as int));
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out@ == Vec2::zero_spec(),
    {
        let out = Self::from_ints(0, 0);
        proof {
            assert(out@ == Vec2::from_ints_spec(0, 0));
            assert(Vec2::zero_spec() == Vec2::from_ints_spec(0, 0));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let neg_rhs = rhs.neg();
        let out = self.add(&neg_rhs);
        proof {
            Vec2::lemma_sub_is_add_neg(self@, rhs@);
            assert(self@.sub_spec(rhs@) == self@.add_spec(rhs@.neg_spec()));
            assert(neg_rhs@ == rhs@.neg_spec());
            assert(out@ == self@.add_spec(neg_rhs@));
            assert(out@ == self@.sub_spec(rhs@));
        }
        out
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.add_spec(rhs@),
    {
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let out = Self { x, y };
        proof {
            assert(out@ == Vec2 { x: self@.x.add_spec(rhs@.x), y: self@.y.add_spec(rhs@.y) });
            assert(out@ == self@.add_spec(rhs@));
        }
        out
    }

    pub fn neg(&self) -> (out: Self)
        ensures
            out@ == self@.neg_spec(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        let out = Self { x, y };
        proof {
            assert(out@ == Vec2 { x: self@.x.neg_spec(), y: self@.y.neg_spec() });
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
        let out = Self { x, y };
        proof {
            assert(out@ == Vec2 { x: self@.x.mul_spec(k@), y: self@.y.mul_spec(k@) });
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
        let out = xx.add(&yy);
        proof {
            assert(xx@ == self@.x.mul_spec(rhs@.x));
            assert(yy@ == self@.y.mul_spec(rhs@.y));
            assert(out@ == xx@.add_spec(yy@));
            assert(out@ == self@.dot_spec(rhs@));
        }
        out
    }

    pub fn cross(&self, rhs: &Self) -> (out: RuntimeScalar)
        ensures
            out@ == self@.cross_spec(rhs@),
    {
        let xy = self.x.mul(&rhs.y);
        let yx = self.y.mul(&rhs.x);
        let out = xy.sub(&yx);
        proof {
            assert(xy@ == self@.x.mul_spec(rhs@.y));
            assert(yx@ == self@.y.mul_spec(rhs@.x));
            assert(out@ == xy@.sub_spec(yx@));
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
