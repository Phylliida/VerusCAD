use vstd::prelude::*;
use crate::scalar::Scalar;

verus! {

pub struct Vec2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Vec2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Vec2 { x: Scalar::from_int_spec(x), y: Scalar::from_int_spec(y) }
    }

    pub proof fn from_ints(x: int, y: int) -> (v: Self)
        ensures
            v == Self::from_ints_spec(x, y),
    {
        let sx = Scalar::from_int(x);
        let sy = Scalar::from_int(y);
        Vec2 { x: sx, y: sy }
    }

    pub open spec fn zero_spec() -> Self {
        Self::from_ints_spec(0, 0)
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.add_spec(rhs.x), y: self.y.add_spec(rhs.y) }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        let x = self.x.add(rhs.x);
        let y = self.y.add(rhs.y);
        Vec2 { x, y }
    }

    pub open spec fn neg_spec(self) -> Self {
        Vec2 { x: self.x.neg_spec(), y: self.y.neg_spec() }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        let x = self.x.neg();
        let y = self.y.neg();
        Vec2 { x, y }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        let x = self.x.sub(rhs.x);
        let y = self.y.sub(rhs.y);
        Vec2 { x, y }
    }

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Vec2 { x: self.x.mul_spec(k), y: self.y.mul_spec(k) }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        let x = self.x.mul(k);
        let y = self.y.mul(k);
        Vec2 { x, y }
    }

    pub open spec fn dot_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.x).add_spec(self.y.mul_spec(rhs.y))
    }

    pub proof fn dot(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.dot_spec(rhs),
    {
        let xx = self.x.mul(rhs.x);
        let yy = self.y.mul(rhs.y);
        xx.add(yy)
    }

    pub open spec fn cross_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.y).sub_spec(self.y.mul_spec(rhs.x))
    }

    pub proof fn cross(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.cross_spec(rhs),
    {
        let xy = self.x.mul(rhs.y);
        let yx = self.y.mul(rhs.x);
        xy.sub(yx)
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.dot_spec(self)
    }
}

} // verus!
