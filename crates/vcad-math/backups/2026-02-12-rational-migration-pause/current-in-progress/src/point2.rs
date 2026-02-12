use vstd::prelude::*;
use crate::scalar::Scalar;
use crate::vec2::Vec2;

verus! {

pub struct Point2 {
    pub x: Scalar,
    pub y: Scalar,
}

impl Point2 {
    pub open spec fn from_ints_spec(x: int, y: int) -> Self {
        Point2 { x: Scalar::from_int_spec(x), y: Scalar::from_int_spec(y) }
    }

    pub proof fn from_ints(x: int, y: int) -> (p: Self)
        ensures
            p == Self::from_ints_spec(x, y),
    {
        let sx = Scalar::from_int(x);
        let sy = Scalar::from_int(y);
        Point2 { x: sx, y: sy }
    }

    pub open spec fn add_vec_spec(self, v: Vec2) -> Self {
        Point2 { x: self.x.add_spec(v.x), y: self.y.add_spec(v.y) }
    }

    pub proof fn add_vec(self, v: Vec2) -> (out: Self)
        ensures
            out == self.add_vec_spec(v),
    {
        let x = self.x.add(v.x);
        let y = self.y.add(v.y);
        Point2 { x, y }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Vec2 {
        Vec2 { x: self.x.sub_spec(rhs.x), y: self.y.sub_spec(rhs.y) }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Vec2)
        ensures
            out == self.sub_spec(rhs),
    {
        let x = self.x.sub(rhs.x);
        let y = self.y.sub(rhs.y);
        Vec2 { x, y }
    }
}

pub open spec fn dist2_spec(p: Point2, q: Point2) -> Scalar {
    p.sub_spec(q).norm2_spec()
}

} // verus!
