use crate::scalar::Scalar;
use crate::vec4::Vec4;
use vstd::prelude::*;

verus! {

pub struct Point4 {
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
    pub w: Scalar,
}

impl Point4 {
    pub open spec fn from_ints_spec(x: int, y: int, z: int, w: int) -> Self {
        Point4 {
            x: Scalar::from_int_spec(x),
            y: Scalar::from_int_spec(y),
            z: Scalar::from_int_spec(z),
            w: Scalar::from_int_spec(w),
        }
    }

    pub proof fn from_ints(x: int, y: int, z: int, w: int) -> (p: Self)
        ensures
            p == Self::from_ints_spec(x, y, z, w),
    {
        Point4 {
            x: Scalar::from_int(x),
            y: Scalar::from_int(y),
            z: Scalar::from_int(z),
            w: Scalar::from_int(w),
        }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x)
            && self.y.eqv_spec(rhs.y)
            && self.z.eqv_spec(rhs.z)
            && self.w.eqv_spec(rhs.w)
    }

    pub open spec fn add_vec_spec(self, v: Vec4) -> Self {
        Point4 {
            x: self.x.add_spec(v.x),
            y: self.y.add_spec(v.y),
            z: self.z.add_spec(v.z),
            w: self.w.add_spec(v.w),
        }
    }

    pub proof fn add_vec(self, v: Vec4) -> (out: Self)
        ensures
            out == self.add_vec_spec(v),
    {
        Point4 {
            x: self.x.add(v.x),
            y: self.y.add(v.y),
            z: self.z.add(v.z),
            w: self.w.add(v.w),
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Vec4 {
        Vec4 {
            x: self.x.sub_spec(rhs.x),
            y: self.y.sub_spec(rhs.y),
            z: self.z.sub_spec(rhs.z),
            w: self.w.sub_spec(rhs.w),
        }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Vec4)
        ensures
            out == self.sub_spec(rhs),
    {
        Vec4 {
            x: self.x.sub(rhs.x),
            y: self.y.sub(rhs.y),
            z: self.z.sub(rhs.z),
            w: self.w.sub(rhs.w),
        }
    }

    pub proof fn lemma_eqv_from_components(p: Self, q: Self)
        requires
            p.x.eqv_spec(q.x),
            p.y.eqv_spec(q.y),
            p.z.eqv_spec(q.z),
            p.w.eqv_spec(q.w),
        ensures
            p.eqv_spec(q),
    {
        assert(p.eqv_spec(q));
    }
}

pub open spec fn dist2_spec(p: Point4, q: Point4) -> Scalar {
    p.sub_spec(q).norm2_spec()
}

pub proof fn lemma_dist2_is_sub_norm2(p: Point4, q: Point4)
    ensures
        dist2_spec(p, q) == p.sub_spec(q).norm2_spec(),
{
    assert(dist2_spec(p, q) == p.sub_spec(q).norm2_spec());
}

} // verus!
