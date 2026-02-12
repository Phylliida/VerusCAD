use crate::scalar::Scalar;
use vstd::prelude::*;

verus! {

pub struct Vec4 {
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
    pub w: Scalar,
}

impl Vec4 {
    pub open spec fn from_ints_spec(x: int, y: int, z: int, w: int) -> Self {
        Vec4 {
            x: Scalar::from_int_spec(x),
            y: Scalar::from_int_spec(y),
            z: Scalar::from_int_spec(z),
            w: Scalar::from_int_spec(w),
        }
    }

    pub proof fn from_ints(x: int, y: int, z: int, w: int) -> (v: Self)
        ensures
            v == Self::from_ints_spec(x, y, z, w),
    {
        Vec4 {
            x: Scalar::from_int(x),
            y: Scalar::from_int(y),
            z: Scalar::from_int(z),
            w: Scalar::from_int(w),
        }
    }

    pub open spec fn zero_spec() -> Self {
        Self::from_ints_spec(0, 0, 0, 0)
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x)
            && self.y.eqv_spec(rhs.y)
            && self.z.eqv_spec(rhs.z)
            && self.w.eqv_spec(rhs.w)
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Vec4 {
            x: self.x.add_spec(rhs.x),
            y: self.y.add_spec(rhs.y),
            z: self.z.add_spec(rhs.z),
            w: self.w.add_spec(rhs.w),
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        Vec4 {
            x: self.x.add(rhs.x),
            y: self.y.add(rhs.y),
            z: self.z.add(rhs.z),
            w: self.w.add(rhs.w),
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Vec4 {
            x: self.x.neg_spec(),
            y: self.y.neg_spec(),
            z: self.z.neg_spec(),
            w: self.w.neg_spec(),
        }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Vec4 {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
            w: self.w.neg(),
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Vec4 {
            x: self.x.sub_spec(rhs.x),
            y: self.y.sub_spec(rhs.y),
            z: self.z.sub_spec(rhs.z),
            w: self.w.sub_spec(rhs.w),
        }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
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

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Vec4 {
            x: self.x.mul_spec(k),
            y: self.y.mul_spec(k),
            z: self.z.mul_spec(k),
            w: self.w.mul_spec(k),
        }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        Vec4 {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
            w: self.w.mul(k),
        }
    }

    pub open spec fn dot_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.x)
            .add_spec(self.y.mul_spec(rhs.y))
            .add_spec(self.z.mul_spec(rhs.z))
            .add_spec(self.w.mul_spec(rhs.w))
    }

    pub proof fn dot(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.dot_spec(rhs),
    {
        let xx = self.x.mul(rhs.x);
        let yy = self.y.mul(rhs.y);
        let zz = self.z.mul(rhs.z);
        let ww = self.w.mul(rhs.w);
        let s0 = xx.add(yy);
        let s1 = s0.add(zz);
        s1.add(ww)
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.dot_spec(self)
    }

    pub proof fn lemma_eqv_from_components(a: Self, b: Self)
        requires
            a.x.eqv_spec(b.x),
            a.y.eqv_spec(b.y),
            a.z.eqv_spec(b.z),
            a.w.eqv_spec(b.w),
        ensures
            a.eqv_spec(b),
    {
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).eqv_spec(b.add_spec(a)),
    {
        let lhs = a.add_spec(b);
        let rhs = b.add_spec(a);
        Scalar::lemma_add_commutative(a.x, b.x);
        Scalar::lemma_add_commutative(a.y, b.y);
        Scalar::lemma_add_commutative(a.z, b.z);
        Scalar::lemma_add_commutative(a.w, b.w);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).eqv_spec(a.add_spec(b.add_spec(c))),
    {
        let lhs = a.add_spec(b).add_spec(c);
        let rhs = a.add_spec(b.add_spec(c));
        Scalar::lemma_add_associative(a.x, b.x, c.x);
        Scalar::lemma_add_associative(a.y, b.y, c.y);
        Scalar::lemma_add_associative(a.z, b.z, c.z);
        Scalar::lemma_add_associative(a.w, b.w, c.w);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_symmetric(u: Self, v: Self)
        ensures
            u.dot_spec(v).eqv_spec(v.dot_spec(u)),
    {
        let lhs = u.dot_spec(v);
        let rhs = v.dot_spec(u);
        Scalar::lemma_mul_commutative(u.x, v.x);
        Scalar::lemma_mul_commutative(u.y, v.y);
        Scalar::lemma_mul_commutative(u.z, v.z);
        Scalar::lemma_mul_commutative(u.w, v.w);
        assert(lhs == rhs);
        Scalar::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_norm2_eqv_congruence(u: Self, v: Self)
        requires
            u.eqv_spec(v),
        ensures
            u.norm2_spec().eqv_spec(v.norm2_spec()),
    {
        let ux = u.x.mul_spec(u.x);
        let uy = u.y.mul_spec(u.y);
        let uz = u.z.mul_spec(u.z);
        let uw = u.w.mul_spec(u.w);
        let vx = v.x.mul_spec(v.x);
        let vy = v.y.mul_spec(v.y);
        let vz = v.z.mul_spec(v.z);
        let vw = v.w.mul_spec(v.w);
        let us0 = ux.add_spec(uy);
        let us1 = us0.add_spec(uz);
        let vs0 = vx.add_spec(vy);
        let vs1 = vs0.add_spec(vz);

        Scalar::lemma_eqv_mul_congruence(u.x, v.x, u.x, v.x);
        Scalar::lemma_eqv_mul_congruence(u.y, v.y, u.y, v.y);
        Scalar::lemma_eqv_mul_congruence(u.z, v.z, u.z, v.z);
        Scalar::lemma_eqv_mul_congruence(u.w, v.w, u.w, v.w);
        Scalar::lemma_eqv_add_congruence(ux, vx, uy, vy);
        assert(us0.eqv_spec(vs0));
        Scalar::lemma_eqv_add_congruence(us0, vs0, uz, vz);
        assert(us1.eqv_spec(vs1));
        Scalar::lemma_eqv_add_congruence(us1, vs1, uw, vw);
        assert(us1.add_spec(uw).eqv_spec(vs1.add_spec(vw)));
        assert(u.norm2_spec() == us1.add_spec(uw));
        assert(v.norm2_spec() == vs1.add_spec(vw));
        assert(u.norm2_spec().eqv_spec(v.norm2_spec()));
    }
}

} // verus!
