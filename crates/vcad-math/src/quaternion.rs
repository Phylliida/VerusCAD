use crate::scalar::Scalar;
use vstd::prelude::*;

verus! {

pub struct Quaternion {
    pub w: Scalar,
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
}

impl Quaternion {
    pub open spec fn from_ints_spec(w: int, x: int, y: int, z: int) -> Self {
        Quaternion {
            w: Scalar::from_int_spec(w),
            x: Scalar::from_int_spec(x),
            y: Scalar::from_int_spec(y),
            z: Scalar::from_int_spec(z),
        }
    }

    pub proof fn from_ints(w: int, x: int, y: int, z: int) -> (q: Self)
        ensures
            q == Self::from_ints_spec(w, x, y, z),
    {
        Quaternion {
            w: Scalar::from_int(w),
            x: Scalar::from_int(x),
            y: Scalar::from_int(y),
            z: Scalar::from_int(z),
        }
    }

    pub open spec fn zero_spec() -> Self {
        Self::from_ints_spec(0, 0, 0, 0)
    }

    pub open spec fn one_spec() -> Self {
        Self::from_ints_spec(1, 0, 0, 0)
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.w.eqv_spec(rhs.w)
            && self.x.eqv_spec(rhs.x)
            && self.y.eqv_spec(rhs.y)
            && self.z.eqv_spec(rhs.z)
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Quaternion {
            w: self.w.add_spec(rhs.w),
            x: self.x.add_spec(rhs.x),
            y: self.y.add_spec(rhs.y),
            z: self.z.add_spec(rhs.z),
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        Quaternion {
            w: self.w.add(rhs.w),
            x: self.x.add(rhs.x),
            y: self.y.add(rhs.y),
            z: self.z.add(rhs.z),
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Quaternion {
            w: self.w.neg_spec(),
            x: self.x.neg_spec(),
            y: self.y.neg_spec(),
            z: self.z.neg_spec(),
        }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Quaternion {
            w: self.w.neg(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Quaternion {
            w: self.w.sub_spec(rhs.w),
            x: self.x.sub_spec(rhs.x),
            y: self.y.sub_spec(rhs.y),
            z: self.z.sub_spec(rhs.z),
        }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        Quaternion {
            w: self.w.sub(rhs.w),
            x: self.x.sub(rhs.x),
            y: self.y.sub(rhs.y),
            z: self.z.sub(rhs.z),
        }
    }

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Quaternion {
            w: self.w.mul_spec(k),
            x: self.x.mul_spec(k),
            y: self.y.mul_spec(k),
            z: self.z.mul_spec(k),
        }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        Quaternion {
            w: self.w.mul(k),
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        let w = self.w.mul_spec(rhs.w)
            .sub_spec(self.x.mul_spec(rhs.x))
            .sub_spec(self.y.mul_spec(rhs.y))
            .sub_spec(self.z.mul_spec(rhs.z));
        let x = self.w.mul_spec(rhs.x)
            .add_spec(self.x.mul_spec(rhs.w))
            .add_spec(self.y.mul_spec(rhs.z))
            .sub_spec(self.z.mul_spec(rhs.y));
        let y = self.w.mul_spec(rhs.y)
            .sub_spec(self.x.mul_spec(rhs.z))
            .add_spec(self.y.mul_spec(rhs.w))
            .add_spec(self.z.mul_spec(rhs.x));
        let z = self.w.mul_spec(rhs.z)
            .add_spec(self.x.mul_spec(rhs.y))
            .sub_spec(self.y.mul_spec(rhs.x))
            .add_spec(self.z.mul_spec(rhs.w));
        Quaternion { w, x, y, z }
    }

    pub proof fn mul(self, rhs: Self) -> (out: Self)
        ensures
            out == self.mul_spec(rhs),
    {
        let ww = self.w.mul(rhs.w);
        let xx = self.x.mul(rhs.x);
        let yy = self.y.mul(rhs.y);
        let zz = self.z.mul(rhs.z);
        let w0 = ww.sub(xx);
        let w1 = w0.sub(yy);
        let w = w1.sub(zz);

        let x0 = self.w.mul(rhs.x);
        let x1 = self.x.mul(rhs.w);
        let x2 = self.y.mul(rhs.z);
        let x3 = self.z.mul(rhs.y);
        let xa = x0.add(x1);
        let xb = xa.add(x2);
        let x = xb.sub(x3);

        let y0 = self.w.mul(rhs.y);
        let y1 = self.x.mul(rhs.z);
        let y2 = self.y.mul(rhs.w);
        let y3 = self.z.mul(rhs.x);
        let ya = y0.sub(y1);
        let yb = ya.add(y2);
        let y = yb.add(y3);

        let z0 = self.w.mul(rhs.z);
        let z1 = self.x.mul(rhs.y);
        let z2 = self.y.mul(rhs.x);
        let z3 = self.z.mul(rhs.w);
        let za = z0.add(z1);
        let zb = za.sub(z2);
        let z = zb.add(z3);
        Quaternion { w, x, y, z }
    }

    pub open spec fn conjugate_spec(self) -> Self {
        Quaternion {
            w: self.w,
            x: self.x.neg_spec(),
            y: self.y.neg_spec(),
            z: self.z.neg_spec(),
        }
    }

    pub proof fn conjugate(self) -> (out: Self)
        ensures
            out == self.conjugate_spec(),
    {
        Quaternion {
            w: self.w,
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.w.mul_spec(self.w)
            .add_spec(self.x.mul_spec(self.x))
            .add_spec(self.y.mul_spec(self.y))
            .add_spec(self.z.mul_spec(self.z))
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).eqv_spec(b.add_spec(a)),
    {
        let lhs = a.add_spec(b);
        let rhs = b.add_spec(a);
        Scalar::lemma_add_commutative(a.w, b.w);
        Scalar::lemma_add_commutative(a.x, b.x);
        Scalar::lemma_add_commutative(a.y, b.y);
        Scalar::lemma_add_commutative(a.z, b.z);
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).eqv_spec(a.add_spec(b.add_spec(c))),
    {
        let lhs = a.add_spec(b).add_spec(c);
        let rhs = a.add_spec(b.add_spec(c));
        Scalar::lemma_add_associative(a.w, b.w, c.w);
        Scalar::lemma_add_associative(a.x, b.x, c.x);
        Scalar::lemma_add_associative(a.y, b.y, c.y);
        Scalar::lemma_add_associative(a.z, b.z, c.z);
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()).eqv_spec(Self::zero_spec()),
            a.neg_spec().add_spec(a).eqv_spec(Self::zero_spec()),
    {
        let z = Self::zero_spec();
        let lhs = a.add_spec(a.neg_spec());
        let rhs = a.neg_spec().add_spec(a);
        Scalar::lemma_add_inverse(a.w);
        Scalar::lemma_add_inverse(a.x);
        Scalar::lemma_add_inverse(a.y);
        Scalar::lemma_add_inverse(a.z);
        assert(lhs.w.eqv_spec(z.w));
        assert(lhs.x.eqv_spec(z.x));
        assert(lhs.y.eqv_spec(z.y));
        assert(lhs.z.eqv_spec(z.z));
        assert(rhs.w.eqv_spec(z.w));
        assert(rhs.x.eqv_spec(z.x));
        assert(rhs.y.eqv_spec(z.y));
        assert(rhs.z.eqv_spec(z.z));
        assert(lhs.eqv_spec(z));
        assert(rhs.eqv_spec(z));
    }

    pub proof fn lemma_conjugate_involution(q: Self)
        ensures
            q.conjugate_spec().conjugate_spec() == q,
    {
        Scalar::lemma_neg_involution(q.x);
        Scalar::lemma_neg_involution(q.y);
        Scalar::lemma_neg_involution(q.z);
        assert(q.conjugate_spec().conjugate_spec().w == q.w);
        assert(q.conjugate_spec().conjugate_spec().x == q.x);
        assert(q.conjugate_spec().conjugate_spec().y == q.y);
        assert(q.conjugate_spec().conjugate_spec().z == q.z);
        assert(q.conjugate_spec().conjugate_spec() == q);
    }
}

} // verus!
