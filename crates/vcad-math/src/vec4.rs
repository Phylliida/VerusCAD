use crate::scalar::Scalar;
use crate::vec3::Vec3;
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

    pub open spec fn xyz_spec(self) -> Vec3 {
        Vec3 { x: self.x, y: self.y, z: self.z }
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

    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        Scalar::lemma_eqv_reflexive(a.x);
        Scalar::lemma_eqv_reflexive(a.y);
        Scalar::lemma_eqv_reflexive(a.z);
        Scalar::lemma_eqv_reflexive(a.w);
        assert(a.eqv_spec(a));
    }

    pub proof fn lemma_scale_eqv_congruence(u: Self, v: Self, k: Scalar)
        requires
            u.eqv_spec(v),
        ensures
            u.scale_spec(k).eqv_spec(v.scale_spec(k)),
    {
        let us = u.scale_spec(k);
        let vs = v.scale_spec(k);
        Scalar::lemma_eqv_mul_congruence_left(u.x, v.x, k);
        Scalar::lemma_eqv_mul_congruence_left(u.y, v.y, k);
        Scalar::lemma_eqv_mul_congruence_left(u.z, v.z, k);
        Scalar::lemma_eqv_mul_congruence_left(u.w, v.w, k);
        assert(us.x.eqv_spec(vs.x));
        assert(us.y.eqv_spec(vs.y));
        assert(us.z.eqv_spec(vs.z));
        assert(us.w.eqv_spec(vs.w));
        assert(us.eqv_spec(vs));
    }

    pub proof fn lemma_dot_eqv_congruence(u1: Self, u2: Self, v1: Self, v2: Self)
        requires
            u1.x.eqv_spec(u2.x),
            u1.y.eqv_spec(u2.y),
            u1.z.eqv_spec(u2.z),
            u1.w.eqv_spec(u2.w),
            v1.x.eqv_spec(v2.x),
            v1.y.eqv_spec(v2.y),
            v1.z.eqv_spec(v2.z),
            v1.w.eqv_spec(v2.w),
        ensures
            u1.dot_spec(v1).eqv_spec(u2.dot_spec(v2)),
    {
        let a1 = u1.x.mul_spec(v1.x);
        let b1 = u1.y.mul_spec(v1.y);
        let c1 = u1.z.mul_spec(v1.z);
        let d1 = u1.w.mul_spec(v1.w);
        let a2 = u2.x.mul_spec(v2.x);
        let b2 = u2.y.mul_spec(v2.y);
        let c2 = u2.z.mul_spec(v2.z);
        let d2 = u2.w.mul_spec(v2.w);
        let s10 = a1.add_spec(b1);
        let s11 = s10.add_spec(c1);
        let s20 = a2.add_spec(b2);
        let s21 = s20.add_spec(c2);

        Scalar::lemma_eqv_mul_congruence(u1.x, u2.x, v1.x, v2.x);
        Scalar::lemma_eqv_mul_congruence(u1.y, u2.y, v1.y, v2.y);
        Scalar::lemma_eqv_mul_congruence(u1.z, u2.z, v1.z, v2.z);
        Scalar::lemma_eqv_mul_congruence(u1.w, u2.w, v1.w, v2.w);
        assert(a1.eqv_spec(a2));
        assert(b1.eqv_spec(b2));
        assert(c1.eqv_spec(c2));
        assert(d1.eqv_spec(d2));
        Scalar::lemma_eqv_add_congruence(a1, a2, b1, b2);
        assert(s10.eqv_spec(s20));
        Scalar::lemma_eqv_add_congruence(s10, s20, c1, c2);
        assert(s11.eqv_spec(s21));
        Scalar::lemma_eqv_add_congruence(s11, s21, d1, d2);
        assert(s11.add_spec(d1).eqv_spec(s21.add_spec(d2)));
        assert(u1.dot_spec(v1) == s11.add_spec(d1));
        assert(u2.dot_spec(v2) == s21.add_spec(d2));
        assert(u1.dot_spec(v1).eqv_spec(u2.dot_spec(v2)));
    }

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Self::zero_spec()) == a,
            Self::zero_spec().add_spec(a) == a,
    {
        let z = Self::zero_spec();
        Scalar::lemma_add_zero_identity(a.x);
        Scalar::lemma_add_zero_identity(a.y);
        Scalar::lemma_add_zero_identity(a.z);
        Scalar::lemma_add_zero_identity(a.w);
        assert(a.add_spec(z).x == a.x);
        assert(a.add_spec(z).y == a.y);
        assert(a.add_spec(z).z == a.z);
        assert(a.add_spec(z).w == a.w);
        assert(a.add_spec(z) == a);
        assert(z.add_spec(a).x == a.x);
        assert(z.add_spec(a).y == a.y);
        assert(z.add_spec(a).z == a.z);
        assert(z.add_spec(a).w == a.w);
        assert(z.add_spec(a) == a);
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()).eqv_spec(Self::zero_spec()),
            a.neg_spec().add_spec(a).eqv_spec(Self::zero_spec()),
    {
        let z = Self::zero_spec();
        let lhs = a.add_spec(a.neg_spec());
        let rhs = a.neg_spec().add_spec(a);
        Scalar::lemma_add_inverse(a.x);
        Scalar::lemma_add_inverse(a.y);
        Scalar::lemma_add_inverse(a.z);
        Scalar::lemma_add_inverse(a.w);
        assert(lhs.x.eqv_spec(z.x));
        assert(lhs.y.eqv_spec(z.y));
        assert(lhs.z.eqv_spec(z.z));
        assert(lhs.w.eqv_spec(z.w));
        assert(rhs.x.eqv_spec(z.x));
        assert(rhs.y.eqv_spec(z.y));
        assert(rhs.z.eqv_spec(z.z));
        assert(rhs.w.eqv_spec(z.w));
        assert(lhs.eqv_spec(z));
        assert(rhs.eqv_spec(z));
    }

    pub proof fn lemma_neg_involution(a: Self)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        assert(a.neg_spec().neg_spec().x.num == -(-a.x.num));
        assert(a.neg_spec().neg_spec().y.num == -(-a.y.num));
        assert(a.neg_spec().neg_spec().z.num == -(-a.z.num));
        assert(a.neg_spec().neg_spec().w.num == -(-a.w.num));
        assert(a.neg_spec().neg_spec().x.num == a.x.num);
        assert(a.neg_spec().neg_spec().y.num == a.y.num);
        assert(a.neg_spec().neg_spec().z.num == a.z.num);
        assert(a.neg_spec().neg_spec().w.num == a.w.num);
        assert(a.neg_spec().neg_spec().x.den == a.x.den);
        assert(a.neg_spec().neg_spec().y.den == a.y.den);
        assert(a.neg_spec().neg_spec().z.den == a.z.den);
        assert(a.neg_spec().neg_spec().w.den == a.w.den);
        assert(a.neg_spec().neg_spec() == a);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        Scalar::lemma_sub_is_add_neg(a.x, b.x);
        Scalar::lemma_sub_is_add_neg(a.y, b.y);
        Scalar::lemma_sub_is_add_neg(a.z, b.z);
        Scalar::lemma_sub_is_add_neg(a.w, b.w);
        assert(a.sub_spec(b).x == a.add_spec(b.neg_spec()).x);
        assert(a.sub_spec(b).y == a.add_spec(b.neg_spec()).y);
        assert(a.sub_spec(b).z == a.add_spec(b.neg_spec()).z);
        assert(a.sub_spec(b).w == a.add_spec(b.neg_spec()).w);
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
    }

    pub proof fn lemma_scale_zero(v: Self)
        ensures
            v.scale_spec(Scalar::from_int_spec(0)).eqv_spec(Self::zero_spec()),
    {
        let z = Self::zero_spec();
        let s = v.scale_spec(Scalar::from_int_spec(0));
        Scalar::lemma_mul_zero(v.x);
        Scalar::lemma_mul_zero(v.y);
        Scalar::lemma_mul_zero(v.z);
        Scalar::lemma_mul_zero(v.w);
        assert(s.x.eqv_spec(z.x));
        assert(s.y.eqv_spec(z.y));
        assert(s.z.eqv_spec(z.z));
        assert(s.w.eqv_spec(z.w));
        assert(s.eqv_spec(z));
    }

    pub proof fn lemma_scale_one_identity(v: Self)
        ensures
            v.scale_spec(Scalar::from_int_spec(1)) == v,
    {
        let s = v.scale_spec(Scalar::from_int_spec(1));
        Scalar::lemma_mul_one_identity(v.x);
        Scalar::lemma_mul_one_identity(v.y);
        Scalar::lemma_mul_one_identity(v.z);
        Scalar::lemma_mul_one_identity(v.w);
        assert(s.x == v.x);
        assert(s.y == v.y);
        assert(s.z == v.z);
        assert(s.w == v.w);
        assert(s == v);
    }

    pub proof fn lemma_scale_associative(v: Self, k1: Scalar, k2: Scalar)
        ensures
            v.scale_spec(k1).scale_spec(k2).eqv_spec(v.scale_spec(k1.mul_spec(k2))),
    {
        let lhs = v.scale_spec(k1).scale_spec(k2);
        let rhs = v.scale_spec(k1.mul_spec(k2));
        Scalar::lemma_mul_associative(v.x, k1, k2);
        Scalar::lemma_mul_associative(v.y, k1, k2);
        Scalar::lemma_mul_associative(v.z, k1, k2);
        Scalar::lemma_mul_associative(v.w, k1, k2);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_distributes_over_vec_add(u: Self, v: Self, k: Scalar)
        ensures
            u.add_spec(v).scale_spec(k).eqv_spec(u.scale_spec(k).add_spec(v.scale_spec(k))),
    {
        let lhs = u.add_spec(v).scale_spec(k);
        let rhs = u.scale_spec(k).add_spec(v.scale_spec(k));

        Scalar::lemma_mul_commutative(u.x.add_spec(v.x), k);
        Scalar::lemma_mul_distributes_over_add(k, u.x, v.x);
        Scalar::lemma_mul_commutative(k, u.x);
        Scalar::lemma_mul_commutative(k, v.x);
        assert(lhs.x == k.mul_spec(u.x.add_spec(v.x)));
        assert(k.mul_spec(u.x.add_spec(v.x)).eqv_spec(k.mul_spec(u.x).add_spec(k.mul_spec(v.x))));
        assert(k.mul_spec(u.x).add_spec(k.mul_spec(v.x)) == rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        Scalar::lemma_mul_commutative(u.y.add_spec(v.y), k);
        Scalar::lemma_mul_distributes_over_add(k, u.y, v.y);
        Scalar::lemma_mul_commutative(k, u.y);
        Scalar::lemma_mul_commutative(k, v.y);
        assert(lhs.y == k.mul_spec(u.y.add_spec(v.y)));
        assert(k.mul_spec(u.y.add_spec(v.y)).eqv_spec(k.mul_spec(u.y).add_spec(k.mul_spec(v.y))));
        assert(k.mul_spec(u.y).add_spec(k.mul_spec(v.y)) == rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        Scalar::lemma_mul_commutative(u.z.add_spec(v.z), k);
        Scalar::lemma_mul_distributes_over_add(k, u.z, v.z);
        Scalar::lemma_mul_commutative(k, u.z);
        Scalar::lemma_mul_commutative(k, v.z);
        assert(lhs.z == k.mul_spec(u.z.add_spec(v.z)));
        assert(k.mul_spec(u.z.add_spec(v.z)).eqv_spec(k.mul_spec(u.z).add_spec(k.mul_spec(v.z))));
        assert(k.mul_spec(u.z).add_spec(k.mul_spec(v.z)) == rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        Scalar::lemma_mul_commutative(u.w.add_spec(v.w), k);
        Scalar::lemma_mul_distributes_over_add(k, u.w, v.w);
        Scalar::lemma_mul_commutative(k, u.w);
        Scalar::lemma_mul_commutative(k, v.w);
        assert(lhs.w == k.mul_spec(u.w.add_spec(v.w)));
        assert(k.mul_spec(u.w.add_spec(v.w)).eqv_spec(k.mul_spec(u.w).add_spec(k.mul_spec(v.w))));
        assert(k.mul_spec(u.w).add_spec(k.mul_spec(v.w)) == rhs.w);
        assert(lhs.w.eqv_spec(rhs.w));

        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_distributes_over_scalar_add(v: Self, a: Scalar, b: Scalar)
        ensures
            v.scale_spec(a.add_spec(b)).eqv_spec(v.scale_spec(a).add_spec(v.scale_spec(b))),
    {
        let lhs = v.scale_spec(a.add_spec(b));
        let rhs = v.scale_spec(a).add_spec(v.scale_spec(b));
        Scalar::lemma_mul_distributes_over_add(v.x, a, b);
        Scalar::lemma_mul_distributes_over_add(v.y, a, b);
        Scalar::lemma_mul_distributes_over_add(v.z, a, b);
        Scalar::lemma_mul_distributes_over_add(v.w, a, b);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_neg_vector(v: Self, k: Scalar)
        ensures
            v.neg_spec().scale_spec(k) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.neg_spec().scale_spec(k);
        let rhs = v.scale_spec(k).neg_spec();
        Scalar::lemma_mul_commutative(v.x.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.x);
        Scalar::lemma_mul_commutative(k, v.x);
        assert(lhs.x == rhs.x);

        Scalar::lemma_mul_commutative(v.y.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.y);
        Scalar::lemma_mul_commutative(k, v.y);
        assert(lhs.y == rhs.y);

        Scalar::lemma_mul_commutative(v.z.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.z);
        Scalar::lemma_mul_commutative(k, v.z);
        assert(lhs.z == rhs.z);

        Scalar::lemma_mul_commutative(v.w.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.w);
        Scalar::lemma_mul_commutative(k, v.w);
        assert(lhs.w == rhs.w);

        assert(lhs == rhs);
    }

    pub proof fn lemma_scale_neg_scalar(v: Self, k: Scalar)
        ensures
            v.scale_spec(k.neg_spec()) == v.scale_spec(k).neg_spec(),
    {
        let lhs = v.scale_spec(k.neg_spec());
        let rhs = v.scale_spec(k).neg_spec();
        Scalar::lemma_mul_neg_right(v.x, k);
        Scalar::lemma_mul_neg_right(v.y, k);
        Scalar::lemma_mul_neg_right(v.z, k);
        Scalar::lemma_mul_neg_right(v.w, k);
        assert(lhs.x == rhs.x);
        assert(lhs.y == rhs.y);
        assert(lhs.z == rhs.z);
        assert(lhs.w == rhs.w);
        assert(lhs == rhs);
    }

    pub proof fn lemma_dot_decompose(u: Self, v: Self)
        ensures
            u.dot_spec(v).eqv_spec(u.xyz_spec().dot_spec(v.xyz_spec()).add_spec(u.w.mul_spec(v.w))),
    {
        let lhs = u.dot_spec(v);
        let rhs = u.xyz_spec().dot_spec(v.xyz_spec()).add_spec(u.w.mul_spec(v.w));
        assert(lhs == rhs);
        Scalar::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.dot_spec(v.add_spec(w)).eqv_spec(u.dot_spec(v).add_spec(u.dot_spec(w))),
    {
        let uvw = v.add_spec(w);
        let u3 = u.xyz_spec();
        let v3 = v.xyz_spec();
        let w3 = w.xyz_spec();
        let uvw3 = uvw.xyz_spec();

        let lhs = u.dot_spec(uvw);
        let lhs3 = u3.dot_spec(uvw3);
        let lhsw = u.w.mul_spec(uvw.w);

        let rhs = u.dot_spec(v).add_spec(u.dot_spec(w));
        let r3 = u3.dot_spec(v3).add_spec(u3.dot_spec(w3));
        let rw = u.w.mul_spec(v.w).add_spec(u.w.mul_spec(w.w));

        assert(uvw3 == v3.add_spec(w3));
        assert(uvw.w == v.w.add_spec(w.w));
        Self::lemma_dot_decompose(u, uvw);
        assert(lhs.eqv_spec(lhs3.add_spec(lhsw)));
        Vec3::lemma_dot_linear_right(u3, v3, w3);
        Scalar::lemma_mul_distributes_over_add(u.w, v.w, w.w);
        assert(lhs3.eqv_spec(r3));
        assert(lhsw.eqv_spec(rw));
        Scalar::lemma_eqv_add_congruence(lhs3, r3, lhsw, rw);
        assert(lhs3.add_spec(lhsw).eqv_spec(r3.add_spec(rw)));

        Self::lemma_dot_decompose(u, v);
        Self::lemma_dot_decompose(u, w);
        assert(u.dot_spec(v).eqv_spec(u3.dot_spec(v3).add_spec(u.w.mul_spec(v.w))));
        assert(u.dot_spec(w).eqv_spec(u3.dot_spec(w3).add_spec(u.w.mul_spec(w.w))));
        Scalar::lemma_eqv_add_congruence(
            u.dot_spec(v),
            u3.dot_spec(v3).add_spec(u.w.mul_spec(v.w)),
            u.dot_spec(w),
            u3.dot_spec(w3).add_spec(u.w.mul_spec(w.w)),
        );
        assert(rhs.eqv_spec(
            u3.dot_spec(v3).add_spec(u.w.mul_spec(v.w)).add_spec(
                u3.dot_spec(w3).add_spec(u.w.mul_spec(w.w)),
            ),
        ));
        Scalar::lemma_add_rearrange_2x2(u3.dot_spec(v3), u.w.mul_spec(v.w), u3.dot_spec(w3), u.w.mul_spec(w.w));
        assert(
            u3.dot_spec(v3).add_spec(u.w.mul_spec(v.w)).add_spec(
                u3.dot_spec(w3).add_spec(u.w.mul_spec(w.w)),
            ).eqv_spec(r3.add_spec(rw))
        );
        Scalar::lemma_eqv_transitive(
            rhs,
            u3.dot_spec(v3).add_spec(u.w.mul_spec(v.w)).add_spec(
                u3.dot_spec(w3).add_spec(u.w.mul_spec(w.w)),
            ),
            r3.add_spec(rw),
        );
        assert(rhs.eqv_spec(r3.add_spec(rw)));

        Scalar::lemma_eqv_transitive(lhs, lhs3.add_spec(lhsw), r3.add_spec(rw));
        Scalar::lemma_eqv_symmetric(rhs, r3.add_spec(rw));
        Scalar::lemma_eqv_transitive(lhs, r3.add_spec(rw), rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).dot_spec(w).eqv_spec(u.dot_spec(w).add_spec(v.dot_spec(w))),
    {
        let lhs = u.add_spec(v).dot_spec(w);
        let mid = w.dot_spec(u.add_spec(v));
        let rhs0 = w.dot_spec(u).add_spec(w.dot_spec(v));
        let rhs = u.dot_spec(w).add_spec(v.dot_spec(w));

        Self::lemma_dot_symmetric(u.add_spec(v), w);
        assert(lhs.eqv_spec(mid));
        Self::lemma_dot_linear_right(w, u, v);
        assert(mid.eqv_spec(rhs0));
        Self::lemma_dot_symmetric(w, u);
        Self::lemma_dot_symmetric(w, v);
        Scalar::lemma_eqv_add_congruence(w.dot_spec(u), u.dot_spec(w), w.dot_spec(v), v.dot_spec(w));
        assert(rhs0.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs0);
        Scalar::lemma_eqv_transitive(lhs, rhs0, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).dot_spec(w).eqv_spec(k.mul_spec(v.dot_spec(w))),
    {
        let v3 = v.xyz_spec();
        let w3 = w.xyz_spec();
        let lhs = v.scale_spec(k).dot_spec(w);
        let lhs3 = v3.scale_spec(k).dot_spec(w3);
        let lhsw = v.w.mul_spec(k).mul_spec(w.w);
        let a = v3.dot_spec(w3);
        let b = v.w.mul_spec(w.w);
        let rhs = k.mul_spec(v.dot_spec(w));
        let ka = k.mul_spec(a);
        let kb = k.mul_spec(b);

        Self::lemma_dot_decompose(v.scale_spec(k), w);
        assert(v.scale_spec(k).xyz_spec() == v3.scale_spec(k));
        assert(lhs.eqv_spec(lhs3.add_spec(lhsw)));
        Vec3::lemma_dot_scale_extract_left(v3, w3, k);
        assert(lhs3.eqv_spec(ka));
        Scalar::lemma_mul_commutative(v.w, k);
        assert(lhsw == k.mul_spec(v.w).mul_spec(w.w));
        Scalar::lemma_mul_associative(k, v.w, w.w);
        assert(lhsw.eqv_spec(kb));
        Scalar::lemma_eqv_add_congruence(lhs3, ka, lhsw, kb);
        assert(lhs3.add_spec(lhsw).eqv_spec(ka.add_spec(kb)));

        Self::lemma_dot_decompose(v, w);
        assert(v.dot_spec(w).eqv_spec(a.add_spec(b)));
        Scalar::lemma_eqv_mul_congruence_right(k, v.dot_spec(w), a.add_spec(b));
        assert(rhs.eqv_spec(k.mul_spec(a.add_spec(b))));
        Scalar::lemma_mul_distributes_over_add(k, a, b);
        assert(k.mul_spec(a.add_spec(b)).eqv_spec(ka.add_spec(kb)));
        Scalar::lemma_eqv_transitive(rhs, k.mul_spec(a.add_spec(b)), ka.add_spec(kb));
        assert(rhs.eqv_spec(ka.add_spec(kb)));

        Scalar::lemma_eqv_transitive(lhs, lhs3.add_spec(lhsw), ka.add_spec(kb));
        Scalar::lemma_eqv_symmetric(rhs, ka.add_spec(kb));
        Scalar::lemma_eqv_transitive(lhs, ka.add_spec(kb), rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_scale_extract_right(v: Self, w: Self, k: Scalar)
        ensures
            v.dot_spec(w.scale_spec(k)).eqv_spec(k.mul_spec(v.dot_spec(w))),
    {
        let lhs = v.dot_spec(w.scale_spec(k));
        let mid = w.scale_spec(k).dot_spec(v);
        let rhs = k.mul_spec(v.dot_spec(w));
        Self::lemma_dot_symmetric(v, w.scale_spec(k));
        assert(lhs.eqv_spec(mid));
        Self::lemma_dot_scale_extract_left(w, v, k);
        assert(mid.eqv_spec(k.mul_spec(w.dot_spec(v))));
        Self::lemma_dot_symmetric(w, v);
        Scalar::lemma_eqv_mul_congruence_right(k, w.dot_spec(v), v.dot_spec(w));
        assert(k.mul_spec(w.dot_spec(v)).eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, k.mul_spec(w.dot_spec(v)));
        Scalar::lemma_eqv_transitive(lhs, k.mul_spec(w.dot_spec(v)), rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_norm2_scale(v: Self, k: Scalar)
        ensures
            v.scale_spec(k).norm2_spec().eqv_spec(k.mul_spec(k).mul_spec(v.norm2_spec())),
    {
        let lhs = v.scale_spec(k).norm2_spec();
        let d0 = v.dot_spec(v.scale_spec(k));
        let d1 = v.scale_spec(k).dot_spec(v);
        let n = v.norm2_spec();
        let k_d0 = k.mul_spec(d0);
        let k_d1 = k.mul_spec(d1);
        let kn = k.mul_spec(n);
        let k_kn = k.mul_spec(kn);
        let kk_n = k.mul_spec(k).mul_spec(n);

        Self::lemma_dot_scale_extract_left(v, v.scale_spec(k), k);
        assert(lhs.eqv_spec(k_d0));
        Self::lemma_dot_symmetric(v, v.scale_spec(k));
        assert(d0.eqv_spec(d1));
        Scalar::lemma_eqv_mul_congruence_right(k, d0, d1);
        assert(k_d0.eqv_spec(k_d1));
        Self::lemma_dot_scale_extract_left(v, v, k);
        assert(d1.eqv_spec(kn));
        Scalar::lemma_eqv_mul_congruence_right(k, d1, kn);
        assert(k_d1.eqv_spec(k_kn));
        Scalar::lemma_mul_associative(k, k, n);
        assert(kk_n.eqv_spec(k_kn));
        Scalar::lemma_eqv_symmetric(kk_n, k_kn);
        assert(k_kn.eqv_spec(kk_n));
        Scalar::lemma_eqv_transitive(lhs, k_d0, k_d1);
        Scalar::lemma_eqv_transitive(lhs, k_d1, k_kn);
        Scalar::lemma_eqv_transitive(lhs, k_kn, kk_n);
        assert(lhs.eqv_spec(kk_n));
    }

    pub proof fn lemma_norm2_neg_invariant(v: Self)
        ensures
            v.neg_spec().norm2_spec().eqv_spec(v.norm2_spec()),
    {
        let nx = v.x.neg_spec().mul_spec(v.x.neg_spec());
        let ny = v.y.neg_spec().mul_spec(v.y.neg_spec());
        let nz = v.z.neg_spec().mul_spec(v.z.neg_spec());
        let nw = v.w.neg_spec().mul_spec(v.w.neg_spec());
        let x2 = v.x.mul_spec(v.x);
        let y2 = v.y.mul_spec(v.y);
        let z2 = v.z.mul_spec(v.z);
        let w2 = v.w.mul_spec(v.w);
        let nn = v.neg_spec().norm2_spec();
        let n = v.norm2_spec();

        assert(nx.num == (-v.x.num) * (-v.x.num));
        assert((-v.x.num) * (-v.x.num) == v.x.num * v.x.num) by (nonlinear_arith);
        assert(nx == x2);
        assert(ny.num == (-v.y.num) * (-v.y.num));
        assert((-v.y.num) * (-v.y.num) == v.y.num * v.y.num) by (nonlinear_arith);
        assert(ny == y2);
        assert(nz.num == (-v.z.num) * (-v.z.num));
        assert((-v.z.num) * (-v.z.num) == v.z.num * v.z.num) by (nonlinear_arith);
        assert(nz == z2);
        assert(nw.num == (-v.w.num) * (-v.w.num));
        assert((-v.w.num) * (-v.w.num) == v.w.num * v.w.num) by (nonlinear_arith);
        assert(nw == w2);

        assert(nn == nx.add_spec(ny).add_spec(nz).add_spec(nw));
        assert(n == x2.add_spec(y2).add_spec(z2).add_spec(w2));
        assert(nn == n);
        Scalar::lemma_eqv_reflexive(n);
        assert(nn.eqv_spec(n));
    }

    pub proof fn lemma_norm2_nonnegative(v: Self)
        ensures
            Scalar::from_int_spec(0).le_spec(v.norm2_spec()),
    {
        let z = Scalar::from_int_spec(0);
        let n = v.norm2_spec();
        let xyz = v.xyz_spec();
        let s = xyz.norm2_spec();
        let ww = v.w.mul_spec(v.w);
        assert(n == s.add_spec(ww));

        Vec3::lemma_norm2_nonnegative(xyz);
        assert(z.le_spec(s));
        assert(z.le_spec(s) == (z.num * s.denom() <= s.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(s) == (0 * s.denom() <= s.num * 1));
        assert(0 * s.denom() == 0);
        assert(s.num * 1 == s.num);
        assert(0 <= s.num);
        assert(s.num >= 0);

        assert(ww.num == v.w.num * v.w.num);
        Scalar::lemma_denom_positive(ww);
        Scalar::lemma_denom_positive(s);
        assert(v.w.num * v.w.num >= 0) by (nonlinear_arith);
        assert(ww.num >= 0);
        assert((s.num >= 0 && ww.denom() > 0) ==> (s.num * ww.denom() >= 0)) by (nonlinear_arith);
        assert((ww.num >= 0 && s.denom() > 0) ==> (ww.num * s.denom() >= 0)) by (nonlinear_arith);
        let a = s.num * ww.denom();
        let b = ww.num * s.denom();
        assert(a >= 0);
        assert(b >= 0);
        assert(n.num == s.num * ww.denom() + ww.num * s.denom());
        assert((a >= 0 && b >= 0) ==> (a + b >= 0)) by (nonlinear_arith);
        assert(a + b >= 0);
        assert(n.num == a + b);
        assert(n.num >= 0);
        assert(z.le_spec(n) == (z.num * n.denom() <= n.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(n) == (0 * n.denom() <= n.num * 1));
        assert(0 * n.denom() == 0);
        assert(n.num * 1 == n.num);
        assert(z.le_spec(n));
    }

    pub proof fn lemma_norm2_zero_iff_zero(v: Self)
        ensures
            v.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == v.eqv_spec(Self::zero_spec()),
    {
        let z = Scalar::from_int_spec(0);
        let zv = Self::zero_spec();
        let n = v.norm2_spec();
        let xyz = v.xyz_spec();
        let s = xyz.norm2_spec();
        let ww = v.w.mul_spec(v.w);
        let z3 = Vec3::zero_spec();

        assert(zv.x == z);
        assert(zv.y == z);
        assert(zv.z == z);
        assert(zv.w == z);
        assert(z3.x == z);
        assert(z3.y == z);
        assert(z3.z == z);
        assert(n == s.add_spec(ww));

        if n.eqv_spec(z) {
            Scalar::lemma_eqv_zero_iff_num_zero(n);
            assert(n.eqv_spec(z) == (n.num == 0));
            assert(n.num == 0);
            assert(n.num == s.num * ww.denom() + ww.num * s.denom());

            Vec3::lemma_norm2_nonnegative(xyz);
            assert(z.le_spec(s));
            assert(z.le_spec(s) == (z.num * s.denom() <= s.num * z.denom()));
            assert(z.num == 0);
            assert(z.denom() == 1);
            assert(z.le_spec(s) == (0 * s.denom() <= s.num * 1));
            assert(0 * s.denom() == 0);
            assert(s.num * 1 == s.num);
            assert(0 <= s.num);
            assert(s.num >= 0);

            assert(ww.num == v.w.num * v.w.num);
            Scalar::lemma_denom_positive(ww);
            Scalar::lemma_denom_positive(s);
            assert(v.w.num * v.w.num >= 0) by (nonlinear_arith);
            assert(ww.num >= 0);
            assert((s.num >= 0 && ww.denom() > 0) ==> (s.num * ww.denom() >= 0)) by (nonlinear_arith);
            assert((ww.num >= 0 && s.denom() > 0) ==> (ww.num * s.denom() >= 0)) by (nonlinear_arith);
            assert(s.num * ww.denom() >= 0);
            assert(ww.num * s.denom() >= 0);
            assert((s.num * ww.denom() >= 0
                && ww.num * s.denom() >= 0
                && s.num * ww.denom() + ww.num * s.denom() == 0)
                ==> (s.num * ww.denom() == 0 && ww.num * s.denom() == 0))
                by (nonlinear_arith);
            assert(s.num * ww.denom() == 0);
            assert(ww.num * s.denom() == 0);
            assert((ww.denom() > 0 && s.num * ww.denom() == 0) ==> s.num == 0) by (nonlinear_arith);
            assert((s.denom() > 0 && ww.num * s.denom() == 0) ==> ww.num == 0) by (nonlinear_arith);
            assert(s.num == 0);
            assert(ww.num == 0);

            assert((v.w.num * v.w.num == 0) ==> v.w.num == 0) by (nonlinear_arith);
            assert(v.w.num == 0);

            Scalar::lemma_eqv_zero_iff_num_zero(s);
            Scalar::lemma_eqv_zero_iff_num_zero(v.w);
            assert(s.eqv_spec(z) == (s.num == 0));
            assert(v.w.eqv_spec(z) == (v.w.num == 0));
            assert(s.eqv_spec(z));
            assert(v.w.eqv_spec(z));

            Vec3::lemma_norm2_zero_iff_zero(xyz);
            assert(s.eqv_spec(z) == xyz.eqv_spec(z3));
            assert(xyz.eqv_spec(z3));
            assert(xyz.x.eqv_spec(z3.x));
            assert(xyz.y.eqv_spec(z3.y));
            assert(xyz.z.eqv_spec(z3.z));
            assert(v.x.eqv_spec(z));
            assert(v.y.eqv_spec(z));
            assert(v.z.eqv_spec(z));
            assert(v.eqv_spec(zv));
        }

        if v.eqv_spec(zv) {
            assert(v.x.eqv_spec(z));
            assert(v.y.eqv_spec(z));
            assert(v.z.eqv_spec(z));
            assert(v.w.eqv_spec(z));
            Vec3::lemma_eqv_from_components(xyz, z3);
            assert(xyz.eqv_spec(z3));
            Vec3::lemma_norm2_zero_iff_zero(xyz);
            assert(s.eqv_spec(z) == xyz.eqv_spec(z3));
            assert(s.eqv_spec(z));

            Scalar::lemma_eqv_zero_iff_num_zero(v.w);
            assert(v.w.eqv_spec(z) == (v.w.num == 0));
            assert(v.w.num == 0);
            assert(ww.num == v.w.num * v.w.num);
            Scalar::lemma_mul_right_zero_num(v.w, v.w);
            assert(v.w.mul_spec(v.w).num == 0);
            assert(ww.num == v.w.mul_spec(v.w).num);
            assert(ww.num == 0);
            Scalar::lemma_eqv_zero_iff_num_zero(ww);
            assert(ww.eqv_spec(z) == (ww.num == 0));
            assert(ww.eqv_spec(z));

            Scalar::lemma_eqv_add_congruence(s, z, ww, z);
            assert(s.add_spec(ww).eqv_spec(z.add_spec(z)));
            Scalar::lemma_add_zero_identity(z);
            assert(z.add_spec(z) == z);
            Scalar::lemma_eqv_reflexive(z);
            assert(z.add_spec(z).eqv_spec(z));
            Scalar::lemma_eqv_transitive(s.add_spec(ww), z.add_spec(z), z);
            assert(n.eqv_spec(z));
        }
        assert((n.eqv_spec(z)) == v.eqv_spec(zv));
    }
}

} // verus!
