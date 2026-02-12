use crate::scalar::Scalar;
use crate::vec2::Vec2;
use vstd::prelude::*;

verus! {

pub struct Vec3 {
    pub x: Scalar,
    pub y: Scalar,
    pub z: Scalar,
}

impl Vec3 {
    pub open spec fn from_ints_spec(x: int, y: int, z: int) -> Self {
        Vec3 {
            x: Scalar::from_int_spec(x),
            y: Scalar::from_int_spec(y),
            z: Scalar::from_int_spec(z),
        }
    }

    pub proof fn from_ints(x: int, y: int, z: int) -> (v: Self)
        ensures
            v == Self::from_ints_spec(x, y, z),
    {
        Vec3 {
            x: Scalar::from_int(x),
            y: Scalar::from_int(y),
            z: Scalar::from_int(z),
        }
    }

    pub open spec fn zero_spec() -> Self {
        Self::from_ints_spec(0, 0, 0)
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.x.eqv_spec(rhs.x) && self.y.eqv_spec(rhs.y) && self.z.eqv_spec(rhs.z)
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        Vec3 {
            x: self.x.add_spec(rhs.x),
            y: self.y.add_spec(rhs.y),
            z: self.z.add_spec(rhs.z),
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        Vec3 {
            x: self.x.add(rhs.x),
            y: self.y.add(rhs.y),
            z: self.z.add(rhs.z),
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Vec3 {
            x: self.x.neg_spec(),
            y: self.y.neg_spec(),
            z: self.z.neg_spec(),
        }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Vec3 {
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        Vec3 {
            x: self.x.sub_spec(rhs.x),
            y: self.y.sub_spec(rhs.y),
            z: self.z.sub_spec(rhs.z),
        }
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        Vec3 {
            x: self.x.sub(rhs.x),
            y: self.y.sub(rhs.y),
            z: self.z.sub(rhs.z),
        }
    }

    pub open spec fn scale_spec(self, k: Scalar) -> Self {
        Vec3 {
            x: self.x.mul_spec(k),
            y: self.y.mul_spec(k),
            z: self.z.mul_spec(k),
        }
    }

    pub proof fn scale(self, k: Scalar) -> (out: Self)
        ensures
            out == self.scale_spec(k),
    {
        Vec3 {
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    pub open spec fn dot_spec(self, rhs: Self) -> Scalar {
        self.x.mul_spec(rhs.x).add_spec(self.y.mul_spec(rhs.y)).add_spec(self.z.mul_spec(rhs.z))
    }

    pub proof fn dot(self, rhs: Self) -> (out: Scalar)
        ensures
            out == self.dot_spec(rhs),
    {
        let xx = self.x.mul(rhs.x);
        let yy = self.y.mul(rhs.y);
        let zz = self.z.mul(rhs.z);
        let s = xx.add(yy);
        s.add(zz)
    }

    pub open spec fn cross_spec(self, rhs: Self) -> Self {
        Vec3 {
            x: self.y.mul_spec(rhs.z).sub_spec(self.z.mul_spec(rhs.y)),
            y: self.z.mul_spec(rhs.x).sub_spec(self.x.mul_spec(rhs.z)),
            z: self.x.mul_spec(rhs.y).sub_spec(self.y.mul_spec(rhs.x)),
        }
    }

    pub proof fn cross(self, rhs: Self) -> (out: Self)
        ensures
            out == self.cross_spec(rhs),
    {
        let yz = self.y.mul(rhs.z);
        let zy = self.z.mul(rhs.y);
        let zx = self.z.mul(rhs.x);
        let xz = self.x.mul(rhs.z);
        let xy = self.x.mul(rhs.y);
        let yx = self.y.mul(rhs.x);
        Vec3 {
            x: yz.sub(zy),
            y: zx.sub(xz),
            z: xy.sub(yx),
        }
    }

    pub open spec fn norm2_spec(self) -> Scalar {
        self.dot_spec(self)
    }

    pub proof fn lemma_eqv_from_components(a: Self, b: Self)
        requires
            a.x.eqv_spec(b.x),
            a.y.eqv_spec(b.y),
            a.z.eqv_spec(b.z),
        ensures
            a.eqv_spec(b),
    {
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        Scalar::lemma_eqv_reflexive(a.x);
        Scalar::lemma_eqv_reflexive(a.y);
        Scalar::lemma_eqv_reflexive(a.z);
        assert(a.eqv_spec(a));
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
        let vx = v.x.mul_spec(v.x);
        let vy = v.y.mul_spec(v.y);
        let vz = v.z.mul_spec(v.z);
        let us = ux.add_spec(uy);
        let vs = vx.add_spec(vy);

        assert(u.eqv_spec(v));
        Scalar::lemma_eqv_mul_congruence(u.x, v.x, u.x, v.x);
        Scalar::lemma_eqv_mul_congruence(u.y, v.y, u.y, v.y);
        Scalar::lemma_eqv_mul_congruence(u.z, v.z, u.z, v.z);
        assert(ux.eqv_spec(vx));
        assert(uy.eqv_spec(vy));
        assert(uz.eqv_spec(vz));
        Scalar::lemma_eqv_add_congruence(ux, vx, uy, vy);
        assert(us.eqv_spec(vs));
        Scalar::lemma_eqv_add_congruence(us, vs, uz, vz);
        assert(us.add_spec(uz).eqv_spec(vs.add_spec(vz)));
        assert(u.norm2_spec() == us.add_spec(uz));
        assert(v.norm2_spec() == vs.add_spec(vz));
        assert(u.norm2_spec().eqv_spec(v.norm2_spec()));
    }

    pub proof fn lemma_dot_eqv_congruence(u1: Self, u2: Self, v1: Self, v2: Self)
        requires
            u1.x.eqv_spec(u2.x),
            u1.y.eqv_spec(u2.y),
            u1.z.eqv_spec(u2.z),
            v1.x.eqv_spec(v2.x),
            v1.y.eqv_spec(v2.y),
            v1.z.eqv_spec(v2.z),
        ensures
            u1.dot_spec(v1).eqv_spec(u2.dot_spec(v2)),
    {
        let a1 = u1.x.mul_spec(v1.x);
        let b1 = u1.y.mul_spec(v1.y);
        let c1 = u1.z.mul_spec(v1.z);
        let a2 = u2.x.mul_spec(v2.x);
        let b2 = u2.y.mul_spec(v2.y);
        let c2 = u2.z.mul_spec(v2.z);
        let s1 = a1.add_spec(b1);
        let s2 = a2.add_spec(b2);

        Scalar::lemma_eqv_mul_congruence(u1.x, u2.x, v1.x, v2.x);
        Scalar::lemma_eqv_mul_congruence(u1.y, u2.y, v1.y, v2.y);
        Scalar::lemma_eqv_mul_congruence(u1.z, u2.z, v1.z, v2.z);
        assert(a1.eqv_spec(a2));
        assert(b1.eqv_spec(b2));
        assert(c1.eqv_spec(c2));
        Scalar::lemma_eqv_add_congruence(a1, a2, b1, b2);
        assert(s1.eqv_spec(s2));
        Scalar::lemma_eqv_add_congruence(s1, s2, c1, c2);
        assert(s1.add_spec(c1).eqv_spec(s2.add_spec(c2)));
        assert(u1.dot_spec(v1) == s1.add_spec(c1));
        assert(u2.dot_spec(v2) == s2.add_spec(c2));
        assert(u1.dot_spec(v1).eqv_spec(u2.dot_spec(v2)));
    }

    pub proof fn lemma_cross_eqv_congruence(u1: Self, u2: Self, v1: Self, v2: Self)
        requires
            u1.x.eqv_spec(u2.x),
            u1.y.eqv_spec(u2.y),
            u1.z.eqv_spec(u2.z),
            v1.x.eqv_spec(v2.x),
            v1.y.eqv_spec(v2.y),
            v1.z.eqv_spec(v2.z),
        ensures
            u1.cross_spec(v1).eqv_spec(u2.cross_spec(v2)),
    {
        let c1 = u1.cross_spec(v1);
        let c2 = u2.cross_spec(v2);

        let x1l = u1.y.mul_spec(v1.z);
        let x1r = u1.z.mul_spec(v1.y);
        let x2l = u2.y.mul_spec(v2.z);
        let x2r = u2.z.mul_spec(v2.y);
        Scalar::lemma_eqv_mul_congruence(u1.y, u2.y, v1.z, v2.z);
        Scalar::lemma_eqv_mul_congruence(u1.z, u2.z, v1.y, v2.y);
        Scalar::lemma_eqv_sub_congruence(x1l, x2l, x1r, x2r);

        let y1l = u1.z.mul_spec(v1.x);
        let y1r = u1.x.mul_spec(v1.z);
        let y2l = u2.z.mul_spec(v2.x);
        let y2r = u2.x.mul_spec(v2.z);
        Scalar::lemma_eqv_mul_congruence(u1.z, u2.z, v1.x, v2.x);
        Scalar::lemma_eqv_mul_congruence(u1.x, u2.x, v1.z, v2.z);
        Scalar::lemma_eqv_sub_congruence(y1l, y2l, y1r, y2r);

        let z1l = u1.x.mul_spec(v1.y);
        let z1r = u1.y.mul_spec(v1.x);
        let z2l = u2.x.mul_spec(v2.y);
        let z2r = u2.y.mul_spec(v2.x);
        Scalar::lemma_eqv_mul_congruence(u1.x, u2.x, v1.y, v2.y);
        Scalar::lemma_eqv_mul_congruence(u1.y, u2.y, v1.x, v2.x);
        Scalar::lemma_eqv_sub_congruence(z1l, z2l, z1r, z2r);

        assert(c1.x.eqv_spec(c2.x));
        assert(c1.y.eqv_spec(c2.y));
        assert(c1.z.eqv_spec(c2.z));
        assert(c1.eqv_spec(c2));
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
        Scalar::lemma_add_associative(a.x, b.x, c.x);
        Scalar::lemma_add_associative(a.y, b.y, c.y);
        Scalar::lemma_add_associative(a.z, b.z, c.z);
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.eqv_spec(rhs));
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
        assert(a.add_spec(z).x == a.x);
        assert(a.add_spec(z).y == a.y);
        assert(a.add_spec(z).z == a.z);
        assert(a.add_spec(z) == a);
        assert(z.add_spec(a).x == a.x);
        assert(z.add_spec(a).y == a.y);
        assert(z.add_spec(a).z == a.z);
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
        assert(lhs.x.eqv_spec(z.x));
        assert(lhs.y.eqv_spec(z.y));
        assert(lhs.z.eqv_spec(z.z));
        assert(rhs.x.eqv_spec(z.x));
        assert(rhs.y.eqv_spec(z.y));
        assert(rhs.z.eqv_spec(z.z));
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
        assert(a.neg_spec().neg_spec().x.num == a.x.num);
        assert(a.neg_spec().neg_spec().y.num == a.y.num);
        assert(a.neg_spec().neg_spec().z.num == a.z.num);
        assert(a.neg_spec().neg_spec().x.den == a.x.den);
        assert(a.neg_spec().neg_spec().y.den == a.y.den);
        assert(a.neg_spec().neg_spec().z.den == a.z.den);
        assert(a.neg_spec().neg_spec() == a);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        Scalar::lemma_sub_is_add_neg(a.x, b.x);
        Scalar::lemma_sub_is_add_neg(a.y, b.y);
        Scalar::lemma_sub_is_add_neg(a.z, b.z);
        assert(a.sub_spec(b).x == a.add_spec(b.neg_spec()).x);
        assert(a.sub_spec(b).y == a.add_spec(b.neg_spec()).y);
        assert(a.sub_spec(b).z == a.add_spec(b.neg_spec()).z);
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
        assert(s.x.eqv_spec(z.x));
        assert(s.y.eqv_spec(z.y));
        assert(s.z.eqv_spec(z.z));
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
        assert(s.x == v.x);
        assert(s.y == v.y);
        assert(s.z == v.z);
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
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_scale_distributes_over_vec_add(u: Self, v: Self, k: Scalar)
        ensures
            u.add_spec(v).scale_spec(k).eqv_spec(u.scale_spec(k).add_spec(v.scale_spec(k))),
    {
        let lhs = u.add_spec(v).scale_spec(k);
        let rhs = u.scale_spec(k).add_spec(v.scale_spec(k));

        let uxk = u.x.mul_spec(k);
        let vxk = v.x.mul_spec(k);
        let kux = k.mul_spec(u.x);
        let kvx = k.mul_spec(v.x);

        let uyk = u.y.mul_spec(k);
        let vyk = v.y.mul_spec(k);
        let kuy = k.mul_spec(u.y);
        let kvy = k.mul_spec(v.y);

        let uzk = u.z.mul_spec(k);
        let vzk = v.z.mul_spec(k);
        let kuz = k.mul_spec(u.z);
        let kvz = k.mul_spec(v.z);

        Scalar::lemma_mul_commutative(u.x.add_spec(v.x), k);
        Scalar::lemma_mul_commutative(u.y.add_spec(v.y), k);
        Scalar::lemma_mul_commutative(u.z.add_spec(v.z), k);
        Scalar::lemma_eqv_mul_distributive_left(k, u.x, v.x);
        Scalar::lemma_eqv_mul_distributive_left(k, u.y, v.y);
        Scalar::lemma_eqv_mul_distributive_left(k, u.z, v.z);
        Scalar::lemma_mul_commutative(k, u.x);
        Scalar::lemma_mul_commutative(k, v.x);
        Scalar::lemma_mul_commutative(k, u.y);
        Scalar::lemma_mul_commutative(k, v.y);
        Scalar::lemma_mul_commutative(k, u.z);
        Scalar::lemma_mul_commutative(k, v.z);

        assert(lhs.x == k.mul_spec(u.x.add_spec(v.x)));
        assert(k.mul_spec(u.x.add_spec(v.x)).eqv_spec(kux.add_spec(kvx)));
        assert(kux == uxk);
        assert(kvx == vxk);
        Scalar::lemma_eqv_reflexive(kux);
        Scalar::lemma_eqv_reflexive(kvx);
        Scalar::lemma_eqv_add_congruence(kux, uxk, kvx, vxk);
        Scalar::lemma_eqv_transitive(lhs.x, kux.add_spec(kvx), uxk.add_spec(vxk));
        assert(lhs.x.eqv_spec(rhs.x));

        assert(lhs.y == k.mul_spec(u.y.add_spec(v.y)));
        assert(k.mul_spec(u.y.add_spec(v.y)).eqv_spec(kuy.add_spec(kvy)));
        assert(kuy == uyk);
        assert(kvy == vyk);
        Scalar::lemma_eqv_reflexive(kuy);
        Scalar::lemma_eqv_reflexive(kvy);
        Scalar::lemma_eqv_add_congruence(kuy, uyk, kvy, vyk);
        Scalar::lemma_eqv_transitive(lhs.y, kuy.add_spec(kvy), uyk.add_spec(vyk));
        assert(lhs.y.eqv_spec(rhs.y));

        assert(lhs.z == k.mul_spec(u.z.add_spec(v.z)));
        assert(k.mul_spec(u.z.add_spec(v.z)).eqv_spec(kuz.add_spec(kvz)));
        assert(kuz == uzk);
        assert(kvz == vzk);
        Scalar::lemma_eqv_reflexive(kuz);
        Scalar::lemma_eqv_reflexive(kvz);
        Scalar::lemma_eqv_add_congruence(kuz, uzk, kvz, vzk);
        Scalar::lemma_eqv_transitive(lhs.z, kuz.add_spec(kvz), uzk.add_spec(vzk));
        assert(lhs.z.eqv_spec(rhs.z));

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
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
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
        assert(lhs.x == v.x.neg_spec().mul_spec(k));
        assert(lhs.x == k.mul_spec(v.x.neg_spec()));
        assert(k.mul_spec(v.x.neg_spec()) == k.mul_spec(v.x).neg_spec());
        assert(k.mul_spec(v.x) == v.x.mul_spec(k));
        assert(lhs.x == v.x.mul_spec(k).neg_spec());
        assert(rhs.x == v.x.mul_spec(k).neg_spec());
        assert(lhs.x == rhs.x);

        Scalar::lemma_mul_commutative(v.y.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.y);
        Scalar::lemma_mul_commutative(k, v.y);
        assert(lhs.y == v.y.neg_spec().mul_spec(k));
        assert(lhs.y == k.mul_spec(v.y.neg_spec()));
        assert(k.mul_spec(v.y.neg_spec()) == k.mul_spec(v.y).neg_spec());
        assert(k.mul_spec(v.y) == v.y.mul_spec(k));
        assert(lhs.y == v.y.mul_spec(k).neg_spec());
        assert(rhs.y == v.y.mul_spec(k).neg_spec());
        assert(lhs.y == rhs.y);

        Scalar::lemma_mul_commutative(v.z.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, v.z);
        Scalar::lemma_mul_commutative(k, v.z);
        assert(lhs.z == v.z.neg_spec().mul_spec(k));
        assert(lhs.z == k.mul_spec(v.z.neg_spec()));
        assert(k.mul_spec(v.z.neg_spec()) == k.mul_spec(v.z).neg_spec());
        assert(k.mul_spec(v.z) == v.z.mul_spec(k));
        assert(lhs.z == v.z.mul_spec(k).neg_spec());
        assert(rhs.z == v.z.mul_spec(k).neg_spec());
        assert(lhs.z == rhs.z);

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
        assert(lhs.x == v.x.mul_spec(k.neg_spec()));
        assert(rhs.x == v.x.mul_spec(k).neg_spec());
        assert(lhs.x == rhs.x);
        assert(lhs.y == v.y.mul_spec(k.neg_spec()));
        assert(rhs.y == v.y.mul_spec(k).neg_spec());
        assert(lhs.y == rhs.y);
        assert(lhs.z == v.z.mul_spec(k.neg_spec()));
        assert(rhs.z == v.z.mul_spec(k).neg_spec());
        assert(lhs.z == rhs.z);
        assert(lhs == rhs);
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
        assert(lhs == rhs);
        Scalar::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.dot_spec(v.add_spec(w)).eqv_spec(u.dot_spec(v).add_spec(u.dot_spec(w))),
    {
        let lhs = u.dot_spec(v.add_spec(w));
        let ux = u.x.mul_spec(v.x.add_spec(w.x));
        let uy = u.y.mul_spec(v.y.add_spec(w.y));
        let uz = u.z.mul_spec(v.z.add_spec(w.z));
        let ax = u.x.mul_spec(v.x);
        let bx = u.x.mul_spec(w.x);
        let ay = u.y.mul_spec(v.y);
        let by = u.y.mul_spec(w.y);
        let az = u.z.mul_spec(v.z);
        let bz = u.z.mul_spec(w.z);
        let mid = ax.add_spec(bx).add_spec(ay.add_spec(by)).add_spec(az.add_spec(bz));
        let rhs = u.dot_spec(v).add_spec(u.dot_spec(w));

        Scalar::lemma_mul_distributes_over_add(u.x, v.x, w.x);
        Scalar::lemma_mul_distributes_over_add(u.y, v.y, w.y);
        Scalar::lemma_mul_distributes_over_add(u.z, v.z, w.z);
        assert(lhs == ux.add_spec(uy).add_spec(uz));
        assert(ux.eqv_spec(ax.add_spec(bx)));
        assert(uy.eqv_spec(ay.add_spec(by)));
        assert(uz.eqv_spec(az.add_spec(bz)));
        Scalar::lemma_eqv_add_congruence(ux, ax.add_spec(bx), uy, ay.add_spec(by));
        assert(ux.add_spec(uy).eqv_spec(ax.add_spec(bx).add_spec(ay.add_spec(by))));
        Scalar::lemma_eqv_add_congruence(
            ux.add_spec(uy),
            ax.add_spec(bx).add_spec(ay.add_spec(by)),
            uz,
            az.add_spec(bz),
        );
        assert(lhs.eqv_spec(mid));

        assert(rhs == ax.add_spec(ay).add_spec(az).add_spec(bx.add_spec(by).add_spec(bz)));
        Scalar::lemma_add_rearrange_2x2(ax, bx, ay, by);
        assert(ax.add_spec(bx).add_spec(ay.add_spec(by)).eqv_spec(ax.add_spec(ay).add_spec(bx.add_spec(by))));
        Scalar::lemma_eqv_add_congruence(
            ax.add_spec(bx).add_spec(ay.add_spec(by)),
            ax.add_spec(ay).add_spec(bx.add_spec(by)),
            az.add_spec(bz),
            az.add_spec(bz),
        );
        assert(mid.eqv_spec(ax.add_spec(ay).add_spec(bx.add_spec(by)).add_spec(az.add_spec(bz))));

        Scalar::lemma_add_rearrange_2x2(ax.add_spec(ay), bx.add_spec(by), az, bz);
        assert(ax.add_spec(ay).add_spec(bx.add_spec(by)).add_spec(az.add_spec(bz)).eqv_spec(
            ax.add_spec(ay).add_spec(az).add_spec(bx.add_spec(by).add_spec(bz)),
        ));
        Scalar::lemma_eqv_transitive(
            mid,
            ax.add_spec(ay).add_spec(bx.add_spec(by)).add_spec(az.add_spec(bz)),
            ax.add_spec(ay).add_spec(az).add_spec(bx.add_spec(by).add_spec(bz)),
        );
        assert(mid.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).dot_spec(w).eqv_spec(u.dot_spec(w).add_spec(v.dot_spec(w))),
    {
        let lhs = u.add_spec(v).dot_spec(w);
        let mid1 = w.dot_spec(u.add_spec(v));
        let mid2 = w.dot_spec(u).add_spec(w.dot_spec(v));
        let rhs = u.dot_spec(w).add_spec(v.dot_spec(w));

        Self::lemma_dot_symmetric(u.add_spec(v), w);
        assert(lhs.eqv_spec(mid1));
        Self::lemma_dot_linear_right(w, u, v);
        assert(mid1.eqv_spec(mid2));
        Self::lemma_dot_symmetric(w, u);
        Self::lemma_dot_symmetric(w, v);
        Scalar::lemma_eqv_add_congruence(w.dot_spec(u), u.dot_spec(w), w.dot_spec(v), v.dot_spec(w));
        assert(mid2.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid1, mid2);
        Scalar::lemma_eqv_transitive(lhs, mid2, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_dot_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.scale_spec(k).dot_spec(w).eqv_spec(k.mul_spec(v.dot_spec(w))),
    {
        let lhs = v.scale_spec(k).dot_spec(w);
        let rhs = k.mul_spec(v.dot_spec(w));

        let a1 = v.x.mul_spec(k).mul_spec(w.x);
        let b1 = v.y.mul_spec(k).mul_spec(w.y);
        let c1 = v.z.mul_spec(k).mul_spec(w.z);
        let a2 = k.mul_spec(v.x).mul_spec(w.x);
        let b2 = k.mul_spec(v.y).mul_spec(w.y);
        let c2 = k.mul_spec(v.z).mul_spec(w.z);
        let a3 = k.mul_spec(v.x.mul_spec(w.x));
        let b3 = k.mul_spec(v.y.mul_spec(w.y));
        let c3 = k.mul_spec(v.z.mul_spec(w.z));
        let mid = a3.add_spec(b3).add_spec(c3);

        Scalar::lemma_mul_commutative(v.x, k);
        Scalar::lemma_mul_commutative(v.y, k);
        Scalar::lemma_mul_commutative(v.z, k);
        assert(v.x.mul_spec(k) == k.mul_spec(v.x));
        assert(v.y.mul_spec(k) == k.mul_spec(v.y));
        assert(v.z.mul_spec(k) == k.mul_spec(v.z));
        assert(a1 == a2);
        assert(b1 == b2);
        assert(c1 == c2);

        Scalar::lemma_mul_associative(k, v.x, w.x);
        Scalar::lemma_mul_associative(k, v.y, w.y);
        Scalar::lemma_mul_associative(k, v.z, w.z);
        Scalar::lemma_eqv_reflexive(a1);
        Scalar::lemma_eqv_reflexive(b1);
        Scalar::lemma_eqv_reflexive(c1);
        assert(a1.eqv_spec(a2));
        assert(b1.eqv_spec(b2));
        assert(c1.eqv_spec(c2));
        Scalar::lemma_eqv_transitive(a1, a2, a3);
        Scalar::lemma_eqv_transitive(b1, b2, b3);
        Scalar::lemma_eqv_transitive(c1, c2, c3);
        assert(a1.eqv_spec(a3));
        assert(b1.eqv_spec(b3));
        assert(c1.eqv_spec(c3));

        assert(lhs == a1.add_spec(b1).add_spec(c1));
        Scalar::lemma_eqv_add_congruence(a1, a3, b1, b3);
        assert(a1.add_spec(b1).eqv_spec(a3.add_spec(b3)));
        Scalar::lemma_eqv_add_congruence(a1.add_spec(b1), a3.add_spec(b3), c1, c3);
        assert(lhs.eqv_spec(mid));

        let p = v.x.mul_spec(w.x);
        let q = v.y.mul_spec(w.y);
        let r = v.z.mul_spec(w.z);
        let pq = p.add_spec(q);
        let kpq = k.mul_spec(pq);
        let kr = k.mul_spec(r);
        assert(v.dot_spec(w) == p.add_spec(q).add_spec(r));
        assert(rhs == k.mul_spec(pq.add_spec(r)));
        Scalar::lemma_eqv_mul_distributive_left(k, pq, r);
        assert(rhs.eqv_spec(kpq.add_spec(kr)));
        Scalar::lemma_eqv_mul_distributive_left(k, p, q);
        assert(kpq.eqv_spec(k.mul_spec(p).add_spec(k.mul_spec(q))));
        Scalar::lemma_eqv_add_congruence(kpq, k.mul_spec(p).add_spec(k.mul_spec(q)), kr, kr);
        assert(kpq.add_spec(kr).eqv_spec(k.mul_spec(p).add_spec(k.mul_spec(q)).add_spec(kr)));
        assert(k.mul_spec(p) == a3);
        assert(k.mul_spec(q) == b3);
        assert(kr == c3);
        assert(k.mul_spec(p).add_spec(k.mul_spec(q)).add_spec(kr) == mid);
        Scalar::lemma_eqv_transitive(rhs, kpq.add_spec(kr), mid);
        assert(rhs.eqv_spec(mid));
        Scalar::lemma_eqv_symmetric(rhs, mid);
        assert(mid.eqv_spec(rhs));
        Scalar::lemma_eqv_transitive(lhs, mid, rhs);
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
        let x2 = v.x.mul_spec(v.x);
        let y2 = v.y.mul_spec(v.y);
        let z2 = v.z.mul_spec(v.z);
        let nn = v.neg_spec().norm2_spec();
        let n = v.norm2_spec();

        assert(nx.num == (-v.x.num) * (-v.x.num));
        assert((-v.x.num) * (-v.x.num) == v.x.num * v.x.num) by (nonlinear_arith);
        assert(nx.num == x2.num);
        assert(nx.den == v.x.den * v.x.den + v.x.den + v.x.den);
        assert(x2.den == v.x.den * v.x.den + v.x.den + v.x.den);
        assert(nx.den == x2.den);
        assert(nx == x2);

        assert(ny.num == (-v.y.num) * (-v.y.num));
        assert((-v.y.num) * (-v.y.num) == v.y.num * v.y.num) by (nonlinear_arith);
        assert(ny.num == y2.num);
        assert(ny.den == v.y.den * v.y.den + v.y.den + v.y.den);
        assert(y2.den == v.y.den * v.y.den + v.y.den + v.y.den);
        assert(ny.den == y2.den);
        assert(ny == y2);

        assert(nz.num == (-v.z.num) * (-v.z.num));
        assert((-v.z.num) * (-v.z.num) == v.z.num * v.z.num) by (nonlinear_arith);
        assert(nz.num == z2.num);
        assert(nz.den == v.z.den * v.z.den + v.z.den + v.z.den);
        assert(z2.den == v.z.den * v.z.den + v.z.den + v.z.den);
        assert(nz.den == z2.den);
        assert(nz == z2);

        assert(nn == nx.add_spec(ny).add_spec(nz));
        assert(n == x2.add_spec(y2).add_spec(z2));
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
        let xy = Vec2 { x: v.x, y: v.y };
        let s = xy.norm2_spec();
        let zz = v.z.mul_spec(v.z);
        assert(n == s.add_spec(zz));

        Vec2::lemma_norm2_nonnegative(xy);
        assert(z.le_spec(s));
        assert(z.le_spec(s) == (z.num * s.denom() <= s.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(s) == (0 * s.denom() <= s.num * 1));
        assert(0 * s.denom() == 0);
        assert(s.num * 1 == s.num);
        assert(0 <= s.num);
        assert(s.num >= 0);

        assert(zz.num == v.z.num * v.z.num);
        Scalar::lemma_denom_positive(zz);
        Scalar::lemma_denom_positive(s);
        assert(v.z.num * v.z.num >= 0) by (nonlinear_arith);
        assert(zz.num >= 0);
        assert((s.num >= 0 && zz.denom() > 0) ==> (s.num * zz.denom() >= 0)) by (nonlinear_arith);
        assert((zz.num >= 0 && s.denom() > 0) ==> (zz.num * s.denom() >= 0)) by (nonlinear_arith);
        let a = s.num * zz.denom();
        let b = zz.num * s.denom();
        assert(a >= 0);
        assert(b >= 0);
        assert(n.num == s.num * zz.denom() + zz.num * s.denom());
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
        let xy = Vec2 { x: v.x, y: v.y };
        let s = xy.norm2_spec();
        let zz = v.z.mul_spec(v.z);
        let z2 = Vec2::zero_spec();

        assert(zv.x == z);
        assert(zv.y == z);
        assert(zv.z == z);
        assert(z2.x == z);
        assert(z2.y == z);
        assert(n == s.add_spec(zz));

        if n.eqv_spec(z) {
            Scalar::lemma_eqv_zero_iff_num_zero(n);
            assert(n.eqv_spec(z) == (n.num == 0));
            assert(n.num == 0);
            assert(n.num == s.num * zz.denom() + zz.num * s.denom());

            Vec2::lemma_norm2_nonnegative(xy);
            assert(z.le_spec(s));
            assert(z.le_spec(s) == (z.num * s.denom() <= s.num * z.denom()));
            assert(z.num == 0);
            assert(z.denom() == 1);
            assert(z.le_spec(s) == (0 * s.denom() <= s.num * 1));
            assert(0 * s.denom() == 0);
            assert(s.num * 1 == s.num);
            assert(0 <= s.num);
            assert(s.num >= 0);

            assert(zz.num == v.z.num * v.z.num);
            Scalar::lemma_denom_positive(zz);
            Scalar::lemma_denom_positive(s);
            assert(v.z.num * v.z.num >= 0) by (nonlinear_arith);
            assert(zz.num >= 0);
            assert((s.num >= 0 && zz.denom() > 0) ==> (s.num * zz.denom() >= 0)) by (nonlinear_arith);
            assert((zz.num >= 0 && s.denom() > 0) ==> (zz.num * s.denom() >= 0)) by (nonlinear_arith);
            assert(s.num * zz.denom() >= 0);
            assert(zz.num * s.denom() >= 0);
            assert((s.num * zz.denom() >= 0
                && zz.num * s.denom() >= 0
                && s.num * zz.denom() + zz.num * s.denom() == 0)
                ==> (s.num * zz.denom() == 0 && zz.num * s.denom() == 0))
                by (nonlinear_arith);
            assert(s.num * zz.denom() == 0);
            assert(zz.num * s.denom() == 0);
            assert((zz.denom() > 0 && s.num * zz.denom() == 0) ==> s.num == 0) by (nonlinear_arith);
            assert((s.denom() > 0 && zz.num * s.denom() == 0) ==> zz.num == 0) by (nonlinear_arith);
            assert(s.num == 0);
            assert(zz.num == 0);

            assert((v.z.num * v.z.num == 0) ==> v.z.num == 0) by (nonlinear_arith);
            assert(v.z.num == 0);

            Scalar::lemma_eqv_zero_iff_num_zero(s);
            Scalar::lemma_eqv_zero_iff_num_zero(v.z);
            assert(s.eqv_spec(z) == (s.num == 0));
            assert(v.z.eqv_spec(z) == (v.z.num == 0));
            assert(s.eqv_spec(z));
            assert(v.z.eqv_spec(z));

            Vec2::lemma_norm2_zero_iff_zero(xy);
            assert(s.eqv_spec(z) == xy.eqv_spec(z2));
            assert(xy.eqv_spec(z2));
            assert(xy.x.eqv_spec(z2.x));
            assert(xy.y.eqv_spec(z2.y));
            assert(v.x.eqv_spec(z));
            assert(v.y.eqv_spec(z));
            assert(v.eqv_spec(zv));
        }

        if v.eqv_spec(zv) {
            assert(v.x.eqv_spec(z));
            assert(v.y.eqv_spec(z));
            assert(v.z.eqv_spec(z));
            Vec2::lemma_eqv_from_components(xy, z2);
            assert(xy.eqv_spec(z2));
            Vec2::lemma_norm2_zero_iff_zero(xy);
            assert(s.eqv_spec(z) == xy.eqv_spec(z2));
            assert(s.eqv_spec(z));

            Scalar::lemma_eqv_zero_iff_num_zero(v.z);
            assert(v.z.eqv_spec(z) == (v.z.num == 0));
            assert(v.z.num == 0);
            assert(zz.num == v.z.num * v.z.num);
            Scalar::lemma_mul_right_zero_num(v.z, v.z);
            assert(v.z.mul_spec(v.z).num == 0);
            assert(zz.num == v.z.mul_spec(v.z).num);
            assert(zz.num == 0);
            Scalar::lemma_eqv_zero_iff_num_zero(zz);
            assert(zz.eqv_spec(z) == (zz.num == 0));
            assert(zz.eqv_spec(z));

            Scalar::lemma_eqv_add_congruence(s, z, zz, z);
            assert(s.add_spec(zz).eqv_spec(z.add_spec(z)));
            Scalar::lemma_add_zero_identity(z);
            assert(z.add_spec(z) == z);
            Scalar::lemma_eqv_reflexive(z);
            assert(z.add_spec(z).eqv_spec(z));
            Scalar::lemma_eqv_transitive(s.add_spec(zz), z.add_spec(z), z);
            assert(n.eqv_spec(z));
        }
        assert((n.eqv_spec(z)) == v.eqv_spec(zv));
    }

    pub proof fn lemma_cross_antisymmetric(a: Self, b: Self)
        ensures
            a.cross_spec(b) == b.cross_spec(a).neg_spec(),
    {
        let ab = a.cross_spec(b);
        let ba = b.cross_spec(a);
        Scalar::lemma_sub_antisymmetric(a.y.mul_spec(b.z), a.z.mul_spec(b.y));
        Scalar::lemma_sub_antisymmetric(a.z.mul_spec(b.x), a.x.mul_spec(b.z));
        Scalar::lemma_sub_antisymmetric(a.x.mul_spec(b.y), a.y.mul_spec(b.x));
        Scalar::lemma_mul_commutative(a.y, b.z);
        Scalar::lemma_mul_commutative(a.z, b.y);
        Scalar::lemma_mul_commutative(a.z, b.x);
        Scalar::lemma_mul_commutative(a.x, b.z);
        Scalar::lemma_mul_commutative(a.x, b.y);
        Scalar::lemma_mul_commutative(a.y, b.x);
        assert(ab.x == ba.x.neg_spec());
        assert(ab.y == ba.y.neg_spec());
        assert(ab.z == ba.z.neg_spec());
        assert(ab == ba.neg_spec());
    }

    pub proof fn lemma_cross_linear_right(u: Self, v: Self, w: Self)
        ensures
            u.cross_spec(v.add_spec(w)).eqv_spec(u.cross_spec(v).add_spec(u.cross_spec(w))),
    {
        let lhs = u.cross_spec(v.add_spec(w));
        let rhs = u.cross_spec(v).add_spec(u.cross_spec(w));

        let px1 = u.y.mul_spec(v.z.add_spec(w.z));
        let qx1 = u.z.mul_spec(v.y.add_spec(w.y));
        let px = u.y.mul_spec(v.z);
        let rx = u.y.mul_spec(w.z);
        let qx = u.z.mul_spec(v.y);
        let sx = u.z.mul_spec(w.y);
        let x_mid = px.add_spec(rx).sub_spec(qx.add_spec(sx));
        let x_rhs_mid = px.sub_spec(qx).add_spec(rx.sub_spec(sx));

        Scalar::lemma_mul_distributes_over_add(u.y, v.z, w.z);
        Scalar::lemma_mul_distributes_over_add(u.z, v.y, w.y);
        assert(px1.eqv_spec(px.add_spec(rx)));
        assert(qx1.eqv_spec(qx.add_spec(sx)));
        assert(lhs.x == px1.sub_spec(qx1));
        Scalar::lemma_eqv_sub_congruence(px1, px.add_spec(rx), qx1, qx.add_spec(sx));
        assert(lhs.x.eqv_spec(x_mid));
        Scalar::lemma_sub_add_distributes(px, rx, qx, sx);
        assert(x_mid.eqv_spec(x_rhs_mid));
        assert(rhs.x == px.sub_spec(qx).add_spec(rx.sub_spec(sx)));
        assert(rhs.x == x_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.x);
        assert(x_rhs_mid.eqv_spec(rhs.x));
        Scalar::lemma_eqv_transitive(lhs.x, x_mid, x_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.x, x_rhs_mid, rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        let py1 = u.z.mul_spec(v.x.add_spec(w.x));
        let qy1 = u.x.mul_spec(v.z.add_spec(w.z));
        let py = u.z.mul_spec(v.x);
        let ry = u.z.mul_spec(w.x);
        let qy = u.x.mul_spec(v.z);
        let sy = u.x.mul_spec(w.z);
        let y_mid = py.add_spec(ry).sub_spec(qy.add_spec(sy));
        let y_rhs_mid = py.sub_spec(qy).add_spec(ry.sub_spec(sy));

        Scalar::lemma_mul_distributes_over_add(u.z, v.x, w.x);
        Scalar::lemma_mul_distributes_over_add(u.x, v.z, w.z);
        assert(py1.eqv_spec(py.add_spec(ry)));
        assert(qy1.eqv_spec(qy.add_spec(sy)));
        assert(lhs.y == py1.sub_spec(qy1));
        Scalar::lemma_eqv_sub_congruence(py1, py.add_spec(ry), qy1, qy.add_spec(sy));
        assert(lhs.y.eqv_spec(y_mid));
        Scalar::lemma_sub_add_distributes(py, ry, qy, sy);
        assert(y_mid.eqv_spec(y_rhs_mid));
        assert(rhs.y == py.sub_spec(qy).add_spec(ry.sub_spec(sy)));
        assert(rhs.y == y_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.y);
        assert(y_rhs_mid.eqv_spec(rhs.y));
        Scalar::lemma_eqv_transitive(lhs.y, y_mid, y_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.y, y_rhs_mid, rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        let pz1 = u.x.mul_spec(v.y.add_spec(w.y));
        let qz1 = u.y.mul_spec(v.x.add_spec(w.x));
        let pz = u.x.mul_spec(v.y);
        let rz = u.x.mul_spec(w.y);
        let qz = u.y.mul_spec(v.x);
        let sz = u.y.mul_spec(w.x);
        let z_mid = pz.add_spec(rz).sub_spec(qz.add_spec(sz));
        let z_rhs_mid = pz.sub_spec(qz).add_spec(rz.sub_spec(sz));

        Scalar::lemma_mul_distributes_over_add(u.x, v.y, w.y);
        Scalar::lemma_mul_distributes_over_add(u.y, v.x, w.x);
        assert(pz1.eqv_spec(pz.add_spec(rz)));
        assert(qz1.eqv_spec(qz.add_spec(sz)));
        assert(lhs.z == pz1.sub_spec(qz1));
        Scalar::lemma_eqv_sub_congruence(pz1, pz.add_spec(rz), qz1, qz.add_spec(sz));
        assert(lhs.z.eqv_spec(z_mid));
        Scalar::lemma_sub_add_distributes(pz, rz, qz, sz);
        assert(z_mid.eqv_spec(z_rhs_mid));
        assert(rhs.z == pz.sub_spec(qz).add_spec(rz.sub_spec(sz)));
        assert(rhs.z == z_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.z);
        assert(z_rhs_mid.eqv_spec(rhs.z));
        Scalar::lemma_eqv_transitive(lhs.z, z_mid, z_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.z, z_rhs_mid, rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_linear_left(u: Self, v: Self, w: Self)
        ensures
            u.add_spec(v).cross_spec(w).eqv_spec(u.cross_spec(w).add_spec(v.cross_spec(w))),
    {
        let lhs = u.add_spec(v).cross_spec(w);
        let rhs = u.cross_spec(w).add_spec(v.cross_spec(w));

        let px1 = u.y.add_spec(v.y).mul_spec(w.z);
        let qx1 = u.z.add_spec(v.z).mul_spec(w.y);
        let px = u.y.mul_spec(w.z);
        let rx = v.y.mul_spec(w.z);
        let qx = u.z.mul_spec(w.y);
        let sx = v.z.mul_spec(w.y);
        let x_mid = px.add_spec(rx).sub_spec(qx.add_spec(sx));
        let x_rhs_mid = px.sub_spec(qx).add_spec(rx.sub_spec(sx));

        Scalar::lemma_mul_distributes_over_add(w.z, u.y, v.y);
        Scalar::lemma_mul_distributes_over_add(w.y, u.z, v.z);
        Scalar::lemma_mul_commutative(u.y.add_spec(v.y), w.z);
        Scalar::lemma_mul_commutative(u.z.add_spec(v.z), w.y);
        assert(px1 == w.z.mul_spec(u.y.add_spec(v.y)));
        assert(qx1 == w.y.mul_spec(u.z.add_spec(v.z)));
        let pxw = w.z.mul_spec(u.y);
        let rxw = w.z.mul_spec(v.y);
        let qxw = w.y.mul_spec(u.z);
        let sxw = w.y.mul_spec(v.z);
        assert(px1.eqv_spec(pxw.add_spec(rxw)));
        assert(qx1.eqv_spec(qxw.add_spec(sxw)));
        Scalar::lemma_mul_commutative(w.z, u.y);
        Scalar::lemma_mul_commutative(w.z, v.y);
        Scalar::lemma_mul_commutative(w.y, u.z);
        Scalar::lemma_mul_commutative(w.y, v.z);
        assert(pxw == px);
        assert(rxw == rx);
        assert(qxw == qx);
        assert(sxw == sx);
        Scalar::lemma_eqv_reflexive(pxw);
        Scalar::lemma_eqv_reflexive(rxw);
        Scalar::lemma_eqv_reflexive(qxw);
        Scalar::lemma_eqv_reflexive(sxw);
        Scalar::lemma_eqv_add_congruence(pxw, px, rxw, rx);
        Scalar::lemma_eqv_add_congruence(qxw, qx, sxw, sx);
        Scalar::lemma_eqv_transitive(px1, pxw.add_spec(rxw), px.add_spec(rx));
        Scalar::lemma_eqv_transitive(qx1, qxw.add_spec(sxw), qx.add_spec(sx));
        assert(px1.eqv_spec(px.add_spec(rx)));
        assert(qx1.eqv_spec(qx.add_spec(sx)));
        assert(lhs.x == px1.sub_spec(qx1));
        Scalar::lemma_eqv_sub_congruence(px1, px.add_spec(rx), qx1, qx.add_spec(sx));
        assert(lhs.x.eqv_spec(x_mid));
        Scalar::lemma_sub_add_distributes(px, rx, qx, sx);
        assert(x_mid.eqv_spec(x_rhs_mid));
        assert(rhs.x == px.sub_spec(qx).add_spec(rx.sub_spec(sx)));
        assert(rhs.x == x_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.x);
        assert(x_rhs_mid.eqv_spec(rhs.x));
        Scalar::lemma_eqv_transitive(lhs.x, x_mid, x_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.x, x_rhs_mid, rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        let py1 = u.z.add_spec(v.z).mul_spec(w.x);
        let qy1 = u.x.add_spec(v.x).mul_spec(w.z);
        let py = u.z.mul_spec(w.x);
        let ry = v.z.mul_spec(w.x);
        let qy = u.x.mul_spec(w.z);
        let sy = v.x.mul_spec(w.z);
        let y_mid = py.add_spec(ry).sub_spec(qy.add_spec(sy));
        let y_rhs_mid = py.sub_spec(qy).add_spec(ry.sub_spec(sy));

        Scalar::lemma_mul_distributes_over_add(w.x, u.z, v.z);
        Scalar::lemma_mul_distributes_over_add(w.z, u.x, v.x);
        Scalar::lemma_mul_commutative(u.z.add_spec(v.z), w.x);
        Scalar::lemma_mul_commutative(u.x.add_spec(v.x), w.z);
        assert(py1 == w.x.mul_spec(u.z.add_spec(v.z)));
        assert(qy1 == w.z.mul_spec(u.x.add_spec(v.x)));
        let pyw = w.x.mul_spec(u.z);
        let ryw = w.x.mul_spec(v.z);
        let qyw = w.z.mul_spec(u.x);
        let syw = w.z.mul_spec(v.x);
        assert(py1.eqv_spec(pyw.add_spec(ryw)));
        assert(qy1.eqv_spec(qyw.add_spec(syw)));
        Scalar::lemma_mul_commutative(w.x, u.z);
        Scalar::lemma_mul_commutative(w.x, v.z);
        Scalar::lemma_mul_commutative(w.z, u.x);
        Scalar::lemma_mul_commutative(w.z, v.x);
        assert(pyw == py);
        assert(ryw == ry);
        assert(qyw == qy);
        assert(syw == sy);
        Scalar::lemma_eqv_reflexive(pyw);
        Scalar::lemma_eqv_reflexive(ryw);
        Scalar::lemma_eqv_reflexive(qyw);
        Scalar::lemma_eqv_reflexive(syw);
        Scalar::lemma_eqv_add_congruence(pyw, py, ryw, ry);
        Scalar::lemma_eqv_add_congruence(qyw, qy, syw, sy);
        Scalar::lemma_eqv_transitive(py1, pyw.add_spec(ryw), py.add_spec(ry));
        Scalar::lemma_eqv_transitive(qy1, qyw.add_spec(syw), qy.add_spec(sy));
        assert(py1.eqv_spec(py.add_spec(ry)));
        assert(qy1.eqv_spec(qy.add_spec(sy)));
        assert(lhs.y == py1.sub_spec(qy1));
        Scalar::lemma_eqv_sub_congruence(py1, py.add_spec(ry), qy1, qy.add_spec(sy));
        assert(lhs.y.eqv_spec(y_mid));
        Scalar::lemma_sub_add_distributes(py, ry, qy, sy);
        assert(y_mid.eqv_spec(y_rhs_mid));
        assert(rhs.y == py.sub_spec(qy).add_spec(ry.sub_spec(sy)));
        assert(rhs.y == y_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.y);
        assert(y_rhs_mid.eqv_spec(rhs.y));
        Scalar::lemma_eqv_transitive(lhs.y, y_mid, y_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.y, y_rhs_mid, rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        let pz1 = u.x.add_spec(v.x).mul_spec(w.y);
        let qz1 = u.y.add_spec(v.y).mul_spec(w.x);
        let pz = u.x.mul_spec(w.y);
        let rz = v.x.mul_spec(w.y);
        let qz = u.y.mul_spec(w.x);
        let sz = v.y.mul_spec(w.x);
        let z_mid = pz.add_spec(rz).sub_spec(qz.add_spec(sz));
        let z_rhs_mid = pz.sub_spec(qz).add_spec(rz.sub_spec(sz));

        Scalar::lemma_mul_distributes_over_add(w.y, u.x, v.x);
        Scalar::lemma_mul_distributes_over_add(w.x, u.y, v.y);
        Scalar::lemma_mul_commutative(u.x.add_spec(v.x), w.y);
        Scalar::lemma_mul_commutative(u.y.add_spec(v.y), w.x);
        assert(pz1 == w.y.mul_spec(u.x.add_spec(v.x)));
        assert(qz1 == w.x.mul_spec(u.y.add_spec(v.y)));
        let pzw = w.y.mul_spec(u.x);
        let rzw = w.y.mul_spec(v.x);
        let qzw = w.x.mul_spec(u.y);
        let szw = w.x.mul_spec(v.y);
        assert(pz1.eqv_spec(pzw.add_spec(rzw)));
        assert(qz1.eqv_spec(qzw.add_spec(szw)));
        Scalar::lemma_mul_commutative(w.y, u.x);
        Scalar::lemma_mul_commutative(w.y, v.x);
        Scalar::lemma_mul_commutative(w.x, u.y);
        Scalar::lemma_mul_commutative(w.x, v.y);
        assert(pzw == pz);
        assert(rzw == rz);
        assert(qzw == qz);
        assert(szw == sz);
        Scalar::lemma_eqv_reflexive(pzw);
        Scalar::lemma_eqv_reflexive(rzw);
        Scalar::lemma_eqv_reflexive(qzw);
        Scalar::lemma_eqv_reflexive(szw);
        Scalar::lemma_eqv_add_congruence(pzw, pz, rzw, rz);
        Scalar::lemma_eqv_add_congruence(qzw, qz, szw, sz);
        Scalar::lemma_eqv_transitive(pz1, pzw.add_spec(rzw), pz.add_spec(rz));
        Scalar::lemma_eqv_transitive(qz1, qzw.add_spec(szw), qz.add_spec(sz));
        assert(pz1.eqv_spec(pz.add_spec(rz)));
        assert(qz1.eqv_spec(qz.add_spec(sz)));
        assert(lhs.z == pz1.sub_spec(qz1));
        Scalar::lemma_eqv_sub_congruence(pz1, pz.add_spec(rz), qz1, qz.add_spec(sz));
        assert(lhs.z.eqv_spec(z_mid));
        Scalar::lemma_sub_add_distributes(pz, rz, qz, sz);
        assert(z_mid.eqv_spec(z_rhs_mid));
        assert(rhs.z == pz.sub_spec(qz).add_spec(rz.sub_spec(sz)));
        assert(rhs.z == z_rhs_mid);
        Scalar::lemma_eqv_reflexive(rhs.z);
        assert(z_rhs_mid.eqv_spec(rhs.z));
        Scalar::lemma_eqv_transitive(lhs.z, z_mid, z_rhs_mid);
        Scalar::lemma_eqv_transitive(lhs.z, z_rhs_mid, rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_scale_extract_left(v: Self, w: Self, k: Scalar)
        ensures
            v.cross_spec(w).scale_spec(k).eqv_spec(v.scale_spec(k).cross_spec(w)),
    {
        let lhs = v.scale_spec(k).cross_spec(w);
        let rhs = v.cross_spec(w).scale_spec(k);

        let px = v.y.mul_spec(w.z);
        let qx = v.z.mul_spec(w.y);
        let px1 = v.y.mul_spec(k).mul_spec(w.z);
        let qx1 = v.z.mul_spec(k).mul_spec(w.y);
        let px2 = k.mul_spec(px);
        let qx2 = k.mul_spec(qx);
        let x_mid = px2.sub_spec(qx2);
        let x_rhs_add = px2.add_spec(qx2.neg_spec());

        let pxx2 = k.mul_spec(v.y).mul_spec(w.z);
        let qxx2 = k.mul_spec(v.z).mul_spec(w.y);
        Scalar::lemma_mul_commutative(v.y, k);
        Scalar::lemma_mul_commutative(v.z, k);
        assert(v.y.mul_spec(k) == k.mul_spec(v.y));
        assert(v.z.mul_spec(k) == k.mul_spec(v.z));
        assert(px1 == pxx2);
        assert(qx1 == qxx2);
        Scalar::lemma_mul_associative(k, v.y, w.z);
        Scalar::lemma_mul_associative(k, v.z, w.y);
        Scalar::lemma_eqv_reflexive(px1);
        Scalar::lemma_eqv_reflexive(qx1);
        assert(px1.eqv_spec(pxx2));
        assert(qx1.eqv_spec(qxx2));
        Scalar::lemma_eqv_transitive(px1, pxx2, px2);
        Scalar::lemma_eqv_transitive(qx1, qxx2, qx2);
        assert(px1.eqv_spec(px2));
        assert(qx1.eqv_spec(qx2));
        assert(lhs.x == px1.sub_spec(qx1));
        Scalar::lemma_eqv_sub_congruence(px1, px2, qx1, qx2);
        assert(lhs.x.eqv_spec(x_mid));
        Scalar::lemma_sub_is_add_neg(px, qx);
        assert(v.cross_spec(w).x == px.sub_spec(qx));
        assert(px.sub_spec(qx) == px.add_spec(qx.neg_spec()));
        assert(rhs.x == v.cross_spec(w).x.mul_spec(k));
        assert(rhs.x == px.add_spec(qx.neg_spec()).mul_spec(k));
        Scalar::lemma_mul_commutative(px.add_spec(qx.neg_spec()), k);
        assert(rhs.x == k.mul_spec(px.add_spec(qx.neg_spec())));
        Scalar::lemma_eqv_mul_distributive_left(k, px, qx.neg_spec());
        assert(rhs.x.eqv_spec(px2.add_spec(k.mul_spec(qx.neg_spec()))));
        Scalar::lemma_mul_neg_right(k, qx);
        assert(k.mul_spec(qx.neg_spec()) == k.mul_spec(qx).neg_spec());
        assert(rhs.x.eqv_spec(x_rhs_add));
        assert(x_mid == x_rhs_add);
        Scalar::lemma_eqv_reflexive(x_mid);
        assert(x_mid.eqv_spec(rhs.x));
        Scalar::lemma_eqv_transitive(lhs.x, x_mid, rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        let py = v.z.mul_spec(w.x);
        let qy = v.x.mul_spec(w.z);
        let py1 = v.z.mul_spec(k).mul_spec(w.x);
        let qy1 = v.x.mul_spec(k).mul_spec(w.z);
        let py2 = k.mul_spec(py);
        let qy2 = k.mul_spec(qy);
        let y_mid = py2.sub_spec(qy2);
        let y_rhs_add = py2.add_spec(qy2.neg_spec());

        let pyy2 = k.mul_spec(v.z).mul_spec(w.x);
        let qyy2 = k.mul_spec(v.x).mul_spec(w.z);
        Scalar::lemma_mul_commutative(v.z, k);
        Scalar::lemma_mul_commutative(v.x, k);
        assert(v.z.mul_spec(k) == k.mul_spec(v.z));
        assert(v.x.mul_spec(k) == k.mul_spec(v.x));
        assert(py1 == pyy2);
        assert(qy1 == qyy2);
        Scalar::lemma_mul_associative(k, v.z, w.x);
        Scalar::lemma_mul_associative(k, v.x, w.z);
        Scalar::lemma_eqv_reflexive(py1);
        Scalar::lemma_eqv_reflexive(qy1);
        assert(py1.eqv_spec(pyy2));
        assert(qy1.eqv_spec(qyy2));
        Scalar::lemma_eqv_transitive(py1, pyy2, py2);
        Scalar::lemma_eqv_transitive(qy1, qyy2, qy2);
        assert(py1.eqv_spec(py2));
        assert(qy1.eqv_spec(qy2));
        assert(lhs.y == py1.sub_spec(qy1));
        Scalar::lemma_eqv_sub_congruence(py1, py2, qy1, qy2);
        assert(lhs.y.eqv_spec(y_mid));
        Scalar::lemma_sub_is_add_neg(py, qy);
        assert(v.cross_spec(w).y == py.sub_spec(qy));
        assert(py.sub_spec(qy) == py.add_spec(qy.neg_spec()));
        assert(rhs.y == v.cross_spec(w).y.mul_spec(k));
        assert(rhs.y == py.add_spec(qy.neg_spec()).mul_spec(k));
        Scalar::lemma_mul_commutative(py.add_spec(qy.neg_spec()), k);
        assert(rhs.y == k.mul_spec(py.add_spec(qy.neg_spec())));
        Scalar::lemma_eqv_mul_distributive_left(k, py, qy.neg_spec());
        assert(rhs.y.eqv_spec(py2.add_spec(k.mul_spec(qy.neg_spec()))));
        Scalar::lemma_mul_neg_right(k, qy);
        assert(k.mul_spec(qy.neg_spec()) == k.mul_spec(qy).neg_spec());
        assert(rhs.y.eqv_spec(y_rhs_add));
        assert(y_mid == y_rhs_add);
        Scalar::lemma_eqv_reflexive(y_mid);
        assert(y_mid.eqv_spec(rhs.y));
        Scalar::lemma_eqv_transitive(lhs.y, y_mid, rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        let pz = v.x.mul_spec(w.y);
        let qz = v.y.mul_spec(w.x);
        let pz1 = v.x.mul_spec(k).mul_spec(w.y);
        let qz1 = v.y.mul_spec(k).mul_spec(w.x);
        let pz2 = k.mul_spec(pz);
        let qz2 = k.mul_spec(qz);
        let z_mid = pz2.sub_spec(qz2);
        let z_rhs_add = pz2.add_spec(qz2.neg_spec());

        let pzz2 = k.mul_spec(v.x).mul_spec(w.y);
        let qzz2 = k.mul_spec(v.y).mul_spec(w.x);
        Scalar::lemma_mul_commutative(v.x, k);
        Scalar::lemma_mul_commutative(v.y, k);
        assert(v.x.mul_spec(k) == k.mul_spec(v.x));
        assert(v.y.mul_spec(k) == k.mul_spec(v.y));
        assert(pz1 == pzz2);
        assert(qz1 == qzz2);
        Scalar::lemma_mul_associative(k, v.x, w.y);
        Scalar::lemma_mul_associative(k, v.y, w.x);
        Scalar::lemma_eqv_reflexive(pz1);
        Scalar::lemma_eqv_reflexive(qz1);
        assert(pz1.eqv_spec(pzz2));
        assert(qz1.eqv_spec(qzz2));
        Scalar::lemma_eqv_transitive(pz1, pzz2, pz2);
        Scalar::lemma_eqv_transitive(qz1, qzz2, qz2);
        assert(pz1.eqv_spec(pz2));
        assert(qz1.eqv_spec(qz2));
        assert(lhs.z == pz1.sub_spec(qz1));
        Scalar::lemma_eqv_sub_congruence(pz1, pz2, qz1, qz2);
        assert(lhs.z.eqv_spec(z_mid));
        Scalar::lemma_sub_is_add_neg(pz, qz);
        assert(v.cross_spec(w).z == pz.sub_spec(qz));
        assert(pz.sub_spec(qz) == pz.add_spec(qz.neg_spec()));
        assert(rhs.z == v.cross_spec(w).z.mul_spec(k));
        assert(rhs.z == pz.add_spec(qz.neg_spec()).mul_spec(k));
        Scalar::lemma_mul_commutative(pz.add_spec(qz.neg_spec()), k);
        assert(rhs.z == k.mul_spec(pz.add_spec(qz.neg_spec())));
        Scalar::lemma_eqv_mul_distributive_left(k, pz, qz.neg_spec());
        assert(rhs.z.eqv_spec(pz2.add_spec(k.mul_spec(qz.neg_spec()))));
        Scalar::lemma_mul_neg_right(k, qz);
        assert(k.mul_spec(qz.neg_spec()) == k.mul_spec(qz).neg_spec());
        assert(rhs.z.eqv_spec(z_rhs_add));
        assert(z_mid == z_rhs_add);
        Scalar::lemma_eqv_reflexive(z_mid);
        assert(z_mid.eqv_spec(rhs.z));
        Scalar::lemma_eqv_transitive(lhs.z, z_mid, rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_cross_scale_extract_right(v: Self, w: Self, k: Scalar)
        ensures
            v.cross_spec(w.scale_spec(k)).eqv_spec(v.cross_spec(w).scale_spec(k)),
    {
        let lhs = v.cross_spec(w.scale_spec(k));
        let c = v.cross_spec(w);
        let m = w.scale_spec(k).cross_spec(v);
        let n = w.cross_spec(v).scale_spec(k);
        let nn = n.neg_spec();

        Self::lemma_cross_antisymmetric(v, w.scale_spec(k));
        assert(lhs == m.neg_spec());
        Self::lemma_cross_scale_extract_left(w, v, k);
        assert(m.eqv_spec(n));
        Scalar::lemma_eqv_neg_congruence(m.x, n.x);
        Scalar::lemma_eqv_neg_congruence(m.y, n.y);
        Scalar::lemma_eqv_neg_congruence(m.z, n.z);
        assert(m.neg_spec().x.eqv_spec(n.neg_spec().x));
        assert(m.neg_spec().y.eqv_spec(n.neg_spec().y));
        assert(m.neg_spec().z.eqv_spec(n.neg_spec().z));
        assert(m.neg_spec().eqv_spec(n.neg_spec()));
        assert(lhs.eqv_spec(nn));

        Self::lemma_cross_antisymmetric(w, v);
        assert(w.cross_spec(v) == c.neg_spec());
        assert(n == c.neg_spec().scale_spec(k));
        Self::lemma_scale_neg_vector(c, k);
        assert(c.neg_spec().scale_spec(k) == c.scale_spec(k).neg_spec());
        assert(n == c.scale_spec(k).neg_spec());
        assert(nn == c.scale_spec(k).neg_spec().neg_spec());
        Self::lemma_neg_involution(c.scale_spec(k));
        assert(nn == c.scale_spec(k));
        assert(lhs.x.eqv_spec(nn.x));
        assert(lhs.y.eqv_spec(nn.y));
        assert(lhs.z.eqv_spec(nn.z));
        assert(lhs.x.eqv_spec(c.scale_spec(k).x));
        assert(lhs.y.eqv_spec(c.scale_spec(k).y));
        assert(lhs.z.eqv_spec(c.scale_spec(k).z));
        Self::lemma_eqv_from_components(lhs, c.scale_spec(k));
        assert(lhs.eqv_spec(c.scale_spec(k)));
    }

    pub proof fn lemma_cross_self_zero(v: Self)
        ensures
            v.cross_spec(v).eqv_spec(Self::zero_spec()),
    {
        let c = v.cross_spec(v);
        let z = Self::zero_spec();

        Scalar::lemma_mul_commutative(v.y, v.z);
        Scalar::lemma_mul_commutative(v.z, v.x);
        Scalar::lemma_mul_commutative(v.x, v.y);
        assert(v.y.mul_spec(v.z) == v.z.mul_spec(v.y));
        assert(v.z.mul_spec(v.x) == v.x.mul_spec(v.z));
        assert(v.x.mul_spec(v.y) == v.y.mul_spec(v.x));

        assert(c.x == v.y.mul_spec(v.z).sub_spec(v.z.mul_spec(v.y)));
        assert(c.y == v.z.mul_spec(v.x).sub_spec(v.x.mul_spec(v.z)));
        assert(c.z == v.x.mul_spec(v.y).sub_spec(v.y.mul_spec(v.x)));

        Scalar::lemma_sub_self_zero_num(v.y.mul_spec(v.z));
        Scalar::lemma_sub_self_zero_num(v.z.mul_spec(v.x));
        Scalar::lemma_sub_self_zero_num(v.x.mul_spec(v.y));
        assert(c.x.num == 0);
        assert(c.y.num == 0);
        assert(c.z.num == 0);

        Scalar::lemma_eqv_zero_iff_num_zero(c.x);
        Scalar::lemma_eqv_zero_iff_num_zero(c.y);
        Scalar::lemma_eqv_zero_iff_num_zero(c.z);
        assert(c.x.eqv_spec(z.x));
        assert(c.y.eqv_spec(z.y));
        assert(c.z.eqv_spec(z.z));
        assert(c.eqv_spec(z));
    }
}

} // verus!
