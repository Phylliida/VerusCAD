use crate::scalar::Scalar;
use crate::vec4::Vec4;
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

    pub open spec fn real_spec(s: Scalar) -> Self {
        Quaternion { w: s, x: Scalar::from_int_spec(0), y: Scalar::from_int_spec(0), z: Scalar::from_int_spec(0) }
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

    pub open spec fn as_vec4_spec(self) -> Vec4 {
        Vec4 { x: self.w, y: self.x, z: self.y, w: self.z }
    }

    pub open spec fn inverse_spec(self) -> Self
        recommends
            self.norm2_spec().num > 0,
    {
        let n = self.norm2_spec();
        let inv_n = Scalar { num: n.denom(), den: (n.num - 1) as nat };
        self.conjugate_spec().scale_spec(inv_n)
    }

    pub proof fn lemma_eqv_from_components(a: Self, b: Self)
        requires
            a.w.eqv_spec(b.w),
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
        Scalar::lemma_eqv_reflexive(a.w);
        Scalar::lemma_eqv_reflexive(a.x);
        Scalar::lemma_eqv_reflexive(a.y);
        Scalar::lemma_eqv_reflexive(a.z);
        assert(a.eqv_spec(a));
    }

    pub proof fn lemma_eqv_symmetric(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            b.eqv_spec(a),
    {
        Scalar::lemma_eqv_symmetric(a.w, b.w);
        Scalar::lemma_eqv_symmetric(a.x, b.x);
        Scalar::lemma_eqv_symmetric(a.y, b.y);
        Scalar::lemma_eqv_symmetric(a.z, b.z);
        assert(b.eqv_spec(a));
    }

    pub proof fn lemma_eqv_transitive(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
            b.eqv_spec(c),
        ensures
            a.eqv_spec(c),
    {
        Scalar::lemma_eqv_transitive(a.w, b.w, c.w);
        Scalar::lemma_eqv_transitive(a.x, b.x, c.x);
        Scalar::lemma_eqv_transitive(a.y, b.y, c.y);
        Scalar::lemma_eqv_transitive(a.z, b.z, c.z);
        assert(a.eqv_spec(c));
    }

    pub proof fn lemma_scale_eqv_congruence(u: Self, v: Self, k: Scalar)
        requires
            u.eqv_spec(v),
        ensures
            u.scale_spec(k).eqv_spec(v.scale_spec(k)),
    {
        let us = u.scale_spec(k);
        let vs = v.scale_spec(k);
        Scalar::lemma_eqv_mul_congruence_left(u.w, v.w, k);
        Scalar::lemma_eqv_mul_congruence_left(u.x, v.x, k);
        Scalar::lemma_eqv_mul_congruence_left(u.y, v.y, k);
        Scalar::lemma_eqv_mul_congruence_left(u.z, v.z, k);
        assert(us.w.eqv_spec(vs.w));
        assert(us.x.eqv_spec(vs.x));
        assert(us.y.eqv_spec(vs.y));
        assert(us.z.eqv_spec(vs.z));
        assert(us.eqv_spec(vs));
    }

    pub proof fn lemma_scale_eqv_scalar_congruence(v: Self, k1: Scalar, k2: Scalar)
        requires
            k1.eqv_spec(k2),
        ensures
            v.scale_spec(k1).eqv_spec(v.scale_spec(k2)),
    {
        let vk1 = v.scale_spec(k1);
        let vk2 = v.scale_spec(k2);
        Scalar::lemma_eqv_mul_congruence_right(v.w, k1, k2);
        Scalar::lemma_eqv_mul_congruence_right(v.x, k1, k2);
        Scalar::lemma_eqv_mul_congruence_right(v.y, k1, k2);
        Scalar::lemma_eqv_mul_congruence_right(v.z, k1, k2);
        assert(vk1.w.eqv_spec(vk2.w));
        assert(vk1.x.eqv_spec(vk2.x));
        assert(vk1.y.eqv_spec(vk2.y));
        assert(vk1.z.eqv_spec(vk2.z));
        assert(vk1.eqv_spec(vk2));
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

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Self::zero_spec()) == a,
            Self::zero_spec().add_spec(a) == a,
    {
        let z = Self::zero_spec();
        Scalar::lemma_add_zero_identity(a.w);
        Scalar::lemma_add_zero_identity(a.x);
        Scalar::lemma_add_zero_identity(a.y);
        Scalar::lemma_add_zero_identity(a.z);
        assert(a.add_spec(z).w == a.w);
        assert(a.add_spec(z).x == a.x);
        assert(a.add_spec(z).y == a.y);
        assert(a.add_spec(z).z == a.z);
        assert(a.add_spec(z) == a);
        assert(z.add_spec(a).w == a.w);
        assert(z.add_spec(a).x == a.x);
        assert(z.add_spec(a).y == a.y);
        assert(z.add_spec(a).z == a.z);
        assert(z.add_spec(a) == a);
    }

    pub proof fn lemma_neg_involution(a: Self)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        Scalar::lemma_neg_involution(a.w);
        Scalar::lemma_neg_involution(a.x);
        Scalar::lemma_neg_involution(a.y);
        Scalar::lemma_neg_involution(a.z);
        assert(a.neg_spec().neg_spec().w == a.w);
        assert(a.neg_spec().neg_spec().x == a.x);
        assert(a.neg_spec().neg_spec().y == a.y);
        assert(a.neg_spec().neg_spec().z == a.z);
        assert(a.neg_spec().neg_spec() == a);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        Scalar::lemma_sub_is_add_neg(a.w, b.w);
        Scalar::lemma_sub_is_add_neg(a.x, b.x);
        Scalar::lemma_sub_is_add_neg(a.y, b.y);
        Scalar::lemma_sub_is_add_neg(a.z, b.z);
        assert(a.sub_spec(b).w == a.add_spec(b.neg_spec()).w);
        assert(a.sub_spec(b).x == a.add_spec(b.neg_spec()).x);
        assert(a.sub_spec(b).y == a.add_spec(b.neg_spec()).y);
        assert(a.sub_spec(b).z == a.add_spec(b.neg_spec()).z);
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
    }

    pub proof fn lemma_mul_one_identity(a: Self)
        ensures
            a.mul_spec(Self::one_spec()).eqv_spec(a),
            Self::one_spec().mul_spec(a).eqv_spec(a),
    {
        let one = Self::one_spec();
        let z = Scalar::from_int_spec(0);
        let lhs = a.mul_spec(one);
        let rhs = one.mul_spec(a);

        Scalar::lemma_mul_one_identity(a.w);
        Scalar::lemma_mul_one_identity(a.x);
        Scalar::lemma_mul_one_identity(a.y);
        Scalar::lemma_mul_one_identity(a.z);
        Scalar::lemma_mul_zero(a.w);
        Scalar::lemma_mul_zero(a.x);
        Scalar::lemma_mul_zero(a.y);
        Scalar::lemma_mul_zero(a.z);
        Scalar::lemma_sub_self_zero_num(z);
        Scalar::lemma_add_zero_identity(a.w);
        Scalar::lemma_add_zero_identity(a.x);
        Scalar::lemma_add_zero_identity(a.y);
        Scalar::lemma_add_zero_identity(a.z);

        assert(one.w == Scalar::from_int_spec(1));
        assert(one.x == z);
        assert(one.y == z);
        assert(one.z == z);

        let lx0 = a.w.mul_spec(one.x);
        let ly0 = a.w.mul_spec(one.y);
        let lz0 = a.w.mul_spec(one.z);
        let lx2 = a.y.mul_spec(one.z);
        let lx3 = a.z.mul_spec(one.y);
        let ly1 = a.x.mul_spec(one.z);
        let ly3 = a.z.mul_spec(one.x);
        let lz1 = a.x.mul_spec(one.y);
        let lz2 = a.y.mul_spec(one.x);

        let rw0 = one.x.mul_spec(a.x);
        let rw1 = one.y.mul_spec(a.y);
        let rw2 = one.z.mul_spec(a.z);
        let rx1 = one.x.mul_spec(a.w);
        let rx2 = one.y.mul_spec(a.z);
        let rx3 = one.z.mul_spec(a.y);
        let ry1 = one.x.mul_spec(a.z);
        let ry2 = one.y.mul_spec(a.w);
        let ry3 = one.z.mul_spec(a.x);
        let rz1 = one.x.mul_spec(a.y);
        let rz2 = one.y.mul_spec(a.x);
        let rz3 = one.z.mul_spec(a.w);

        assert(lx0.eqv_spec(z));
        assert(ly0.eqv_spec(z));
        assert(lz0.eqv_spec(z));
        assert(lx2.eqv_spec(z));
        assert(lx3.eqv_spec(z));
        assert(ly1.eqv_spec(z));
        assert(ly3.eqv_spec(z));
        assert(lz1.eqv_spec(z));
        assert(lz2.eqv_spec(z));
        assert(rw0.eqv_spec(z));
        assert(rw1.eqv_spec(z));
        assert(rw2.eqv_spec(z));
        assert(rx1.eqv_spec(z));
        assert(rx2.eqv_spec(z));
        assert(rx3.eqv_spec(z));
        assert(ry1.eqv_spec(z));
        assert(ry2.eqv_spec(z));
        assert(ry3.eqv_spec(z));
        assert(rz1.eqv_spec(z));
        assert(rz2.eqv_spec(z));
        assert(rz3.eqv_spec(z));

        assert(lhs.w == a.w.mul_spec(one.w).sub_spec(a.x.mul_spec(one.x)).sub_spec(a.y.mul_spec(one.y)).sub_spec(a.z.mul_spec(one.z)));
        assert(a.w.mul_spec(one.w) == a.w);
        let lw0 = a.w.sub_spec(a.x.mul_spec(one.x));
        Scalar::lemma_eqv_sub_congruence(a.w, a.w, a.x.mul_spec(one.x), z);
        assert(lw0.eqv_spec(a.w.sub_spec(z)));
        Scalar::lemma_add_zero_identity(a.w);
        assert(a.w.sub_spec(z) == a.w);
        assert(lw0.eqv_spec(a.w));
        let lw1 = lw0.sub_spec(a.y.mul_spec(one.y));
        Scalar::lemma_eqv_sub_congruence(lw0, a.w, a.y.mul_spec(one.y), z);
        assert(lw1.eqv_spec(a.w.sub_spec(z)));
        assert(a.w.sub_spec(z) == a.w);
        assert(lw1.eqv_spec(a.w));
        let lw2 = lw1.sub_spec(a.z.mul_spec(one.z));
        Scalar::lemma_eqv_sub_congruence(lw1, a.w, a.z.mul_spec(one.z), z);
        assert(lw2.eqv_spec(a.w.sub_spec(z)));
        assert(a.w.sub_spec(z) == a.w);
        assert(lw2.eqv_spec(a.w));
        assert(lhs.w == lw2);
        assert(lhs.w.eqv_spec(a.w));

        assert(lhs.x == lx0.add_spec(a.x.mul_spec(one.w)).add_spec(lx2).sub_spec(lx3));
        assert(a.x.mul_spec(one.w) == a.x);
        let lx_a = lx0.add_spec(a.x);
        Scalar::lemma_eqv_add_congruence(lx0, z, a.x, a.x);
        assert(lx_a.eqv_spec(z.add_spec(a.x)));
        Scalar::lemma_add_zero_identity(a.x);
        assert(z.add_spec(a.x) == a.x);
        assert(lx_a.eqv_spec(a.x));
        let lx_b = lx_a.add_spec(lx2);
        Scalar::lemma_eqv_add_congruence(lx_a, a.x, lx2, z);
        assert(lx_b.eqv_spec(a.x.add_spec(z)));
        assert(a.x.add_spec(z) == a.x);
        assert(lx_b.eqv_spec(a.x));
        let lx_c = lx_b.sub_spec(lx3);
        Scalar::lemma_eqv_sub_congruence(lx_b, a.x, lx3, z);
        assert(lx_c.eqv_spec(a.x.sub_spec(z)));
        assert(a.x.sub_spec(z) == a.x);
        assert(lx_c.eqv_spec(a.x));
        assert(lhs.x == lx_c);
        assert(lhs.x.eqv_spec(a.x));

        assert(lhs.y == ly0.sub_spec(ly1).add_spec(a.y.mul_spec(one.w)).add_spec(ly3));
        assert(a.y.mul_spec(one.w) == a.y);
        let ly_a = ly0.sub_spec(ly1);
        Scalar::lemma_eqv_sub_congruence(ly0, z, ly1, z);
        assert(ly_a.eqv_spec(z.sub_spec(z)));
        Scalar::lemma_sub_self_zero_num(z);
        assert(z.sub_spec(z).num == 0);
        Scalar::lemma_eqv_zero_iff_num_zero(z.sub_spec(z));
        assert(z.sub_spec(z).eqv_spec(z) == (z.sub_spec(z).num == 0));
        assert(z.sub_spec(z).eqv_spec(z));
        Scalar::lemma_eqv_transitive(ly_a, z.sub_spec(z), z);
        assert(ly_a.eqv_spec(z));
        let ly_b = ly_a.add_spec(a.y);
        Scalar::lemma_eqv_add_congruence(ly_a, z, a.y, a.y);
        assert(ly_b.eqv_spec(z.add_spec(a.y)));
        assert(z.add_spec(a.y) == a.y);
        assert(ly_b.eqv_spec(a.y));
        let ly_c = ly_b.add_spec(ly3);
        Scalar::lemma_eqv_add_congruence(ly_b, a.y, ly3, z);
        assert(ly_c.eqv_spec(a.y.add_spec(z)));
        assert(a.y.add_spec(z) == a.y);
        assert(ly_c.eqv_spec(a.y));
        assert(lhs.y == ly_c);
        assert(lhs.y.eqv_spec(a.y));

        assert(lhs.z == lz0.add_spec(lz1).sub_spec(lz2).add_spec(a.z.mul_spec(one.w)));
        assert(a.z.mul_spec(one.w) == a.z);
        let lz_a = lz0.add_spec(lz1);
        Scalar::lemma_eqv_add_congruence(lz0, z, lz1, z);
        assert(lz_a.eqv_spec(z.add_spec(z)));
        assert(z.add_spec(z) == z);
        assert(lz_a.eqv_spec(z));
        let lz_b = lz_a.sub_spec(lz2);
        Scalar::lemma_eqv_sub_congruence(lz_a, z, lz2, z);
        assert(lz_b.eqv_spec(z.sub_spec(z)));
        assert(z.sub_spec(z).eqv_spec(z));
        Scalar::lemma_eqv_transitive(lz_b, z.sub_spec(z), z);
        assert(lz_b.eqv_spec(z));
        let lz_c = lz_b.add_spec(a.z);
        Scalar::lemma_eqv_add_congruence(lz_b, z, a.z, a.z);
        assert(lz_c.eqv_spec(z.add_spec(a.z)));
        assert(z.add_spec(a.z) == a.z);
        assert(lz_c.eqv_spec(a.z));
        assert(lhs.z == lz_c);
        assert(lhs.z.eqv_spec(a.z));
        Self::lemma_eqv_from_components(lhs, a);
        assert(lhs.eqv_spec(a));

        assert(rhs.w == one.w.mul_spec(a.w).sub_spec(one.x.mul_spec(a.x)).sub_spec(one.y.mul_spec(a.y)).sub_spec(one.z.mul_spec(a.z)));
        assert(one.w.mul_spec(a.w) == a.w);
        let rw_a = a.w.sub_spec(rw0);
        Scalar::lemma_eqv_sub_congruence(a.w, a.w, rw0, z);
        assert(rw_a.eqv_spec(a.w.sub_spec(z)));
        assert(a.w.sub_spec(z) == a.w);
        assert(rw_a.eqv_spec(a.w));
        let rw_b = rw_a.sub_spec(rw1);
        Scalar::lemma_eqv_sub_congruence(rw_a, a.w, rw1, z);
        assert(rw_b.eqv_spec(a.w.sub_spec(z)));
        assert(a.w.sub_spec(z) == a.w);
        assert(rw_b.eqv_spec(a.w));
        let rw_c = rw_b.sub_spec(rw2);
        Scalar::lemma_eqv_sub_congruence(rw_b, a.w, rw2, z);
        assert(rw_c.eqv_spec(a.w.sub_spec(z)));
        assert(a.w.sub_spec(z) == a.w);
        assert(rw_c.eqv_spec(a.w));
        assert(rhs.w == rw_c);
        assert(rhs.w.eqv_spec(a.w));

        assert(rhs.x == one.w.mul_spec(a.x).add_spec(rx1).add_spec(rx2).sub_spec(rx3));
        assert(one.w.mul_spec(a.x) == a.x);
        let rx_a = a.x.add_spec(rx1);
        Scalar::lemma_eqv_add_congruence(a.x, a.x, rx1, z);
        assert(rx_a.eqv_spec(a.x.add_spec(z)));
        assert(a.x.add_spec(z) == a.x);
        assert(rx_a.eqv_spec(a.x));
        let rx_b = rx_a.add_spec(rx2);
        Scalar::lemma_eqv_add_congruence(rx_a, a.x, rx2, z);
        assert(rx_b.eqv_spec(a.x.add_spec(z)));
        assert(a.x.add_spec(z) == a.x);
        assert(rx_b.eqv_spec(a.x));
        let rx_c = rx_b.sub_spec(rx3);
        Scalar::lemma_eqv_sub_congruence(rx_b, a.x, rx3, z);
        assert(rx_c.eqv_spec(a.x.sub_spec(z)));
        assert(a.x.sub_spec(z) == a.x);
        assert(rx_c.eqv_spec(a.x));
        assert(rhs.x == rx_c);
        assert(rhs.x.eqv_spec(a.x));

        assert(rhs.y == one.w.mul_spec(a.y).sub_spec(ry1).add_spec(ry2).add_spec(ry3));
        assert(one.w.mul_spec(a.y) == a.y);
        let ry_a = a.y.sub_spec(ry1);
        Scalar::lemma_eqv_sub_congruence(a.y, a.y, ry1, z);
        assert(ry_a.eqv_spec(a.y.sub_spec(z)));
        assert(a.y.sub_spec(z) == a.y);
        assert(ry_a.eqv_spec(a.y));
        let ry_b = ry_a.add_spec(ry2);
        Scalar::lemma_eqv_add_congruence(ry_a, a.y, ry2, z);
        assert(ry_b.eqv_spec(a.y.add_spec(z)));
        assert(a.y.add_spec(z) == a.y);
        assert(ry_b.eqv_spec(a.y));
        let ry_c = ry_b.add_spec(ry3);
        Scalar::lemma_eqv_add_congruence(ry_b, a.y, ry3, z);
        assert(ry_c.eqv_spec(a.y.add_spec(z)));
        assert(a.y.add_spec(z) == a.y);
        assert(ry_c.eqv_spec(a.y));
        assert(rhs.y == ry_c);
        assert(rhs.y.eqv_spec(a.y));

        assert(rhs.z == one.w.mul_spec(a.z).add_spec(rz1).sub_spec(rz2).add_spec(rz3));
        assert(one.w.mul_spec(a.z) == a.z);
        let rz_a = a.z.add_spec(rz1);
        Scalar::lemma_eqv_add_congruence(a.z, a.z, rz1, z);
        assert(rz_a.eqv_spec(a.z.add_spec(z)));
        assert(a.z.add_spec(z) == a.z);
        assert(rz_a.eqv_spec(a.z));
        let rz_b = rz_a.sub_spec(rz2);
        Scalar::lemma_eqv_sub_congruence(rz_a, a.z, rz2, z);
        assert(rz_b.eqv_spec(a.z.sub_spec(z)));
        assert(a.z.sub_spec(z) == a.z);
        assert(rz_b.eqv_spec(a.z));
        let rz_c = rz_b.add_spec(rz3);
        Scalar::lemma_eqv_add_congruence(rz_b, a.z, rz3, z);
        assert(rz_c.eqv_spec(a.z.add_spec(z)));
        assert(a.z.add_spec(z) == a.z);
        assert(rz_c.eqv_spec(a.z));
        assert(rhs.z == rz_c);
        assert(rhs.z.eqv_spec(a.z));
        Self::lemma_eqv_from_components(rhs, a);
        assert(rhs.eqv_spec(a));
    }

    pub proof fn lemma_mul_noncommutative_witness()
        ensures
            {
                let i = Self::from_ints_spec(0, 1, 0, 0);
                let j = Self::from_ints_spec(0, 0, 1, 0);
                !i.mul_spec(j).eqv_spec(j.mul_spec(i))
            },
    {
        let i = Self::from_ints_spec(0, 1, 0, 0);
        let j = Self::from_ints_spec(0, 0, 1, 0);
        let ij = i.mul_spec(j);
        let ji = j.mul_spec(i);
        let one = Scalar::from_int_spec(1);
        let neg_one = Scalar::from_int_spec(-1);
        assert(ij.w == Scalar::from_int_spec(0));
        assert(ij.x == Scalar::from_int_spec(0));
        assert(ij.y == Scalar::from_int_spec(0));
        assert(ij.z.eqv_spec(one));
        assert(ji.w == Scalar::from_int_spec(0));
        assert(ji.x == Scalar::from_int_spec(0));
        assert(ji.y == Scalar::from_int_spec(0));
        assert(ji.z.eqv_spec(neg_one));
        assert(one.num == 1);
        assert(neg_one.num == -1);
        assert(one.denom() == 1);
        assert(neg_one.denom() == 1);
        assert(one.eqv_spec(neg_one) == (one.num * neg_one.denom() == neg_one.num * one.denom()));
        assert(one.eqv_spec(neg_one) == (1 * 1 == (-1) * 1));
        assert(!(1 * 1 == (-1) * 1)) by (nonlinear_arith);
        assert(!one.eqv_spec(neg_one));
        if ij.eqv_spec(ji) {
            assert(ij.z.eqv_spec(ji.z));
            Scalar::lemma_eqv_transitive(one, ij.z, ji.z);
            Scalar::lemma_eqv_transitive(one, ji.z, neg_one);
            assert(one.eqv_spec(neg_one));
            assert(false);
        }
        assert(!ij.eqv_spec(ji));
        assert(!i.mul_spec(j).eqv_spec(j.mul_spec(i)));
    }

    pub proof fn lemma_mul_scale_right(a: Self, b: Self, k: Scalar)
        ensures
            a.mul_spec(b.scale_spec(k)).eqv_spec(a.mul_spec(b).scale_spec(k)),
    {
        let bs = b.scale_spec(k);
        let lhs = a.mul_spec(bs);
        let ab = a.mul_spec(b);
        let rhs = ab.scale_spec(k);

        let w0 = a.w.mul_spec(b.w);
        let w1 = a.x.mul_spec(b.x);
        let w2 = a.y.mul_spec(b.y);
        let w3 = a.z.mul_spec(b.z);
        let wb = w0.sub_spec(w1).sub_spec(w2).sub_spec(w3);
        let wk = w0.mul_spec(k).sub_spec(w1.mul_spec(k)).sub_spec(w2.mul_spec(k)).sub_spec(w3.mul_spec(k));

        let x0 = a.w.mul_spec(b.x);
        let x1 = a.x.mul_spec(b.w);
        let x2 = a.y.mul_spec(b.z);
        let x3 = a.z.mul_spec(b.y);
        let xb = x0.add_spec(x1).add_spec(x2).sub_spec(x3);
        let xk = x0.mul_spec(k).add_spec(x1.mul_spec(k)).add_spec(x2.mul_spec(k)).sub_spec(x3.mul_spec(k));

        let y0 = a.w.mul_spec(b.y);
        let y1 = a.x.mul_spec(b.z);
        let y2 = a.y.mul_spec(b.w);
        let y3 = a.z.mul_spec(b.x);
        let yb = y0.sub_spec(y1).add_spec(y2).add_spec(y3);
        let yk = y0.mul_spec(k).sub_spec(y1.mul_spec(k)).add_spec(y2.mul_spec(k)).add_spec(y3.mul_spec(k));

        let z0 = a.w.mul_spec(b.z);
        let z1 = a.x.mul_spec(b.y);
        let z2 = a.y.mul_spec(b.x);
        let z3 = a.z.mul_spec(b.w);
        let zb = z0.add_spec(z1).sub_spec(z2).add_spec(z3);
        let zk = z0.mul_spec(k).add_spec(z1.mul_spec(k)).sub_spec(z2.mul_spec(k)).add_spec(z3.mul_spec(k));

        assert(lhs.w == a.w.mul_spec(bs.w).sub_spec(a.x.mul_spec(bs.x)).sub_spec(a.y.mul_spec(bs.y)).sub_spec(a.z.mul_spec(bs.z)));
        assert(lhs.x == a.w.mul_spec(bs.x).add_spec(a.x.mul_spec(bs.w)).add_spec(a.y.mul_spec(bs.z)).sub_spec(a.z.mul_spec(bs.y)));
        assert(lhs.y == a.w.mul_spec(bs.y).sub_spec(a.x.mul_spec(bs.z)).add_spec(a.y.mul_spec(bs.w)).add_spec(a.z.mul_spec(bs.x)));
        assert(lhs.z == a.w.mul_spec(bs.z).add_spec(a.x.mul_spec(bs.y)).sub_spec(a.y.mul_spec(bs.x)).add_spec(a.z.mul_spec(bs.w)));

        assert(bs.w == b.w.mul_spec(k));
        assert(bs.x == b.x.mul_spec(k));
        assert(bs.y == b.y.mul_spec(k));
        assert(bs.z == b.z.mul_spec(k));

        let lw0 = a.w.mul_spec(bs.w);
        let lw1 = a.x.mul_spec(bs.x);
        let lw2 = a.y.mul_spec(bs.y);
        let lw3 = a.z.mul_spec(bs.z);
        let lx0 = a.w.mul_spec(bs.x);
        let lx1 = a.x.mul_spec(bs.w);
        let lx2 = a.y.mul_spec(bs.z);
        let lx3 = a.z.mul_spec(bs.y);
        let ly0 = a.w.mul_spec(bs.y);
        let ly1 = a.x.mul_spec(bs.z);
        let ly2 = a.y.mul_spec(bs.w);
        let ly3 = a.z.mul_spec(bs.x);
        let lz0 = a.w.mul_spec(bs.z);
        let lz1 = a.x.mul_spec(bs.y);
        let lz2 = a.y.mul_spec(bs.x);
        let lz3 = a.z.mul_spec(bs.w);

        Scalar::lemma_mul_associative(a.w, b.w, k);
        Scalar::lemma_mul_associative(a.x, b.x, k);
        Scalar::lemma_mul_associative(a.y, b.y, k);
        Scalar::lemma_mul_associative(a.z, b.z, k);
        Scalar::lemma_mul_associative(a.w, b.x, k);
        Scalar::lemma_mul_associative(a.x, b.w, k);
        Scalar::lemma_mul_associative(a.y, b.z, k);
        Scalar::lemma_mul_associative(a.z, b.y, k);
        Scalar::lemma_mul_associative(a.w, b.y, k);
        Scalar::lemma_mul_associative(a.x, b.z, k);
        Scalar::lemma_mul_associative(a.y, b.w, k);
        Scalar::lemma_mul_associative(a.z, b.x, k);
        Scalar::lemma_mul_associative(a.w, b.z, k);
        Scalar::lemma_mul_associative(a.x, b.y, k);
        Scalar::lemma_mul_associative(a.y, b.x, k);
        Scalar::lemma_mul_associative(a.z, b.w, k);

        assert(lw0.eqv_spec(w0.mul_spec(k)));
        assert(lw1.eqv_spec(w1.mul_spec(k)));
        assert(lw2.eqv_spec(w2.mul_spec(k)));
        assert(lw3.eqv_spec(w3.mul_spec(k)));
        assert(lx0.eqv_spec(x0.mul_spec(k)));
        assert(lx1.eqv_spec(x1.mul_spec(k)));
        assert(lx2.eqv_spec(x2.mul_spec(k)));
        assert(lx3.eqv_spec(x3.mul_spec(k)));
        assert(ly0.eqv_spec(y0.mul_spec(k)));
        assert(ly1.eqv_spec(y1.mul_spec(k)));
        assert(ly2.eqv_spec(y2.mul_spec(k)));
        assert(ly3.eqv_spec(y3.mul_spec(k)));
        assert(lz0.eqv_spec(z0.mul_spec(k)));
        assert(lz1.eqv_spec(z1.mul_spec(k)));
        assert(lz2.eqv_spec(z2.mul_spec(k)));
        assert(lz3.eqv_spec(z3.mul_spec(k)));

        let lww = lw0.sub_spec(lw1).sub_spec(lw2).sub_spec(lw3);
        let lxx = lx0.add_spec(lx1).add_spec(lx2).sub_spec(lx3);
        let lyy = ly0.sub_spec(ly1).add_spec(ly2).add_spec(ly3);
        let lzz = lz0.add_spec(lz1).sub_spec(lz2).add_spec(lz3);
        assert(lhs.w == lww);
        assert(lhs.x == lxx);
        assert(lhs.y == lyy);
        assert(lhs.z == lzz);

        Scalar::lemma_eqv_sub_congruence(lw0, w0.mul_spec(k), lw1, w1.mul_spec(k));
        Scalar::lemma_eqv_sub_congruence(lw0.sub_spec(lw1), w0.mul_spec(k).sub_spec(w1.mul_spec(k)), lw2, w2.mul_spec(k));
        Scalar::lemma_eqv_sub_congruence(
            lw0.sub_spec(lw1).sub_spec(lw2),
            w0.mul_spec(k).sub_spec(w1.mul_spec(k)).sub_spec(w2.mul_spec(k)),
            lw3,
            w3.mul_spec(k),
        );
        assert(lww.eqv_spec(wk));

        Scalar::lemma_eqv_add_congruence(lx0, x0.mul_spec(k), lx1, x1.mul_spec(k));
        Scalar::lemma_eqv_add_congruence(lx0.add_spec(lx1), x0.mul_spec(k).add_spec(x1.mul_spec(k)), lx2, x2.mul_spec(k));
        Scalar::lemma_eqv_sub_congruence(
            lx0.add_spec(lx1).add_spec(lx2),
            x0.mul_spec(k).add_spec(x1.mul_spec(k)).add_spec(x2.mul_spec(k)),
            lx3,
            x3.mul_spec(k),
        );
        assert(lxx.eqv_spec(xk));

        Scalar::lemma_eqv_sub_congruence(ly0, y0.mul_spec(k), ly1, y1.mul_spec(k));
        Scalar::lemma_eqv_add_congruence(ly0.sub_spec(ly1), y0.mul_spec(k).sub_spec(y1.mul_spec(k)), ly2, y2.mul_spec(k));
        Scalar::lemma_eqv_add_congruence(
            ly0.sub_spec(ly1).add_spec(ly2),
            y0.mul_spec(k).sub_spec(y1.mul_spec(k)).add_spec(y2.mul_spec(k)),
            ly3,
            y3.mul_spec(k),
        );
        assert(lyy.eqv_spec(yk));

        Scalar::lemma_eqv_add_congruence(lz0, z0.mul_spec(k), lz1, z1.mul_spec(k));
        Scalar::lemma_eqv_sub_congruence(lz0.add_spec(lz1), z0.mul_spec(k).add_spec(z1.mul_spec(k)), lz2, z2.mul_spec(k));
        Scalar::lemma_eqv_add_congruence(
            lz0.add_spec(lz1).sub_spec(lz2),
            z0.mul_spec(k).add_spec(z1.mul_spec(k)).sub_spec(z2.mul_spec(k)),
            lz3,
            z3.mul_spec(k),
        );
        assert(lzz.eqv_spec(zk));

        let w01 = w0.sub_spec(w1);
        let w012 = w01.sub_spec(w2);
        Scalar::lemma_sub_mul_right(w01, w2, k);
        Scalar::lemma_sub_mul_right(w012, w3, k);
        Scalar::lemma_sub_mul_right(w0, w1, k);
        let wk01 = w0.mul_spec(k).sub_spec(w1.mul_spec(k));
        let wk012 = wk01.sub_spec(w2.mul_spec(k));
        let wk0123 = wk012.sub_spec(w3.mul_spec(k));
        assert(wk == wk0123);
        assert(wb == w012.sub_spec(w3));
        assert(wb.mul_spec(k).eqv_spec(w012.mul_spec(k).sub_spec(w3.mul_spec(k))));
        assert(w012.mul_spec(k).eqv_spec(w01.mul_spec(k).sub_spec(w2.mul_spec(k))));
        assert(w01.mul_spec(k).eqv_spec(w0.mul_spec(k).sub_spec(w1.mul_spec(k))));
        Scalar::lemma_eqv_sub_congruence(w01.mul_spec(k), wk01, w2.mul_spec(k), w2.mul_spec(k));
        assert(w01.mul_spec(k).sub_spec(w2.mul_spec(k)).eqv_spec(wk012));
        Scalar::lemma_eqv_transitive(w012.mul_spec(k), w01.mul_spec(k).sub_spec(w2.mul_spec(k)), wk012);
        assert(w012.mul_spec(k).eqv_spec(wk012));
        Scalar::lemma_eqv_sub_congruence(w012.mul_spec(k), wk012, w3.mul_spec(k), w3.mul_spec(k));
        assert(w012.mul_spec(k).sub_spec(w3.mul_spec(k)).eqv_spec(wk0123));
        Scalar::lemma_eqv_transitive(wb.mul_spec(k), w012.mul_spec(k).sub_spec(w3.mul_spec(k)), wk0123);
        assert(wb.mul_spec(k).eqv_spec(wk0123));
        Scalar::lemma_eqv_transitive(wb.mul_spec(k), wk0123, wk);
        assert(wb.mul_spec(k).eqv_spec(wk));

        let x01 = x0.add_spec(x1);
        let x012 = x01.add_spec(x2);
        Scalar::lemma_eqv_mul_distributive_right(x0, x1, k);
        Scalar::lemma_eqv_mul_distributive_right(x01, x2, k);
        let xk01 = x0.mul_spec(k).add_spec(x1.mul_spec(k));
        let xk012 = xk01.add_spec(x2.mul_spec(k));
        assert(xk == xk012.sub_spec(x3.mul_spec(k)));
        assert(x01.mul_spec(k).eqv_spec(xk01));
        Scalar::lemma_eqv_add_congruence(x01.mul_spec(k), xk01, x2.mul_spec(k), x2.mul_spec(k));
        assert(x01.mul_spec(k).add_spec(x2.mul_spec(k)).eqv_spec(xk012));
        assert(x012.mul_spec(k).eqv_spec(x01.mul_spec(k).add_spec(x2.mul_spec(k))));
        Scalar::lemma_eqv_transitive(x012.mul_spec(k), x01.mul_spec(k).add_spec(x2.mul_spec(k)), xk012);
        assert(x012.mul_spec(k).eqv_spec(xk012));
        assert(xk012 == x0.mul_spec(k).add_spec(x1.mul_spec(k)).add_spec(x2.mul_spec(k)));
        assert(x012.mul_spec(k).eqv_spec(x0.mul_spec(k).add_spec(x1.mul_spec(k)).add_spec(x2.mul_spec(k))));
        Scalar::lemma_sub_mul_right(x012, x3, k);
        assert(xb == x012.sub_spec(x3));
        Scalar::lemma_eqv_sub_congruence(
            x012.mul_spec(k),
            xk012,
            x3.mul_spec(k),
            x3.mul_spec(k),
        );
        assert(x012.mul_spec(k).sub_spec(x3.mul_spec(k)).eqv_spec(xk012.sub_spec(x3.mul_spec(k))));
        assert(x012.mul_spec(k).sub_spec(x3.mul_spec(k)).eqv_spec(xk));
        assert(xb.mul_spec(k).eqv_spec(x012.mul_spec(k).sub_spec(x3.mul_spec(k))));
        Scalar::lemma_eqv_transitive(xb.mul_spec(k), x012.mul_spec(k).sub_spec(x3.mul_spec(k)), xk);
        assert(xb.mul_spec(k).eqv_spec(xk));

        let y01 = y0.sub_spec(y1);
        let y012 = y01.add_spec(y2);
        let yk01 = y0.mul_spec(k).sub_spec(y1.mul_spec(k));
        let yk012 = yk01.add_spec(y2.mul_spec(k));
        assert(yk == yk012.add_spec(y3.mul_spec(k)));
        Scalar::lemma_sub_mul_right(y0, y1, k);
        Scalar::lemma_eqv_mul_distributive_right(y01, y2, k);
        assert(y01.mul_spec(k).eqv_spec(yk01));
        Scalar::lemma_eqv_add_congruence(y01.mul_spec(k), yk01, y2.mul_spec(k), y2.mul_spec(k));
        assert(y01.mul_spec(k).add_spec(y2.mul_spec(k)).eqv_spec(yk012));
        assert(y012.mul_spec(k).eqv_spec(y01.mul_spec(k).add_spec(y2.mul_spec(k))));
        Scalar::lemma_eqv_transitive(y012.mul_spec(k), y01.mul_spec(k).add_spec(y2.mul_spec(k)), yk012);
        assert(y012.mul_spec(k).eqv_spec(yk012));
        Scalar::lemma_eqv_mul_distributive_right(y012, y3, k);
        Scalar::lemma_eqv_add_congruence(
            y012.mul_spec(k),
            yk012,
            y3.mul_spec(k),
            y3.mul_spec(k),
        );
        assert(y012.mul_spec(k).add_spec(y3.mul_spec(k)).eqv_spec(yk012.add_spec(y3.mul_spec(k))));
        assert(yb == y012.add_spec(y3));
        assert(yb.mul_spec(k).eqv_spec(y012.mul_spec(k).add_spec(y3.mul_spec(k))));
        assert(y012.mul_spec(k).add_spec(y3.mul_spec(k)).eqv_spec(yk));
        Scalar::lemma_eqv_transitive(yb.mul_spec(k), y012.mul_spec(k).add_spec(y3.mul_spec(k)), yk);
        assert(yb.mul_spec(k).eqv_spec(yk));

        let z01 = z0.add_spec(z1);
        let z012 = z01.sub_spec(z2);
        let zk01 = z0.mul_spec(k).add_spec(z1.mul_spec(k));
        let zk012 = zk01.sub_spec(z2.mul_spec(k));
        assert(zk == zk012.add_spec(z3.mul_spec(k)));
        Scalar::lemma_eqv_mul_distributive_right(z0, z1, k);
        Scalar::lemma_sub_mul_right(z01, z2, k);
        assert(z01.mul_spec(k).eqv_spec(zk01));
        Scalar::lemma_eqv_sub_congruence(z01.mul_spec(k), zk01, z2.mul_spec(k), z2.mul_spec(k));
        assert(z01.mul_spec(k).sub_spec(z2.mul_spec(k)).eqv_spec(zk012));
        assert(z012.mul_spec(k).eqv_spec(z01.mul_spec(k).sub_spec(z2.mul_spec(k))));
        Scalar::lemma_eqv_transitive(z012.mul_spec(k), z01.mul_spec(k).sub_spec(z2.mul_spec(k)), zk012);
        assert(z012.mul_spec(k).eqv_spec(zk012));
        Scalar::lemma_eqv_mul_distributive_right(z012, z3, k);
        Scalar::lemma_eqv_add_congruence(
            z012.mul_spec(k),
            zk012,
            z3.mul_spec(k),
            z3.mul_spec(k),
        );
        assert(z012.mul_spec(k).add_spec(z3.mul_spec(k)).eqv_spec(zk012.add_spec(z3.mul_spec(k))));
        assert(zb == z012.add_spec(z3));
        assert(zb.mul_spec(k).eqv_spec(z012.mul_spec(k).add_spec(z3.mul_spec(k))));
        assert(z012.mul_spec(k).add_spec(z3.mul_spec(k)).eqv_spec(zk));
        Scalar::lemma_eqv_transitive(zb.mul_spec(k), z012.mul_spec(k).add_spec(z3.mul_spec(k)), zk);
        assert(zb.mul_spec(k).eqv_spec(zk));

        assert(rhs.w == wb.mul_spec(k));
        assert(rhs.x == xb.mul_spec(k));
        assert(rhs.y == yb.mul_spec(k));
        assert(rhs.z == zb.mul_spec(k));
        Scalar::lemma_eqv_transitive(lhs.w, lww, wk);
        Scalar::lemma_eqv_transitive(lhs.w, wk, rhs.w);
        Scalar::lemma_eqv_transitive(lhs.x, lxx, xk);
        Scalar::lemma_eqv_transitive(lhs.x, xk, rhs.x);
        Scalar::lemma_eqv_transitive(lhs.y, lyy, yk);
        Scalar::lemma_eqv_transitive(lhs.y, yk, rhs.y);
        Scalar::lemma_eqv_transitive(lhs.z, lzz, zk);
        Scalar::lemma_eqv_transitive(lhs.z, zk, rhs.z);
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_scale_commutes_operands(a: Self, b: Self, k: Scalar)
        ensures
            a.scale_spec(k).mul_spec(b).eqv_spec(a.mul_spec(b.scale_spec(k))),
    {
        let a_scaled = a.scale_spec(k);
        let bs = b.scale_spec(k);
        let lhs = a_scaled.mul_spec(b);
        let rhs = a.mul_spec(bs);

        let lw0 = a_scaled.w.mul_spec(b.w);
        let lw1 = a_scaled.x.mul_spec(b.x);
        let lw2 = a_scaled.y.mul_spec(b.y);
        let lw3 = a_scaled.z.mul_spec(b.z);
        let rw0 = a.w.mul_spec(bs.w);
        let rw1 = a.x.mul_spec(bs.x);
        let rw2 = a.y.mul_spec(bs.y);
        let rw3 = a.z.mul_spec(bs.z);

        let lx0 = a_scaled.w.mul_spec(b.x);
        let lx1 = a_scaled.x.mul_spec(b.w);
        let lx2 = a_scaled.y.mul_spec(b.z);
        let lx3 = a_scaled.z.mul_spec(b.y);
        let rx0 = a.w.mul_spec(bs.x);
        let rx1 = a.x.mul_spec(bs.w);
        let rx2 = a.y.mul_spec(bs.z);
        let rx3 = a.z.mul_spec(bs.y);

        let ly0 = a_scaled.w.mul_spec(b.y);
        let ly1 = a_scaled.x.mul_spec(b.z);
        let ly2 = a_scaled.y.mul_spec(b.w);
        let ly3 = a_scaled.z.mul_spec(b.x);
        let ry0 = a.w.mul_spec(bs.y);
        let ry1 = a.x.mul_spec(bs.z);
        let ry2 = a.y.mul_spec(bs.w);
        let ry3 = a.z.mul_spec(bs.x);

        let lz0 = a_scaled.w.mul_spec(b.z);
        let lz1 = a_scaled.x.mul_spec(b.y);
        let lz2 = a_scaled.y.mul_spec(b.x);
        let lz3 = a_scaled.z.mul_spec(b.w);
        let rz0 = a.w.mul_spec(bs.z);
        let rz1 = a.x.mul_spec(bs.y);
        let rz2 = a.y.mul_spec(bs.x);
        let rz3 = a.z.mul_spec(bs.w);

        assert(a_scaled.w == a.w.mul_spec(k));
        assert(a_scaled.x == a.x.mul_spec(k));
        assert(a_scaled.y == a.y.mul_spec(k));
        assert(a_scaled.z == a.z.mul_spec(k));
        assert(bs.w == b.w.mul_spec(k));
        assert(bs.x == b.x.mul_spec(k));
        assert(bs.y == b.y.mul_spec(k));
        assert(bs.z == b.z.mul_spec(k));

        Scalar::lemma_mul_associative(a.w, k, b.w);
        Scalar::lemma_mul_associative(a.x, k, b.x);
        Scalar::lemma_mul_associative(a.y, k, b.y);
        Scalar::lemma_mul_associative(a.z, k, b.z);
        Scalar::lemma_mul_associative(a.w, k, b.x);
        Scalar::lemma_mul_associative(a.x, k, b.w);
        Scalar::lemma_mul_associative(a.y, k, b.z);
        Scalar::lemma_mul_associative(a.z, k, b.y);
        Scalar::lemma_mul_associative(a.w, k, b.y);
        Scalar::lemma_mul_associative(a.x, k, b.z);
        Scalar::lemma_mul_associative(a.y, k, b.w);
        Scalar::lemma_mul_associative(a.z, k, b.x);
        Scalar::lemma_mul_associative(a.w, k, b.z);
        Scalar::lemma_mul_associative(a.x, k, b.y);
        Scalar::lemma_mul_associative(a.y, k, b.x);
        Scalar::lemma_mul_associative(a.z, k, b.w);

        Scalar::lemma_mul_commutative(k, b.w);
        Scalar::lemma_mul_commutative(k, b.x);
        Scalar::lemma_mul_commutative(k, b.y);
        Scalar::lemma_mul_commutative(k, b.z);

        assert(lw0.eqv_spec(rw0));
        assert(lw1.eqv_spec(rw1));
        assert(lw2.eqv_spec(rw2));
        assert(lw3.eqv_spec(rw3));
        assert(lx0.eqv_spec(rx0));
        assert(lx1.eqv_spec(rx1));
        assert(lx2.eqv_spec(rx2));
        assert(lx3.eqv_spec(rx3));
        assert(ly0.eqv_spec(ry0));
        assert(ly1.eqv_spec(ry1));
        assert(ly2.eqv_spec(ry2));
        assert(ly3.eqv_spec(ry3));
        assert(lz0.eqv_spec(rz0));
        assert(lz1.eqv_spec(rz1));
        assert(lz2.eqv_spec(rz2));
        assert(lz3.eqv_spec(rz3));

        let lww = lw0.sub_spec(lw1).sub_spec(lw2).sub_spec(lw3);
        let rww = rw0.sub_spec(rw1).sub_spec(rw2).sub_spec(rw3);
        let lxx = lx0.add_spec(lx1).add_spec(lx2).sub_spec(lx3);
        let rxx = rx0.add_spec(rx1).add_spec(rx2).sub_spec(rx3);
        let lyy = ly0.sub_spec(ly1).add_spec(ly2).add_spec(ly3);
        let ryy = ry0.sub_spec(ry1).add_spec(ry2).add_spec(ry3);
        let lzz = lz0.add_spec(lz1).sub_spec(lz2).add_spec(lz3);
        let rzz = rz0.add_spec(rz1).sub_spec(rz2).add_spec(rz3);

        assert(lhs.w == lww);
        assert(lhs.x == lxx);
        assert(lhs.y == lyy);
        assert(lhs.z == lzz);
        assert(rhs.w == rww);
        assert(rhs.x == rxx);
        assert(rhs.y == ryy);
        assert(rhs.z == rzz);

        Scalar::lemma_eqv_sub_congruence(lw0, rw0, lw1, rw1);
        Scalar::lemma_eqv_sub_congruence(lw0.sub_spec(lw1), rw0.sub_spec(rw1), lw2, rw2);
        Scalar::lemma_eqv_sub_congruence(lw0.sub_spec(lw1).sub_spec(lw2), rw0.sub_spec(rw1).sub_spec(rw2), lw3, rw3);
        assert(lww.eqv_spec(rww));

        Scalar::lemma_eqv_add_congruence(lx0, rx0, lx1, rx1);
        Scalar::lemma_eqv_add_congruence(lx0.add_spec(lx1), rx0.add_spec(rx1), lx2, rx2);
        Scalar::lemma_eqv_sub_congruence(lx0.add_spec(lx1).add_spec(lx2), rx0.add_spec(rx1).add_spec(rx2), lx3, rx3);
        assert(lxx.eqv_spec(rxx));

        Scalar::lemma_eqv_sub_congruence(ly0, ry0, ly1, ry1);
        Scalar::lemma_eqv_add_congruence(ly0.sub_spec(ly1), ry0.sub_spec(ry1), ly2, ry2);
        Scalar::lemma_eqv_add_congruence(ly0.sub_spec(ly1).add_spec(ly2), ry0.sub_spec(ry1).add_spec(ry2), ly3, ry3);
        assert(lyy.eqv_spec(ryy));

        Scalar::lemma_eqv_add_congruence(lz0, rz0, lz1, rz1);
        Scalar::lemma_eqv_sub_congruence(lz0.add_spec(lz1), rz0.add_spec(rz1), lz2, rz2);
        Scalar::lemma_eqv_add_congruence(lz0.add_spec(lz1).sub_spec(lz2), rz0.add_spec(rz1).sub_spec(rz2), lz3, rz3);
        assert(lzz.eqv_spec(rzz));

        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_scale_left(a: Self, b: Self, k: Scalar)
        ensures
            a.scale_spec(k).mul_spec(b).eqv_spec(a.mul_spec(b).scale_spec(k)),
    {
        let lhs = a.scale_spec(k).mul_spec(b);
        let mid = a.mul_spec(b.scale_spec(k));
        let rhs = a.mul_spec(b).scale_spec(k);
        Self::lemma_mul_scale_commutes_operands(a, b, k);
        Self::lemma_mul_scale_right(a, b, k);
        assert(lhs.eqv_spec(mid));
        assert(mid.eqv_spec(rhs));
        Self::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
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

    pub proof fn lemma_norm2_conjugate_invariant(q: Self)
        ensures
            q.conjugate_spec().norm2_spec().eqv_spec(q.norm2_spec()),
    {
        let qc = q.conjugate_spec();
        let nqc = qc.norm2_spec();
        let nq = q.norm2_spec();

        Scalar::lemma_neg_involution(q.x);
        Scalar::lemma_neg_involution(q.y);
        Scalar::lemma_neg_involution(q.z);

        assert(qc.w.mul_spec(qc.w) == q.w.mul_spec(q.w));
        assert(qc.x.mul_spec(qc.x).num == (-q.x.num) * (-q.x.num));
        assert((-q.x.num) * (-q.x.num) == q.x.num * q.x.num) by (nonlinear_arith);
        assert(qc.x.mul_spec(qc.x).num == q.x.mul_spec(q.x).num);
        assert(qc.x.mul_spec(qc.x).den == q.x.mul_spec(q.x).den);
        assert(qc.x.mul_spec(qc.x) == q.x.mul_spec(q.x));
        assert(qc.y.mul_spec(qc.y).num == (-q.y.num) * (-q.y.num));
        assert((-q.y.num) * (-q.y.num) == q.y.num * q.y.num) by (nonlinear_arith);
        assert(qc.y.mul_spec(qc.y).num == q.y.mul_spec(q.y).num);
        assert(qc.y.mul_spec(qc.y).den == q.y.mul_spec(q.y).den);
        assert(qc.y.mul_spec(qc.y) == q.y.mul_spec(q.y));
        assert(qc.z.mul_spec(qc.z).num == (-q.z.num) * (-q.z.num));
        assert((-q.z.num) * (-q.z.num) == q.z.num * q.z.num) by (nonlinear_arith);
        assert(qc.z.mul_spec(qc.z).num == q.z.mul_spec(q.z).num);
        assert(qc.z.mul_spec(qc.z).den == q.z.mul_spec(q.z).den);
        assert(qc.z.mul_spec(qc.z) == q.z.mul_spec(q.z));

        assert(nqc == nq);
        Scalar::lemma_eqv_reflexive(nq);
        assert(nqc.eqv_spec(nq));
    }

    pub proof fn lemma_norm2_nonnegative(q: Self)
        ensures
            Scalar::from_int_spec(0).le_spec(q.norm2_spec()),
    {
        let v = q.as_vec4_spec();
        assert(v.norm2_spec() == q.norm2_spec());
        Vec4::lemma_norm2_nonnegative(v);
        assert(Scalar::from_int_spec(0).le_spec(v.norm2_spec()));
        assert(Scalar::from_int_spec(0).le_spec(q.norm2_spec()));
    }

    pub proof fn lemma_norm2_zero_iff_zero(q: Self)
        ensures
            q.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == q.eqv_spec(Self::zero_spec()),
    {
        let v = q.as_vec4_spec();
        let zq = Self::zero_spec();
        let zv = Vec4::zero_spec();
        Vec4::lemma_norm2_zero_iff_zero(v);
        assert(v.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == v.eqv_spec(zv));
        assert(v.norm2_spec() == q.norm2_spec());
        assert(v.eqv_spec(zv) == q.eqv_spec(zq));
        assert(q.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == q.eqv_spec(zq));
    }

    pub proof fn lemma_norm2_positive_if_nonzero(q: Self)
        ensures
            q.norm2_spec().num != 0 ==> q.norm2_spec().num > 0,
    {
        let n = q.norm2_spec();
        let z = Scalar::from_int_spec(0);
        Self::lemma_norm2_nonnegative(q);
        assert(z.le_spec(n));
        assert(z.le_spec(n) == (z.num * n.denom() <= n.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(n) == (0 * n.denom() <= n.num * 1));
        assert(0 * n.denom() == 0);
        assert(n.num * 1 == n.num);
        assert(0 <= n.num);
        if n.num != 0 {
            Scalar::lemma_signum_cases(n);
            Scalar::lemma_signum_zero_iff(n);
            assert((n.signum() == 0) == (n.num == 0));
            assert(n.signum() != 0);
            if n.signum() == 1 {
                Scalar::lemma_signum_positive_iff(n);
                assert((n.signum() == 1) == (n.num > 0));
                assert(n.num > 0);
            } else {
                assert(n.signum() == -1);
                Scalar::lemma_signum_negative_iff(n);
                assert((n.signum() == -1) == (n.num < 0));
                assert(n.num < 0);
                assert((0 <= n.num) ==> !(n.num < 0)) by (nonlinear_arith);
                assert(!(n.num < 0));
                assert(false);
            }
        }
    }

    pub proof fn lemma_mul_conjugate_right_real_norm2_components(q: Self)
        ensures
            {
                let p = q.mul_spec(q.conjugate_spec());
                p.w.eqv_spec(q.norm2_spec())
            },
            {
                let p = q.mul_spec(q.conjugate_spec());
                p.x.eqv_spec(Scalar::from_int_spec(0))
            },
            {
                let p = q.mul_spec(q.conjugate_spec());
                p.y.eqv_spec(Scalar::from_int_spec(0))
            },
            {
                let p = q.mul_spec(q.conjugate_spec());
                p.z.eqv_spec(Scalar::from_int_spec(0))
            },
    {
        let qc = q.conjugate_spec();
        let p = q.mul_spec(qc);
        let z = Scalar::from_int_spec(0);

        let ww = q.w.mul_spec(q.w);
        let xx = q.x.mul_spec(q.x);
        let yy = q.y.mul_spec(q.y);
        let zz = q.z.mul_spec(q.z);

        let wx = q.w.mul_spec(q.x);
        let xw = q.x.mul_spec(q.w);
        let wy = q.w.mul_spec(q.y);
        let yw = q.y.mul_spec(q.w);
        let wz = q.w.mul_spec(q.z);
        let zw = q.z.mul_spec(q.w);
        let yz = q.y.mul_spec(q.z);
        let zy = q.z.mul_spec(q.y);
        let xz = q.x.mul_spec(q.z);
        let zx = q.z.mul_spec(q.x);
        let xy = q.x.mul_spec(q.y);
        let yx = q.y.mul_spec(q.x);

        let twx = q.x.mul_spec(qc.x);
        let twy = q.y.mul_spec(qc.y);
        let twz = q.z.mul_spec(qc.z);
        Scalar::lemma_mul_neg_right(q.x, q.x);
        Scalar::lemma_mul_neg_right(q.y, q.y);
        Scalar::lemma_mul_neg_right(q.z, q.z);
        assert(twx == xx.neg_spec());
        assert(twy == yy.neg_spec());
        assert(twz == zz.neg_spec());

        assert(p.w == ww.sub_spec(twx).sub_spec(twy).sub_spec(twz));
        Scalar::lemma_sub_is_add_neg(ww, twx);
        let w0 = ww.add_spec(twx.neg_spec());
        assert(ww.sub_spec(twx) == w0);
        Scalar::lemma_neg_involution(xx);
        assert(twx.neg_spec() == xx);
        assert(w0 == ww.add_spec(xx));
        Scalar::lemma_sub_is_add_neg(w0, twy);
        let w1 = w0.add_spec(twy.neg_spec());
        assert(w0.sub_spec(twy) == w1);
        Scalar::lemma_neg_involution(yy);
        assert(twy.neg_spec() == yy);
        assert(w1 == ww.add_spec(xx).add_spec(yy));
        Scalar::lemma_sub_is_add_neg(w1, twz);
        let w2 = w1.add_spec(twz.neg_spec());
        assert(w1.sub_spec(twz) == w2);
        Scalar::lemma_neg_involution(zz);
        assert(twz.neg_spec() == zz);
        assert(w2 == ww.add_spec(xx).add_spec(yy).add_spec(zz));
        assert(p.w == w2);
        assert(q.norm2_spec() == ww.add_spec(xx).add_spec(yy).add_spec(zz));
        assert(p.w == q.norm2_spec());
        Scalar::lemma_eqv_reflexive(p.w);
        assert(p.w.eqv_spec(q.norm2_spec()));

        let tx0 = q.w.mul_spec(qc.x);
        let tx2 = q.y.mul_spec(qc.z);
        let tx3 = q.z.mul_spec(qc.y);
        Scalar::lemma_mul_neg_right(q.w, q.x);
        Scalar::lemma_mul_neg_right(q.y, q.z);
        Scalar::lemma_mul_neg_right(q.z, q.y);
        assert(tx0 == wx.neg_spec());
        assert(tx2 == yz.neg_spec());
        assert(tx3 == zy.neg_spec());
        assert(p.x == tx0.add_spec(xw).add_spec(tx2).sub_spec(tx3));
        Scalar::lemma_sub_is_add_neg(tx0.add_spec(xw).add_spec(tx2), tx3);
        let px0 = tx0.add_spec(xw).add_spec(tx2).add_spec(tx3.neg_spec());
        assert(p.x == px0);
        Scalar::lemma_neg_involution(zy);
        assert(tx3.neg_spec() == zy);
        let px1 = tx0.add_spec(xw).add_spec(tx2).add_spec(zy);
        assert(p.x == px1);
        Scalar::lemma_mul_commutative(q.x, q.w);
        Scalar::lemma_mul_commutative(q.z, q.y);
        assert(xw == wx);
        assert(zy == yz);
        let ux = wx.neg_spec().add_spec(wx);
        let vx = yz.neg_spec().add_spec(yz);
        let ex1 = ux.add_spec(yz.neg_spec()).add_spec(yz);
        let ex2 = ux.add_spec(vx);
        assert(px1 == ex1);
        Scalar::lemma_add_associative(ux, yz.neg_spec(), yz);
        assert(ex1.eqv_spec(ex2));
        Scalar::lemma_add_inverse(wx);
        Scalar::lemma_add_inverse(yz);
        assert(ux.eqv_spec(z));
        assert(vx.eqv_spec(z));
        Scalar::lemma_eqv_add_congruence(ux, z, vx, z);
        assert(ex2.eqv_spec(z.add_spec(z)));
        Scalar::lemma_add_zero_identity(z);
        assert(z.add_spec(z) == z);
        Scalar::lemma_eqv_reflexive(z);
        assert(z.add_spec(z).eqv_spec(z));
        assert(p.x.eqv_spec(ex1));
        Scalar::lemma_eqv_transitive(p.x, ex1, ex2);
        Scalar::lemma_eqv_transitive(p.x, ex2, z.add_spec(z));
        Scalar::lemma_eqv_transitive(p.x, z.add_spec(z), z);
        assert(p.x.eqv_spec(z));

        let ty0 = q.w.mul_spec(qc.y);
        let ty1 = q.x.mul_spec(qc.z);
        let ty3 = q.z.mul_spec(qc.x);
        Scalar::lemma_mul_neg_right(q.w, q.y);
        Scalar::lemma_mul_neg_right(q.x, q.z);
        Scalar::lemma_mul_neg_right(q.z, q.x);
        assert(ty0 == wy.neg_spec());
        assert(ty1 == xz.neg_spec());
        assert(ty3 == zx.neg_spec());
        assert(p.y == ty0.sub_spec(ty1).add_spec(yw).add_spec(ty3));
        Scalar::lemma_sub_is_add_neg(ty0, ty1);
        let py0 = ty0.add_spec(ty1.neg_spec()).add_spec(yw).add_spec(ty3);
        assert(p.y == py0);
        Scalar::lemma_neg_involution(xz);
        assert(ty1.neg_spec() == xz);
        let py1 = ty0.add_spec(xz).add_spec(yw).add_spec(ty3);
        assert(p.y == py1);
        Scalar::lemma_mul_commutative(q.y, q.w);
        Scalar::lemma_mul_commutative(q.z, q.x);
        assert(yw == wy);
        assert(ty3 == zx.neg_spec());
        let uy = wy.neg_spec().add_spec(wy);
        let vy = xz.add_spec(zx.neg_spec());
        let ey2 = uy.add_spec(vy);
        let py_reassoc0 = wy.neg_spec().add_spec(xz).add_spec(wy.add_spec(zx.neg_spec()));
        Scalar::lemma_add_associative(wy.neg_spec().add_spec(xz), wy, zx.neg_spec());
        assert(py1.eqv_spec(py_reassoc0));
        Scalar::lemma_add_rearrange_2x2(wy.neg_spec(), xz, wy, zx.neg_spec());
        assert(py_reassoc0.eqv_spec(uy.add_spec(vy)));
        Scalar::lemma_eqv_transitive(py1, py_reassoc0, ey2);
        Scalar::lemma_add_inverse(wy);
        assert(uy.eqv_spec(z));
        Scalar::lemma_mul_commutative(q.x, q.z);
        assert(xz == zx);
        Scalar::lemma_add_inverse(xz);
        assert(vy.eqv_spec(z));
        Scalar::lemma_eqv_add_congruence(uy, z, vy, z);
        assert(ey2.eqv_spec(z.add_spec(z)));
        assert(p.y.eqv_spec(py1));
        Scalar::lemma_eqv_transitive(p.y, py1, ey2);
        Scalar::lemma_eqv_transitive(p.y, ey2, z.add_spec(z));
        Scalar::lemma_eqv_transitive(p.y, z.add_spec(z), z);
        assert(p.y.eqv_spec(z));

        let tz0 = q.w.mul_spec(qc.z);
        let tz1 = q.x.mul_spec(qc.y);
        let tz2 = q.y.mul_spec(qc.x);
        Scalar::lemma_mul_neg_right(q.w, q.z);
        Scalar::lemma_mul_neg_right(q.x, q.y);
        Scalar::lemma_mul_neg_right(q.y, q.x);
        assert(tz0 == wz.neg_spec());
        assert(tz1 == xy.neg_spec());
        assert(tz2 == yx.neg_spec());
        assert(p.z == tz0.add_spec(tz1).sub_spec(tz2).add_spec(zw));
        Scalar::lemma_sub_is_add_neg(tz0.add_spec(tz1), tz2);
        let pz0 = tz0.add_spec(tz1).add_spec(tz2.neg_spec()).add_spec(zw);
        assert(p.z == pz0);
        Scalar::lemma_neg_involution(yx);
        assert(tz2.neg_spec() == yx);
        let pz1 = tz0.add_spec(tz1).add_spec(yx).add_spec(zw);
        assert(p.z == pz1);
        Scalar::lemma_mul_commutative(q.z, q.w);
        Scalar::lemma_mul_commutative(q.y, q.x);
        assert(zw == wz);
        assert(yx == xy);
        let uz = wz.neg_spec().add_spec(wz);
        let vz = xy.neg_spec().add_spec(xy);
        let ez2 = uz.add_spec(vz);
        let pz_reassoc0 = wz.neg_spec().add_spec(xy.neg_spec()).add_spec(xy.add_spec(wz));
        let pz_reassoc1 = wz.neg_spec().add_spec(xy.neg_spec()).add_spec(wz.add_spec(xy));
        Scalar::lemma_add_associative(wz.neg_spec().add_spec(xy.neg_spec()), xy, wz);
        assert(pz1.eqv_spec(pz_reassoc0));
        Scalar::lemma_add_commutative(xy, wz);
        assert(xy.add_spec(wz).eqv_spec(wz.add_spec(xy)));
        Scalar::lemma_eqv_add_congruence(
            wz.neg_spec().add_spec(xy.neg_spec()),
            wz.neg_spec().add_spec(xy.neg_spec()),
            xy.add_spec(wz),
            wz.add_spec(xy),
        );
        assert(pz_reassoc0.eqv_spec(pz_reassoc1));
        Scalar::lemma_add_rearrange_2x2(wz.neg_spec(), xy.neg_spec(), wz, xy);
        assert(pz_reassoc1.eqv_spec(uz.add_spec(vz)));
        Scalar::lemma_eqv_transitive(pz1, pz_reassoc0, pz_reassoc1);
        Scalar::lemma_eqv_transitive(pz1, pz_reassoc1, ez2);
        Scalar::lemma_add_inverse(wz);
        Scalar::lemma_add_inverse(xy);
        assert(uz.eqv_spec(z));
        assert(vz.eqv_spec(z));
        Scalar::lemma_eqv_add_congruence(uz, z, vz, z);
        assert(ez2.eqv_spec(z.add_spec(z)));
        assert(p.z.eqv_spec(pz1));
        Scalar::lemma_eqv_transitive(p.z, pz1, ez2);
        Scalar::lemma_eqv_transitive(p.z, ez2, z.add_spec(z));
        Scalar::lemma_eqv_transitive(p.z, z.add_spec(z), z);
        assert(p.z.eqv_spec(z));
    }

    pub proof fn lemma_mul_conjugate_right_real_norm2(q: Self)
        ensures
            q.mul_spec(q.conjugate_spec()).eqv_spec(Self::real_spec(q.norm2_spec())),
    {
        let p = q.mul_spec(q.conjugate_spec());
        let r = Self::real_spec(q.norm2_spec());
        let z = Scalar::from_int_spec(0);
        Self::lemma_mul_conjugate_right_real_norm2_components(q);
        assert(p.w.eqv_spec(q.norm2_spec()));
        assert(p.x.eqv_spec(z));
        assert(p.y.eqv_spec(z));
        assert(p.z.eqv_spec(z));
        assert(r.w == q.norm2_spec());
        assert(r.x == z);
        assert(r.y == z);
        assert(r.z == z);
        Self::lemma_eqv_from_components(p, r);
        assert(p.eqv_spec(r));
    }

    pub proof fn lemma_mul_conjugate_left_real_norm2_components(q: Self)
        ensures
            {
                let p = q.conjugate_spec().mul_spec(q);
                p.w.eqv_spec(q.norm2_spec())
            },
            {
                let p = q.conjugate_spec().mul_spec(q);
                p.x.eqv_spec(Scalar::from_int_spec(0))
            },
            {
                let p = q.conjugate_spec().mul_spec(q);
                p.y.eqv_spec(Scalar::from_int_spec(0))
            },
            {
                let p = q.conjugate_spec().mul_spec(q);
                p.z.eqv_spec(Scalar::from_int_spec(0))
            },
    {
        let qc = q.conjugate_spec();
        let p = qc.mul_spec(q);
        let z = Scalar::from_int_spec(0);
        Self::lemma_mul_conjugate_right_real_norm2_components(qc);
        Self::lemma_conjugate_involution(q);
        assert(qc.conjugate_spec() == q);
        assert(p == qc.mul_spec(qc.conjugate_spec()));
        assert(p.w.eqv_spec(qc.norm2_spec()));
        assert(p.x.eqv_spec(z));
        assert(p.y.eqv_spec(z));
        assert(p.z.eqv_spec(z));
        Self::lemma_norm2_conjugate_invariant(q);
        assert(qc.norm2_spec().eqv_spec(q.norm2_spec()));
        Scalar::lemma_eqv_transitive(p.w, qc.norm2_spec(), q.norm2_spec());
        assert(p.w.eqv_spec(q.norm2_spec()));
        assert(p.x.eqv_spec(z));
        assert(p.y.eqv_spec(z));
        assert(p.z.eqv_spec(z));
    }

    pub proof fn lemma_mul_conjugate_left_real_norm2(q: Self)
        ensures
            q.conjugate_spec().mul_spec(q).eqv_spec(Self::real_spec(q.norm2_spec())),
    {
        let p = q.conjugate_spec().mul_spec(q);
        let r = Self::real_spec(q.norm2_spec());
        let z = Scalar::from_int_spec(0);
        Self::lemma_mul_conjugate_left_real_norm2_components(q);
        assert(p.w.eqv_spec(q.norm2_spec()));
        assert(p.x.eqv_spec(z));
        assert(p.y.eqv_spec(z));
        assert(p.z.eqv_spec(z));
        assert(r.w == q.norm2_spec());
        assert(r.x == z);
        assert(r.y == z);
        assert(r.z == z);
        Self::lemma_eqv_from_components(p, r);
        assert(p.eqv_spec(r));
    }

    pub proof fn lemma_inverse_right(q: Self)
        requires
            q.norm2_spec().num > 0,
        ensures
            q.mul_spec(q.inverse_spec()).eqv_spec(Self::one_spec()),
    {
        let n = q.norm2_spec();
        let inv_n = Scalar { num: n.denom(), den: (n.num - 1) as nat };
        let qc = q.conjugate_spec();
        let inv = q.inverse_spec();
        let lhs = q.mul_spec(inv);
        let p = q.mul_spec(qc);
        let r = Self::real_spec(n);
        let rs = r.scale_spec(inv_n);
        let one = Self::one_spec();
        let z = Scalar::from_int_spec(0);

        assert(inv == qc.scale_spec(inv_n));
        assert(lhs == q.mul_spec(qc.scale_spec(inv_n)));
        Self::lemma_mul_scale_right(q, qc, inv_n);
        assert(q.mul_spec(qc.scale_spec(inv_n)).eqv_spec(q.mul_spec(qc).scale_spec(inv_n)));
        assert(lhs.eqv_spec(p.scale_spec(inv_n)));

        Self::lemma_mul_conjugate_right_real_norm2(q);
        assert(p.eqv_spec(r));
        Self::lemma_scale_eqv_congruence(p, r, inv_n);
        assert(p.scale_spec(inv_n).eqv_spec(rs));

        assert(rs.w == n.mul_spec(inv_n));
        assert(rs.x == z.mul_spec(inv_n));
        assert(rs.y == z.mul_spec(inv_n));
        assert(rs.z == z.mul_spec(inv_n));

        Scalar::lemma_mul_reciprocal_positive_num(n);
        assert(n.mul_spec(inv_n).eqv_spec(Scalar::from_int_spec(1)));
        Scalar::lemma_mul_zero(inv_n);
        assert(z.mul_spec(inv_n).eqv_spec(z));
        assert(one.w == Scalar::from_int_spec(1));
        assert(one.x == z);
        assert(one.y == z);
        assert(one.z == z);
        assert(rs.w.eqv_spec(one.w));
        assert(rs.x.eqv_spec(one.x));
        assert(rs.y.eqv_spec(one.y));
        assert(rs.z.eqv_spec(one.z));
        Self::lemma_eqv_from_components(rs, one);
        assert(rs.eqv_spec(one));

        Self::lemma_eqv_transitive(lhs, p.scale_spec(inv_n), rs);
        Self::lemma_eqv_transitive(lhs, rs, one);
        assert(lhs.eqv_spec(one));
    }

    pub proof fn lemma_inverse_left(q: Self)
        requires
            q.norm2_spec().num > 0,
        ensures
            q.inverse_spec().mul_spec(q).eqv_spec(Self::one_spec()),
    {
        let n = q.norm2_spec();
        let inv_n = Scalar { num: n.denom(), den: (n.num - 1) as nat };
        let qc = q.conjugate_spec();
        let inv = q.inverse_spec();
        let lhs = inv.mul_spec(q);
        let p = qc.mul_spec(q);
        let r = Self::real_spec(n);
        let rs = r.scale_spec(inv_n);
        let one = Self::one_spec();
        let z = Scalar::from_int_spec(0);

        assert(inv == qc.scale_spec(inv_n));
        assert(lhs == qc.scale_spec(inv_n).mul_spec(q));
        Self::lemma_mul_scale_left(qc, q, inv_n);
        assert(qc.scale_spec(inv_n).mul_spec(q).eqv_spec(qc.mul_spec(q).scale_spec(inv_n)));
        assert(lhs.eqv_spec(p.scale_spec(inv_n)));

        Self::lemma_mul_conjugate_left_real_norm2(q);
        assert(p.eqv_spec(r));
        Self::lemma_scale_eqv_congruence(p, r, inv_n);
        assert(p.scale_spec(inv_n).eqv_spec(rs));

        assert(rs.w == n.mul_spec(inv_n));
        assert(rs.x == z.mul_spec(inv_n));
        assert(rs.y == z.mul_spec(inv_n));
        assert(rs.z == z.mul_spec(inv_n));

        Scalar::lemma_mul_reciprocal_positive_num(n);
        assert(n.mul_spec(inv_n).eqv_spec(Scalar::from_int_spec(1)));
        Scalar::lemma_mul_zero(inv_n);
        assert(z.mul_spec(inv_n).eqv_spec(z));
        assert(one.w == Scalar::from_int_spec(1));
        assert(one.x == z);
        assert(one.y == z);
        assert(one.z == z);
        assert(rs.w.eqv_spec(one.w));
        assert(rs.x.eqv_spec(one.x));
        assert(rs.y.eqv_spec(one.y));
        assert(rs.z.eqv_spec(one.z));
        Self::lemma_eqv_from_components(rs, one);
        assert(rs.eqv_spec(one));

        Self::lemma_eqv_transitive(lhs, p.scale_spec(inv_n), rs);
        Self::lemma_eqv_transitive(lhs, rs, one);
        assert(lhs.eqv_spec(one));
    }
}

} // verus!
