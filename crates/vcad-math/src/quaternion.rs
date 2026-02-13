use crate::scalar::Scalar;
use crate::vec3::Vec3;
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

    pub open spec fn i_spec() -> Self {
        Self::from_ints_spec(0, 1, 0, 0)
    }

    pub open spec fn j_spec() -> Self {
        Self::from_ints_spec(0, 0, 1, 0)
    }

    pub open spec fn k_spec() -> Self {
        Self::from_ints_spec(0, 0, 0, 1)
    }

    pub proof fn lemma_basis_i_squared()
        ensures
            Self::i_spec().mul_spec(Self::i_spec()).eqv_spec(Self::from_ints_spec(-1, 0, 0, 0)),
    {
        let i = Self::i_spec();
        let minus_one = Self::from_ints_spec(-1, 0, 0, 0);
        let p = i.mul_spec(i);
        assert(p.w.eqv_spec(minus_one.w));
        assert(p.x.eqv_spec(minus_one.x));
        assert(p.y.eqv_spec(minus_one.y));
        assert(p.z.eqv_spec(minus_one.z));
        Self::lemma_eqv_from_components(p, minus_one);
        assert(p.eqv_spec(minus_one));
    }

    pub proof fn lemma_basis_j_squared()
        ensures
            Self::j_spec().mul_spec(Self::j_spec()).eqv_spec(Self::from_ints_spec(-1, 0, 0, 0)),
    {
        let j = Self::j_spec();
        let minus_one = Self::from_ints_spec(-1, 0, 0, 0);
        let p = j.mul_spec(j);
        assert(p.w.eqv_spec(minus_one.w));
        assert(p.x.eqv_spec(minus_one.x));
        assert(p.y.eqv_spec(minus_one.y));
        assert(p.z.eqv_spec(minus_one.z));
        Self::lemma_eqv_from_components(p, minus_one);
        assert(p.eqv_spec(minus_one));
    }

    pub proof fn lemma_basis_k_squared()
        ensures
            Self::k_spec().mul_spec(Self::k_spec()).eqv_spec(Self::from_ints_spec(-1, 0, 0, 0)),
    {
        let k = Self::k_spec();
        let minus_one = Self::from_ints_spec(-1, 0, 0, 0);
        let p = k.mul_spec(k);
        assert(p.w.eqv_spec(minus_one.w));
        assert(p.x.eqv_spec(minus_one.x));
        assert(p.y.eqv_spec(minus_one.y));
        assert(p.z.eqv_spec(minus_one.z));
        Self::lemma_eqv_from_components(p, minus_one);
        assert(p.eqv_spec(minus_one));
    }

    pub proof fn lemma_basis_i_mul_j()
        ensures
            Self::i_spec().mul_spec(Self::j_spec()).eqv_spec(Self::k_spec()),
    {
        let i = Self::i_spec();
        let j = Self::j_spec();
        let k = Self::k_spec();
        let p = i.mul_spec(j);
        assert(p.w.eqv_spec(k.w));
        assert(p.x.eqv_spec(k.x));
        assert(p.y.eqv_spec(k.y));
        assert(p.z.eqv_spec(k.z));
        Self::lemma_eqv_from_components(p, k);
        assert(p.eqv_spec(k));
    }

    pub proof fn lemma_basis_j_mul_k()
        ensures
            Self::j_spec().mul_spec(Self::k_spec()).eqv_spec(Self::i_spec()),
    {
        let j = Self::j_spec();
        let k = Self::k_spec();
        let i = Self::i_spec();
        let p = j.mul_spec(k);
        assert(p.w.eqv_spec(i.w));
        assert(p.x.eqv_spec(i.x));
        assert(p.y.eqv_spec(i.y));
        assert(p.z.eqv_spec(i.z));
        Self::lemma_eqv_from_components(p, i);
        assert(p.eqv_spec(i));
    }

    pub proof fn lemma_basis_k_mul_i()
        ensures
            Self::k_spec().mul_spec(Self::i_spec()).eqv_spec(Self::j_spec()),
    {
        assert(Self::k_spec().mul_spec(Self::i_spec()).eqv_spec(Self::j_spec())) by (compute);
    }

    pub proof fn lemma_basis_j_mul_i()
        ensures
            Self::j_spec().mul_spec(Self::i_spec()).eqv_spec(Self::from_ints_spec(0, 0, 0, -1)),
    {
        assert(Self::j_spec().mul_spec(Self::i_spec()).eqv_spec(Self::from_ints_spec(0, 0, 0, -1))) by (compute);
    }

    pub proof fn lemma_basis_k_mul_j()
        ensures
            Self::k_spec().mul_spec(Self::j_spec()).eqv_spec(Self::from_ints_spec(0, -1, 0, 0)),
    {
        assert(Self::k_spec().mul_spec(Self::j_spec()).eqv_spec(Self::from_ints_spec(0, -1, 0, 0))) by (compute);
    }

    pub proof fn lemma_basis_i_mul_k()
        ensures
            Self::i_spec().mul_spec(Self::k_spec()).eqv_spec(Self::from_ints_spec(0, 0, -1, 0)),
    {
        let i = Self::i_spec();
        let k = Self::k_spec();
        let minus_j = Self::from_ints_spec(0, 0, -1, 0);
        let p = i.mul_spec(k);
        assert(p.w.eqv_spec(minus_j.w));
        assert(p.x.eqv_spec(minus_j.x));
        assert(p.y.eqv_spec(minus_j.y));
        assert(p.z.eqv_spec(minus_j.z));
        Self::lemma_eqv_from_components(p, minus_j);
        assert(p.eqv_spec(minus_j));
    }

    pub proof fn lemma_basis_assoc_i_j_k_trial()
        ensures
            Self::assoc_instance_spec(Self::i_spec(), Self::j_spec(), Self::k_spec()),
    {
        let a = Self::i_spec();
        let b = Self::j_spec();
        let c = Self::k_spec();
        let lhs = a.mul_spec(b).mul_spec(c);
        let rhs = a.mul_spec(b.mul_spec(c));
        let minus_one = Self::from_ints_spec(-1, 0, 0, 0);

        Self::lemma_basis_i_mul_j();
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(b), Self::k_spec(), c);
        assert(lhs.eqv_spec(Self::k_spec().mul_spec(c)));
        Self::lemma_basis_k_squared();
        Self::lemma_eqv_transitive(lhs, Self::k_spec().mul_spec(c), minus_one);
        assert(lhs.eqv_spec(minus_one));

        Self::lemma_basis_j_mul_k();
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(c), Self::i_spec());
        assert(rhs.eqv_spec(a.mul_spec(Self::i_spec())));
        Self::lemma_basis_i_squared();
        Self::lemma_eqv_transitive(rhs, a.mul_spec(Self::i_spec()), minus_one);
        assert(rhs.eqv_spec(minus_one));

        Self::lemma_eqv_symmetric(rhs, minus_one);
        Self::lemma_eqv_transitive(lhs, minus_one, rhs);
        assert(lhs.eqv_spec(rhs));
        assert(Self::assoc_instance_spec(a, b, c));
    }

    pub open spec fn basis_spec(i: int) -> Self
        recommends
            0 <= i < 4,
    {
        if i == 0 {
            Self::one_spec()
        } else if i == 1 {
            Self::i_spec()
        } else if i == 2 {
            Self::j_spec()
        } else {
            Self::k_spec()
        }
    }

    pub open spec fn signed_basis_spec(sign: int, i: int) -> Self
        recommends
            (sign == 1 || sign == -1) && 0 <= i < 4,
    {
        Self::basis_spec(i).scale_spec(Scalar::from_int_spec(sign))
    }

    pub open spec fn basis_mul_idx_spec(i: int, j: int) -> int
        recommends
            0 <= i < 4 && 0 <= j < 4,
    {
        if i == 0 {
            j
        } else if j == 0 {
            i
        } else if i == j {
            0
        } else if i == 1 && j == 2 {
            3
        } else if i == 2 && j == 3 {
            1
        } else if i == 3 && j == 1 {
            2
        } else if i == 2 && j == 1 {
            3
        } else if i == 3 && j == 2 {
            1
        } else {
            2
        }
    }

    pub open spec fn basis_mul_sign_spec(i: int, j: int) -> int
        recommends
            0 <= i < 4 && 0 <= j < 4,
    {
        if i == 0 || j == 0 {
            1
        } else if i == j {
            -1
        } else if i == 1 && j == 2 {
            1
        } else if i == 2 && j == 3 {
            1
        } else if i == 3 && j == 1 {
            1
        } else {
            -1
        }
    }

    pub open spec fn basis_decompose_spec(q: Self) -> Self {
        Self::basis_spec(0).scale_spec(q.w)
            .add_spec(Self::basis_spec(1).scale_spec(q.x))
            .add_spec(Self::basis_spec(2).scale_spec(q.y))
            .add_spec(Self::basis_spec(3).scale_spec(q.z))
    }

    pub proof fn lemma_scale_one_identity(q: Self)
        ensures
            q.scale_spec(Scalar::from_int_spec(1)).eqv_spec(q),
    {
        let one = Scalar::from_int_spec(1);
        let qs = q.scale_spec(one);
        Scalar::lemma_mul_one_identity(q.w);
        Scalar::lemma_mul_one_identity(q.x);
        Scalar::lemma_mul_one_identity(q.y);
        Scalar::lemma_mul_one_identity(q.z);
        assert(qs.w.eqv_spec(q.w));
        assert(qs.x.eqv_spec(q.x));
        assert(qs.y.eqv_spec(q.y));
        assert(qs.z.eqv_spec(q.z));
        Self::lemma_eqv_from_components(qs, q);
        assert(qs.eqv_spec(q));
    }

    pub proof fn lemma_scale_associative(q: Self, a: Scalar, b: Scalar)
        ensures
            q.scale_spec(a).scale_spec(b).eqv_spec(q.scale_spec(a.mul_spec(b))),
    {
        let lhs = q.scale_spec(a).scale_spec(b);
        let rhs = q.scale_spec(a.mul_spec(b));
        Scalar::lemma_mul_associative(q.w, a, b);
        Scalar::lemma_mul_associative(q.x, a, b);
        Scalar::lemma_mul_associative(q.y, a, b);
        Scalar::lemma_mul_associative(q.z, a, b);
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_signed_basis_neg_constant(i: int)
        requires
            0 <= i < 4,
        ensures
            if i == 0 {
                Self::signed_basis_spec(-1, i).eqv_spec(Self::from_ints_spec(-1, 0, 0, 0))
            } else if i == 1 {
                Self::signed_basis_spec(-1, i).eqv_spec(Self::from_ints_spec(0, -1, 0, 0))
            } else if i == 2 {
                Self::signed_basis_spec(-1, i).eqv_spec(Self::from_ints_spec(0, 0, -1, 0))
            } else {
                Self::signed_basis_spec(-1, i).eqv_spec(Self::from_ints_spec(0, 0, 0, -1))
            },
    {
        let m = Scalar::from_int_spec(-1);
        let z = Scalar::from_int_spec(0);
        if i == 0 {
            let q = Self::signed_basis_spec(-1, i);
            let t = Self::from_ints_spec(-1, 0, 0, 0);
            Scalar::lemma_mul_one_identity(m);
            Scalar::lemma_mul_zero(m);
            assert(q.w.eqv_spec(t.w));
            assert(q.x.eqv_spec(t.x));
            assert(q.y.eqv_spec(t.y));
            assert(q.z.eqv_spec(t.z));
            Self::lemma_eqv_from_components(q, t);
            assert(q.eqv_spec(t));
        } else if i == 1 {
            let q = Self::signed_basis_spec(-1, i);
            let t = Self::from_ints_spec(0, -1, 0, 0);
            Scalar::lemma_mul_one_identity(m);
            Scalar::lemma_mul_zero(m);
            assert(q.w.eqv_spec(z));
            assert(q.x.eqv_spec(Scalar::from_int_spec(-1)));
            assert(q.y.eqv_spec(z));
            assert(q.z.eqv_spec(z));
            assert(t.w == z);
            assert(t.x == Scalar::from_int_spec(-1));
            assert(t.y == z);
            assert(t.z == z);
            assert(q.w.eqv_spec(t.w));
            assert(q.x.eqv_spec(t.x));
            assert(q.y.eqv_spec(t.y));
            assert(q.z.eqv_spec(t.z));
            Self::lemma_eqv_from_components(q, t);
            assert(q.eqv_spec(t));
        } else if i == 2 {
            let q = Self::signed_basis_spec(-1, i);
            let t = Self::from_ints_spec(0, 0, -1, 0);
            Scalar::lemma_mul_one_identity(m);
            Scalar::lemma_mul_zero(m);
            assert(q.w.eqv_spec(z));
            assert(q.x.eqv_spec(z));
            assert(q.y.eqv_spec(Scalar::from_int_spec(-1)));
            assert(q.z.eqv_spec(z));
            assert(t.w == z);
            assert(t.x == z);
            assert(t.y == Scalar::from_int_spec(-1));
            assert(t.z == z);
            assert(q.w.eqv_spec(t.w));
            assert(q.x.eqv_spec(t.x));
            assert(q.y.eqv_spec(t.y));
            assert(q.z.eqv_spec(t.z));
            Self::lemma_eqv_from_components(q, t);
            assert(q.eqv_spec(t));
        } else {
            let q = Self::signed_basis_spec(-1, i);
            let t = Self::from_ints_spec(0, 0, 0, -1);
            Scalar::lemma_mul_one_identity(m);
            Scalar::lemma_mul_zero(m);
            assert(q.w.eqv_spec(z));
            assert(q.x.eqv_spec(z));
            assert(q.y.eqv_spec(z));
            assert(q.z.eqv_spec(Scalar::from_int_spec(-1)));
            assert(t.w == z);
            assert(t.x == z);
            assert(t.y == z);
            assert(t.z == Scalar::from_int_spec(-1));
            assert(q.w.eqv_spec(t.w));
            assert(q.x.eqv_spec(t.x));
            assert(q.y.eqv_spec(t.y));
            assert(q.z.eqv_spec(t.z));
            Self::lemma_eqv_from_components(q, t);
            assert(q.eqv_spec(t));
        }
    }

    pub proof fn lemma_basis_mul_to_signed(i: int, j: int)
        requires
            0 <= i < 4,
            0 <= j < 4,
        ensures
            Self::basis_spec(i).mul_spec(Self::basis_spec(j)).eqv_spec(
                Self::signed_basis_spec(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j)),
            ),
    {
        let a = Self::basis_spec(i);
        let b = Self::basis_spec(j);
        let p = a.mul_spec(b);
        let target = Self::signed_basis_spec(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));
        if i == 0 {
            Self::lemma_mul_one_identity(b);
            assert(a == Self::one_spec());
            assert(a.mul_spec(b).eqv_spec(b));
            Self::lemma_scale_one_identity(b);
            assert(target == Self::signed_basis_spec(1, j));
            assert(target.eqv_spec(b));
            Self::lemma_eqv_symmetric(target, b);
            Self::lemma_eqv_transitive(p, b, target);
            assert(p.eqv_spec(target));
        } else if j == 0 {
            Self::lemma_mul_one_identity(a);
            assert(b == Self::one_spec());
            assert(a.mul_spec(b).eqv_spec(a));
            Self::lemma_scale_one_identity(a);
            assert(target == Self::signed_basis_spec(1, i));
            assert(target.eqv_spec(a));
            Self::lemma_eqv_symmetric(target, a);
            Self::lemma_eqv_transitive(p, a, target);
            assert(p.eqv_spec(target));
        } else if i == j {
            let minus_one = Self::from_ints_spec(-1, 0, 0, 0);
            if i == 1 {
                Self::lemma_basis_i_squared();
            } else if i == 2 {
                Self::lemma_basis_j_squared();
            } else {
                Self::lemma_basis_k_squared();
            }
            Self::lemma_signed_basis_neg_constant(0);
            assert(target == Self::signed_basis_spec(-1, 0));
            assert(target.eqv_spec(minus_one));
            Self::lemma_eqv_symmetric(target, minus_one);
            Self::lemma_eqv_transitive(p, minus_one, target);
            assert(p.eqv_spec(target));
        } else if i == 1 && j == 2 {
            Self::lemma_basis_i_mul_j();
            let k = Self::k_spec();
            Self::lemma_scale_one_identity(k);
            assert(target == Self::signed_basis_spec(1, 3));
            assert(target.eqv_spec(k));
            Self::lemma_eqv_symmetric(target, k);
            Self::lemma_eqv_transitive(p, k, target);
            assert(p.eqv_spec(target));
        } else if i == 2 && j == 3 {
            Self::lemma_basis_j_mul_k();
            let x = Self::i_spec();
            Self::lemma_scale_one_identity(x);
            assert(target == Self::signed_basis_spec(1, 1));
            assert(target.eqv_spec(x));
            Self::lemma_eqv_symmetric(target, x);
            Self::lemma_eqv_transitive(p, x, target);
            assert(p.eqv_spec(target));
        } else if i == 3 && j == 1 {
            Self::lemma_basis_k_mul_i();
            let y = Self::j_spec();
            Self::lemma_scale_one_identity(y);
            assert(target == Self::signed_basis_spec(1, 2));
            assert(target.eqv_spec(y));
            Self::lemma_eqv_symmetric(target, y);
            Self::lemma_eqv_transitive(p, y, target);
            assert(p.eqv_spec(target));
        } else if i == 2 && j == 1 {
            let minus_k = Self::from_ints_spec(0, 0, 0, -1);
            Self::lemma_basis_j_mul_i();
            Self::lemma_signed_basis_neg_constant(3);
            assert(target == Self::signed_basis_spec(-1, 3));
            assert(target.eqv_spec(minus_k));
            Self::lemma_eqv_symmetric(target, minus_k);
            Self::lemma_eqv_transitive(p, minus_k, target);
            assert(p.eqv_spec(target));
        } else if i == 3 && j == 2 {
            let minus_i = Self::from_ints_spec(0, -1, 0, 0);
            Self::lemma_basis_k_mul_j();
            Self::lemma_signed_basis_neg_constant(1);
            assert(target == Self::signed_basis_spec(-1, 1));
            assert(target.eqv_spec(minus_i));
            Self::lemma_eqv_symmetric(target, minus_i);
            Self::lemma_eqv_transitive(p, minus_i, target);
            assert(p.eqv_spec(target));
        } else {
            let minus_j = Self::from_ints_spec(0, 0, -1, 0);
            Self::lemma_basis_i_mul_k();
            Self::lemma_signed_basis_neg_constant(2);
            assert(target == Self::signed_basis_spec(-1, 2));
            assert(target.eqv_spec(minus_j));
            Self::lemma_eqv_symmetric(target, minus_j);
            Self::lemma_eqv_transitive(p, minus_j, target);
            assert(p.eqv_spec(target));
        }
    }

    pub proof fn lemma_signed_basis_scale_neg_one(sign: int, i: int)
        requires
            (sign == 1 || sign == -1),
            0 <= i < 4,
        ensures
            Self::signed_basis_spec(sign, i).scale_spec(Scalar::from_int_spec(-1))
                .eqv_spec(Self::signed_basis_spec(-sign, i)),
    {
        let m = Scalar::from_int_spec(-1);
        let s = Scalar::from_int_spec(sign);
        let lhs = Self::signed_basis_spec(sign, i).scale_spec(m);
        let rhs = Self::signed_basis_spec(-sign, i);
        let b = Self::basis_spec(i);
        Self::lemma_scale_associative(b, s, m);
        assert(Self::signed_basis_spec(sign, i) == b.scale_spec(s));
        assert(lhs.eqv_spec(b.scale_spec(s.mul_spec(m))));
        Scalar::lemma_mul_commutative(s, m);
        assert(s.mul_spec(m).eqv_spec(m.mul_spec(s)));
        Self::lemma_eqv_transitive(b.scale_spec(s.mul_spec(m)), b.scale_spec(m.mul_spec(s)), rhs);
        if sign == 1 {
            assert(m.mul_spec(s) == Scalar::from_int_spec(-1));
            assert(rhs == b.scale_spec(Scalar::from_int_spec(-1)));
            Self::lemma_eqv_reflexive(rhs);
            assert(b.scale_spec(m.mul_spec(s)).eqv_spec(rhs));
        } else {
            assert(sign == -1);
            assert(s == Scalar::from_int_spec(-1));
            assert(m.mul_spec(s).num == (-1) * (-1));
            assert((-1) * (-1) == 1) by (nonlinear_arith);
            assert(m.mul_spec(s).num == 1);
            assert(m.mul_spec(s).den == 0);
            assert(m.mul_spec(s) == Scalar::from_int_spec(1));
            assert(rhs == b.scale_spec(Scalar::from_int_spec(1)));
            Self::lemma_eqv_reflexive(rhs);
            assert(b.scale_spec(m.mul_spec(s)).eqv_spec(rhs));
        }
        Self::lemma_eqv_transitive(lhs, b.scale_spec(s.mul_spec(m)), b.scale_spec(m.mul_spec(s)));
        Self::lemma_eqv_transitive(lhs, b.scale_spec(m.mul_spec(s)), rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_signed_basis_mul_basis(sign: int, i: int, j: int)
        requires
            (sign == 1 || sign == -1),
            0 <= i < 4,
            0 <= j < 4,
        ensures
            Self::signed_basis_spec(sign, i).mul_spec(Self::basis_spec(j)).eqv_spec(
                Self::signed_basis_spec(sign * Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j)),
            ),
    {
        let a = Self::basis_spec(i);
        let b = Self::basis_spec(j);
        let s = Scalar::from_int_spec(sign);
        let lhs = Self::signed_basis_spec(sign, i).mul_spec(b);
        let mid0 = a.mul_spec(b).scale_spec(s);
        let base = Self::signed_basis_spec(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));
        let mid1 = base.scale_spec(s);
        let rhs = Self::signed_basis_spec(sign * Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));

        Self::lemma_mul_scale_left(a, b, s);
        assert(lhs.eqv_spec(mid0));

        Self::lemma_basis_mul_to_signed(i, j);
        Self::lemma_scale_eqv_congruence(a.mul_spec(b), base, s);
        assert(mid0.eqv_spec(mid1));

        Self::lemma_signed_basis_scale_neg_one(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));
        if sign == 1 {
            Self::lemma_scale_one_identity(base);
            assert(mid1.eqv_spec(base));
            assert(rhs == base);
            Self::lemma_eqv_reflexive(rhs);
            assert(base.eqv_spec(rhs));
            Self::lemma_eqv_transitive(lhs, mid0, mid1);
            Self::lemma_eqv_transitive(lhs, mid1, rhs);
            assert(lhs.eqv_spec(rhs));
        } else {
            assert(sign == -1);
            assert(mid1 == base.scale_spec(Scalar::from_int_spec(-1)));
            assert(rhs == Self::signed_basis_spec(-Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j)));
            assert(base.scale_spec(Scalar::from_int_spec(-1)).eqv_spec(rhs));
            Self::lemma_eqv_transitive(lhs, mid0, mid1);
            Self::lemma_eqv_transitive(lhs, mid1, rhs);
            assert(lhs.eqv_spec(rhs));
        }
    }

    pub proof fn lemma_basis_mul_signed_basis(i: int, sign: int, j: int)
        requires
            0 <= i < 4,
            (sign == 1 || sign == -1),
            0 <= j < 4,
        ensures
            Self::basis_spec(i).mul_spec(Self::signed_basis_spec(sign, j)).eqv_spec(
                Self::signed_basis_spec(sign * Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j)),
            ),
    {
        let a = Self::basis_spec(i);
        let b = Self::basis_spec(j);
        let s = Scalar::from_int_spec(sign);
        let lhs = a.mul_spec(Self::signed_basis_spec(sign, j));
        let mid0 = a.mul_spec(b).scale_spec(s);
        let base = Self::signed_basis_spec(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));
        let mid1 = base.scale_spec(s);
        let rhs = Self::signed_basis_spec(sign * Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));

        Self::lemma_mul_scale_right(a, b, s);
        assert(lhs.eqv_spec(mid0));

        Self::lemma_basis_mul_to_signed(i, j);
        Self::lemma_scale_eqv_congruence(a.mul_spec(b), base, s);
        assert(mid0.eqv_spec(mid1));

        Self::lemma_signed_basis_scale_neg_one(Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j));
        if sign == 1 {
            Self::lemma_scale_one_identity(base);
            assert(mid1.eqv_spec(base));
            assert(rhs == base);
            Self::lemma_eqv_reflexive(rhs);
            assert(base.eqv_spec(rhs));
            Self::lemma_eqv_transitive(lhs, mid0, mid1);
            Self::lemma_eqv_transitive(lhs, mid1, rhs);
            assert(lhs.eqv_spec(rhs));
        } else {
            assert(sign == -1);
            assert(mid1 == base.scale_spec(Scalar::from_int_spec(-1)));
            assert(rhs == Self::signed_basis_spec(-Self::basis_mul_sign_spec(i, j), Self::basis_mul_idx_spec(i, j)));
            assert(base.scale_spec(Scalar::from_int_spec(-1)).eqv_spec(rhs));
            Self::lemma_eqv_transitive(lhs, mid0, mid1);
            Self::lemma_eqv_transitive(lhs, mid1, rhs);
            assert(lhs.eqv_spec(rhs));
        }
    }

    #[verifier::rlimit(300)]
    pub proof fn lemma_basis_decompose_eqv(q: Self)
        ensures
            q.eqv_spec(Self::basis_decompose_spec(q)),
    {
        let z = Scalar::from_int_spec(0);
        let d0 = Self::basis_spec(0).scale_spec(q.w);
        let d1 = Self::basis_spec(1).scale_spec(q.x);
        let d2 = Self::basis_spec(2).scale_spec(q.y);
        let d3 = Self::basis_spec(3).scale_spec(q.z);
        let d = Self::basis_decompose_spec(q);

        Scalar::lemma_mul_one_identity(q.w);
        Scalar::lemma_mul_one_identity(q.x);
        Scalar::lemma_mul_one_identity(q.y);
        Scalar::lemma_mul_one_identity(q.z);
        Scalar::lemma_mul_zero(q.w);
        Scalar::lemma_mul_zero(q.x);
        Scalar::lemma_mul_zero(q.y);
        Scalar::lemma_mul_zero(q.z);

        assert(d0.w.eqv_spec(q.w));
        assert(d0.x.eqv_spec(z));
        assert(d0.y.eqv_spec(z));
        assert(d0.z.eqv_spec(z));

        assert(d1.w.eqv_spec(z));
        assert(d1.x.eqv_spec(q.x));
        assert(d1.y.eqv_spec(z));
        assert(d1.z.eqv_spec(z));

        assert(d2.w.eqv_spec(z));
        assert(d2.x.eqv_spec(z));
        assert(d2.y.eqv_spec(q.y));
        assert(d2.z.eqv_spec(z));

        assert(d3.w.eqv_spec(z));
        assert(d3.x.eqv_spec(z));
        assert(d3.y.eqv_spec(z));
        assert(d3.z.eqv_spec(q.z));

        assert(d.w == d0.w.add_spec(d1.w).add_spec(d2.w).add_spec(d3.w));
        assert(d.x == d0.x.add_spec(d1.x).add_spec(d2.x).add_spec(d3.x));
        assert(d.y == d0.y.add_spec(d1.y).add_spec(d2.y).add_spec(d3.y));
        assert(d.z == d0.z.add_spec(d1.z).add_spec(d2.z).add_spec(d3.z));

        let w01 = d0.w.add_spec(d1.w);
        Scalar::lemma_eqv_add_congruence(d0.w, q.w, d1.w, z);
        assert(w01.eqv_spec(q.w.add_spec(z)));
        Scalar::lemma_add_zero_identity(q.w);
        assert(w01.eqv_spec(q.w));
        let w012 = w01.add_spec(d2.w);
        Scalar::lemma_eqv_add_congruence(w01, q.w, d2.w, z);
        assert(w012.eqv_spec(q.w.add_spec(z)));
        assert(w012.eqv_spec(q.w));
        let w0123 = w012.add_spec(d3.w);
        Scalar::lemma_eqv_add_congruence(w012, q.w, d3.w, z);
        assert(w0123.eqv_spec(q.w.add_spec(z)));
        assert(w0123.eqv_spec(q.w));
        assert(d.w.eqv_spec(w0123));
        Scalar::lemma_eqv_transitive(d.w, w0123, q.w);
        assert(d.w.eqv_spec(q.w));

        let x01 = d0.x.add_spec(d1.x);
        Scalar::lemma_eqv_add_congruence(d0.x, z, d1.x, q.x);
        assert(x01.eqv_spec(z.add_spec(q.x)));
        Scalar::lemma_add_zero_identity(q.x);
        assert(x01.eqv_spec(q.x));
        let x012 = x01.add_spec(d2.x);
        Scalar::lemma_eqv_add_congruence(x01, q.x, d2.x, z);
        assert(x012.eqv_spec(q.x.add_spec(z)));
        assert(x012.eqv_spec(q.x));
        let x0123 = x012.add_spec(d3.x);
        Scalar::lemma_eqv_add_congruence(x012, q.x, d3.x, z);
        assert(x0123.eqv_spec(q.x.add_spec(z)));
        assert(x0123.eqv_spec(q.x));
        assert(d.x.eqv_spec(x0123));
        Scalar::lemma_eqv_transitive(d.x, x0123, q.x);
        assert(d.x.eqv_spec(q.x));

        let y01 = d0.y.add_spec(d1.y);
        Scalar::lemma_eqv_add_congruence(d0.y, z, d1.y, z);
        assert(y01.eqv_spec(z.add_spec(z)));
        assert(z.add_spec(z) == z);
        assert(y01.eqv_spec(z));
        let y012 = y01.add_spec(d2.y);
        Scalar::lemma_eqv_add_congruence(y01, z, d2.y, q.y);
        assert(y012.eqv_spec(z.add_spec(q.y)));
        Scalar::lemma_add_zero_identity(q.y);
        assert(y012.eqv_spec(q.y));
        let y0123 = y012.add_spec(d3.y);
        Scalar::lemma_eqv_add_congruence(y012, q.y, d3.y, z);
        assert(y0123.eqv_spec(q.y.add_spec(z)));
        assert(y0123.eqv_spec(q.y));
        assert(d.y.eqv_spec(y0123));
        Scalar::lemma_eqv_transitive(d.y, y0123, q.y);
        assert(d.y.eqv_spec(q.y));

        let z01 = d0.z.add_spec(d1.z);
        Scalar::lemma_eqv_add_congruence(d0.z, z, d1.z, z);
        assert(z01.eqv_spec(z.add_spec(z)));
        assert(z01.eqv_spec(z));
        let z012 = z01.add_spec(d2.z);
        Scalar::lemma_eqv_add_congruence(z01, z, d2.z, z);
        assert(z012.eqv_spec(z.add_spec(z)));
        assert(z012.eqv_spec(z));
        let z0123 = z012.add_spec(d3.z);
        Scalar::lemma_eqv_add_congruence(z012, z, d3.z, q.z);
        assert(z0123.eqv_spec(z.add_spec(q.z)));
        Scalar::lemma_add_zero_identity(q.z);
        assert(z0123.eqv_spec(q.z));
        assert(d.z.eqv_spec(z0123));
        Scalar::lemma_eqv_transitive(d.z, z0123, q.z);
        assert(d.z.eqv_spec(q.z));

        Self::lemma_eqv_symmetric(q, d);
        assert(q.w.eqv_spec(d.w));
        assert(q.x.eqv_spec(d.x));
        assert(q.y.eqv_spec(d.y));
        assert(q.z.eqv_spec(d.z));
        Self::lemma_eqv_from_components(q, d);
        assert(q.eqv_spec(d));
    }

    #[verifier::rlimit(1200)]
    pub proof fn lemma_assoc_basis_any(i: int, b: Self, c: Self)
        requires
            0 <= i < 4,
        ensures
            Self::assoc_instance_spec(Self::basis_spec(i), b, c),
    {
        let a = Self::basis_spec(i);

        let b0 = Self::basis_spec(0).scale_spec(b.w);
        let b1 = Self::basis_spec(1).scale_spec(b.x);
        let b2 = Self::basis_spec(2).scale_spec(b.y);
        let b3 = Self::basis_spec(3).scale_spec(b.z);
        let bsum = Self::basis_decompose_spec(b);

        let c0 = Self::basis_spec(0).scale_spec(c.w);
        let c1 = Self::basis_spec(1).scale_spec(c.x);
        let c2 = Self::basis_spec(2).scale_spec(c.y);
        let c3 = Self::basis_spec(3).scale_spec(c.z);
        let csum = Self::basis_decompose_spec(c);

        // Basis-triple associativity cases are generated in quaternion_assoc_cases.rs.
        // j = 0
        Self::lemma_basis_assoc_indices(i, 0, 0);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(0), Self::basis_spec(0), c.w);
        Self::lemma_basis_assoc_indices(i, 0, 1);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(0), Self::basis_spec(1), c.x);
        Self::lemma_basis_assoc_indices(i, 0, 2);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(0), Self::basis_spec(2), c.y);
        Self::lemma_basis_assoc_indices(i, 0, 3);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(0), Self::basis_spec(3), c.z);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(0), c0, c1);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(0), c0.add_spec(c1), c2);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(0), c0.add_spec(c1).add_spec(c2), c3);

        // j = 1
        Self::lemma_basis_assoc_indices(i, 1, 0);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(1), Self::basis_spec(0), c.w);
        Self::lemma_basis_assoc_indices(i, 1, 1);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(1), Self::basis_spec(1), c.x);
        Self::lemma_basis_assoc_indices(i, 1, 2);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(1), Self::basis_spec(2), c.y);
        Self::lemma_basis_assoc_indices(i, 1, 3);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(1), Self::basis_spec(3), c.z);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(1), c0, c1);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(1), c0.add_spec(c1), c2);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(1), c0.add_spec(c1).add_spec(c2), c3);

        // j = 2
        Self::lemma_basis_assoc_indices(i, 2, 0);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(2), Self::basis_spec(0), c.w);
        Self::lemma_basis_assoc_indices(i, 2, 1);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(2), Self::basis_spec(1), c.x);
        Self::lemma_basis_assoc_indices(i, 2, 2);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(2), Self::basis_spec(2), c.y);
        Self::lemma_basis_assoc_indices(i, 2, 3);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(2), Self::basis_spec(3), c.z);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(2), c0, c1);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(2), c0.add_spec(c1), c2);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(2), c0.add_spec(c1).add_spec(c2), c3);

        // j = 3
        Self::lemma_basis_assoc_indices(i, 3, 0);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(3), Self::basis_spec(0), c.w);
        Self::lemma_basis_assoc_indices(i, 3, 1);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(3), Self::basis_spec(1), c.x);
        Self::lemma_basis_assoc_indices(i, 3, 2);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(3), Self::basis_spec(2), c.y);
        Self::lemma_basis_assoc_indices(i, 3, 3);
        Self::lemma_assoc_linear_right_scale(a, Self::basis_spec(3), Self::basis_spec(3), c.z);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(3), c0, c1);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(3), c0.add_spec(c1), c2);
        Self::lemma_assoc_linear_right_add(a, Self::basis_spec(3), c0.add_spec(c1).add_spec(c2), c3);

        // Lift middle operand from basis terms to full decomposition.
        Self::lemma_assoc_linear_middle_scale(a, Self::basis_spec(0), csum, b.w);
        Self::lemma_assoc_linear_middle_scale(a, Self::basis_spec(1), csum, b.x);
        Self::lemma_assoc_linear_middle_scale(a, Self::basis_spec(2), csum, b.y);
        Self::lemma_assoc_linear_middle_scale(a, Self::basis_spec(3), csum, b.z);
        Self::lemma_assoc_linear_middle_add(a, b0, b1, csum);
        Self::lemma_assoc_linear_middle_add(a, b0.add_spec(b1), b2, csum);
        Self::lemma_assoc_linear_middle_add(a, b0.add_spec(b1).add_spec(b2), b3, csum);

        // Move from decomposition representatives back to b and c.
        Self::lemma_basis_decompose_eqv(c);
        Self::lemma_eqv_symmetric(c, csum);
        Self::lemma_assoc_eqv_right(a, bsum, csum, c);

        Self::lemma_basis_decompose_eqv(b);
        Self::lemma_eqv_symmetric(b, bsum);
        Self::lemma_assoc_eqv_middle(a, bsum, b, c);
        assert(Self::assoc_instance_spec(a, b, c));
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

    pub proof fn lemma_conjugate_add(a: Self, b: Self)
        ensures
            a.add_spec(b).conjugate_spec() == a.conjugate_spec().add_spec(b.conjugate_spec()),
    {
        let lhs = a.add_spec(b).conjugate_spec();
        let rhs = a.conjugate_spec().add_spec(b.conjugate_spec());
        Scalar::lemma_neg_add(a.x, b.x);
        Scalar::lemma_neg_add(a.y, b.y);
        Scalar::lemma_neg_add(a.z, b.z);
        assert(lhs.w == a.w.add_spec(b.w));
        assert(rhs.w == a.w.add_spec(b.w));
        assert(lhs.x == a.x.add_spec(b.x).neg_spec());
        assert(rhs.x == a.x.neg_spec().add_spec(b.x.neg_spec()));
        assert(lhs.y == a.y.add_spec(b.y).neg_spec());
        assert(rhs.y == a.y.neg_spec().add_spec(b.y.neg_spec()));
        assert(lhs.z == a.z.add_spec(b.z).neg_spec());
        assert(rhs.z == a.z.neg_spec().add_spec(b.z.neg_spec()));
        assert(lhs == rhs);
    }

    pub proof fn lemma_conjugate_scale(a: Self, k: Scalar)
        ensures
            a.scale_spec(k).conjugate_spec() == a.conjugate_spec().scale_spec(k),
    {
        let lhs = a.scale_spec(k).conjugate_spec();
        let rhs = a.conjugate_spec().scale_spec(k);

        Scalar::lemma_mul_commutative(a.x.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, a.x);
        Scalar::lemma_mul_commutative(k, a.x);
        Scalar::lemma_mul_commutative(a.y.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, a.y);
        Scalar::lemma_mul_commutative(k, a.y);
        Scalar::lemma_mul_commutative(a.z.neg_spec(), k);
        Scalar::lemma_mul_neg_right(k, a.z);
        Scalar::lemma_mul_commutative(k, a.z);

        assert(lhs.w == a.w.mul_spec(k));
        assert(rhs.w == a.w.mul_spec(k));

        assert(rhs.x == a.x.neg_spec().mul_spec(k));
        assert(rhs.x == k.mul_spec(a.x.neg_spec()));
        assert(rhs.x == k.mul_spec(a.x).neg_spec());
        assert(rhs.x == a.x.mul_spec(k).neg_spec());
        assert(lhs.x == a.x.mul_spec(k).neg_spec());

        assert(rhs.y == a.y.neg_spec().mul_spec(k));
        assert(rhs.y == k.mul_spec(a.y.neg_spec()));
        assert(rhs.y == k.mul_spec(a.y).neg_spec());
        assert(rhs.y == a.y.mul_spec(k).neg_spec());
        assert(lhs.y == a.y.mul_spec(k).neg_spec());

        assert(rhs.z == a.z.neg_spec().mul_spec(k));
        assert(rhs.z == k.mul_spec(a.z.neg_spec()));
        assert(rhs.z == k.mul_spec(a.z).neg_spec());
        assert(rhs.z == a.z.mul_spec(k).neg_spec());
        assert(lhs.z == a.z.mul_spec(k).neg_spec());

        assert(lhs == rhs);
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

    pub proof fn lemma_as_vec4_add(a: Self, b: Self)
        ensures
            a.add_spec(b).as_vec4_spec() == a.as_vec4_spec().add_spec(b.as_vec4_spec()),
    {
        let lhs = a.add_spec(b).as_vec4_spec();
        let rhs = a.as_vec4_spec().add_spec(b.as_vec4_spec());
        assert(lhs.x == a.w.add_spec(b.w));
        assert(lhs.y == a.x.add_spec(b.x));
        assert(lhs.z == a.y.add_spec(b.y));
        assert(lhs.w == a.z.add_spec(b.z));
        assert(rhs.x == a.w.add_spec(b.w));
        assert(rhs.y == a.x.add_spec(b.x));
        assert(rhs.z == a.y.add_spec(b.y));
        assert(rhs.w == a.z.add_spec(b.z));
        assert(lhs == rhs);
    }

    pub proof fn lemma_as_vec4_scale(a: Self, k: Scalar)
        ensures
            a.scale_spec(k).as_vec4_spec() == a.as_vec4_spec().scale_spec(k),
    {
        let lhs = a.scale_spec(k).as_vec4_spec();
        let rhs = a.as_vec4_spec().scale_spec(k);
        assert(lhs.x == a.w.mul_spec(k));
        assert(lhs.y == a.x.mul_spec(k));
        assert(lhs.z == a.y.mul_spec(k));
        assert(lhs.w == a.z.mul_spec(k));
        assert(rhs.x == a.w.mul_spec(k));
        assert(rhs.y == a.x.mul_spec(k));
        assert(rhs.z == a.y.mul_spec(k));
        assert(rhs.w == a.z.mul_spec(k));
        assert(lhs == rhs);
    }

    pub open spec fn mul_row_w_spec(rhs: Self) -> Vec4 {
        Vec4 {
            x: rhs.w,
            y: rhs.x.neg_spec(),
            z: rhs.y.neg_spec(),
            w: rhs.z.neg_spec(),
        }
    }

    pub open spec fn mul_row_x_spec(rhs: Self) -> Vec4 {
        Vec4 {
            x: rhs.x,
            y: rhs.w,
            z: rhs.z,
            w: rhs.y.neg_spec(),
        }
    }

    pub open spec fn mul_row_y_spec(rhs: Self) -> Vec4 {
        Vec4 {
            x: rhs.y,
            y: rhs.z.neg_spec(),
            z: rhs.w,
            w: rhs.x,
        }
    }

    pub open spec fn mul_row_z_spec(rhs: Self) -> Vec4 {
        Vec4 {
            x: rhs.z,
            y: rhs.y,
            z: rhs.x.neg_spec(),
            w: rhs.w,
        }
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

    pub proof fn lemma_conjugate_eqv_congruence(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.conjugate_spec().eqv_spec(b.conjugate_spec()),
    {
        let ac = a.conjugate_spec();
        let bc = b.conjugate_spec();
        Scalar::lemma_eqv_neg_congruence(a.x, b.x);
        Scalar::lemma_eqv_neg_congruence(a.y, b.y);
        Scalar::lemma_eqv_neg_congruence(a.z, b.z);
        assert(ac.w.eqv_spec(bc.w));
        assert(ac.x.eqv_spec(bc.x));
        assert(ac.y.eqv_spec(bc.y));
        assert(ac.z.eqv_spec(bc.z));
        Self::lemma_eqv_from_components(ac, bc);
        assert(ac.eqv_spec(bc));
    }

    pub open spec fn assoc_instance_spec(a: Self, b: Self, c: Self) -> bool {
        a.mul_spec(b).mul_spec(c).eqv_spec(a.mul_spec(b.mul_spec(c)))
    }

    pub open spec fn conjugate_mul_reverse_instance_spec(a: Self, b: Self) -> bool {
        a.mul_spec(b).conjugate_spec().eqv_spec(b.conjugate_spec().mul_spec(a.conjugate_spec()))
    }

    pub proof fn lemma_conjugate_mul_reverse_linear_left_add(a1: Self, a2: Self, b: Self)
        requires
            Self::conjugate_mul_reverse_instance_spec(a1, b),
            Self::conjugate_mul_reverse_instance_spec(a2, b),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a1.add_spec(a2), b),
    {
        let lhs = a1.add_spec(a2).mul_spec(b).conjugate_spec();
        let rhs = b.conjugate_spec().mul_spec(a1.add_spec(a2).conjugate_spec());

        let lsplit = a1.mul_spec(b).add_spec(a2.mul_spec(b));
        let lsplit_c = lsplit.conjugate_spec();
        let ltarget = a1.mul_spec(b).conjugate_spec().add_spec(a2.mul_spec(b).conjugate_spec());

        let rtarget = b.conjugate_spec().mul_spec(a1.conjugate_spec()).add_spec(
            b.conjugate_spec().mul_spec(a2.conjugate_spec()),
        );

        Self::lemma_mul_distributes_over_add_left(a1, a2, b);
        Self::lemma_conjugate_eqv_congruence(a1.add_spec(a2).mul_spec(b), lsplit);
        assert(lhs.eqv_spec(lsplit_c));
        Self::lemma_conjugate_add(a1.mul_spec(b), a2.mul_spec(b));
        assert(lsplit_c == ltarget);

        Self::lemma_conjugate_add(a1, a2);
        assert(a1.add_spec(a2).conjugate_spec() == a1.conjugate_spec().add_spec(a2.conjugate_spec()));
        Self::lemma_mul_distributes_over_add_right(b.conjugate_spec(), a1.conjugate_spec(), a2.conjugate_spec());
        assert(rhs.eqv_spec(rtarget));

        Self::lemma_add_eqv_congruence(
            a1.mul_spec(b).conjugate_spec(),
            b.conjugate_spec().mul_spec(a1.conjugate_spec()),
            a2.mul_spec(b).conjugate_spec(),
            b.conjugate_spec().mul_spec(a2.conjugate_spec()),
        );
        assert(ltarget.eqv_spec(rtarget));

        Self::lemma_eqv_transitive(lhs, lsplit_c, ltarget);
        Self::lemma_eqv_transitive(lhs, ltarget, rtarget);
        Self::lemma_eqv_symmetric(rhs, rtarget);
        Self::lemma_eqv_transitive(lhs, rtarget, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_conjugate_mul_reverse_linear_left_scale(a: Self, b: Self, k: Scalar)
        requires
            Self::conjugate_mul_reverse_instance_spec(a, b),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a.scale_spec(k), b),
    {
        let lhs = a.scale_spec(k).mul_spec(b).conjugate_spec();
        let rhs = b.conjugate_spec().mul_spec(a.scale_spec(k).conjugate_spec());

        let lscaled = a.mul_spec(b).scale_spec(k);
        let ltarget = a.mul_spec(b).conjugate_spec().scale_spec(k);

        let rmid = b.conjugate_spec().mul_spec(a.conjugate_spec().scale_spec(k));
        let rtarget = b.conjugate_spec().mul_spec(a.conjugate_spec()).scale_spec(k);

        Self::lemma_mul_scale_left(a, b, k);
        Self::lemma_conjugate_eqv_congruence(a.scale_spec(k).mul_spec(b), lscaled);
        assert(lhs.eqv_spec(lscaled.conjugate_spec()));
        Self::lemma_conjugate_scale(a.mul_spec(b), k);
        assert(lscaled.conjugate_spec() == ltarget);

        Self::lemma_conjugate_scale(a, k);
        assert(a.scale_spec(k).conjugate_spec() == a.conjugate_spec().scale_spec(k));
        assert(rmid == rhs);
        Self::lemma_mul_scale_right(b.conjugate_spec(), a.conjugate_spec(), k);
        assert(rmid.eqv_spec(rtarget));

        Self::lemma_scale_eqv_congruence(a.mul_spec(b).conjugate_spec(), b.conjugate_spec().mul_spec(a.conjugate_spec()), k);
        assert(ltarget.eqv_spec(rtarget));

        Self::lemma_eqv_transitive(lhs, lscaled.conjugate_spec(), ltarget);
        Self::lemma_eqv_transitive(lhs, ltarget, rtarget);
        Self::lemma_eqv_symmetric(rmid, rtarget);
        Self::lemma_eqv_symmetric(rhs, rmid);
        Self::lemma_eqv_transitive(lhs, rtarget, rmid);
        Self::lemma_eqv_transitive(lhs, rmid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_conjugate_mul_reverse_linear_right_add(a: Self, b1: Self, b2: Self)
        requires
            Self::conjugate_mul_reverse_instance_spec(a, b1),
            Self::conjugate_mul_reverse_instance_spec(a, b2),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a, b1.add_spec(b2)),
    {
        let lhs = a.mul_spec(b1.add_spec(b2)).conjugate_spec();
        let rhs = b1.add_spec(b2).conjugate_spec().mul_spec(a.conjugate_spec());

        let lsplit = a.mul_spec(b1).add_spec(a.mul_spec(b2));
        let lsplit_c = lsplit.conjugate_spec();
        let ltarget = a.mul_spec(b1).conjugate_spec().add_spec(a.mul_spec(b2).conjugate_spec());

        let rtarget = b1.conjugate_spec().mul_spec(a.conjugate_spec()).add_spec(
            b2.conjugate_spec().mul_spec(a.conjugate_spec()),
        );

        Self::lemma_mul_distributes_over_add_right(a, b1, b2);
        Self::lemma_conjugate_eqv_congruence(a.mul_spec(b1.add_spec(b2)), lsplit);
        assert(lhs.eqv_spec(lsplit_c));
        Self::lemma_conjugate_add(a.mul_spec(b1), a.mul_spec(b2));
        assert(lsplit_c == ltarget);

        Self::lemma_conjugate_add(b1, b2);
        assert(b1.add_spec(b2).conjugate_spec() == b1.conjugate_spec().add_spec(b2.conjugate_spec()));
        Self::lemma_mul_distributes_over_add_left(b1.conjugate_spec(), b2.conjugate_spec(), a.conjugate_spec());
        assert(rhs.eqv_spec(rtarget));

        Self::lemma_add_eqv_congruence(
            a.mul_spec(b1).conjugate_spec(),
            b1.conjugate_spec().mul_spec(a.conjugate_spec()),
            a.mul_spec(b2).conjugate_spec(),
            b2.conjugate_spec().mul_spec(a.conjugate_spec()),
        );
        assert(ltarget.eqv_spec(rtarget));

        Self::lemma_eqv_transitive(lhs, lsplit_c, ltarget);
        Self::lemma_eqv_transitive(lhs, ltarget, rtarget);
        Self::lemma_eqv_symmetric(rhs, rtarget);
        Self::lemma_eqv_transitive(lhs, rtarget, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_conjugate_mul_reverse_linear_right_scale(a: Self, b: Self, k: Scalar)
        requires
            Self::conjugate_mul_reverse_instance_spec(a, b),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a, b.scale_spec(k)),
    {
        let lhs = a.mul_spec(b.scale_spec(k)).conjugate_spec();
        let rhs = b.scale_spec(k).conjugate_spec().mul_spec(a.conjugate_spec());

        let lscaled = a.mul_spec(b).scale_spec(k);
        let ltarget = a.mul_spec(b).conjugate_spec().scale_spec(k);

        let rmid = b.conjugate_spec().scale_spec(k).mul_spec(a.conjugate_spec());
        let rtarget = b.conjugate_spec().mul_spec(a.conjugate_spec()).scale_spec(k);

        Self::lemma_mul_scale_right(a, b, k);
        Self::lemma_conjugate_eqv_congruence(a.mul_spec(b.scale_spec(k)), lscaled);
        assert(lhs.eqv_spec(lscaled.conjugate_spec()));
        Self::lemma_conjugate_scale(a.mul_spec(b), k);
        assert(lscaled.conjugate_spec() == ltarget);

        Self::lemma_conjugate_scale(b, k);
        assert(b.scale_spec(k).conjugate_spec() == b.conjugate_spec().scale_spec(k));
        assert(rmid == rhs);
        Self::lemma_mul_scale_left(b.conjugate_spec(), a.conjugate_spec(), k);
        assert(rmid.eqv_spec(rtarget));

        Self::lemma_scale_eqv_congruence(a.mul_spec(b).conjugate_spec(), b.conjugate_spec().mul_spec(a.conjugate_spec()), k);
        assert(ltarget.eqv_spec(rtarget));

        Self::lemma_eqv_transitive(lhs, lscaled.conjugate_spec(), ltarget);
        Self::lemma_eqv_transitive(lhs, ltarget, rtarget);
        Self::lemma_eqv_symmetric(rmid, rtarget);
        Self::lemma_eqv_symmetric(rhs, rmid);
        Self::lemma_eqv_transitive(lhs, rtarget, rmid);
        Self::lemma_eqv_transitive(lhs, rmid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_conjugate_mul_reverse_eqv_right(a: Self, b1: Self, b2: Self)
        requires
            Self::conjugate_mul_reverse_instance_spec(a, b1),
            b1.eqv_spec(b2),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a, b2),
    {
        let lhs1 = a.mul_spec(b1).conjugate_spec();
        let lhs2 = a.mul_spec(b2).conjugate_spec();
        let rhs1 = b1.conjugate_spec().mul_spec(a.conjugate_spec());
        let rhs2 = b2.conjugate_spec().mul_spec(a.conjugate_spec());

        Self::lemma_mul_eqv_congruence_right(a, b1, b2);
        Self::lemma_conjugate_eqv_congruence(a.mul_spec(b1), a.mul_spec(b2));
        assert(lhs1.eqv_spec(lhs2));

        Self::lemma_conjugate_eqv_congruence(b1, b2);
        Self::lemma_mul_eqv_congruence_left(b1.conjugate_spec(), b2.conjugate_spec(), a.conjugate_spec());
        assert(rhs1.eqv_spec(rhs2));

        Self::lemma_eqv_symmetric(lhs1, lhs2);
        Self::lemma_eqv_transitive(lhs2, lhs1, rhs1);
        Self::lemma_eqv_transitive(lhs2, rhs1, rhs2);
        assert(lhs2.eqv_spec(rhs2));
    }

    pub proof fn lemma_conjugate_mul_reverse_eqv_left(a1: Self, a2: Self, b: Self)
        requires
            Self::conjugate_mul_reverse_instance_spec(a1, b),
            a1.eqv_spec(a2),
        ensures
            Self::conjugate_mul_reverse_instance_spec(a2, b),
    {
        let lhs1 = a1.mul_spec(b).conjugate_spec();
        let lhs2 = a2.mul_spec(b).conjugate_spec();
        let rhs1 = b.conjugate_spec().mul_spec(a1.conjugate_spec());
        let rhs2 = b.conjugate_spec().mul_spec(a2.conjugate_spec());

        Self::lemma_mul_eqv_congruence_left(a1, a2, b);
        Self::lemma_conjugate_eqv_congruence(a1.mul_spec(b), a2.mul_spec(b));
        assert(lhs1.eqv_spec(lhs2));

        Self::lemma_conjugate_eqv_congruence(a1, a2);
        Self::lemma_mul_eqv_congruence_right(b.conjugate_spec(), a1.conjugate_spec(), a2.conjugate_spec());
        assert(rhs1.eqv_spec(rhs2));

        Self::lemma_eqv_symmetric(lhs1, lhs2);
        Self::lemma_eqv_transitive(lhs2, lhs1, rhs1);
        Self::lemma_eqv_transitive(lhs2, rhs1, rhs2);
        assert(lhs2.eqv_spec(rhs2));
    }

    pub proof fn lemma_conjugate_mul_reverse_basis_indices(i: int, j: int)
        requires
            0 <= i < 4,
            0 <= j < 4,
        ensures
            Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(i), Self::basis_spec(j)),
    {
        if i == 0 {
            if j == 0 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(0), Self::basis_spec(0))) by (compute);
            } else if j == 1 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(0), Self::basis_spec(1))) by (compute);
            } else if j == 2 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(0), Self::basis_spec(2))) by (compute);
            } else {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(0), Self::basis_spec(3))) by (compute);
            }
        } else if i == 1 {
            if j == 0 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(1), Self::basis_spec(0))) by (compute);
            } else if j == 1 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(1), Self::basis_spec(1))) by (compute);
            } else if j == 2 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(1), Self::basis_spec(2))) by (compute);
            } else {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(1), Self::basis_spec(3))) by (compute);
            }
        } else if i == 2 {
            if j == 0 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(2), Self::basis_spec(0))) by (compute);
            } else if j == 1 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(2), Self::basis_spec(1))) by (compute);
            } else if j == 2 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(2), Self::basis_spec(2))) by (compute);
            } else {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(2), Self::basis_spec(3))) by (compute);
            }
        } else {
            if j == 0 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(3), Self::basis_spec(0))) by (compute);
            } else if j == 1 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(3), Self::basis_spec(1))) by (compute);
            } else if j == 2 {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(3), Self::basis_spec(2))) by (compute);
            } else {
                assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(3), Self::basis_spec(3))) by (compute);
            }
        }

        assert(Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(i), Self::basis_spec(j)));
    }

    pub proof fn lemma_conjugate_mul_reverse_basis_any(i: int, b: Self)
        requires
            0 <= i < 4,
        ensures
            Self::conjugate_mul_reverse_instance_spec(Self::basis_spec(i), b),
    {
        let a = Self::basis_spec(i);

        let b0 = Self::basis_spec(0).scale_spec(b.w);
        let b1 = Self::basis_spec(1).scale_spec(b.x);
        let b2 = Self::basis_spec(2).scale_spec(b.y);
        let b3 = Self::basis_spec(3).scale_spec(b.z);
        let bsum = Self::basis_decompose_spec(b);

        Self::lemma_conjugate_mul_reverse_basis_indices(i, 0);
        Self::lemma_conjugate_mul_reverse_linear_right_scale(a, Self::basis_spec(0), b.w);
        Self::lemma_conjugate_mul_reverse_basis_indices(i, 1);
        Self::lemma_conjugate_mul_reverse_linear_right_scale(a, Self::basis_spec(1), b.x);
        Self::lemma_conjugate_mul_reverse_basis_indices(i, 2);
        Self::lemma_conjugate_mul_reverse_linear_right_scale(a, Self::basis_spec(2), b.y);
        Self::lemma_conjugate_mul_reverse_basis_indices(i, 3);
        Self::lemma_conjugate_mul_reverse_linear_right_scale(a, Self::basis_spec(3), b.z);
        Self::lemma_conjugate_mul_reverse_linear_right_add(a, b0, b1);
        Self::lemma_conjugate_mul_reverse_linear_right_add(a, b0.add_spec(b1), b2);
        Self::lemma_conjugate_mul_reverse_linear_right_add(a, b0.add_spec(b1).add_spec(b2), b3);

        Self::lemma_basis_decompose_eqv(b);
        Self::lemma_eqv_symmetric(b, bsum);
        Self::lemma_conjugate_mul_reverse_eqv_right(a, bsum, b);
        assert(Self::conjugate_mul_reverse_instance_spec(a, b));
    }

    #[verifier::rlimit(1200)]
    pub proof fn lemma_conjugate_mul_reverse(a: Self, b: Self)
        ensures
            Self::conjugate_mul_reverse_instance_spec(a, b),
    {
        let a0 = Self::basis_spec(0).scale_spec(a.w);
        let a1 = Self::basis_spec(1).scale_spec(a.x);
        let a2 = Self::basis_spec(2).scale_spec(a.y);
        let a3 = Self::basis_spec(3).scale_spec(a.z);
        let asum = Self::basis_decompose_spec(a);

        Self::lemma_conjugate_mul_reverse_basis_any(0, b);
        Self::lemma_conjugate_mul_reverse_linear_left_scale(Self::basis_spec(0), b, a.w);
        Self::lemma_conjugate_mul_reverse_basis_any(1, b);
        Self::lemma_conjugate_mul_reverse_linear_left_scale(Self::basis_spec(1), b, a.x);
        Self::lemma_conjugate_mul_reverse_basis_any(2, b);
        Self::lemma_conjugate_mul_reverse_linear_left_scale(Self::basis_spec(2), b, a.y);
        Self::lemma_conjugate_mul_reverse_basis_any(3, b);
        Self::lemma_conjugate_mul_reverse_linear_left_scale(Self::basis_spec(3), b, a.z);

        Self::lemma_conjugate_mul_reverse_linear_left_add(a0, a1, b);
        Self::lemma_conjugate_mul_reverse_linear_left_add(a0.add_spec(a1), a2, b);
        Self::lemma_conjugate_mul_reverse_linear_left_add(a0.add_spec(a1).add_spec(a2), a3, b);

        Self::lemma_basis_decompose_eqv(a);
        Self::lemma_eqv_symmetric(a, asum);
        Self::lemma_conjugate_mul_reverse_eqv_left(asum, a, b);
        assert(Self::conjugate_mul_reverse_instance_spec(a, b));
    }

    pub proof fn lemma_add_eqv_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.add_spec(b1).eqv_spec(a2.add_spec(b2)),
    {
        let lhs = a1.add_spec(b1);
        let rhs = a2.add_spec(b2);
        Scalar::lemma_eqv_add_congruence(a1.w, a2.w, b1.w, b2.w);
        Scalar::lemma_eqv_add_congruence(a1.x, a2.x, b1.x, b2.x);
        Scalar::lemma_eqv_add_congruence(a1.y, a2.y, b1.y, b2.y);
        Scalar::lemma_eqv_add_congruence(a1.z, a2.z, b1.z, b2.z);
        assert(lhs.w.eqv_spec(rhs.w));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));
        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_left_add(a1: Self, a2: Self, b: Self, c: Self)
        requires
            Self::assoc_instance_spec(a1, b, c),
            Self::assoc_instance_spec(a2, b, c),
        ensures
            Self::assoc_instance_spec(a1.add_spec(a2), b, c),
    {
        let lhs = a1.add_spec(a2).mul_spec(b).mul_spec(c);
        let rhs = a1.add_spec(a2).mul_spec(b.mul_spec(c));
        let mid_ab = a1.mul_spec(b).add_spec(a2.mul_spec(b));
        let mid_l = mid_ab.mul_spec(c);
        let sum_l = a1.mul_spec(b).mul_spec(c).add_spec(a2.mul_spec(b).mul_spec(c));
        let sum_r = a1.mul_spec(b.mul_spec(c)).add_spec(a2.mul_spec(b.mul_spec(c)));
        let mid_r = a1.mul_spec(b.mul_spec(c)).add_spec(a2.mul_spec(b.mul_spec(c)));

        Self::lemma_mul_distributes_over_add_left(a1, a2, b);
        Self::lemma_mul_distributes_over_add_left(a1.mul_spec(b), a2.mul_spec(b), c);
        Self::lemma_mul_distributes_over_add_left(a1, a2, b.mul_spec(c));
        Self::lemma_mul_eqv_congruence_left(a1.add_spec(a2).mul_spec(b), mid_ab, c);

        assert(a1.add_spec(a2).mul_spec(b).eqv_spec(mid_ab));
        assert(lhs.eqv_spec(mid_l));
        assert(mid_ab.mul_spec(c).eqv_spec(sum_l));
        assert(a1.mul_spec(b).mul_spec(c).eqv_spec(a1.mul_spec(b.mul_spec(c))));
        assert(a2.mul_spec(b).mul_spec(c).eqv_spec(a2.mul_spec(b.mul_spec(c))));
        Self::lemma_add_eqv_congruence(
            a1.mul_spec(b).mul_spec(c),
            a1.mul_spec(b.mul_spec(c)),
            a2.mul_spec(b).mul_spec(c),
            a2.mul_spec(b.mul_spec(c)),
        );
        assert(sum_l.eqv_spec(sum_r));
        assert(mid_r == sum_r);
        assert(rhs.eqv_spec(mid_r));
        Self::lemma_eqv_symmetric(rhs, mid_r);
        Self::lemma_eqv_transitive(lhs, mid_l, sum_l);
        Self::lemma_eqv_transitive(lhs, sum_l, sum_r);
        Self::lemma_eqv_transitive(lhs, sum_r, mid_r);
        Self::lemma_eqv_transitive(lhs, mid_r, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_left_scale(a: Self, b: Self, c: Self, k: Scalar)
        requires
            Self::assoc_instance_spec(a, b, c),
        ensures
            Self::assoc_instance_spec(a.scale_spec(k), b, c),
    {
        let lhs = a.scale_spec(k).mul_spec(b).mul_spec(c);
        let rhs = a.scale_spec(k).mul_spec(b.mul_spec(c));

        let ab = a.mul_spec(b);
        let abc = ab.mul_spec(c);
        let abc_r = a.mul_spec(b.mul_spec(c));

        let lhs_mid = ab.scale_spec(k).mul_spec(c);
        let lhs_scaled = abc.scale_spec(k);
        let rhs_scaled = abc_r.scale_spec(k);
        let rhs_mid = a.mul_spec(b.mul_spec(c)).scale_spec(k);

        Self::lemma_mul_scale_left(a, b, k);
        Self::lemma_mul_eqv_congruence_left(a.scale_spec(k).mul_spec(b), ab.scale_spec(k), c);
        Self::lemma_mul_scale_left(ab, c, k);
        Self::lemma_scale_eqv_congruence(abc, abc_r, k);
        Self::lemma_mul_scale_left(a, b.mul_spec(c), k);

        assert(a.scale_spec(k).mul_spec(b).eqv_spec(ab.scale_spec(k)));
        assert(lhs.eqv_spec(lhs_mid));
        assert(lhs_mid.eqv_spec(lhs_scaled));
        assert(abc.eqv_spec(abc_r));
        assert(lhs_scaled.eqv_spec(rhs_scaled));
        assert(rhs_mid == rhs_scaled);
        assert(rhs.eqv_spec(rhs_mid));
        Self::lemma_eqv_symmetric(rhs, rhs_mid);
        Self::lemma_eqv_transitive(lhs, lhs_mid, lhs_scaled);
        Self::lemma_eqv_transitive(lhs, lhs_scaled, rhs_scaled);
        Self::lemma_eqv_transitive(lhs, rhs_scaled, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_middle_add(a: Self, b1: Self, b2: Self, c: Self)
        requires
            Self::assoc_instance_spec(a, b1, c),
            Self::assoc_instance_spec(a, b2, c),
        ensures
            Self::assoc_instance_spec(a, b1.add_spec(b2), c),
    {
        let lhs = a.mul_spec(b1.add_spec(b2)).mul_spec(c);
        let rhs = a.mul_spec(b1.add_spec(b2).mul_spec(c));

        let mid_ab = a.mul_spec(b1).add_spec(a.mul_spec(b2));
        let mid_l = mid_ab.mul_spec(c);
        let sum_l = a.mul_spec(b1).mul_spec(c).add_spec(a.mul_spec(b2).mul_spec(c));
        let sum_r = a.mul_spec(b1.mul_spec(c)).add_spec(a.mul_spec(b2.mul_spec(c)));

        let bc_sum = b1.mul_spec(c).add_spec(b2.mul_spec(c));
        let rhs_mid = a.mul_spec(bc_sum);

        Self::lemma_mul_distributes_over_add_right(a, b1, b2);
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(b1.add_spec(b2)), mid_ab, c);
        Self::lemma_mul_distributes_over_add_left(a.mul_spec(b1), a.mul_spec(b2), c);

        assert(a.mul_spec(b1.add_spec(b2)).eqv_spec(mid_ab));
        assert(lhs.eqv_spec(mid_l));
        assert(mid_l.eqv_spec(sum_l));

        assert(a.mul_spec(b1).mul_spec(c).eqv_spec(a.mul_spec(b1.mul_spec(c))));
        assert(a.mul_spec(b2).mul_spec(c).eqv_spec(a.mul_spec(b2.mul_spec(c))));
        Self::lemma_add_eqv_congruence(
            a.mul_spec(b1).mul_spec(c),
            a.mul_spec(b1.mul_spec(c)),
            a.mul_spec(b2).mul_spec(c),
            a.mul_spec(b2.mul_spec(c)),
        );
        assert(sum_l.eqv_spec(sum_r));

        Self::lemma_mul_distributes_over_add_left(b1, b2, c);
        assert(b1.add_spec(b2).mul_spec(c).eqv_spec(bc_sum));
        Self::lemma_mul_eqv_congruence_right(a, b1.add_spec(b2).mul_spec(c), bc_sum);
        assert(rhs.eqv_spec(rhs_mid));

        Self::lemma_mul_distributes_over_add_right(a, b1.mul_spec(c), b2.mul_spec(c));
        assert(rhs_mid.eqv_spec(sum_r));

        Self::lemma_eqv_transitive(lhs, mid_l, sum_l);
        Self::lemma_eqv_transitive(lhs, sum_l, sum_r);
        Self::lemma_eqv_symmetric(rhs_mid, sum_r);
        Self::lemma_eqv_symmetric(rhs, rhs_mid);
        Self::lemma_eqv_transitive(lhs, sum_r, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_right_add(a: Self, b: Self, c1: Self, c2: Self)
        requires
            Self::assoc_instance_spec(a, b, c1),
            Self::assoc_instance_spec(a, b, c2),
        ensures
            Self::assoc_instance_spec(a, b, c1.add_spec(c2)),
    {
        let lhs = a.mul_spec(b).mul_spec(c1.add_spec(c2));
        let rhs = a.mul_spec(b.mul_spec(c1.add_spec(c2)));

        let lhs_mid = a.mul_spec(b).mul_spec(c1).add_spec(a.mul_spec(b).mul_spec(c2));
        let sum_r = a.mul_spec(b.mul_spec(c1)).add_spec(a.mul_spec(b.mul_spec(c2)));

        let bc_sum = b.mul_spec(c1).add_spec(b.mul_spec(c2));
        let rhs_mid = a.mul_spec(bc_sum);

        Self::lemma_mul_distributes_over_add_right(a.mul_spec(b), c1, c2);
        assert(lhs.eqv_spec(lhs_mid));

        assert(a.mul_spec(b).mul_spec(c1).eqv_spec(a.mul_spec(b.mul_spec(c1))));
        assert(a.mul_spec(b).mul_spec(c2).eqv_spec(a.mul_spec(b.mul_spec(c2))));
        Self::lemma_add_eqv_congruence(
            a.mul_spec(b).mul_spec(c1),
            a.mul_spec(b.mul_spec(c1)),
            a.mul_spec(b).mul_spec(c2),
            a.mul_spec(b.mul_spec(c2)),
        );
        assert(lhs_mid.eqv_spec(sum_r));

        Self::lemma_mul_distributes_over_add_right(b, c1, c2);
        assert(b.mul_spec(c1.add_spec(c2)).eqv_spec(bc_sum));
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(c1.add_spec(c2)), bc_sum);
        assert(rhs.eqv_spec(rhs_mid));

        Self::lemma_mul_distributes_over_add_right(a, b.mul_spec(c1), b.mul_spec(c2));
        assert(rhs_mid.eqv_spec(sum_r));

        Self::lemma_eqv_transitive(lhs, lhs_mid, sum_r);
        Self::lemma_eqv_symmetric(rhs_mid, sum_r);
        Self::lemma_eqv_symmetric(rhs, rhs_mid);
        Self::lemma_eqv_transitive(lhs, sum_r, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_middle_scale(a: Self, b: Self, c: Self, k: Scalar)
        requires
            Self::assoc_instance_spec(a, b, c),
        ensures
            Self::assoc_instance_spec(a, b.scale_spec(k), c),
    {
        let lhs = a.mul_spec(b.scale_spec(k)).mul_spec(c);
        let rhs = a.mul_spec(b.scale_spec(k).mul_spec(c));

        let ab = a.mul_spec(b);
        let abc = ab.mul_spec(c);
        let abc_r = a.mul_spec(b.mul_spec(c));

        let lhs_mid = ab.scale_spec(k).mul_spec(c);
        let lhs_scaled = abc.scale_spec(k);

        let bc_scaled = b.mul_spec(c).scale_spec(k);
        let rhs_mid = a.mul_spec(bc_scaled);
        let rhs_scaled = abc_r.scale_spec(k);

        Self::lemma_mul_scale_right(a, b, k);
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(b.scale_spec(k)), ab.scale_spec(k), c);
        Self::lemma_mul_scale_left(ab, c, k);
        Self::lemma_scale_eqv_congruence(abc, abc_r, k);
        Self::lemma_mul_scale_left(b, c, k);
        Self::lemma_mul_eqv_congruence_right(a, b.scale_spec(k).mul_spec(c), bc_scaled);
        Self::lemma_mul_scale_right(a, b.mul_spec(c), k);

        assert(a.mul_spec(b.scale_spec(k)).eqv_spec(ab.scale_spec(k)));
        assert(lhs.eqv_spec(lhs_mid));
        assert(lhs_mid.eqv_spec(lhs_scaled));
        assert(abc.eqv_spec(abc_r));
        assert(lhs_scaled.eqv_spec(rhs_scaled));

        assert(b.scale_spec(k).mul_spec(c).eqv_spec(bc_scaled));
        assert(rhs.eqv_spec(rhs_mid));
        assert(rhs_mid.eqv_spec(rhs_scaled));

        Self::lemma_eqv_transitive(lhs, lhs_mid, lhs_scaled);
        Self::lemma_eqv_transitive(lhs, lhs_scaled, rhs_scaled);
        Self::lemma_eqv_symmetric(rhs_mid, rhs_scaled);
        Self::lemma_eqv_symmetric(rhs, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_scaled, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_linear_right_scale(a: Self, b: Self, c: Self, k: Scalar)
        requires
            Self::assoc_instance_spec(a, b, c),
        ensures
            Self::assoc_instance_spec(a, b, c.scale_spec(k)),
    {
        let lhs = a.mul_spec(b).mul_spec(c.scale_spec(k));
        let rhs = a.mul_spec(b.mul_spec(c.scale_spec(k)));

        let abc = a.mul_spec(b).mul_spec(c);
        let abc_r = a.mul_spec(b.mul_spec(c));
        let target = abc.scale_spec(k);
        let target_r = abc_r.scale_spec(k);

        let bc_scaled = b.mul_spec(c).scale_spec(k);
        let rhs_mid = a.mul_spec(bc_scaled);

        Self::lemma_mul_scale_right(a.mul_spec(b), c, k);
        assert(lhs.eqv_spec(target));
        assert(abc.eqv_spec(abc_r));
        Self::lemma_scale_eqv_congruence(abc, abc_r, k);
        assert(target.eqv_spec(target_r));

        Self::lemma_mul_scale_right(b, c, k);
        assert(b.mul_spec(c.scale_spec(k)).eqv_spec(bc_scaled));
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(c.scale_spec(k)), bc_scaled);
        assert(rhs.eqv_spec(rhs_mid));

        Self::lemma_mul_scale_right(a, b.mul_spec(c), k);
        assert(rhs_mid.eqv_spec(target_r));

        Self::lemma_eqv_transitive(lhs, target, target_r);
        Self::lemma_eqv_symmetric(rhs_mid, target_r);
        Self::lemma_eqv_symmetric(rhs, rhs_mid);
        Self::lemma_eqv_transitive(lhs, target_r, rhs_mid);
        Self::lemma_eqv_transitive(lhs, rhs_mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_assoc_eqv_right(a: Self, b: Self, c1: Self, c2: Self)
        requires
            Self::assoc_instance_spec(a, b, c1),
            c1.eqv_spec(c2),
        ensures
            Self::assoc_instance_spec(a, b, c2),
    {
        let lhs1 = a.mul_spec(b).mul_spec(c1);
        let lhs2 = a.mul_spec(b).mul_spec(c2);
        let rhs1 = a.mul_spec(b.mul_spec(c1));
        let rhs2 = a.mul_spec(b.mul_spec(c2));

        Self::lemma_mul_eqv_congruence_right(a.mul_spec(b), c1, c2);
        assert(lhs1.eqv_spec(lhs2));
        Self::lemma_mul_eqv_congruence_right(b, c1, c2);
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(c1), b.mul_spec(c2));
        assert(rhs1.eqv_spec(rhs2));

        Self::lemma_eqv_symmetric(lhs1, lhs2);
        Self::lemma_eqv_transitive(lhs2, lhs1, rhs1);
        Self::lemma_eqv_transitive(lhs2, rhs1, rhs2);
        assert(lhs2.eqv_spec(rhs2));
    }

    pub proof fn lemma_assoc_eqv_middle(a: Self, b1: Self, b2: Self, c: Self)
        requires
            Self::assoc_instance_spec(a, b1, c),
            b1.eqv_spec(b2),
        ensures
            Self::assoc_instance_spec(a, b2, c),
    {
        let lhs1 = a.mul_spec(b1).mul_spec(c);
        let lhs2 = a.mul_spec(b2).mul_spec(c);
        let rhs1 = a.mul_spec(b1.mul_spec(c));
        let rhs2 = a.mul_spec(b2.mul_spec(c));

        Self::lemma_mul_eqv_congruence_right(a, b1, b2);
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(b1), a.mul_spec(b2), c);
        assert(lhs1.eqv_spec(lhs2));

        Self::lemma_mul_eqv_congruence_left(b1, b2, c);
        Self::lemma_mul_eqv_congruence_right(a, b1.mul_spec(c), b2.mul_spec(c));
        assert(rhs1.eqv_spec(rhs2));

        Self::lemma_eqv_symmetric(lhs1, lhs2);
        Self::lemma_eqv_transitive(lhs2, lhs1, rhs1);
        Self::lemma_eqv_transitive(lhs2, rhs1, rhs2);
        assert(lhs2.eqv_spec(rhs2));
    }

    pub proof fn lemma_assoc_eqv_left(a1: Self, a2: Self, b: Self, c: Self)
        requires
            Self::assoc_instance_spec(a1, b, c),
            a1.eqv_spec(a2),
        ensures
            Self::assoc_instance_spec(a2, b, c),
    {
        let lhs1 = a1.mul_spec(b).mul_spec(c);
        let lhs2 = a2.mul_spec(b).mul_spec(c);
        let rhs1 = a1.mul_spec(b.mul_spec(c));
        let rhs2 = a2.mul_spec(b.mul_spec(c));

        Self::lemma_mul_eqv_congruence_left(a1, a2, b);
        Self::lemma_mul_eqv_congruence_left(a1.mul_spec(b), a2.mul_spec(b), c);
        assert(lhs1.eqv_spec(lhs2));

        Self::lemma_mul_eqv_congruence_left(a1, a2, b.mul_spec(c));
        assert(rhs1.eqv_spec(rhs2));

        Self::lemma_eqv_symmetric(lhs1, lhs2);
        Self::lemma_eqv_transitive(lhs2, lhs1, rhs1);
        Self::lemma_eqv_transitive(lhs2, rhs1, rhs2);
        assert(lhs2.eqv_spec(rhs2));
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

    pub proof fn lemma_mul_row_w_additive(b: Self, c: Self)
        ensures
            Self::mul_row_w_spec(b.add_spec(c))
                == Self::mul_row_w_spec(b).add_spec(Self::mul_row_w_spec(c)),
    {
        let lhs = Self::mul_row_w_spec(b.add_spec(c));
        let rhs = Self::mul_row_w_spec(b).add_spec(Self::mul_row_w_spec(c));
        Scalar::lemma_neg_add(b.x, c.x);
        Scalar::lemma_neg_add(b.y, c.y);
        Scalar::lemma_neg_add(b.z, c.z);
        assert(lhs.x == b.w.add_spec(c.w));
        assert(lhs.y == b.x.add_spec(c.x).neg_spec());
        assert(lhs.z == b.y.add_spec(c.y).neg_spec());
        assert(lhs.w == b.z.add_spec(c.z).neg_spec());
        assert(rhs.x == b.w.add_spec(c.w));
        assert(rhs.y == b.x.neg_spec().add_spec(c.x.neg_spec()));
        assert(rhs.z == b.y.neg_spec().add_spec(c.y.neg_spec()));
        assert(rhs.w == b.z.neg_spec().add_spec(c.z.neg_spec()));
        assert(lhs.y == rhs.y);
        assert(lhs.z == rhs.z);
        assert(lhs.w == rhs.w);
        assert(lhs == rhs);
    }

    pub proof fn lemma_mul_row_x_additive(b: Self, c: Self)
        ensures
            Self::mul_row_x_spec(b.add_spec(c))
                == Self::mul_row_x_spec(b).add_spec(Self::mul_row_x_spec(c)),
    {
        let lhs = Self::mul_row_x_spec(b.add_spec(c));
        let rhs = Self::mul_row_x_spec(b).add_spec(Self::mul_row_x_spec(c));
        Scalar::lemma_neg_add(b.y, c.y);
        assert(lhs.x == b.x.add_spec(c.x));
        assert(lhs.y == b.w.add_spec(c.w));
        assert(lhs.z == b.z.add_spec(c.z));
        assert(lhs.w == b.y.add_spec(c.y).neg_spec());
        assert(rhs.x == b.x.add_spec(c.x));
        assert(rhs.y == b.w.add_spec(c.w));
        assert(rhs.z == b.z.add_spec(c.z));
        assert(rhs.w == b.y.neg_spec().add_spec(c.y.neg_spec()));
        assert(lhs.w == rhs.w);
        assert(lhs == rhs);
    }

    pub proof fn lemma_mul_row_y_additive(b: Self, c: Self)
        ensures
            Self::mul_row_y_spec(b.add_spec(c))
                == Self::mul_row_y_spec(b).add_spec(Self::mul_row_y_spec(c)),
    {
        let lhs = Self::mul_row_y_spec(b.add_spec(c));
        let rhs = Self::mul_row_y_spec(b).add_spec(Self::mul_row_y_spec(c));
        Scalar::lemma_neg_add(b.z, c.z);
        assert(lhs.x == b.y.add_spec(c.y));
        assert(lhs.y == b.z.add_spec(c.z).neg_spec());
        assert(lhs.z == b.w.add_spec(c.w));
        assert(lhs.w == b.x.add_spec(c.x));
        assert(rhs.x == b.y.add_spec(c.y));
        assert(rhs.y == b.z.neg_spec().add_spec(c.z.neg_spec()));
        assert(rhs.z == b.w.add_spec(c.w));
        assert(rhs.w == b.x.add_spec(c.x));
        assert(lhs.y == rhs.y);
        assert(lhs == rhs);
    }

    pub proof fn lemma_mul_row_z_additive(b: Self, c: Self)
        ensures
            Self::mul_row_z_spec(b.add_spec(c))
                == Self::mul_row_z_spec(b).add_spec(Self::mul_row_z_spec(c)),
    {
        let lhs = Self::mul_row_z_spec(b.add_spec(c));
        let rhs = Self::mul_row_z_spec(b).add_spec(Self::mul_row_z_spec(c));
        Scalar::lemma_neg_add(b.x, c.x);
        assert(lhs.x == b.z.add_spec(c.z));
        assert(lhs.y == b.y.add_spec(c.y));
        assert(lhs.z == b.x.add_spec(c.x).neg_spec());
        assert(lhs.w == b.w.add_spec(c.w));
        assert(rhs.x == b.z.add_spec(c.z));
        assert(rhs.y == b.y.add_spec(c.y));
        assert(rhs.z == b.x.neg_spec().add_spec(c.x.neg_spec()));
        assert(rhs.w == b.w.add_spec(c.w));
        assert(lhs.z == rhs.z);
        assert(lhs == rhs);
    }

    pub proof fn lemma_as_vec4_eqv_congruence(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.as_vec4_spec().eqv_spec(b.as_vec4_spec()),
    {
        let av = a.as_vec4_spec();
        let bv = b.as_vec4_spec();
        assert(a.w.eqv_spec(b.w));
        assert(a.x.eqv_spec(b.x));
        assert(a.y.eqv_spec(b.y));
        assert(a.z.eqv_spec(b.z));
        assert(av.x.eqv_spec(bv.x));
        assert(av.y.eqv_spec(bv.y));
        assert(av.z.eqv_spec(bv.z));
        assert(av.w.eqv_spec(bv.w));
        Vec4::lemma_eqv_from_components(av, bv);
        assert(av.eqv_spec(bv));
    }

    pub proof fn lemma_mul_row_w_eqv_congruence(b1: Self, b2: Self)
        requires
            b1.eqv_spec(b2),
        ensures
            Self::mul_row_w_spec(b1).eqv_spec(Self::mul_row_w_spec(b2)),
    {
        let r1 = Self::mul_row_w_spec(b1);
        let r2 = Self::mul_row_w_spec(b2);
        Scalar::lemma_eqv_neg_congruence(b1.x, b2.x);
        Scalar::lemma_eqv_neg_congruence(b1.y, b2.y);
        Scalar::lemma_eqv_neg_congruence(b1.z, b2.z);
        assert(r1.x.eqv_spec(r2.x));
        assert(r1.y.eqv_spec(r2.y));
        assert(r1.z.eqv_spec(r2.z));
        assert(r1.w.eqv_spec(r2.w));
        Vec4::lemma_eqv_from_components(r1, r2);
        assert(r1.eqv_spec(r2));
    }

    pub proof fn lemma_mul_row_x_eqv_congruence(b1: Self, b2: Self)
        requires
            b1.eqv_spec(b2),
        ensures
            Self::mul_row_x_spec(b1).eqv_spec(Self::mul_row_x_spec(b2)),
    {
        let r1 = Self::mul_row_x_spec(b1);
        let r2 = Self::mul_row_x_spec(b2);
        Scalar::lemma_eqv_neg_congruence(b1.y, b2.y);
        assert(r1.x.eqv_spec(r2.x));
        assert(r1.y.eqv_spec(r2.y));
        assert(r1.z.eqv_spec(r2.z));
        assert(r1.w.eqv_spec(r2.w));
        Vec4::lemma_eqv_from_components(r1, r2);
        assert(r1.eqv_spec(r2));
    }

    pub proof fn lemma_mul_row_y_eqv_congruence(b1: Self, b2: Self)
        requires
            b1.eqv_spec(b2),
        ensures
            Self::mul_row_y_spec(b1).eqv_spec(Self::mul_row_y_spec(b2)),
    {
        let r1 = Self::mul_row_y_spec(b1);
        let r2 = Self::mul_row_y_spec(b2);
        Scalar::lemma_eqv_neg_congruence(b1.z, b2.z);
        assert(r1.x.eqv_spec(r2.x));
        assert(r1.y.eqv_spec(r2.y));
        assert(r1.z.eqv_spec(r2.z));
        assert(r1.w.eqv_spec(r2.w));
        Vec4::lemma_eqv_from_components(r1, r2);
        assert(r1.eqv_spec(r2));
    }

    pub proof fn lemma_mul_row_z_eqv_congruence(b1: Self, b2: Self)
        requires
            b1.eqv_spec(b2),
        ensures
            Self::mul_row_z_spec(b1).eqv_spec(Self::mul_row_z_spec(b2)),
    {
        let r1 = Self::mul_row_z_spec(b1);
        let r2 = Self::mul_row_z_spec(b2);
        Scalar::lemma_eqv_neg_congruence(b1.x, b2.x);
        assert(r1.x.eqv_spec(r2.x));
        assert(r1.y.eqv_spec(r2.y));
        assert(r1.z.eqv_spec(r2.z));
        assert(r1.w.eqv_spec(r2.w));
        Vec4::lemma_eqv_from_components(r1, r2);
        assert(r1.eqv_spec(r2));
    }

    pub proof fn lemma_mul_eqv_congruence_left(a1: Self, a2: Self, b: Self)
        requires
            a1.eqv_spec(a2),
        ensures
            a1.mul_spec(b).eqv_spec(a2.mul_spec(b)),
    {
        let p1 = a1.mul_spec(b);
        let p2 = a2.mul_spec(b);
        let av1 = a1.as_vec4_spec();
        let av2 = a2.as_vec4_spec();
        let rw = Self::mul_row_w_spec(b);
        let rx = Self::mul_row_x_spec(b);
        let ry = Self::mul_row_y_spec(b);
        let rz = Self::mul_row_z_spec(b);

        Self::lemma_as_vec4_eqv_congruence(a1, a2);
        Vec4::lemma_eqv_reflexive(rw);
        Vec4::lemma_eqv_reflexive(rx);
        Vec4::lemma_eqv_reflexive(ry);
        Vec4::lemma_eqv_reflexive(rz);

        Self::lemma_mul_w_dot_row(a1, b);
        Self::lemma_mul_w_dot_row(a2, b);
        Vec4::lemma_dot_eqv_congruence(av1, av2, rw, rw);
        assert(p1.w == av1.dot_spec(rw));
        assert(p2.w == av2.dot_spec(rw));
        assert(p1.w.eqv_spec(p2.w));

        Self::lemma_mul_x_dot_row(a1, b);
        Self::lemma_mul_x_dot_row(a2, b);
        Vec4::lemma_dot_eqv_congruence(av1, av2, rx, rx);
        assert(p1.x == av1.dot_spec(rx));
        assert(p2.x == av2.dot_spec(rx));
        assert(p1.x.eqv_spec(p2.x));

        Self::lemma_mul_y_dot_row(a1, b);
        Self::lemma_mul_y_dot_row(a2, b);
        Vec4::lemma_dot_eqv_congruence(av1, av2, ry, ry);
        assert(p1.y == av1.dot_spec(ry));
        assert(p2.y == av2.dot_spec(ry));
        assert(p1.y.eqv_spec(p2.y));

        Self::lemma_mul_z_dot_row(a1, b);
        Self::lemma_mul_z_dot_row(a2, b);
        Vec4::lemma_dot_eqv_congruence(av1, av2, rz, rz);
        assert(p1.z == av1.dot_spec(rz));
        assert(p2.z == av2.dot_spec(rz));
        assert(p1.z.eqv_spec(p2.z));

        Self::lemma_eqv_from_components(p1, p2);
        assert(p1.eqv_spec(p2));
    }

    pub proof fn lemma_mul_eqv_congruence_right(a: Self, b1: Self, b2: Self)
        requires
            b1.eqv_spec(b2),
        ensures
            a.mul_spec(b1).eqv_spec(a.mul_spec(b2)),
    {
        let p1 = a.mul_spec(b1);
        let p2 = a.mul_spec(b2);
        let av = a.as_vec4_spec();
        let rw1 = Self::mul_row_w_spec(b1);
        let rw2 = Self::mul_row_w_spec(b2);
        let rx1 = Self::mul_row_x_spec(b1);
        let rx2 = Self::mul_row_x_spec(b2);
        let ry1 = Self::mul_row_y_spec(b1);
        let ry2 = Self::mul_row_y_spec(b2);
        let rz1 = Self::mul_row_z_spec(b1);
        let rz2 = Self::mul_row_z_spec(b2);

        Self::lemma_mul_row_w_eqv_congruence(b1, b2);
        Self::lemma_mul_row_x_eqv_congruence(b1, b2);
        Self::lemma_mul_row_y_eqv_congruence(b1, b2);
        Self::lemma_mul_row_z_eqv_congruence(b1, b2);
        Vec4::lemma_eqv_reflexive(av);

        Self::lemma_mul_w_dot_row(a, b1);
        Self::lemma_mul_w_dot_row(a, b2);
        Vec4::lemma_dot_eqv_congruence(av, av, rw1, rw2);
        assert(p1.w == av.dot_spec(rw1));
        assert(p2.w == av.dot_spec(rw2));
        assert(p1.w.eqv_spec(p2.w));

        Self::lemma_mul_x_dot_row(a, b1);
        Self::lemma_mul_x_dot_row(a, b2);
        Vec4::lemma_dot_eqv_congruence(av, av, rx1, rx2);
        assert(p1.x == av.dot_spec(rx1));
        assert(p2.x == av.dot_spec(rx2));
        assert(p1.x.eqv_spec(p2.x));

        Self::lemma_mul_y_dot_row(a, b1);
        Self::lemma_mul_y_dot_row(a, b2);
        Vec4::lemma_dot_eqv_congruence(av, av, ry1, ry2);
        assert(p1.y == av.dot_spec(ry1));
        assert(p2.y == av.dot_spec(ry2));
        assert(p1.y.eqv_spec(p2.y));

        Self::lemma_mul_z_dot_row(a, b1);
        Self::lemma_mul_z_dot_row(a, b2);
        Vec4::lemma_dot_eqv_congruence(av, av, rz1, rz2);
        assert(p1.z == av.dot_spec(rz1));
        assert(p2.z == av.dot_spec(rz2));
        assert(p1.z.eqv_spec(p2.z));

        Self::lemma_eqv_from_components(p1, p2);
        assert(p1.eqv_spec(p2));
    }

    pub proof fn lemma_mul_eqv_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.mul_spec(b1).eqv_spec(a2.mul_spec(b2)),
    {
        Self::lemma_mul_eqv_congruence_left(a1, a2, b1);
        Self::lemma_mul_eqv_congruence_right(a2, b1, b2);
        Self::lemma_eqv_transitive(a1.mul_spec(b1), a2.mul_spec(b1), a2.mul_spec(b2));
        assert(a1.mul_spec(b1).eqv_spec(a2.mul_spec(b2)));
    }

    pub proof fn lemma_mul_w_dot_row(a: Self, b: Self)
        ensures
            a.mul_spec(b).w == a.as_vec4_spec().dot_spec(Self::mul_row_w_spec(b)),
    {
        let p = a.mul_spec(b);
        let av = a.as_vec4_spec();
        let row = Self::mul_row_w_spec(b);
        let m0 = a.w.mul_spec(b.w);
        let m1 = a.x.mul_spec(b.x);
        let m2 = a.y.mul_spec(b.y);
        let m3 = a.z.mul_spec(b.z);
        let d1 = a.x.mul_spec(b.x.neg_spec());
        let d2 = a.y.mul_spec(b.y.neg_spec());
        let d3 = a.z.mul_spec(b.z.neg_spec());
        Scalar::lemma_mul_neg_right(a.x, b.x);
        Scalar::lemma_mul_neg_right(a.y, b.y);
        Scalar::lemma_mul_neg_right(a.z, b.z);
        assert(d1 == m1.neg_spec());
        assert(d2 == m2.neg_spec());
        assert(d3 == m3.neg_spec());
        assert(av.dot_spec(row) == m0.add_spec(d1).add_spec(d2).add_spec(d3));
        Scalar::lemma_sub_is_add_neg(m0, m1);
        let w0 = m0.add_spec(m1.neg_spec());
        assert(m0.sub_spec(m1) == w0);
        Scalar::lemma_sub_is_add_neg(w0, m2);
        let w1 = w0.add_spec(m2.neg_spec());
        assert(w0.sub_spec(m2) == w1);
        Scalar::lemma_sub_is_add_neg(w1, m3);
        let w2 = w1.add_spec(m3.neg_spec());
        assert(w1.sub_spec(m3) == w2);
        assert(p.w == w2);
        assert(m0.add_spec(d1).add_spec(d2).add_spec(d3) == w2);
        assert(p.w == av.dot_spec(row));
    }

    pub proof fn lemma_mul_x_dot_row(a: Self, b: Self)
        ensures
            a.mul_spec(b).x == a.as_vec4_spec().dot_spec(Self::mul_row_x_spec(b)),
    {
        let p = a.mul_spec(b);
        let av = a.as_vec4_spec();
        let row = Self::mul_row_x_spec(b);
        let m0 = a.w.mul_spec(b.x);
        let m1 = a.x.mul_spec(b.w);
        let m2 = a.y.mul_spec(b.z);
        let m3 = a.z.mul_spec(b.y);
        let d3 = a.z.mul_spec(b.y.neg_spec());
        Scalar::lemma_mul_neg_right(a.z, b.y);
        assert(d3 == m3.neg_spec());
        let mid = m0.add_spec(m1).add_spec(m2);
        Scalar::lemma_sub_is_add_neg(mid, m3);
        let px = mid.add_spec(m3.neg_spec());
        assert(mid.sub_spec(m3) == px);
        assert(p.x == px);
        assert(av.dot_spec(row) == m0.add_spec(m1).add_spec(m2).add_spec(d3));
        assert(px == m0.add_spec(m1).add_spec(m2).add_spec(d3));
        assert(p.x == av.dot_spec(row));
    }

    pub proof fn lemma_mul_y_dot_row(a: Self, b: Self)
        ensures
            a.mul_spec(b).y == a.as_vec4_spec().dot_spec(Self::mul_row_y_spec(b)),
    {
        let p = a.mul_spec(b);
        let av = a.as_vec4_spec();
        let row = Self::mul_row_y_spec(b);
        let m0 = a.w.mul_spec(b.y);
        let m1 = a.x.mul_spec(b.z);
        let m2 = a.y.mul_spec(b.w);
        let m3 = a.z.mul_spec(b.x);
        let d1 = a.x.mul_spec(b.z.neg_spec());
        Scalar::lemma_mul_neg_right(a.x, b.z);
        assert(d1 == m1.neg_spec());
        Scalar::lemma_sub_is_add_neg(m0, m1);
        let y0 = m0.add_spec(m1.neg_spec());
        assert(m0.sub_spec(m1) == y0);
        let y1 = y0.add_spec(m2).add_spec(m3);
        assert(p.y == y1);
        assert(av.dot_spec(row) == m0.add_spec(d1).add_spec(m2).add_spec(m3));
        assert(y1 == m0.add_spec(d1).add_spec(m2).add_spec(m3));
        assert(p.y == av.dot_spec(row));
    }

    pub proof fn lemma_mul_z_dot_row(a: Self, b: Self)
        ensures
            a.mul_spec(b).z == a.as_vec4_spec().dot_spec(Self::mul_row_z_spec(b)),
    {
        let p = a.mul_spec(b);
        let av = a.as_vec4_spec();
        let row = Self::mul_row_z_spec(b);
        let m0 = a.w.mul_spec(b.z);
        let m1 = a.x.mul_spec(b.y);
        let m2 = a.y.mul_spec(b.x);
        let m3 = a.z.mul_spec(b.w);
        let d2 = a.y.mul_spec(b.x.neg_spec());
        Scalar::lemma_mul_neg_right(a.y, b.x);
        assert(d2 == m2.neg_spec());
        let z0 = m0.add_spec(m1);
        Scalar::lemma_sub_is_add_neg(z0, m2);
        let z1 = z0.add_spec(m2.neg_spec());
        assert(z0.sub_spec(m2) == z1);
        let z2 = z1.add_spec(m3);
        assert(p.z == z2);
        assert(av.dot_spec(row) == m0.add_spec(m1).add_spec(d2).add_spec(m3));
        assert(z2 == m0.add_spec(m1).add_spec(d2).add_spec(m3));
        assert(p.z == av.dot_spec(row));
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

    #[verifier::rlimit(1200)]
    pub proof fn lemma_mul_associative(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b).mul_spec(c).eqv_spec(a.mul_spec(b.mul_spec(c))),
    {
        let a0 = Self::basis_spec(0).scale_spec(a.w);
        let a1 = Self::basis_spec(1).scale_spec(a.x);
        let a2 = Self::basis_spec(2).scale_spec(a.y);
        let a3 = Self::basis_spec(3).scale_spec(a.z);
        let asum = Self::basis_decompose_spec(a);

        Self::lemma_assoc_basis_any(0, b, c);
        Self::lemma_assoc_linear_left_scale(Self::basis_spec(0), b, c, a.w);
        Self::lemma_assoc_basis_any(1, b, c);
        Self::lemma_assoc_linear_left_scale(Self::basis_spec(1), b, c, a.x);
        Self::lemma_assoc_basis_any(2, b, c);
        Self::lemma_assoc_linear_left_scale(Self::basis_spec(2), b, c, a.y);
        Self::lemma_assoc_basis_any(3, b, c);
        Self::lemma_assoc_linear_left_scale(Self::basis_spec(3), b, c, a.z);

        Self::lemma_assoc_linear_left_add(a0, a1, b, c);
        Self::lemma_assoc_linear_left_add(a0.add_spec(a1), a2, b, c);
        Self::lemma_assoc_linear_left_add(a0.add_spec(a1).add_spec(a2), a3, b, c);
        assert(Self::assoc_instance_spec(asum, b, c));

        Self::lemma_basis_decompose_eqv(a);
        Self::lemma_eqv_symmetric(a, asum);
        Self::lemma_assoc_eqv_left(asum, a, b, c);
        assert(Self::assoc_instance_spec(a, b, c));
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

    pub proof fn lemma_mul_distributes_over_add_left(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).mul_spec(c).eqv_spec(a.mul_spec(c).add_spec(b.mul_spec(c))),
    {
        let lhs = a.add_spec(b).mul_spec(c);
        let rhs = a.mul_spec(c).add_spec(b.mul_spec(c));
        let av = a.as_vec4_spec();
        let bv = b.as_vec4_spec();
        let abv = a.add_spec(b).as_vec4_spec();
        let rw = Self::mul_row_w_spec(c);
        let rx = Self::mul_row_x_spec(c);
        let ry = Self::mul_row_y_spec(c);
        let rz = Self::mul_row_z_spec(c);

        Self::lemma_as_vec4_add(a, b);
        assert(abv == av.add_spec(bv));

        Self::lemma_mul_w_dot_row(a.add_spec(b), c);
        Self::lemma_mul_w_dot_row(a, c);
        Self::lemma_mul_w_dot_row(b, c);
        Vec4::lemma_dot_linear_left(av, bv, rw);
        assert(lhs.w == abv.dot_spec(rw));
        assert(abv.dot_spec(rw) == av.add_spec(bv).dot_spec(rw));
        assert(av.add_spec(bv).dot_spec(rw).eqv_spec(av.dot_spec(rw).add_spec(bv.dot_spec(rw))));
        assert(lhs.w.eqv_spec(av.dot_spec(rw).add_spec(bv.dot_spec(rw))));
        assert(a.mul_spec(c).w == av.dot_spec(rw));
        assert(b.mul_spec(c).w == bv.dot_spec(rw));
        assert(rhs.w == a.mul_spec(c).w.add_spec(b.mul_spec(c).w));
        assert(rhs.w == av.dot_spec(rw).add_spec(bv.dot_spec(rw)));
        Scalar::lemma_eqv_reflexive(rhs.w);
        assert(lhs.w.eqv_spec(rhs.w));

        Self::lemma_mul_x_dot_row(a.add_spec(b), c);
        Self::lemma_mul_x_dot_row(a, c);
        Self::lemma_mul_x_dot_row(b, c);
        Vec4::lemma_dot_linear_left(av, bv, rx);
        assert(lhs.x == abv.dot_spec(rx));
        assert(abv.dot_spec(rx) == av.add_spec(bv).dot_spec(rx));
        assert(av.add_spec(bv).dot_spec(rx).eqv_spec(av.dot_spec(rx).add_spec(bv.dot_spec(rx))));
        assert(lhs.x.eqv_spec(av.dot_spec(rx).add_spec(bv.dot_spec(rx))));
        assert(a.mul_spec(c).x == av.dot_spec(rx));
        assert(b.mul_spec(c).x == bv.dot_spec(rx));
        assert(rhs.x == a.mul_spec(c).x.add_spec(b.mul_spec(c).x));
        assert(rhs.x == av.dot_spec(rx).add_spec(bv.dot_spec(rx)));
        Scalar::lemma_eqv_reflexive(rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        Self::lemma_mul_y_dot_row(a.add_spec(b), c);
        Self::lemma_mul_y_dot_row(a, c);
        Self::lemma_mul_y_dot_row(b, c);
        Vec4::lemma_dot_linear_left(av, bv, ry);
        assert(lhs.y == abv.dot_spec(ry));
        assert(abv.dot_spec(ry) == av.add_spec(bv).dot_spec(ry));
        assert(av.add_spec(bv).dot_spec(ry).eqv_spec(av.dot_spec(ry).add_spec(bv.dot_spec(ry))));
        assert(lhs.y.eqv_spec(av.dot_spec(ry).add_spec(bv.dot_spec(ry))));
        assert(a.mul_spec(c).y == av.dot_spec(ry));
        assert(b.mul_spec(c).y == bv.dot_spec(ry));
        assert(rhs.y == a.mul_spec(c).y.add_spec(b.mul_spec(c).y));
        assert(rhs.y == av.dot_spec(ry).add_spec(bv.dot_spec(ry)));
        Scalar::lemma_eqv_reflexive(rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        Self::lemma_mul_z_dot_row(a.add_spec(b), c);
        Self::lemma_mul_z_dot_row(a, c);
        Self::lemma_mul_z_dot_row(b, c);
        Vec4::lemma_dot_linear_left(av, bv, rz);
        assert(lhs.z == abv.dot_spec(rz));
        assert(abv.dot_spec(rz) == av.add_spec(bv).dot_spec(rz));
        assert(av.add_spec(bv).dot_spec(rz).eqv_spec(av.dot_spec(rz).add_spec(bv.dot_spec(rz))));
        assert(lhs.z.eqv_spec(av.dot_spec(rz).add_spec(bv.dot_spec(rz))));
        assert(a.mul_spec(c).z == av.dot_spec(rz));
        assert(b.mul_spec(c).z == bv.dot_spec(rz));
        assert(rhs.z == a.mul_spec(c).z.add_spec(b.mul_spec(c).z));
        assert(rhs.z == av.dot_spec(rz).add_spec(bv.dot_spec(rz)));
        Scalar::lemma_eqv_reflexive(rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_distributes_over_add_right(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))),
    {
        let lhs = a.mul_spec(b.add_spec(c));
        let rhs = a.mul_spec(b).add_spec(a.mul_spec(c));
        let av = a.as_vec4_spec();
        let bv = b.as_vec4_spec();
        let cv = c.as_vec4_spec();
        let bcv = b.add_spec(c).as_vec4_spec();
        let rw_bc = Self::mul_row_w_spec(b.add_spec(c));
        let rx_bc = Self::mul_row_x_spec(b.add_spec(c));
        let ry_bc = Self::mul_row_y_spec(b.add_spec(c));
        let rz_bc = Self::mul_row_z_spec(b.add_spec(c));
        let rw_b = Self::mul_row_w_spec(b);
        let rx_b = Self::mul_row_x_spec(b);
        let ry_b = Self::mul_row_y_spec(b);
        let rz_b = Self::mul_row_z_spec(b);
        let rw_c = Self::mul_row_w_spec(c);
        let rx_c = Self::mul_row_x_spec(c);
        let ry_c = Self::mul_row_y_spec(c);
        let rz_c = Self::mul_row_z_spec(c);

        Self::lemma_as_vec4_add(b, c);
        assert(bcv == bv.add_spec(cv));

        Self::lemma_mul_row_w_additive(b, c);
        Self::lemma_mul_row_x_additive(b, c);
        Self::lemma_mul_row_y_additive(b, c);
        Self::lemma_mul_row_z_additive(b, c);
        assert(rw_bc == rw_b.add_spec(rw_c));
        assert(rx_bc == rx_b.add_spec(rx_c));
        assert(ry_bc == ry_b.add_spec(ry_c));
        assert(rz_bc == rz_b.add_spec(rz_c));

        Self::lemma_mul_w_dot_row(a, b.add_spec(c));
        Self::lemma_mul_w_dot_row(a, b);
        Self::lemma_mul_w_dot_row(a, c);
        Vec4::lemma_dot_linear_right(av, rw_b, rw_c);
        assert(lhs.w == av.dot_spec(rw_bc));
        assert(av.dot_spec(rw_bc) == av.dot_spec(rw_b.add_spec(rw_c)));
        assert(av.dot_spec(rw_b.add_spec(rw_c)).eqv_spec(av.dot_spec(rw_b).add_spec(av.dot_spec(rw_c))));
        assert(lhs.w.eqv_spec(av.dot_spec(rw_b).add_spec(av.dot_spec(rw_c))));
        assert(a.mul_spec(b).w == av.dot_spec(rw_b));
        assert(a.mul_spec(c).w == av.dot_spec(rw_c));
        assert(rhs.w == a.mul_spec(b).w.add_spec(a.mul_spec(c).w));
        assert(rhs.w == av.dot_spec(rw_b).add_spec(av.dot_spec(rw_c)));
        Scalar::lemma_eqv_reflexive(rhs.w);
        assert(lhs.w.eqv_spec(rhs.w));

        Self::lemma_mul_x_dot_row(a, b.add_spec(c));
        Self::lemma_mul_x_dot_row(a, b);
        Self::lemma_mul_x_dot_row(a, c);
        Vec4::lemma_dot_linear_right(av, rx_b, rx_c);
        assert(lhs.x == av.dot_spec(rx_bc));
        assert(av.dot_spec(rx_bc) == av.dot_spec(rx_b.add_spec(rx_c)));
        assert(av.dot_spec(rx_b.add_spec(rx_c)).eqv_spec(av.dot_spec(rx_b).add_spec(av.dot_spec(rx_c))));
        assert(lhs.x.eqv_spec(av.dot_spec(rx_b).add_spec(av.dot_spec(rx_c))));
        assert(a.mul_spec(b).x == av.dot_spec(rx_b));
        assert(a.mul_spec(c).x == av.dot_spec(rx_c));
        assert(rhs.x == a.mul_spec(b).x.add_spec(a.mul_spec(c).x));
        assert(rhs.x == av.dot_spec(rx_b).add_spec(av.dot_spec(rx_c)));
        Scalar::lemma_eqv_reflexive(rhs.x);
        assert(lhs.x.eqv_spec(rhs.x));

        Self::lemma_mul_y_dot_row(a, b.add_spec(c));
        Self::lemma_mul_y_dot_row(a, b);
        Self::lemma_mul_y_dot_row(a, c);
        Vec4::lemma_dot_linear_right(av, ry_b, ry_c);
        assert(lhs.y == av.dot_spec(ry_bc));
        assert(av.dot_spec(ry_bc) == av.dot_spec(ry_b.add_spec(ry_c)));
        assert(av.dot_spec(ry_b.add_spec(ry_c)).eqv_spec(av.dot_spec(ry_b).add_spec(av.dot_spec(ry_c))));
        assert(lhs.y.eqv_spec(av.dot_spec(ry_b).add_spec(av.dot_spec(ry_c))));
        assert(a.mul_spec(b).y == av.dot_spec(ry_b));
        assert(a.mul_spec(c).y == av.dot_spec(ry_c));
        assert(rhs.y == a.mul_spec(b).y.add_spec(a.mul_spec(c).y));
        assert(rhs.y == av.dot_spec(ry_b).add_spec(av.dot_spec(ry_c)));
        Scalar::lemma_eqv_reflexive(rhs.y);
        assert(lhs.y.eqv_spec(rhs.y));

        Self::lemma_mul_z_dot_row(a, b.add_spec(c));
        Self::lemma_mul_z_dot_row(a, b);
        Self::lemma_mul_z_dot_row(a, c);
        Vec4::lemma_dot_linear_right(av, rz_b, rz_c);
        assert(lhs.z == av.dot_spec(rz_bc));
        assert(av.dot_spec(rz_bc) == av.dot_spec(rz_b.add_spec(rz_c)));
        assert(av.dot_spec(rz_b.add_spec(rz_c)).eqv_spec(av.dot_spec(rz_b).add_spec(av.dot_spec(rz_c))));
        assert(lhs.z.eqv_spec(av.dot_spec(rz_b).add_spec(av.dot_spec(rz_c))));
        assert(a.mul_spec(b).z == av.dot_spec(rz_b));
        assert(a.mul_spec(c).z == av.dot_spec(rz_c));
        assert(rhs.z == a.mul_spec(b).z.add_spec(a.mul_spec(c).z));
        assert(rhs.z == av.dot_spec(rz_b).add_spec(av.dot_spec(rz_c)));
        Scalar::lemma_eqv_reflexive(rhs.z);
        assert(lhs.z.eqv_spec(rhs.z));

        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
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

    pub proof fn lemma_real_from_one_scale(s: Scalar)
        ensures
            Self::one_spec().scale_spec(s).eqv_spec(Self::real_spec(s)),
    {
        let one = Self::one_spec();
        let lhs = one.scale_spec(s);
        let rhs = Self::real_spec(s);
        let z = Scalar::from_int_spec(0);

        Scalar::lemma_mul_one_identity(s);
        Scalar::lemma_mul_zero(s);

        assert(one.w == Scalar::from_int_spec(1));
        assert(one.x == z);
        assert(one.y == z);
        assert(one.z == z);

        assert(lhs.w == one.w.mul_spec(s));
        assert(lhs.w == Scalar::from_int_spec(1).mul_spec(s));
        assert(lhs.w == s);
        assert(rhs.w == s);
        Scalar::lemma_eqv_reflexive(s);
        assert(lhs.w.eqv_spec(rhs.w));

        assert(lhs.x == one.x.mul_spec(s));
        assert(lhs.y == one.y.mul_spec(s));
        assert(lhs.z == one.z.mul_spec(s));
        assert(lhs.x == z.mul_spec(s));
        assert(lhs.y == z.mul_spec(s));
        assert(lhs.z == z.mul_spec(s));
        assert(rhs.x == z);
        assert(rhs.y == z);
        assert(rhs.z == z);
        assert(lhs.x.eqv_spec(z));
        assert(lhs.y.eqv_spec(z));
        assert(lhs.z.eqv_spec(z));
        assert(lhs.x.eqv_spec(rhs.x));
        assert(lhs.y.eqv_spec(rhs.y));
        assert(lhs.z.eqv_spec(rhs.z));

        Self::lemma_eqv_from_components(lhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_real_scale(s: Scalar, k: Scalar)
        ensures
            Self::real_spec(s).scale_spec(k).eqv_spec(Self::real_spec(s.mul_spec(k))),
    {
        let lhs = Self::real_spec(s).scale_spec(k);
        let one_s = Self::one_spec().scale_spec(s);
        let one_sk = Self::one_spec().scale_spec(s.mul_spec(k));
        let rhs = Self::real_spec(s.mul_spec(k));

        Self::lemma_real_from_one_scale(s);
        Self::lemma_eqv_symmetric(one_s, Self::real_spec(s));
        Self::lemma_scale_eqv_congruence(Self::real_spec(s), one_s, k);
        assert(lhs.eqv_spec(one_s.scale_spec(k)));

        Self::lemma_scale_associative(Self::one_spec(), s, k);
        assert(one_s.scale_spec(k).eqv_spec(one_sk));

        Self::lemma_real_from_one_scale(s.mul_spec(k));
        assert(one_sk.eqv_spec(rhs));

        Self::lemma_eqv_transitive(lhs, one_s.scale_spec(k), one_sk);
        Self::lemma_eqv_transitive(lhs, one_sk, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_real_right(q: Self, s: Scalar)
        ensures
            q.mul_spec(Self::real_spec(s)).eqv_spec(q.scale_spec(s)),
    {
        let r = Self::real_spec(s);
        let one_scaled = Self::one_spec().scale_spec(s);
        let lhs = q.mul_spec(r);
        let mid = q.mul_spec(one_scaled);
        let mid_scaled = q.mul_spec(Self::one_spec()).scale_spec(s);
        let rhs = q.scale_spec(s);

        Self::lemma_real_from_one_scale(s);
        Self::lemma_eqv_symmetric(one_scaled, r);
        Self::lemma_mul_eqv_congruence_right(q, r, one_scaled);
        assert(lhs.eqv_spec(mid));

        Self::lemma_mul_scale_right(q, Self::one_spec(), s);
        assert(mid.eqv_spec(mid_scaled));

        Self::lemma_mul_one_identity(q);
        Self::lemma_scale_eqv_congruence(q.mul_spec(Self::one_spec()), q, s);
        assert(mid_scaled.eqv_spec(rhs));

        Self::lemma_eqv_transitive(lhs, mid, mid_scaled);
        Self::lemma_eqv_transitive(lhs, mid_scaled, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_real_left(s: Scalar, q: Self)
        ensures
            Self::real_spec(s).mul_spec(q).eqv_spec(q.scale_spec(s)),
    {
        let r = Self::real_spec(s);
        let one_scaled = Self::one_spec().scale_spec(s);
        let lhs = r.mul_spec(q);
        let mid = one_scaled.mul_spec(q);
        let mid_scaled = Self::one_spec().mul_spec(q).scale_spec(s);
        let rhs = q.scale_spec(s);

        Self::lemma_real_from_one_scale(s);
        Self::lemma_eqv_symmetric(one_scaled, r);
        Self::lemma_mul_eqv_congruence_left(r, one_scaled, q);
        assert(lhs.eqv_spec(mid));

        Self::lemma_mul_scale_left(Self::one_spec(), q, s);
        assert(mid.eqv_spec(mid_scaled));

        Self::lemma_mul_one_identity(q);
        Self::lemma_scale_eqv_congruence(Self::one_spec().mul_spec(q), q, s);
        assert(mid_scaled.eqv_spec(rhs));

        Self::lemma_eqv_transitive(lhs, mid, mid_scaled);
        Self::lemma_eqv_transitive(lhs, mid_scaled, rhs);
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

    pub proof fn lemma_norm2_scale(q: Self, k: Scalar)
        ensures
            q.scale_spec(k).norm2_spec().eqv_spec(k.mul_spec(k).mul_spec(q.norm2_spec())),
    {
        let v = q.as_vec4_spec();
        let lhs = q.scale_spec(k).norm2_spec();
        let lhs_v = v.scale_spec(k).norm2_spec();
        let n_v = v.norm2_spec();
        let n_q = q.norm2_spec();
        let rhs_v = k.mul_spec(k).mul_spec(n_v);
        let rhs_q = k.mul_spec(k).mul_spec(n_q);

        Self::lemma_as_vec4_scale(q, k);
        assert(q.scale_spec(k).as_vec4_spec() == v.scale_spec(k));
        assert(lhs == q.scale_spec(k).as_vec4_spec().norm2_spec());
        assert(lhs == lhs_v);
        assert(n_v == n_q);

        Vec4::lemma_norm2_scale(v, k);
        assert(lhs_v.eqv_spec(rhs_v));
        assert(lhs.eqv_spec(rhs_v));

        Scalar::lemma_eqv_mul_congruence_right(k.mul_spec(k), n_v, n_q);
        assert(rhs_v.eqv_spec(rhs_q));
        Scalar::lemma_eqv_transitive(lhs, rhs_v, rhs_q);
        assert(lhs.eqv_spec(rhs_q));
    }

    #[verifier::rlimit(1200)]
    pub proof fn lemma_norm2_mul(a: Self, b: Self)
        ensures
            a.mul_spec(b).norm2_spec().eqv_spec(a.norm2_spec().mul_spec(b.norm2_spec())),
    {
        let ab = a.mul_spec(b);
        let ac = a.conjugate_spec();
        let bc = b.conjugate_spec();

        let n_ab = ab.norm2_spec();
        let n_a = a.norm2_spec();
        let n_b = b.norm2_spec();
        let n_ab_expected = n_a.mul_spec(n_b);

        let q0 = ab.mul_spec(ab.conjugate_spec());
        let q1 = ab.mul_spec(bc.mul_spec(ac));
        let q2 = a.mul_spec(b.mul_spec(bc.mul_spec(ac)));
        let q3 = a.mul_spec(b.mul_spec(bc).mul_spec(ac));
        let q4 = a.mul_spec(b.mul_spec(bc)).mul_spec(ac);
        let q5 = a.mul_spec(Self::real_spec(n_b)).mul_spec(ac);
        let q6 = a.scale_spec(n_b).mul_spec(ac);
        let q7 = a.mul_spec(ac).scale_spec(n_b);
        let q8 = Self::real_spec(n_a).scale_spec(n_b);
        let q9 = Self::real_spec(n_ab_expected);

        let lhs_real = Self::real_spec(n_ab);
        let rhs_real = Self::real_spec(n_ab_expected);

        Self::lemma_mul_conjugate_right_real_norm2(ab);
        assert(q0.eqv_spec(lhs_real));

        Self::lemma_conjugate_mul_reverse(a, b);
        assert(Self::conjugate_mul_reverse_instance_spec(a, b));
        Self::lemma_mul_eqv_congruence_right(ab, ab.conjugate_spec(), bc.mul_spec(ac));
        assert(q0.eqv_spec(q1));

        Self::lemma_mul_associative(a, b, bc.mul_spec(ac));
        assert(q1.eqv_spec(q2));

        Self::lemma_mul_associative(b, bc, ac);
        assert(b.mul_spec(bc).mul_spec(ac).eqv_spec(b.mul_spec(bc.mul_spec(ac))));
        Self::lemma_eqv_symmetric(b.mul_spec(bc).mul_spec(ac), b.mul_spec(bc.mul_spec(ac)));
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(bc.mul_spec(ac)), b.mul_spec(bc).mul_spec(ac));
        assert(q2.eqv_spec(q3));

        Self::lemma_mul_associative(a, b.mul_spec(bc), ac);
        assert(q4.eqv_spec(q3));
        Self::lemma_eqv_symmetric(q4, q3);
        assert(q3.eqv_spec(q4));

        Self::lemma_mul_conjugate_right_real_norm2(b);
        assert(b.mul_spec(bc).eqv_spec(Self::real_spec(n_b)));
        Self::lemma_mul_eqv_congruence_right(a, b.mul_spec(bc), Self::real_spec(n_b));
        assert(a.mul_spec(b.mul_spec(bc)).eqv_spec(a.mul_spec(Self::real_spec(n_b))));
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(b.mul_spec(bc)), a.mul_spec(Self::real_spec(n_b)), ac);
        assert(q4.eqv_spec(q5));

        Self::lemma_mul_real_right(a, n_b);
        assert(a.mul_spec(Self::real_spec(n_b)).eqv_spec(a.scale_spec(n_b)));
        Self::lemma_mul_eqv_congruence_left(a.mul_spec(Self::real_spec(n_b)), a.scale_spec(n_b), ac);
        assert(q5.eqv_spec(q6));

        Self::lemma_mul_scale_left(a, ac, n_b);
        assert(q6.eqv_spec(q7));

        Self::lemma_mul_conjugate_right_real_norm2(a);
        assert(a.mul_spec(ac).eqv_spec(Self::real_spec(n_a)));
        Self::lemma_scale_eqv_congruence(a.mul_spec(ac), Self::real_spec(n_a), n_b);
        assert(q7.eqv_spec(q8));

        Self::lemma_real_scale(n_a, n_b);
        assert(q8.eqv_spec(q9));

        Self::lemma_eqv_symmetric(q0, lhs_real);
        assert(lhs_real.eqv_spec(q0));
        Self::lemma_eqv_transitive(lhs_real, q0, q1);
        Self::lemma_eqv_transitive(lhs_real, q1, q2);
        Self::lemma_eqv_transitive(lhs_real, q2, q3);
        Self::lemma_eqv_transitive(lhs_real, q3, q4);
        Self::lemma_eqv_transitive(lhs_real, q4, q5);
        Self::lemma_eqv_transitive(lhs_real, q5, q6);
        Self::lemma_eqv_transitive(lhs_real, q6, q7);
        Self::lemma_eqv_transitive(lhs_real, q7, q8);
        Self::lemma_eqv_transitive(lhs_real, q8, q9);
        assert(lhs_real.eqv_spec(rhs_real));

        assert(lhs_real.w == n_ab);
        assert(rhs_real.w == n_ab_expected);
        assert(lhs_real.w.eqv_spec(rhs_real.w));
        assert(n_ab.eqv_spec(n_ab_expected));
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

    pub open spec fn unit_spec(self) -> bool {
        self.norm2_spec().eqv_spec(Scalar::from_int_spec(1))
    }

    pub open spec fn pure_vec3_spec(v: Vec3) -> Self {
        Quaternion { w: Scalar::from_int_spec(0), x: v.x, y: v.y, z: v.z }
    }

    pub open spec fn vector_part_spec(self) -> Vec3 {
        Vec3 { x: self.x, y: self.y, z: self.z }
    }

    pub open spec fn rotate_quat_spec(v: Vec3, q: Self) -> Self {
        q.mul_spec(Self::pure_vec3_spec(v)).mul_spec(q.conjugate_spec())
    }

    pub open spec fn rotate_vec3_spec(v: Vec3, q: Self) -> Vec3 {
        Self::rotate_quat_spec(v, q).vector_part_spec()
    }

    pub proof fn lemma_vector_part_eqv_congruence(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.vector_part_spec().eqv_spec(b.vector_part_spec()),
    {
        let av = a.vector_part_spec();
        let bv = b.vector_part_spec();
        assert(a.x.eqv_spec(b.x));
        assert(a.y.eqv_spec(b.y));
        assert(a.z.eqv_spec(b.z));
        Vec3::lemma_eqv_from_components(av, bv);
        assert(av.eqv_spec(bv));
    }

    pub proof fn lemma_pure_vec3_conjugate_neg(v: Vec3)
        ensures
            Self::pure_vec3_spec(v).conjugate_spec() == Self::pure_vec3_spec(v).neg_spec(),
    {
        let p = Self::pure_vec3_spec(v);
        let c = p.conjugate_spec();
        let n = p.neg_spec();
        let z = Scalar::from_int_spec(0);
        Scalar::lemma_neg_involution(v.x);
        Scalar::lemma_neg_involution(v.y);
        Scalar::lemma_neg_involution(v.z);
        assert(p.w == z);
        assert(c.w == z);
        assert(n.w == z.neg_spec());
        assert(z.neg_spec() == z);
        assert(c.w == n.w);
        assert(c.x == v.x.neg_spec());
        assert(n.x == v.x.neg_spec());
        assert(c.y == v.y.neg_spec());
        assert(n.y == v.y.neg_spec());
        assert(c.z == v.z.neg_spec());
        assert(n.z == v.z.neg_spec());
        assert(c == n);
    }

    pub proof fn lemma_neg_eqv_scale_minus_one(q: Self)
        ensures
            q.neg_spec().eqv_spec(q.scale_spec(Scalar::from_int_spec(-1))),
    {
        let n = q.neg_spec();
        let one = Scalar::from_int_spec(1);
        let m = one.neg_spec();
        let s = q.scale_spec(m);
        assert(m == Scalar::from_int_spec(-1));

        Scalar::lemma_mul_neg_right(q.w, one);
        Scalar::lemma_mul_one_identity(q.w);
        assert(s.w == q.w.mul_spec(one.neg_spec()));
        assert(s.w == q.w.mul_spec(one).neg_spec());
        assert(s.w == q.w.neg_spec());
        assert(n.w.eqv_spec(s.w));

        Scalar::lemma_mul_neg_right(q.x, one);
        Scalar::lemma_mul_one_identity(q.x);
        assert(s.x == q.x.mul_spec(one.neg_spec()));
        assert(s.x == q.x.mul_spec(one).neg_spec());
        assert(s.x == q.x.neg_spec());
        assert(n.x.eqv_spec(s.x));

        Scalar::lemma_mul_neg_right(q.y, one);
        Scalar::lemma_mul_one_identity(q.y);
        assert(s.y == q.y.mul_spec(one.neg_spec()));
        assert(s.y == q.y.mul_spec(one).neg_spec());
        assert(s.y == q.y.neg_spec());
        assert(n.y.eqv_spec(s.y));

        Scalar::lemma_mul_neg_right(q.z, one);
        Scalar::lemma_mul_one_identity(q.z);
        assert(s.z == q.z.mul_spec(one.neg_spec()));
        assert(s.z == q.z.mul_spec(one).neg_spec());
        assert(s.z == q.z.neg_spec());
        assert(n.z.eqv_spec(s.z));

        Self::lemma_eqv_from_components(n, s);
        assert(n.eqv_spec(s));
    }

    pub proof fn lemma_scalar_eqv_neg_implies_zero(a: Scalar)
        requires
            a.eqv_spec(a.neg_spec()),
        ensures
            a.eqv_spec(Scalar::from_int_spec(0)),
    {
        let z = Scalar::from_int_spec(0);
        Scalar::lemma_denom_positive(a);
        assert(a.eqv_spec(a.neg_spec()) == (a.num * a.neg_spec().denom() == a.neg_spec().num * a.denom()));
        assert(a.neg_spec().denom() == a.denom());
        assert(a.neg_spec().num == -a.num);
        assert(a.num * a.denom() == (-a.num) * a.denom());
        assert(a.denom() != 0);
        assert((a.num * a.denom() == (-a.num) * a.denom() && a.denom() != 0) ==> a.num == 0)
            by (nonlinear_arith);
        assert(a.num == 0);
        Scalar::lemma_eqv_zero_iff_num_zero(a);
        assert(a.eqv_spec(z) == (a.num == 0));
        assert(a.eqv_spec(z));
    }

    pub proof fn lemma_rotate_quat_conjugate_neg(v: Vec3, q: Self)
        ensures
            Self::rotate_quat_spec(v, q).conjugate_spec().eqv_spec(Self::rotate_quat_spec(v, q).neg_spec()),
    {
        let p = Self::pure_vec3_spec(v);
        let qc = q.conjugate_spec();
        let r = Self::rotate_quat_spec(v, q);
        let rc = r.conjugate_spec();
        let rneg = r.neg_spec();
        let one = Scalar::from_int_spec(1);
        let m = one.neg_spec();

        let qp = q.mul_spec(p);
        let qpn_assoc = q.mul_spec(p.neg_spec().mul_spec(qc));
        let qpn = q.mul_spec(p.neg_spec()).mul_spec(qc);

        Self::lemma_conjugate_mul_reverse(qp, qc);
        assert(rc.eqv_spec(qc.conjugate_spec().mul_spec(qp.conjugate_spec())));

        Self::lemma_conjugate_involution(q);
        assert(qc.conjugate_spec() == q);

        Self::lemma_conjugate_mul_reverse(q, p);
        assert(qp.conjugate_spec().eqv_spec(p.conjugate_spec().mul_spec(q.conjugate_spec())));
        assert(q.conjugate_spec() == qc);
        Self::lemma_mul_eqv_congruence_right(qc.conjugate_spec(), qp.conjugate_spec(), p.conjugate_spec().mul_spec(qc));
        assert(qc.conjugate_spec().mul_spec(qp.conjugate_spec()).eqv_spec(qc.conjugate_spec().mul_spec(p.conjugate_spec().mul_spec(qc))));

        Self::lemma_pure_vec3_conjugate_neg(v);
        assert(p.conjugate_spec() == p.neg_spec());
        assert(qc.conjugate_spec().mul_spec(p.conjugate_spec().mul_spec(qc)) == qpn_assoc);
        Self::lemma_eqv_transitive(rc, qc.conjugate_spec().mul_spec(qp.conjugate_spec()), qpn_assoc);

        Self::lemma_mul_associative(q, p.neg_spec(), qc);
        assert(qpn.eqv_spec(qpn_assoc));
        Self::lemma_eqv_symmetric(qpn, qpn_assoc);
        assert(qpn_assoc.eqv_spec(qpn));
        Self::lemma_eqv_transitive(rc, qpn_assoc, qpn);

        Self::lemma_neg_eqv_scale_minus_one(p);
        assert(p.neg_spec().eqv_spec(p.scale_spec(m)));
        Self::lemma_mul_eqv_congruence_right(q, p.neg_spec(), p.scale_spec(m));
        assert(q.mul_spec(p.neg_spec()).eqv_spec(q.mul_spec(p.scale_spec(m))));
        Self::lemma_mul_scale_right(q, p, m);
        assert(q.mul_spec(p.scale_spec(m)).eqv_spec(q.mul_spec(p).scale_spec(m)));
        Self::lemma_eqv_transitive(q.mul_spec(p.neg_spec()), q.mul_spec(p.scale_spec(m)), q.mul_spec(p).scale_spec(m));
        Self::lemma_mul_eqv_congruence_left(q.mul_spec(p.neg_spec()), q.mul_spec(p).scale_spec(m), qc);
        assert(qpn.eqv_spec(q.mul_spec(p).scale_spec(m).mul_spec(qc)));

        Self::lemma_mul_scale_left(q.mul_spec(p), qc, m);
        assert(q.mul_spec(p).scale_spec(m).mul_spec(qc).eqv_spec(r.scale_spec(m)));
        Self::lemma_eqv_transitive(qpn, q.mul_spec(p).scale_spec(m).mul_spec(qc), r.scale_spec(m));

        Self::lemma_neg_eqv_scale_minus_one(r);
        assert(rneg.eqv_spec(r.scale_spec(m)));
        Self::lemma_eqv_symmetric(rneg, r.scale_spec(m));
        assert(r.scale_spec(m).eqv_spec(rneg));
        Self::lemma_eqv_transitive(qpn, r.scale_spec(m), rneg);
        Self::lemma_eqv_transitive(rc, qpn, rneg);
        assert(rc.eqv_spec(rneg));
    }

    pub proof fn lemma_rotate_quat_scalar_zero(v: Vec3, q: Self)
        ensures
            Self::rotate_quat_spec(v, q).w.eqv_spec(Scalar::from_int_spec(0)),
    {
        let r = Self::rotate_quat_spec(v, q);
        let rc = r.conjugate_spec();
        let rn = r.neg_spec();
        let z = Scalar::from_int_spec(0);
        Self::lemma_rotate_quat_conjugate_neg(v, q);
        assert(rc.eqv_spec(rn));
        assert(rc.w.eqv_spec(rn.w));
        assert(rc.w == r.w);
        assert(rn.w == r.w.neg_spec());
        assert(r.w.eqv_spec(r.w.neg_spec()));
        Self::lemma_scalar_eqv_neg_implies_zero(r.w);
        assert(r.w.eqv_spec(z));
    }

    pub proof fn lemma_pure_of_vector_part_if_pure(q: Self)
        requires
            q.w.eqv_spec(Scalar::from_int_spec(0)),
        ensures
            Self::pure_vec3_spec(q.vector_part_spec()).eqv_spec(q),
    {
        let z = Scalar::from_int_spec(0);
        let p = Self::pure_vec3_spec(q.vector_part_spec());
        Scalar::lemma_eqv_symmetric(q.w, z);
        assert(q.w.eqv_spec(z) == z.eqv_spec(q.w));
        assert(z.eqv_spec(q.w));
        assert(p.w == z);
        assert(p.x == q.x);
        assert(p.y == q.y);
        assert(p.z == q.z);
        assert(p.w.eqv_spec(q.w));
        Scalar::lemma_eqv_reflexive(q.x);
        Scalar::lemma_eqv_reflexive(q.y);
        Scalar::lemma_eqv_reflexive(q.z);
        assert(p.x.eqv_spec(q.x));
        assert(p.y.eqv_spec(q.y));
        assert(p.z.eqv_spec(q.z));
        Self::lemma_eqv_from_components(p, q);
        assert(p.eqv_spec(q));
    }

    pub proof fn lemma_vector_part_norm2_if_pure(q: Self)
        requires
            q.w.eqv_spec(Scalar::from_int_spec(0)),
        ensures
            q.vector_part_spec().norm2_spec().eqv_spec(q.norm2_spec()),
    {
        let z = Scalar::from_int_spec(0);
        let v = q.vector_part_spec();
        let xx = q.x.mul_spec(q.x);
        let yy = q.y.mul_spec(q.y);
        let zz = q.z.mul_spec(q.z);
        let vv = v.norm2_spec();
        let ww = q.w.mul_spec(q.w);
        let nq = q.norm2_spec();
        let n1 = ww.add_spec(xx).add_spec(yy);
        let n2 = ww.add_spec(xx.add_spec(yy));
        let n3 = n2.add_spec(zz);
        let n4 = ww.add_spec(xx.add_spec(yy).add_spec(zz));

        assert(vv == xx.add_spec(yy).add_spec(zz));
        assert(nq == ww.add_spec(xx).add_spec(yy).add_spec(zz));

        Scalar::lemma_eqv_mul_congruence(q.w, z, q.w, z);
        assert(ww.eqv_spec(z.mul_spec(z)));
        Scalar::lemma_mul_zero(z);
        assert(z.mul_spec(z).eqv_spec(z));
        Scalar::lemma_eqv_transitive(ww, z.mul_spec(z), z);
        assert(ww.eqv_spec(z));

        Scalar::lemma_add_associative(ww, xx, yy);
        assert(n1.eqv_spec(n2));
        Scalar::lemma_eqv_add_congruence(n1, n2, zz, zz);
        assert(nq.eqv_spec(n3));
        Scalar::lemma_add_associative(ww, xx.add_spec(yy), zz);
        assert(n3.eqv_spec(n4));
        Scalar::lemma_eqv_transitive(nq, n3, n4);
        assert(nq.eqv_spec(n4));

        Scalar::lemma_eqv_add_congruence(ww, z, vv, vv);
        assert(n4.eqv_spec(z.add_spec(vv)));
        Scalar::lemma_eqv_transitive(nq, n4, z.add_spec(vv));
        Scalar::lemma_add_zero_identity(vv);
        assert(z.add_spec(vv) == vv);
        assert(nq.eqv_spec(vv));
        Scalar::lemma_eqv_symmetric(nq, vv);
        assert(nq.eqv_spec(vv) == vv.eqv_spec(nq));
        assert(vv.eqv_spec(nq));
    }

    pub proof fn lemma_pure_vec3_norm2(v: Vec3)
        ensures
            Self::pure_vec3_spec(v).norm2_spec().eqv_spec(v.norm2_spec()),
    {
        let p = Self::pure_vec3_spec(v);
        let pv = p.vector_part_spec();
        let z = Scalar::from_int_spec(0);
        assert(p.w == z);
        Scalar::lemma_eqv_reflexive(z);
        assert(p.w.eqv_spec(z));
        Self::lemma_vector_part_norm2_if_pure(p);
        assert(pv.norm2_spec().eqv_spec(p.norm2_spec()));
        assert(pv == v);
        assert(v.norm2_spec().eqv_spec(p.norm2_spec()));
        Scalar::lemma_eqv_symmetric(v.norm2_spec(), p.norm2_spec());
        assert(v.norm2_spec().eqv_spec(p.norm2_spec()) == p.norm2_spec().eqv_spec(v.norm2_spec()));
        assert(p.norm2_spec().eqv_spec(v.norm2_spec()));
    }

    pub proof fn lemma_rotate_vec3_norm_preserves(v: Vec3, q: Self)
        requires
            q.unit_spec(),
        ensures
            Self::rotate_vec3_spec(v, q).norm2_spec().eqv_spec(v.norm2_spec()),
    {
        let one = Scalar::from_int_spec(1);
        let p = Self::pure_vec3_spec(v);
        let qc = q.conjugate_spec();
        let r = Self::rotate_quat_spec(v, q);
        let rv = Self::rotate_vec3_spec(v, q);

        let n_r = r.norm2_spec();
        let n_qp = q.mul_spec(p).norm2_spec();
        let n_q = q.norm2_spec();
        let n_qc = qc.norm2_spec();
        let n_p = p.norm2_spec();
        let n_mid0 = n_q.mul_spec(n_p).mul_spec(n_qc);
        let n_mid1 = n_q.mul_spec(n_p).mul_spec(n_q);
        let n_mid2 = n_q.mul_spec(n_p).mul_spec(one);
        let n_mid3 = n_q.mul_spec(n_p);
        let n_mid4 = one.mul_spec(n_p);

        Self::lemma_rotate_quat_scalar_zero(v, q);
        Self::lemma_vector_part_norm2_if_pure(r);
        assert(rv == r.vector_part_spec());
        assert(rv.norm2_spec().eqv_spec(n_r));

        Self::lemma_norm2_mul(q.mul_spec(p), qc);
        assert(n_r.eqv_spec(n_qp.mul_spec(n_qc)));
        Self::lemma_norm2_mul(q, p);
        assert(n_qp.eqv_spec(n_q.mul_spec(n_p)));
        Scalar::lemma_eqv_mul_congruence_left(n_qp, n_q.mul_spec(n_p), n_qc);
        assert(n_qp.mul_spec(n_qc).eqv_spec(n_mid0));
        Scalar::lemma_eqv_transitive(n_r, n_qp.mul_spec(n_qc), n_mid0);
        assert(n_r.eqv_spec(n_mid0));

        Self::lemma_norm2_conjugate_invariant(q);
        assert(n_qc.eqv_spec(n_q));
        Scalar::lemma_eqv_mul_congruence_right(n_q.mul_spec(n_p), n_qc, n_q);
        assert(n_mid0.eqv_spec(n_mid1));
        Scalar::lemma_eqv_transitive(n_r, n_mid0, n_mid1);
        assert(n_r.eqv_spec(n_mid1));

        assert(q.unit_spec());
        assert(n_q.eqv_spec(one));
        Scalar::lemma_eqv_mul_congruence_right(n_q.mul_spec(n_p), n_q, one);
        assert(n_mid1.eqv_spec(n_mid2));
        Scalar::lemma_mul_one_identity(n_q.mul_spec(n_p));
        assert(n_mid2 == n_mid3);
        Scalar::lemma_eqv_reflexive(n_mid3);
        assert(n_mid2.eqv_spec(n_mid3));
        Scalar::lemma_eqv_transitive(n_r, n_mid1, n_mid2);
        Scalar::lemma_eqv_transitive(n_r, n_mid2, n_mid3);
        assert(n_r.eqv_spec(n_mid3));

        Scalar::lemma_eqv_mul_congruence_left(n_q, one, n_p);
        assert(n_mid3.eqv_spec(n_mid4));
        Scalar::lemma_mul_one_identity(n_p);
        assert(n_mid4 == n_p);
        Scalar::lemma_eqv_reflexive(n_p);
        assert(n_mid4.eqv_spec(n_p));
        Scalar::lemma_eqv_transitive(n_r, n_mid3, n_mid4);
        Scalar::lemma_eqv_transitive(n_r, n_mid4, n_p);
        assert(n_r.eqv_spec(n_p));

        Self::lemma_pure_vec3_norm2(v);
        assert(n_p.eqv_spec(v.norm2_spec()));
        Scalar::lemma_eqv_transitive(rv.norm2_spec(), n_r, n_p);
        Scalar::lemma_eqv_transitive(rv.norm2_spec(), n_p, v.norm2_spec());
        assert(rv.norm2_spec().eqv_spec(v.norm2_spec()));
    }

    pub proof fn lemma_rotate_vec3_composition(v: Vec3, q1: Self, q2: Self)
        requires
            q1.unit_spec(),
            q2.unit_spec(),
        ensures
            Self::rotate_vec3_spec(Self::rotate_vec3_spec(v, q2), q1).eqv_spec(
                Self::rotate_vec3_spec(v, q1.mul_spec(q2)),
            ),
    {
        let p = Self::pure_vec3_spec(v);
        let q1c = q1.conjugate_spec();
        let q2c = q2.conjugate_spec();
        let q12 = q1.mul_spec(q2);
        let q12c = q12.conjugate_spec();

        let v2 = Self::rotate_vec3_spec(v, q2);
        let r2 = Self::rotate_quat_spec(v, q2);
        let p2 = Self::pure_vec3_spec(v2);
        let lhs_q = Self::rotate_quat_spec(v2, q1);
        let rhs_q = Self::rotate_quat_spec(v, q12);
        let lhs_t0 = q1.mul_spec(r2).mul_spec(q1c);
        let lhs_t1 = q1.mul_spec(q2.mul_spec(p).mul_spec(q2c)).mul_spec(q1c);
        let lhs_t2 = q1.mul_spec(q2.mul_spec(p).mul_spec(q2c).mul_spec(q1c));
        let lhs_t3 = q1.mul_spec(q2.mul_spec(p).mul_spec(q2c.mul_spec(q1c)));
        let lhs_t4 = q1.mul_spec(q2.mul_spec(p.mul_spec(q2c.mul_spec(q1c))));
        let lhs_t5 = q1.mul_spec(q2).mul_spec(p.mul_spec(q2c.mul_spec(q1c)));
        let lhs_t6 = q1.mul_spec(q2).mul_spec(p).mul_spec(q2c.mul_spec(q1c));

        Self::lemma_rotate_quat_scalar_zero(v, q2);
        assert(r2.w.eqv_spec(Scalar::from_int_spec(0)));
        Self::lemma_pure_of_vector_part_if_pure(r2);
        assert(v2 == r2.vector_part_spec());
        assert(p2 == Self::pure_vec3_spec(r2.vector_part_spec()));
        assert(p2.eqv_spec(r2));

        Self::lemma_mul_eqv_congruence_right(q1, p2, r2);
        Self::lemma_mul_eqv_congruence_left(q1.mul_spec(p2), q1.mul_spec(r2), q1c);
        assert(lhs_q.eqv_spec(lhs_t0));

        assert(r2 == q2.mul_spec(p).mul_spec(q2c));
        assert(lhs_t0 == lhs_t1);
        Self::lemma_mul_associative(q1, q2.mul_spec(p).mul_spec(q2c), q1c);
        assert(lhs_t1.eqv_spec(lhs_t2));

        Self::lemma_mul_associative(q2.mul_spec(p), q2c, q1c);
        assert(q2.mul_spec(p).mul_spec(q2c).mul_spec(q1c).eqv_spec(q2.mul_spec(p).mul_spec(q2c.mul_spec(q1c))));
        Self::lemma_mul_eqv_congruence_right(
            q1,
            q2.mul_spec(p).mul_spec(q2c).mul_spec(q1c),
            q2.mul_spec(p).mul_spec(q2c.mul_spec(q1c)),
        );
        assert(lhs_t2.eqv_spec(lhs_t3));

        Self::lemma_mul_associative(q2, p, q2c.mul_spec(q1c));
        assert(q2.mul_spec(p).mul_spec(q2c.mul_spec(q1c)).eqv_spec(q2.mul_spec(p.mul_spec(q2c.mul_spec(q1c)))));
        Self::lemma_mul_eqv_congruence_right(q1, q2.mul_spec(p).mul_spec(q2c.mul_spec(q1c)), q2.mul_spec(p.mul_spec(q2c.mul_spec(q1c))));
        assert(lhs_t3.eqv_spec(lhs_t4));

        Self::lemma_mul_associative(q1, q2, p.mul_spec(q2c.mul_spec(q1c)));
        assert(lhs_t5.eqv_spec(lhs_t4));
        Self::lemma_eqv_symmetric(lhs_t5, lhs_t4);
        assert(lhs_t4.eqv_spec(lhs_t5));

        Self::lemma_mul_associative(q12, p, q2c.mul_spec(q1c));
        assert(lhs_t6.eqv_spec(lhs_t5));
        Self::lemma_eqv_symmetric(lhs_t6, lhs_t5);
        assert(lhs_t5.eqv_spec(lhs_t6));

        Self::lemma_eqv_transitive(lhs_q, lhs_t0, lhs_t1);
        Self::lemma_eqv_transitive(lhs_q, lhs_t1, lhs_t2);
        Self::lemma_eqv_transitive(lhs_q, lhs_t2, lhs_t3);
        Self::lemma_eqv_transitive(lhs_q, lhs_t3, lhs_t4);
        Self::lemma_eqv_transitive(lhs_q, lhs_t4, lhs_t5);
        Self::lemma_eqv_transitive(lhs_q, lhs_t5, lhs_t6);
        assert(lhs_q.eqv_spec(lhs_t6));

        Self::lemma_conjugate_mul_reverse(q1, q2);
        assert(q12c.eqv_spec(q2c.mul_spec(q1c)));
        Self::lemma_mul_eqv_congruence_right(q12.mul_spec(p), q12c, q2c.mul_spec(q1c));
        assert(rhs_q.eqv_spec(lhs_t6));

        Self::lemma_eqv_symmetric(rhs_q, lhs_t6);
        assert(lhs_t6.eqv_spec(rhs_q));
        Self::lemma_eqv_transitive(lhs_q, lhs_t6, rhs_q);
        assert(lhs_q.eqv_spec(rhs_q));

        Self::lemma_vector_part_eqv_congruence(lhs_q, rhs_q);
        assert(lhs_q.vector_part_spec().eqv_spec(rhs_q.vector_part_spec()));
        assert(Self::rotate_vec3_spec(v2, q1) == lhs_q.vector_part_spec());
        assert(Self::rotate_vec3_spec(v, q12) == rhs_q.vector_part_spec());
        assert(Self::rotate_vec3_spec(v2, q1).eqv_spec(Self::rotate_vec3_spec(v, q12)));
    }
}

} // verus!
