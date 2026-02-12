use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::mul::{
    lemma_mul_basics,
    lemma_mul_by_zero_is_zero,
    lemma_mul_is_associative,
    lemma_mul_is_commutative,
    lemma_mul_strict_inequality,
};

verus! {

/// Exact rational scalar.
///
/// `den` stores `(effective_denominator - 1)`, so effective denominator is
/// always at least `1`.
pub struct Scalar {
    pub num: int,
    pub den: nat,
}

impl Scalar {
    pub proof fn lemma_nat_mul_cast(a: nat, b: nat)
        ensures
            (a * b) as int == (a as int) * (b as int),
    {
        assert((a * b) as int == (a as int) * (b as int)) by (nonlinear_arith);
    }

    pub open spec fn denom_nat(self) -> nat {
        self.den + 1
    }

    pub open spec fn denom(self) -> int {
        self.denom_nat() as int
    }

    pub open spec fn as_real(self) -> real {
        self.num as real / self.denom_nat() as real
    }

    pub open spec fn from_int_spec(value: int) -> Self {
        Scalar { num: value, den: 0 }
    }

    pub proof fn new(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Scalar { num: value, den: 0 }
    }

    pub proof fn from_int(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Self::new(value)
    }

    pub proof fn from_frac(num: int, den: nat) -> (s: Self)
        requires
            den > 0,
        ensures
            s.num == num,
    {
        let dm1 = (den as int - 1) as nat;
        Scalar { num, den: dm1 }
    }

    pub proof fn zero() -> (s: Self)
        ensures
            s == Self::from_int_spec(0),
    {
        Scalar { num: 0, den: 0 }
    }

    pub proof fn one() -> (s: Self)
        ensures
            s == Self::from_int_spec(1),
    {
        Scalar { num: 1, den: 0 }
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Scalar {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Scalar { num: -self.num, den: self.den }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Scalar { num: -self.num, den: self.den }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        self.add_spec(rhs.neg_spec())
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        let neg_rhs = rhs.neg();
        self.add(neg_rhs)
    }

    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        Scalar {
            num: self.num * rhs.num,
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub proof fn mul(self, rhs: Self) -> (out: Self)
        ensures
            out == self.mul_spec(rhs),
    {
        Scalar {
            num: self.num * rhs.num,
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub open spec fn signum(self) -> int {
        if self.num > 0 {
            1
        } else if self.num < 0 {
            -1
        } else {
            0
        }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() == rhs.num * self.denom()
    }

    pub open spec fn le_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() <= rhs.num * self.denom()
    }

    pub open spec fn lt_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() < rhs.num * self.denom()
    }

    pub proof fn lemma_denom_positive(a: Self)
        ensures
            a.denom_nat() > 0,
            a.denom() > 0,
    {
        assert(a.denom_nat() > 0);
        assert(a.denom() == a.denom_nat() as int);
        assert(a.denom() > 0);
    }

    pub proof fn lemma_eqv_zero_iff_num_zero(a: Self)
        ensures
            a.eqv_spec(Self::from_int_spec(0)) == (a.num == 0),
    {
        let z = Self::from_int_spec(0);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.eqv_spec(z) == (a.num * z.denom() == z.num * a.denom()));
        assert(a.eqv_spec(z) == (a.num * 1 == 0 * a.denom()));
        lemma_mul_by_zero_is_zero(a.denom());
        assert(0 * a.denom() == 0);
        assert(a.eqv_spec(z) == (a.num * 1 == 0));
        assert((a.num * 1 == 0) == (a.num == 0)) by (nonlinear_arith);
    }

    pub proof fn lemma_add_denom_product(a: Self, b: Self)
        ensures
            a.add_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let out = a.add_spec(b);
        let lhs = out.denom_nat();
        let rhs = a.denom_nat() * b.denom_nat();

        assert(lhs == (a.den * b.den + a.den + b.den) + 1);
        assert(rhs == (a.den + 1) * (b.den + 1));
        assert((a.den * b.den + a.den + b.den) + 1 == (a.den + 1) * (b.den + 1))
            by (nonlinear_arith);
    }

    pub proof fn lemma_add_denom_product_int(a: Self, b: Self)
        ensures
            a.add_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.add_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_add_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

    pub proof fn lemma_mul_denom_product(a: Self, b: Self)
        ensures
            a.mul_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let out = a.mul_spec(b);
        let lhs = out.denom_nat();
        let rhs = a.denom_nat() * b.denom_nat();

        assert(lhs == (a.den * b.den + a.den + b.den) + 1);
        assert(rhs == (a.den + 1) * (b.den + 1));
        assert((a.den * b.den + a.den + b.den) + 1 == (a.den + 1) * (b.den + 1))
            by (nonlinear_arith);
    }

    pub proof fn lemma_mul_denom_product_int(a: Self, b: Self)
        ensures
            a.mul_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.mul_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_mul_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

    pub proof fn lemma_sub_denom_product(a: Self, b: Self)
        ensures
            a.sub_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let s = a.sub_spec(b);
        assert(s == a.add_spec(b.neg_spec()));
        Self::lemma_add_denom_product(a, b.neg_spec());
        assert(a.add_spec(b.neg_spec()).denom_nat() == a.denom_nat() * b.neg_spec().denom_nat());
        assert(b.neg_spec().denom_nat() == b.denom_nat());
        assert(s.denom_nat() == a.denom_nat() * b.denom_nat());
    }

    pub proof fn lemma_sub_denom_product_int(a: Self, b: Self)
        ensures
            a.sub_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.sub_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_sub_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

    pub proof fn lemma_mul_commutative(a: Self, b: Self)
        ensures
            a.mul_spec(b) == b.mul_spec(a),
    {
        let lhs = a.mul_spec(b);
        let rhs = b.mul_spec(a);
        assert(lhs.num == a.num * b.num);
        assert(rhs.num == b.num * a.num);
        assert(a.num * b.num == b.num * a.num) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(rhs.den == b.den * a.den + b.den + a.den);
        assert(a.den * b.den + a.den + b.den == b.den * a.den + b.den + a.den) by (nonlinear_arith);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
    }

    pub proof fn lemma_neg_involution(a: Self)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        let n = a.neg_spec().neg_spec();
        assert(n.num == -(-a.num));
        assert(-(-a.num) == a.num);
        assert(n.num == a.num);
        assert(n.den == a.den);
        assert(n == a);
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).eqv_spec(b.add_spec(a)),
    {
        let l = a.add_spec(b);
        let r = b.add_spec(a);
        let da = a.denom();
        let db = b.denom();
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(b, a);
        assert(l.num == a.num * db + b.num * da);
        assert(r.num == b.num * da + a.num * db);
        assert(l.denom() == da * db);
        assert(r.denom() == db * da);
        assert(l.eqv_spec(r) == (l.num * r.denom() == r.num * l.denom()));
        calc! {
            (==)
            l.num * r.denom();
            {
                assert(l.num == a.num * db + b.num * da);
                assert(r.denom() == db * da);
            }
            (a.num * db + b.num * da) * (db * da);
            {
                assert((a.num * db + b.num * da) * (db * da)
                    == (b.num * da + a.num * db) * (da * db)) by (nonlinear_arith);
            }
            (b.num * da + a.num * db) * (da * db);
            {
                assert(r.num == b.num * da + a.num * db);
                assert(l.denom() == da * db);
            }
            r.num * l.denom();
        }
        assert(l.num * r.denom() == r.num * l.denom());
        assert(l.eqv_spec(r));
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).eqv_spec(a.add_spec(b.add_spec(c))),
    {
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        let ab = a.add_spec(b);
        let bc = b.add_spec(c);
        let lhs = ab.add_spec(c);
        let rhs = a.add_spec(bc);

        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(b, c);
        Self::lemma_add_denom_product_int(ab, c);
        Self::lemma_add_denom_product_int(a, bc);

        assert(ab.num == a.num * db + b.num * da);
        assert(bc.num == b.num * dc + c.num * db);
        assert(ab.denom() == da * db);
        assert(bc.denom() == db * dc);

        assert(lhs.num == ab.num * dc + c.num * ab.denom());
        assert(rhs.num == a.num * bc.denom() + bc.num * da);
        assert(lhs.denom() == ab.denom() * dc);
        assert(rhs.denom() == da * bc.denom());
        assert(lhs.denom() == (da * db) * dc);
        assert(rhs.denom() == da * (db * dc));
        assert(lhs.num == (a.num * db + b.num * da) * dc + c.num * (da * db));
        assert(rhs.num == a.num * (db * dc) + (b.num * dc + c.num * db) * da);
        assert((a.num * db + b.num * da) * dc == (a.num * db) * dc + (b.num * da) * dc)
            by (nonlinear_arith);
        lemma_mul_is_associative(a.num, db, dc);
        assert((a.num * db) * dc == a.num * (db * dc));
        lemma_mul_is_associative(b.num, da, dc);
        assert((b.num * da) * dc == b.num * (da * dc));
        lemma_mul_is_commutative(da, db);
        assert(da * db == db * da);
        assert(c.num * (da * db) == c.num * (db * da));
        assert(b.num * (da * dc) == (b.num * dc) * da) by (nonlinear_arith);
        assert(c.num * (db * da) == (c.num * db) * da) by (nonlinear_arith);
        assert(lhs.num == a.num * (db * dc) + (b.num * dc) * da + (c.num * db) * da);
        assert((b.num * dc + c.num * db) * da == (b.num * dc) * da + (c.num * db) * da)
            by (nonlinear_arith);
        assert(rhs.num == a.num * (db * dc) + (b.num * dc) * da + (c.num * db) * da);
        assert(lhs.num == rhs.num);
        lemma_mul_is_associative(da, db, dc);
        assert((da * db) * dc == da * (db * dc));
        assert(lhs.denom() == rhs.denom());

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(lhs.num * rhs.denom() == lhs.num * lhs.denom());
        assert(rhs.num * lhs.denom() == lhs.num * lhs.denom());
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_rearrange_2x2(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.add_spec(b).add_spec(c.add_spec(d)).eqv_spec(a.add_spec(c).add_spec(b.add_spec(d))),
    {
        let e0 = a.add_spec(b).add_spec(c.add_spec(d));
        let e1 = a.add_spec(b.add_spec(c.add_spec(d)));
        let e2 = a.add_spec(c.add_spec(d).add_spec(b));
        let e3 = a.add_spec(c.add_spec(d.add_spec(b)));
        let e4 = a.add_spec(c.add_spec(b.add_spec(d)));
        let e5 = a.add_spec(c.add_spec(b).add_spec(d));
        let e6 = a.add_spec(c.add_spec(b)).add_spec(d);
        let e7 = a.add_spec(c).add_spec(b).add_spec(d);
        let e8 = a.add_spec(c).add_spec(b.add_spec(d));

        Self::lemma_add_associative(a, b, c.add_spec(d));
        assert(e0.eqv_spec(e1));

        Self::lemma_add_commutative(b, c.add_spec(d));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, b.add_spec(c.add_spec(d)), c.add_spec(d).add_spec(b));
        assert(e1.eqv_spec(e2));

        Self::lemma_add_associative(c, d, b);
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(d).add_spec(b), c.add_spec(d.add_spec(b)));
        assert(e2.eqv_spec(e3));

        Self::lemma_add_commutative(d, b);
        Self::lemma_eqv_reflexive(c);
        Self::lemma_eqv_add_congruence(c, c, d.add_spec(b), b.add_spec(d));
        assert(c.add_spec(d.add_spec(b)).eqv_spec(c.add_spec(b.add_spec(d))));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(d.add_spec(b)), c.add_spec(b.add_spec(d)));
        assert(e3.eqv_spec(e4));

        Self::lemma_add_associative(c, b, d);
        Self::lemma_eqv_symmetric(c.add_spec(b).add_spec(d), c.add_spec(b.add_spec(d)));
        assert(c.add_spec(b.add_spec(d)).eqv_spec(c.add_spec(b).add_spec(d)));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(b.add_spec(d)), c.add_spec(b).add_spec(d));
        assert(e4.eqv_spec(e5));

        Self::lemma_add_associative(a, c.add_spec(b), d);
        Self::lemma_eqv_symmetric(a.add_spec(c.add_spec(b)).add_spec(d), a.add_spec(c.add_spec(b).add_spec(d)));
        assert(a.add_spec(c.add_spec(b).add_spec(d)).eqv_spec(a.add_spec(c.add_spec(b)).add_spec(d)));
        assert(e5.eqv_spec(e6));

        Self::lemma_add_associative(a, c, b);
        Self::lemma_eqv_symmetric(a.add_spec(c).add_spec(b), a.add_spec(c.add_spec(b)));
        assert(a.add_spec(c.add_spec(b)).eqv_spec(a.add_spec(c).add_spec(b)));
        Self::lemma_eqv_reflexive(d);
        Self::lemma_eqv_add_congruence(a.add_spec(c.add_spec(b)), a.add_spec(c).add_spec(b), d, d);
        assert(e6.eqv_spec(e7));

        Self::lemma_add_associative(a.add_spec(c), b, d);
        assert(e7.eqv_spec(e8));

        Self::lemma_eqv_transitive(e0, e1, e2);
        Self::lemma_eqv_transitive(e0, e2, e3);
        Self::lemma_eqv_transitive(e0, e3, e4);
        Self::lemma_eqv_transitive(e0, e4, e5);
        Self::lemma_eqv_transitive(e0, e5, e6);
        Self::lemma_eqv_transitive(e0, e6, e7);
        Self::lemma_eqv_transitive(e0, e7, e8);
        assert(e0.eqv_spec(e8));
    }

    pub proof fn lemma_neg_add(a: Self, b: Self)
        ensures
            a.add_spec(b).neg_spec() == a.neg_spec().add_spec(b.neg_spec()),
    {
        let lhs = a.add_spec(b).neg_spec();
        let rhs = a.neg_spec().add_spec(b.neg_spec());
        assert(lhs.num == -(a.num * b.denom() + b.num * a.denom()));
        assert(rhs.num == (-a.num) * b.neg_spec().denom() + b.neg_spec().num * a.neg_spec().denom());
        assert(b.neg_spec().denom() == b.denom());
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().num == -b.num);
        assert(rhs.num == (-a.num) * b.denom() + (-b.num) * a.denom());
        assert(-(a.num * b.denom() + b.num * a.denom())
            == (-a.num) * b.denom() + (-b.num) * a.denom()) by (nonlinear_arith);
        assert(lhs.num == rhs.num);
        assert(lhs.den == a.add_spec(b).den);
        assert(a.add_spec(b).den == a.den * b.den + a.den + b.den);
        assert(rhs.den == a.neg_spec().den * b.neg_spec().den + a.neg_spec().den + b.neg_spec().den);
        assert(a.neg_spec().den == a.den);
        assert(b.neg_spec().den == b.den);
        assert(rhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_add_distributes(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.add_spec(b).sub_spec(c.add_spec(d)).eqv_spec(a.sub_spec(c).add_spec(b.sub_spec(d))),
    {
        let lhs = a.add_spec(b).sub_spec(c.add_spec(d));
        let t1 = a.add_spec(b).sub_spec(c);
        let t2 = c.sub_spec(c.add_spec(d));
        let t3 = t1.add_spec(t2);
        let u1 = a.add_spec(b).sub_spec(a);
        let u2 = a.sub_spec(c);
        let u3 = u1.add_spec(u2);
        let u4 = b.add_spec(u2);
        let u5 = u2.add_spec(b);
        let v1 = c.add_spec(d).sub_spec(c);
        let v2 = v1.neg_spec();
        let v3 = d.neg_spec();
        let w1 = u5.add_spec(v2);
        let w2 = u5.add_spec(v3);
        let rhs = a.sub_spec(c).add_spec(b.sub_spec(d));

        Self::lemma_eqv_sub_chain(a.add_spec(b), c, c.add_spec(d));
        assert(lhs.eqv_spec(t3));

        Self::lemma_eqv_sub_chain(a.add_spec(b), a, c);
        assert(t1.eqv_spec(u3));
        Self::lemma_add_then_sub_cancel(a, b);
        assert(u1.eqv_spec(b));
        Self::lemma_eqv_reflexive(u2);
        Self::lemma_eqv_add_congruence(u1, b, u2, u2);
        assert(u3.eqv_spec(u4));
        Self::lemma_add_commutative(b, u2);
        assert(u4.eqv_spec(u5));
        Self::lemma_eqv_transitive(t1, u3, u4);
        Self::lemma_eqv_transitive(t1, u4, u5);
        assert(t1.eqv_spec(u5));

        Self::lemma_sub_antisymmetric(c, c.add_spec(d));
        assert(t2 == v1.neg_spec());
        Self::lemma_add_then_sub_cancel(c, d);
        assert(v1.eqv_spec(d));
        Self::lemma_eqv_neg_congruence(v1, d);
        assert(v2.eqv_spec(v3));
        Self::lemma_eqv_reflexive(u5);
        Self::lemma_eqv_add_congruence(u5, u5, v2, v3);
        assert(w1.eqv_spec(w2));
        Self::lemma_eqv_sub_chain(b, d, Self::from_int_spec(0));
        Self::lemma_sub_is_add_neg(b, d);
        assert(b.sub_spec(d) == b.add_spec(d.neg_spec()));
        assert(w2 == u2.add_spec(b).add_spec(d.neg_spec()));
        Self::lemma_add_associative(u2, b, d.neg_spec());
        assert(w2.eqv_spec(u2.add_spec(b.add_spec(d.neg_spec()))));
        assert(u2.add_spec(b.add_spec(d.neg_spec())) == u2.add_spec(b.sub_spec(d)));
        assert(rhs == u2.add_spec(b.sub_spec(d)));
        assert(w2.eqv_spec(rhs));

        Self::lemma_eqv_add_congruence(t1, u5, t2, v2);
        assert(t3.eqv_spec(w1));
        Self::lemma_eqv_transitive(t3, w1, w2);
        Self::lemma_eqv_transitive(t3, w2, rhs);
        Self::lemma_eqv_transitive(lhs, t3, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_mul_right(a: Self, b: Self, k: Self)
        ensures
            a.sub_spec(b).mul_spec(k).eqv_spec(a.mul_spec(k).sub_spec(b.mul_spec(k))),
    {
        let lhs = a.sub_spec(b).mul_spec(k);
        let rhs = a.mul_spec(k).sub_spec(b.mul_spec(k));
        let s = a.sub_spec(b);
        let ks = k.mul_spec(s);
        let ka = k.mul_spec(a);
        let kbn = k.mul_spec(b.neg_spec());
        let kb = k.mul_spec(b);
        let mid = ka.add_spec(kbn);

        Self::lemma_sub_is_add_neg(a, b);
        assert(s == a.add_spec(b.neg_spec()));
        assert(lhs == s.mul_spec(k));
        Self::lemma_mul_commutative(s, k);
        assert(s.mul_spec(k) == ks);
        assert(lhs == ks);

        Self::lemma_eqv_mul_distributive_left(k, a, b.neg_spec());
        assert(ks.eqv_spec(ka.add_spec(kbn)));
        assert(lhs.eqv_spec(mid));

        Self::lemma_mul_neg_right(k, b);
        assert(kbn == kb.neg_spec());
        assert(mid == ka.add_spec(kb.neg_spec()));
        assert(rhs == a.mul_spec(k).add_spec(b.mul_spec(k).neg_spec()));
        assert(ka == a.mul_spec(k));
        assert(kb == b.mul_spec(k));
        assert(mid == rhs);
        Self::lemma_eqv_reflexive(rhs);
        assert(mid.eqv_spec(rhs));
        Self::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Self::from_int_spec(0)) == a,
            Self::from_int_spec(0).add_spec(a) == a,
    {
        let z = Self::from_int_spec(0);
        let l = a.add_spec(z);
        let r = z.add_spec(a);
        let da = a.denom();
        assert(z.num == 0);
        assert(z.den == 0);
        assert(z.denom() == 1);
        assert(a.denom() == da);

        assert(l.num == a.num * z.denom() + z.num * da);
        assert(l.num == a.num * 1 + 0 * da);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(0 * da == 0) by (nonlinear_arith);
        assert(l.num == a.num);
        assert(l.den == a.den * z.den + a.den + z.den);
        assert(l.den == a.den * 0 + a.den + 0);
        assert(a.den * 0 == 0);
        assert(l.den == 0 + a.den + 0);
        assert(l.den == a.den);
        assert(l == a);

        assert(r.num == z.num * da + a.num * z.denom());
        assert(r.num == 0 * da + a.num * 1);
        assert(0 * da == 0) by (nonlinear_arith);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(r.num == a.num);
        assert(r.den == z.den * a.den + z.den + a.den);
        assert(r.den == 0 * a.den + 0 + a.den);
        assert(0 * a.den == 0);
        assert(r.den == 0 + 0 + a.den);
        assert(r.den == a.den);
        assert(r == a);
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()).eqv_spec(Self::from_int_spec(0)),
            a.neg_spec().add_spec(a).eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::from_int_spec(0);
        let l = a.add_spec(a.neg_spec());
        let r = a.neg_spec().add_spec(a);
        let d = a.denom();
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.neg_spec().denom() == d);
        assert(a.denom() == d);
        assert(a.neg_spec().num == -a.num);
        assert(l.num == a.num * a.neg_spec().denom() + a.neg_spec().num * a.denom());
        assert(r.num == a.neg_spec().num * a.denom() + a.num * a.neg_spec().denom());
        assert(l.num == a.num * d + (-a.num) * d);
        assert(r.num == (-a.num) * d + a.num * d);
        calc! {
            (==)
            l.num;
            { }
            a.num * d + (-a.num) * d;
            {
                assert(a.num * d + (-a.num) * d == 0) by (nonlinear_arith);
            }
            0;
        }
        calc! {
            (==)
            r.num;
            { }
            (-a.num) * d + a.num * d;
            {
                assert((-a.num) * d + a.num * d == 0) by (nonlinear_arith);
            }
            0;
        }
        assert(l.eqv_spec(z) == (l.num * z.denom() == z.num * l.denom()));
        assert(r.eqv_spec(z) == (r.num * z.denom() == z.num * r.denom()));
        calc! {
            (==)
            l.num * z.denom();
            { assert(l.num == 0); assert(z.denom() == 1); }
            0int * 1int;
            { }
            0int;
        }
        calc! {
            (==)
            z.num * l.denom();
            { assert(z.num == 0); }
            0 * l.denom();
            {
                lemma_mul_by_zero_is_zero(l.denom());
                assert(0 * l.denom() == 0);
            }
            0;
        }
        assert(l.num * z.denom() == z.num * l.denom());
        calc! {
            (==)
            r.num * z.denom();
            { assert(r.num == 0); assert(z.denom() == 1); }
            0int * 1int;
            { }
            0int;
        }
        calc! {
            (==)
            z.num * r.denom();
            { assert(z.num == 0); }
            0 * r.denom();
            {
                lemma_mul_by_zero_is_zero(r.denom());
                assert(0 * r.denom() == 0);
            }
            0;
        }
        assert(r.num * z.denom() == z.num * r.denom());
        assert(l.eqv_spec(z));
        assert(r.eqv_spec(z));
    }

    pub proof fn lemma_mul_one_identity(a: Self)
        ensures
            a.mul_spec(Self::from_int_spec(1)) == a,
            Self::from_int_spec(1).mul_spec(a) == a,
    {
        let o = Self::from_int_spec(1);
        let l = a.mul_spec(o);
        let r = o.mul_spec(a);
        let da = a.denom();
        assert(o.num == 1);
        assert(o.den == 0);
        assert(o.denom() == 1);

        assert(l.num == a.num * o.num);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(l.num == a.num);
        assert(l.den == a.den * o.den + a.den + o.den);
        assert(l.den == a.den * 0 + a.den + 0);
        assert(a.den * 0 == 0);
        assert(l.den == 0 + a.den + 0);
        assert(l.den == a.den);
        assert(l == a);

        assert(r.num == o.num * a.num);
        assert(1 * a.num == a.num) by (nonlinear_arith);
        assert(r.num == a.num);
        assert(r.den == o.den * a.den + o.den + a.den);
        assert(r.den == 0 * a.den + 0 + a.den);
        assert(0 * a.den == 0);
        assert(r.den == 0 + 0 + a.den);
        assert(r.den == a.den);
        assert(a.denom() == da);
        assert(r == a);
    }

    pub proof fn lemma_mul_associative(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b).mul_spec(c).eqv_spec(a.mul_spec(b.mul_spec(c))),
    {
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        let ab = a.mul_spec(b);
        let bc = b.mul_spec(c);
        let lhs = ab.mul_spec(c);
        let rhs = a.mul_spec(bc);

        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(b, c);
        Self::lemma_mul_denom_product_int(ab, c);
        Self::lemma_mul_denom_product_int(a, bc);

        assert(ab.num == a.num * b.num);
        assert(bc.num == b.num * c.num);
        assert(lhs.num == ab.num * c.num);
        assert(rhs.num == a.num * bc.num);
        assert(lhs.num == (a.num * b.num) * c.num);
        assert(rhs.num == a.num * (b.num * c.num));

        assert(ab.denom() == da * db);
        assert(bc.denom() == db * dc);
        assert(lhs.denom() == ab.denom() * dc);
        assert(rhs.denom() == da * bc.denom());
        assert(lhs.denom() == (da * db) * dc);
        assert(rhs.denom() == da * (db * dc));

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        lemma_mul_is_associative(a.num, b.num, c.num);
        assert((a.num * b.num) * c.num == a.num * (b.num * c.num));
        assert(lhs.num == rhs.num);
        lemma_mul_is_associative(da, db, dc);
        assert((da * db) * dc == da * (db * dc));
        assert(lhs.denom() == rhs.denom());
        assert(lhs.num * rhs.denom() == lhs.num * lhs.denom());
        assert(rhs.num * lhs.denom() == lhs.num * lhs.denom());
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_zero(a: Self)
        ensures
            a.mul_spec(Self::from_int_spec(0)).eqv_spec(Self::from_int_spec(0)),
            Self::from_int_spec(0).mul_spec(a).eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::zero();
        let l = a.mul_spec(z);
        let r = z.mul_spec(a);
        assert(z.num == 0);
        Self::lemma_mul_right_zero_num(a, z);
        Self::lemma_mul_left_zero_num(z, a);
        assert(l.num == 0);
        assert(r.num == 0);
        assert(l.eqv_spec(z) == (l.num * z.denom() == z.num * l.denom()));
        assert(r.eqv_spec(z) == (r.num * z.denom() == z.num * r.denom()));
        assert(l.eqv_spec(z));
        assert(r.eqv_spec(z));
    }

    pub proof fn lemma_mul_distributes_over_add(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))),
    {
        Self::lemma_eqv_mul_distributive_left(a, b, c);
        assert(a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))));
    }

    pub proof fn lemma_mul_zero_implies_factor_zero(a: Self, b: Self)
        requires
            a.mul_spec(b).num == 0,
        ensures
            a.num == 0 || b.num == 0,
    {
        assert(a.mul_spec(b).num == a.num * b.num);
        assert(a.num * b.num == 0);
        assert((a.num * b.num == 0) ==> (a.num == 0 || b.num == 0)) by (nonlinear_arith);
        assert(a.num == 0 || b.num == 0);
    }

    pub proof fn lemma_mul_reciprocal_positive_num(a: Self)
        requires
            a.num > 0,
        ensures
            {
                let an = a.num as nat;
                let inv = Scalar { num: a.denom(), den: (an - 1) as nat };
                a.mul_spec(inv).eqv_spec(Self::from_int_spec(1))
            },
            {
                let an = a.num as nat;
                let inv = Scalar { num: a.denom(), den: (an - 1) as nat };
                inv.mul_spec(a).eqv_spec(Self::from_int_spec(1))
            },
    {
        let one = Self::from_int_spec(1);
        let an = a.num as nat;
        assert(an > 0);
        assert((a.num as nat) as int == a.num);
        let inv = Scalar { num: a.denom(), den: (an - 1) as nat };
        let prod = a.mul_spec(inv);
        let rprod = inv.mul_spec(a);
        Self::lemma_mul_denom_product_int(a, inv);
        assert(inv.denom_nat() == (an - 1) + 1);
        assert((an - 1) + 1 == an) by (nonlinear_arith);
        assert(inv.denom_nat() == an);
        assert(inv.denom() == inv.denom_nat() as int);
        assert(inv.denom() == an as int);
        assert(inv.denom() == a.num);
        assert(prod.num == a.num * inv.num);
        assert(inv.num == a.denom());
        assert(prod.num == a.num * a.denom());
        assert(prod.denom() == a.denom() * inv.denom());
        assert(prod.denom() == a.denom() * a.num);
        assert(prod.eqv_spec(one) == (prod.num * one.denom() == one.num * prod.denom()));
        assert(one.denom() == 1);
        assert(one.num == 1);
        assert((prod.num * 1 == 1 * prod.denom()) == (prod.num == prod.denom())) by (nonlinear_arith);
        assert(prod.eqv_spec(one) == (prod.num == prod.denom()));
        assert(a.num * a.denom() == a.denom() * a.num) by (nonlinear_arith);
        assert(prod.num == prod.denom());
        assert(prod.eqv_spec(one));

        Self::lemma_mul_commutative(inv, a);
        assert(rprod == prod);
        Self::lemma_eqv_reflexive(prod);
        assert(rprod.eqv_spec(prod));
        Self::lemma_eqv_transitive(rprod, prod, one);
        assert(rprod.eqv_spec(one));
    }

    pub proof fn lemma_le_add_monotone_strong(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
        ensures
            a.add_spec(c).le_spec(b.add_spec(c)),
    {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(b, c);
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(ac.le_spec(bc) == (ac.num * bc.denom() <= bc.num * ac.denom()));
        assert(a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()));
        assert(a.num * b.denom() <= b.num * a.denom());
        assert((a.num * b.denom() <= b.num * a.denom())
            ==> ((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
                <= (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
            <= (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() == (a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom()));
        assert(bc.num * ac.denom() == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() <= bc.num * ac.denom());
        assert(ac.le_spec(bc));
    }

    pub proof fn lemma_le_add_monotone(a: Self, b: Self, c: Self)
        ensures
            a.le_spec(b) ==> a.add_spec(c).le_spec(b.add_spec(c)),
    {
        if a.le_spec(b) {
            Self::lemma_le_add_monotone_strong(a, b, c);
            assert(a.add_spec(c).le_spec(b.add_spec(c)));
        }
    }

    pub proof fn lemma_le_mul_monotone_nonnegative_strong(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            Self::from_int_spec(0).le_spec(c),
        ensures
            a.mul_spec(c).le_spec(b.mul_spec(c)),
    {
        let z = Self::from_int_spec(0);
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(ac.le_spec(bc) == (ac.num * bc.denom() <= bc.num * ac.denom()));
        assert(a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()));
        assert(a.num * b.denom() <= b.num * a.denom());
        assert(z.le_spec(c) == (z.num * c.denom() <= c.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(c) == (0 * c.denom() <= c.num * 1));
        lemma_mul_by_zero_is_zero(c.denom());
        assert(0 * c.denom() == 0);
        assert(0 <= c.num * 1);
        assert((0 <= c.num * 1) ==> (0 <= c.num)) by (nonlinear_arith);
        assert(c.num >= 0);
        assert((a.num * b.denom() <= b.num * a.denom() && c.num >= 0 && c.denom() > 0)
            ==> ((a.num * c.num) * (b.denom() * c.denom())
                <= (b.num * c.num) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.num) * (b.denom() * c.denom())
            <= (b.num * c.num) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() == (a.num * c.num) * (b.denom() * c.denom()));
        assert(bc.num * ac.denom() == (b.num * c.num) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() <= bc.num * ac.denom());
        assert(ac.le_spec(bc));
    }

    pub proof fn lemma_le_mul_monotone_nonnegative(a: Self, b: Self, c: Self)
        ensures
            (a.le_spec(b) && Self::from_int_spec(0).le_spec(c)) ==> a.mul_spec(c).le_spec(b.mul_spec(c)),
    {
        if a.le_spec(b) && Self::from_int_spec(0).le_spec(c) {
            Self::lemma_le_mul_monotone_nonnegative_strong(a, b, c);
            assert(a.mul_spec(c).le_spec(b.mul_spec(c)));
        }
    }

    pub proof fn lemma_add_right_cancel_strong(a: Self, b: Self, k: Self)
        requires
            a.add_spec(k).eqv_spec(b.add_spec(k)),
        ensures
            a.eqv_spec(b),
    {
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);
        let lhs = ak.sub_spec(bk);
        let s = a.sub_spec(b);
        let z = Self::from_int_spec(0);

        Self::lemma_eqv_reflexive(bk);
        Self::lemma_eqv_sub_congruence(ak, bk, bk, bk);
        assert(lhs.eqv_spec(bk.sub_spec(bk)));

        Self::lemma_sub_self_zero_num(bk);
        assert(bk.sub_spec(bk).num == 0);
        assert(z.num == 0);
        assert(bk.sub_spec(bk).eqv_spec(z)
            == (bk.sub_spec(bk).num * z.denom() == z.num * bk.sub_spec(bk).denom()));
        assert(bk.sub_spec(bk).num * z.denom() == 0 * z.denom());
        assert(z.num * bk.sub_spec(bk).denom() == 0 * bk.sub_spec(bk).denom());
        lemma_mul_by_zero_is_zero(z.denom());
        lemma_mul_by_zero_is_zero(bk.sub_spec(bk).denom());
        assert(0 * z.denom() == 0);
        assert(0 * bk.sub_spec(bk).denom() == 0);
        assert(bk.sub_spec(bk).num * z.denom() == z.num * bk.sub_spec(bk).denom());
        assert(bk.sub_spec(bk).eqv_spec(z));
        Self::lemma_eqv_transitive(lhs, bk.sub_spec(bk), z);
        assert(lhs.eqv_spec(z));

        Self::lemma_eqv_sub_cancel_right(a, b, k);
        assert(lhs.eqv_spec(s));
        Self::lemma_eqv_symmetric(lhs, s);
        assert(s.eqv_spec(lhs));
        Self::lemma_eqv_transitive(s, lhs, z);
        assert(s.eqv_spec(z));

        assert(s.eqv_spec(z) == (s.num * z.denom() == z.num * s.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(s.num * z.denom() == z.num * s.denom());
        assert(s.num * 1 == 0 * s.denom());
        lemma_mul_by_zero_is_zero(s.denom());
        assert(0 * s.denom() == 0);
        assert(s.num == 0);
        assert(s.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(a.num * b.denom() + (-b.num) * a.denom() == a.num * b.denom() - b.num * a.denom())
            by (nonlinear_arith);
        assert(a.num * b.denom() - b.num * a.denom() == 0);
        assert((a.num * b.denom() - b.num * a.denom() == 0) ==> (a.num * b.denom() == b.num * a.denom()))
            by (nonlinear_arith);
        assert(a.num * b.denom() == b.num * a.denom());
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_right_cancel(a: Self, b: Self, k: Self)
        ensures
            a.add_spec(k).eqv_spec(b.add_spec(k)) ==> a.eqv_spec(b),
    {
        if a.add_spec(k).eqv_spec(b.add_spec(k)) {
            Self::lemma_add_right_cancel_strong(a, b, k);
            assert(a.eqv_spec(b));
        }
    }

    pub proof fn lemma_add_left_cancel_strong(a: Self, b: Self, k: Self)
        requires
            k.add_spec(a).eqv_spec(k.add_spec(b)),
        ensures
            a.eqv_spec(b),
    {
        let ka = k.add_spec(a);
        let kb = k.add_spec(b);
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);

        Self::lemma_add_commutative(k, a);
        Self::lemma_add_commutative(k, b);
        assert(ka.eqv_spec(ak));
        assert(kb.eqv_spec(bk));
        Self::lemma_eqv_symmetric(ka, ak);
        assert(ak.eqv_spec(ka));
        Self::lemma_eqv_transitive(ak, ka, kb);
        assert(ak.eqv_spec(kb));
        Self::lemma_eqv_transitive(ak, kb, bk);
        assert(ak.eqv_spec(bk));

        Self::lemma_add_right_cancel_strong(a, b, k);
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_left_cancel(a: Self, b: Self, k: Self)
        ensures
            k.add_spec(a).eqv_spec(k.add_spec(b)) ==> a.eqv_spec(b),
    {
        if k.add_spec(a).eqv_spec(k.add_spec(b)) {
            Self::lemma_add_left_cancel_strong(a, b, k);
            assert(a.eqv_spec(b));
        }
    }

    pub proof fn lemma_add_then_sub_cancel(a: Self, b: Self)
        ensures
            a.add_spec(b).sub_spec(a).eqv_spec(b),
    {
        let lhs = a.add_spec(b).sub_spec(a);
        let z = Self::from_int_spec(0);
        let mid1 = b.add_spec(a).sub_spec(z.add_spec(a));
        let mid2 = b.sub_spec(z);

        Self::lemma_add_zero_identity(a);
        Self::lemma_add_zero_identity(b);
        Self::lemma_add_commutative(a, b);
        assert(z.add_spec(a) == a);

        Self::lemma_eqv_reflexive(a);
        assert(a.eqv_spec(z.add_spec(a)));
        Self::lemma_eqv_sub_congruence(a.add_spec(b), b.add_spec(a), a, z.add_spec(a));
        assert(lhs.eqv_spec(mid1));

        Self::lemma_eqv_sub_cancel_right(b, z, a);
        assert(mid1.eqv_spec(mid2));

        assert(mid2 == b.sub_spec(z));
        assert(b.sub_spec(z) == b.add_spec(z.neg_spec()));
        assert(z.num == 0);
        assert(z.neg_spec().num == -z.num);
        assert(z.neg_spec().num == 0);
        assert(z.neg_spec().den == z.den);
        assert(z.neg_spec() == z);
        assert(b.add_spec(z.neg_spec()) == b.add_spec(z));
        assert(b.add_spec(z) == b);
        Self::lemma_eqv_reflexive(b);
        assert(mid2.eqv_spec(b));

        Self::lemma_eqv_transitive(lhs, mid1, mid2);
        Self::lemma_eqv_transitive(lhs, mid2, b);
        assert(lhs.eqv_spec(b));
    }

    pub proof fn lemma_sub_then_add_cancel(a: Self, b: Self)
        ensures
            b.add_spec(a.sub_spec(b)).eqv_spec(a),
    {
        let lhs = b.add_spec(a.sub_spec(b));
        let rhs = a;
        let k = b.neg_spec();
        let z = Self::from_int_spec(0);

        let lhs_swap = a.sub_spec(b).add_spec(b);
        Self::lemma_add_commutative(b, a.sub_spec(b));
        assert(lhs.eqv_spec(lhs_swap));

        let lhsk = lhs.add_spec(k);
        let s1 = lhs_swap.add_spec(k);
        Self::lemma_eqv_reflexive(k);
        Self::lemma_eqv_add_congruence(lhs, lhs_swap, k, k);
        assert(lhsk.eqv_spec(s1));

        let s2 = a.sub_spec(b).add_spec(b.add_spec(k));
        Self::lemma_add_associative(a.sub_spec(b), b, k);
        assert(s1.eqv_spec(s2));

        Self::lemma_add_inverse(b);
        assert(k == b.neg_spec());
        assert(b.add_spec(k).eqv_spec(z));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        Self::lemma_eqv_add_congruence(a.sub_spec(b), a.sub_spec(b), b.add_spec(k), z);
        assert(s2.eqv_spec(a.sub_spec(b).add_spec(z)));

        Self::lemma_add_zero_identity(a.sub_spec(b));
        assert(a.sub_spec(b).add_spec(z) == a.sub_spec(b));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        assert(a.sub_spec(b).add_spec(z).eqv_spec(a.sub_spec(b)));

        Self::lemma_eqv_transitive(s1, s2, a.sub_spec(b).add_spec(z));
        Self::lemma_eqv_transitive(s1, a.sub_spec(b).add_spec(z), a.sub_spec(b));
        assert(s1.eqv_spec(a.sub_spec(b)));

        let rhsk = rhs.add_spec(k);
        Self::lemma_sub_is_add_neg(a, b);
        assert(rhsk == a.add_spec(b.neg_spec()));
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
        assert(rhsk == a.sub_spec(b));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        assert(rhsk.eqv_spec(a.sub_spec(b)));

        Self::lemma_eqv_transitive(lhsk, s1, a.sub_spec(b));
        assert(lhsk.eqv_spec(a.sub_spec(b)));
        Self::lemma_eqv_symmetric(rhsk, a.sub_spec(b));
        assert(a.sub_spec(b).eqv_spec(rhsk));
        Self::lemma_eqv_transitive(lhsk, a.sub_spec(b), rhsk);
        assert(lhsk.eqv_spec(rhsk));

        Self::lemma_add_right_cancel_strong(lhs, rhs, k);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_eqv_zero_iff_eqv(a: Self, b: Self)
        ensures
            a.sub_spec(b).eqv_spec(Self::from_int_spec(0)) == a.eqv_spec(b),
    {
        let s = a.sub_spec(b);
        let z = Self::from_int_spec(0);

        if s.eqv_spec(z) {
            let bs = b.add_spec(s);
            Self::lemma_sub_then_add_cancel(a, b);
            assert(bs.eqv_spec(a));
            Self::lemma_eqv_reflexive(b);
            Self::lemma_eqv_add_congruence(b, b, s, z);
            assert(bs.eqv_spec(b.add_spec(z)));
            Self::lemma_add_zero_identity(b);
            assert(b.add_spec(z) == b);
            Self::lemma_eqv_reflexive(b);
            assert(bs.eqv_spec(b));
            Self::lemma_eqv_symmetric(bs, b);
            assert(b.eqv_spec(bs));
            Self::lemma_eqv_transitive(b, bs, a);
            assert(b.eqv_spec(a));
            Self::lemma_eqv_symmetric(b, a);
            assert(a.eqv_spec(b));
        }

        if a.eqv_spec(b) {
            Self::lemma_eqv_reflexive(b);
            Self::lemma_eqv_sub_congruence(a, b, b, b);
            assert(a.sub_spec(b).eqv_spec(b.sub_spec(b)));
            Self::lemma_sub_self_zero_num(b);
            assert(b.sub_spec(b).num == 0);
            Self::lemma_eqv_zero_iff_num_zero(b.sub_spec(b));
            assert(b.sub_spec(b).eqv_spec(z) == (b.sub_spec(b).num == 0));
            assert(b.sub_spec(b).eqv_spec(z));
            Self::lemma_eqv_transitive(a.sub_spec(b), b.sub_spec(b), z);
            assert(a.sub_spec(b).eqv_spec(z));
        }
        assert((a.sub_spec(b).eqv_spec(z)) == a.eqv_spec(b));
    }

    pub proof fn lemma_sub_antisymmetric(a: Self, b: Self)
        ensures
            a.sub_spec(b) == b.sub_spec(a).neg_spec(),
    {
        let lhs = a.sub_spec(b);
        let rhs = b.sub_spec(a).neg_spec();
        assert(lhs == a.add_spec(b.neg_spec()));
        assert(rhs == b.add_spec(a.neg_spec()).neg_spec());

        assert(lhs.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(rhs.num == -(b.num * a.denom() + (-a.num) * b.denom()));
        assert(a.num * b.denom() + (-b.num) * a.denom()
            == -(b.num * a.denom() + (-a.num) * b.denom())) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(rhs.den == b.den * a.den + b.den + a.den);
        assert(a.den * b.den + a.den + b.den == b.den * a.den + b.den + a.den) by (nonlinear_arith);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_mul_neg_right(a: Self, b: Self)
        ensures
            a.mul_spec(b.neg_spec()) == a.mul_spec(b).neg_spec(),
    {
        let lhs = a.mul_spec(b.neg_spec());
        let rhs = a.mul_spec(b).neg_spec();

        assert(lhs.num == a.num * (-b.num));
        assert(rhs.num == -(a.num * b.num));
        assert(a.num * (-b.num) == -(a.num * b.num)) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.neg_spec().den + a.den + b.neg_spec().den);
        assert(rhs.den == a.mul_spec(b).den);
        assert(b.neg_spec().den == b.den);
        assert(a.mul_spec(b).den == a.den * b.den + a.den + b.den);
        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_neg_both(a: Self, b: Self)
        ensures
            a.neg_spec().sub_spec(b.neg_spec()) == a.sub_spec(b).neg_spec(),
    {
        let lhs = a.neg_spec().sub_spec(b.neg_spec());
        let rhs = a.sub_spec(b).neg_spec();

        assert(lhs.num == (-a.num) * b.neg_spec().denom() + (-b.neg_spec().num) * a.neg_spec().denom());
        assert(rhs.num == -(a.num * b.denom() + (-b.num) * a.denom()));
        assert(b.neg_spec().denom() == b.denom());
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().num == -b.num);
        assert(-b.neg_spec().num == b.num) by (nonlinear_arith);
        calc! {
            (==)
            lhs.num;
            { }
            (-a.num) * b.neg_spec().denom() + (-b.neg_spec().num) * a.neg_spec().denom();
            {
                assert(b.neg_spec().denom() == b.denom());
                assert(a.neg_spec().denom() == a.denom());
                assert(-b.neg_spec().num == b.num);
            }
            (-a.num) * b.denom() + b.num * a.denom();
        }
        calc! {
            (==)
            rhs.num;
            { }
            -(a.num * b.denom() + (-b.num) * a.denom());
            {
                assert(-(a.num * b.denom() + (-b.num) * a.denom())
                    == (-a.num) * b.denom() + b.num * a.denom()) by (nonlinear_arith);
            }
            (-a.num) * b.denom() + b.num * a.denom();
        }
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.neg_spec().den * b.neg_spec().den + a.neg_spec().den + b.neg_spec().den);
        assert(rhs.den == a.sub_spec(b).den);
        assert(a.neg_spec().den == a.den);
        assert(b.neg_spec().den == b.den);
        assert(a.sub_spec(b).den == a.den * b.den + a.den + b.den);
        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_self_zero_num(a: Self)
        ensures
            a.sub_spec(a).num == 0,
    {
        let d = a.denom();
        let s = a.sub_spec(a);
        assert(s == a.add_spec(a.neg_spec()));
        assert(s.num == a.num * d + (-a.num) * d);
        assert(a.num * d + (-a.num) * d == a.num * d - a.num * d) by (nonlinear_arith);
        assert(a.num * d - a.num * d == 0) by (nonlinear_arith);
        assert(s.num == 0);
    }

    pub proof fn lemma_sub_self_zero_signum(a: Self)
        ensures
            a.sub_spec(a).signum() == 0,
    {
        let s = a.sub_spec(a);
        Self::lemma_sub_self_zero_num(a);
        assert(s.num == 0);
        Self::lemma_signum_zero_iff(s);
        assert((s.signum() == 0) == (s.num == 0));
        assert(s.signum() == 0);
    }

    pub proof fn lemma_mul_left_zero_num(a: Self, b: Self)
        requires
            a.num == 0,
        ensures
            a.mul_spec(b).num == 0,
    {
        let p = a.mul_spec(b);
        assert(a.num == 0);
        calc! {
            (==)
            a.num * b.num;
            { assert(a.num == 0); }
            0 * b.num;
            {
                lemma_mul_by_zero_is_zero(b.num);
                assert(0 * b.num == 0);
            }
            0;
        }
        assert(p.num == a.num * b.num);
        assert(p.num == 0);
    }

    pub proof fn lemma_mul_right_zero_num(a: Self, b: Self)
        requires
            b.num == 0,
        ensures
            a.mul_spec(b).num == 0,
    {
        let p = a.mul_spec(b);
        assert(b.num == 0);
        calc! {
            (==)
            a.num * b.num;
            { assert(b.num == 0); }
            a.num * 0;
            {
                lemma_mul_by_zero_is_zero(a.num);
                assert(a.num * 0 == 0);
            }
            0;
        }
        assert(p.num == a.num * b.num);
        assert(p.num == 0);
    }

    pub proof fn lemma_sub_both_zero_num(a: Self, b: Self)
        requires
            a.num == 0,
            b.num == 0,
        ensures
            a.sub_spec(b).num == 0,
    {
        let s = a.sub_spec(b);
        assert(a.num == 0);
        assert(b.num == 0);
        calc! {
            (==)
            -b.num;
            { assert(b.num == 0); }
            -0;
            { }
            0;
        }
        calc! {
            (==)
            a.num * b.neg_spec().denom();
            { assert(a.num == 0); }
            0 * b.neg_spec().denom();
            {
                lemma_mul_by_zero_is_zero(b.neg_spec().denom());
                assert(0 * b.neg_spec().denom() == 0);
            }
            0;
        }
        calc! {
            (==)
            (-b.num) * a.denom();
            { assert(-b.num == 0); }
            0 * a.denom();
            {
                lemma_mul_by_zero_is_zero(a.denom());
                assert(0 * a.denom() == 0);
            }
            0;
        }
        assert(s == a.add_spec(b.neg_spec()));
        assert(s.num == a.num * b.neg_spec().denom() + (-b.num) * a.denom());
        assert(s.num == 0 + 0);
        assert(s.num == 0);
    }

    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        assert(a.num * a.denom() == a.num * a.denom());
    }

    pub proof fn lemma_eqv_symmetric(a: Self, b: Self)
        ensures
            a.eqv_spec(b) == b.eqv_spec(a),
    {
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(b.eqv_spec(a) == (b.num * a.denom() == a.num * b.denom()));
    }

    pub proof fn lemma_eqv_transitive(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
            b.eqv_spec(c),
        ensures
            a.eqv_spec(c),
    {
        Self::lemma_denom_positive(b);
        assert(b.denom() != 0);

        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(b.num * c.denom() == c.num * b.denom());

        calc! {
            (==)
            a.num * b.denom() * c.denom();
            {
                assert(a.num * b.denom() == b.num * a.denom());
            }
            b.num * a.denom() * c.denom();
            {
                assert(b.num * a.denom() * c.denom() == b.num * c.denom() * a.denom()) by (nonlinear_arith);
            }
            b.num * c.denom() * a.denom();
            {
                assert(b.num * c.denom() == c.num * b.denom());
            }
            c.num * b.denom() * a.denom();
        }
        assert((b.denom() != 0 && a.num * b.denom() * c.denom() == c.num * b.denom() * a.denom())
            ==> (a.num * c.denom() == c.num * a.denom())) by (nonlinear_arith);
        assert(a.num * c.denom() == c.num * a.denom());
    }

    /// Canonical normalization predicate for the model:
    /// among semantically-equivalent representations, this value has a
    /// minimal denominator.
    pub open spec fn normalized_spec(self) -> bool {
        forall|other: Self| #[trigger] self.eqv_spec(other) ==> self.denom_nat() <= other.denom_nat()
    }

    pub proof fn lemma_from_int_is_normalized(value: int)
        ensures
            Self::from_int_spec(value).normalized_spec(),
    {
        let s = Self::from_int_spec(value);
        assert(s.denom_nat() == 1);
        assert forall|other: Self| #![auto] s.eqv_spec(other) implies s.denom_nat() <= other.denom_nat() by {
            Self::lemma_denom_positive(other);
            assert(other.denom_nat() > 0);
            assert(1 <= other.denom_nat());
        };
    }

    pub proof fn lemma_normalized_eqv_implies_equal_denom(a: Self, b: Self)
        requires
            a.normalized_spec(),
            b.normalized_spec(),
            a.eqv_spec(b),
        ensures
            a.denom_nat() == b.denom_nat(),
    {
        Self::lemma_eqv_symmetric(a, b);
        assert(a.eqv_spec(b) == b.eqv_spec(a));
        assert(b.eqv_spec(a));

        assert(a.denom_nat() <= b.denom_nat());
        assert(b.denom_nat() <= a.denom_nat());
        assert((a.denom_nat() <= b.denom_nat() && b.denom_nat() <= a.denom_nat())
            ==> a.denom_nat() == b.denom_nat()) by (nonlinear_arith);
        assert(a.denom_nat() == b.denom_nat());
    }

    pub proof fn lemma_eqv_and_equal_denom_implies_equal_num(a: Self, b: Self)
        requires
            a.eqv_spec(b),
            a.denom_nat() == b.denom_nat(),
        ensures
            a.num == b.num,
    {
        Self::lemma_denom_positive(a);
        assert(a.denom() > 0);
        assert(a.denom() != 0);

        assert(a.denom() == a.denom_nat() as int);
        assert(b.denom() == b.denom_nat() as int);
        assert((a.denom_nat() as int) == (b.denom_nat() as int));
        assert(a.denom() == b.denom());

        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(a.num * a.denom() == b.num * a.denom());
        assert((a.denom() != 0 && a.num * a.denom() == b.num * a.denom()) ==> (a.num == b.num))
            by (nonlinear_arith);
        assert(a.num == b.num);
    }

    /// Strongest normalization bridge currently available:
    /// normalized semantic-equality implies structural equality.
    pub proof fn lemma_normalized_eqv_implies_equal(a: Self, b: Self)
        requires
            a.normalized_spec(),
            b.normalized_spec(),
            a.eqv_spec(b),
        ensures
            a == b,
    {
        Self::lemma_normalized_eqv_implies_equal_denom(a, b);
        Self::lemma_eqv_and_equal_denom_implies_equal_num(a, b);
        assert(a.den + 1 == b.den + 1);
        assert((a.den + 1 == b.den + 1) ==> a.den == b.den) by (nonlinear_arith);
        assert(a.den == b.den);
        assert(a.num == b.num);
        assert(a == b);
    }

    /// Normalized values use canonical zero representation.
    pub proof fn lemma_normalized_zero_has_unit_denom(a: Self)
        requires
            a.normalized_spec(),
            a.num == 0,
        ensures
            a.denom_nat() == 1,
    {
        let z = Self::from_int_spec(0);
        Self::lemma_eqv_zero_iff_num_zero(a);
        assert(a.eqv_spec(z) == (a.num == 0));
        assert(a.eqv_spec(z));
        assert(a.denom_nat() <= z.denom_nat());
        assert(z.denom_nat() == 1);
        Self::lemma_denom_positive(a);
        assert(a.denom_nat() > 0);
        assert((a.denom_nat() > 0 && a.denom_nat() <= 1) ==> a.denom_nat() == 1) by (nonlinear_arith);
        assert(a.denom_nat() == 1);
    }

    /// Canonical sign placement for rationals:
    /// denominator positive, and zero has denominator `1`.
    pub open spec fn canonical_sign_spec(self) -> bool {
        &&& self.denom_nat() > 0
        &&& (self.num == 0 ==> self.denom_nat() == 1)
    }

    pub open spec fn common_divisor_spec(self, d: nat) -> bool {
        &&& d > 0
        &&& exists|kn: int, kd: nat|
            (#[trigger] (d * kd)) == self.denom_nat()
                && (#[trigger] ((d as int) * kn)) == self.num
    }

    pub open spec fn gcd_one_spec(self) -> bool {
        forall|d: nat| #![auto] self.common_divisor_spec(d) ==> d == 1
    }

    pub proof fn lemma_normalized_implies_gcd_one(a: Self)
        requires
            a.normalized_spec(),
        ensures
            a.gcd_one_spec(),
    {
        assert forall|d: nat| #![auto] a.common_divisor_spec(d) implies d == 1 by {
            assert(d > 0);
            let (kn, kd) = choose|kn: int, kd: nat|
                (#[trigger] ((d as int) * kn)) == a.num && (#[trigger] (d * kd)) == a.denom_nat();
            assert((d as int) * kn == a.num);
            assert(d * kd == a.denom_nat());

            if d == 1 {
                assert(d == 1);
            } else {
                assert(d != 1);
                assert((d > 0 && d != 1) ==> 1 < d) by (nonlinear_arith);
                assert(1 < d);
                Self::lemma_denom_positive(a);
                assert(a.denom_nat() > 0);
                assert((d > 0 && d * kd == a.denom_nat() && a.denom_nat() > 0) ==> kd > 0)
                    by (nonlinear_arith);
                assert(kd > 0);

                let b = Scalar { num: kn, den: (kd as int - 1) as nat };
                assert(b.denom_nat() == kd);
                assert(b.denom() == b.denom_nat() as int);
                assert(a.denom() == a.denom_nat() as int);
                Self::lemma_nat_mul_cast(d, kd);
                assert((d * kd) as int == (d as int) * (kd as int));
                assert((d as int) * (kd as int) == a.denom());
                assert(b.denom_nat() == kd);
                assert(b.denom() == kd as int);

                assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
                assert(a.num == (d as int) * kn);
                assert(b.num == kn);
                assert(a.num * b.denom() == ((d as int) * kn) * (kd as int));
                assert(b.num * a.denom() == kn * ((d as int) * (kd as int)));
                assert(((d as int) * kn) * (kd as int) == kn * ((d as int) * (kd as int)))
                    by (nonlinear_arith);
                assert(a.eqv_spec(b));

                assert(a.denom_nat() <= b.denom_nat());
                assert(a.denom_nat() == d * kd);
                assert((d > 1 && kd > 0) ==> kd < d * kd) by (nonlinear_arith);
                assert(b.denom_nat() == kd);
                assert(b.denom_nat() < a.denom_nat());
                assert((a.denom_nat() <= b.denom_nat() && b.denom_nat() < a.denom_nat()) ==> false)
                    by (nonlinear_arith);
                assert(false);
            }
        };
    }

    pub proof fn lemma_normalized_implies_canonical_sign(a: Self)
        requires
            a.normalized_spec(),
        ensures
            a.canonical_sign_spec(),
    {
        Self::lemma_denom_positive(a);
        if a.num == 0 {
            Self::lemma_normalized_zero_has_unit_denom(a);
        }
    }

    pub proof fn lemma_nat_not_le_prev_implies_ge_bound(x: nat, bound: nat)
        requires
            bound > 0,
            !(x <= bound - 1),
        ensures
            bound <= x,
    {
        assert((bound > 0 && !(x <= bound - 1)) ==> bound <= x) by (nonlinear_arith);
        assert(bound <= x);
    }

    pub proof fn lemma_nat_le_and_not_le_prev_implies_eq(x: nat, bound: nat)
        requires
            bound > 0,
            x <= bound,
            !(x <= bound - 1),
        ensures
            x == bound,
    {
        Self::lemma_nat_not_le_prev_implies_ge_bound(x, bound);
        assert(bound <= x);
        assert((bound <= x && x <= bound) ==> x == bound) by (nonlinear_arith);
        assert(x == bound);
    }

    /// Constructively picks an equivalent scalar whose denominator is minimal
    /// among all equivalent forms with denominator at most `bound`.
    pub proof fn normalize_bounded(a: Self, bound: nat) -> (m: Self)
        requires
            exists|s: Self| s.eqv_spec(a) && s.denom_nat() <= bound,
        ensures
            m.eqv_spec(a),
            m.denom_nat() <= bound,
            forall|t: Self| #![auto]
                t.eqv_spec(a) && t.denom_nat() <= bound ==> m.denom_nat() <= t.denom_nat(),
        decreases bound,
    {
        if bound == 0 {
            let s = choose|s: Self| s.eqv_spec(a) && s.denom_nat() <= bound;
            Self::lemma_denom_positive(s);
            assert(s.denom_nat() > 0);
            assert(s.denom_nat() <= 0);
            assert(false);
            s
        } else {
            let prev = (bound as int - 1) as nat;
            if exists|s: Self| s.eqv_spec(a) && s.denom_nat() <= prev {
                let mprev = Self::normalize_bounded(a, prev);
                assert(mprev.eqv_spec(a));
                assert(mprev.denom_nat() <= prev);
                assert((mprev.denom_nat() <= prev && prev <= bound) ==> mprev.denom_nat() <= bound)
                    by (nonlinear_arith);
                assert(mprev.denom_nat() <= bound);

                assert forall|t: Self| #![auto]
                    t.eqv_spec(a) && t.denom_nat() <= bound implies mprev.denom_nat() <= t.denom_nat() by {
                    if t.denom_nat() <= prev {
                        assert(t.eqv_spec(a) && t.denom_nat() <= prev);
                        assert(mprev.denom_nat() <= t.denom_nat());
                    } else {
                        Self::lemma_nat_not_le_prev_implies_ge_bound(t.denom_nat(), bound);
                        assert(bound <= t.denom_nat());
                        assert((mprev.denom_nat() <= bound && bound <= t.denom_nat())
                            ==> mprev.denom_nat() <= t.denom_nat()) by (nonlinear_arith);
                        assert(mprev.denom_nat() <= t.denom_nat());
                    }
                };
                mprev
            } else {
                let s0 = choose|s: Self| s.eqv_spec(a) && s.denom_nat() <= bound;
                assert(s0.eqv_spec(a));
                assert(s0.denom_nat() <= bound);
                if s0.denom_nat() <= prev {
                    assert(exists|s: Self| s.eqv_spec(a) && s.denom_nat() <= prev) by {
                        assert(s0.eqv_spec(a));
                        assert(s0.denom_nat() <= prev);
                    };
                    assert(false);
                }
                Self::lemma_nat_le_and_not_le_prev_implies_eq(s0.denom_nat(), bound);
                assert(s0.denom_nat() == bound);

                assert forall|t: Self| #![auto]
                    t.eqv_spec(a) && t.denom_nat() <= bound implies s0.denom_nat() <= t.denom_nat() by {
                    if t.denom_nat() <= prev {
                        assert(exists|s: Self| s.eqv_spec(a) && s.denom_nat() <= prev) by {
                            assert(t.eqv_spec(a));
                            assert(t.denom_nat() <= prev);
                        };
                        assert(false);
                    } else {
                        Self::lemma_nat_not_le_prev_implies_ge_bound(t.denom_nat(), bound);
                        assert(bound <= t.denom_nat());
                        assert(s0.denom_nat() == bound);
                        assert(s0.denom_nat() <= t.denom_nat());
                    }
                };
                s0
            }
        }
    }

    /// Fully verified constructive normalization:
    /// returns an equivalent scalar with globally minimal denominator.
    pub proof fn normalize_constructive(a: Self) -> (m: Self)
        ensures
            m.eqv_spec(a),
            m.normalized_spec(),
            m.canonical_sign_spec(),
    {
        Self::lemma_eqv_reflexive(a);
        assert(exists|s: Self| s.eqv_spec(a) && s.denom_nat() <= a.denom_nat()) by {
            assert(a.eqv_spec(a));
            assert(a.denom_nat() <= a.denom_nat());
        };
        let m0 = Self::normalize_bounded(a, a.denom_nat());
        assert(m0.eqv_spec(a));
        assert(m0.denom_nat() <= a.denom_nat());

        assert forall|t: Self| #![auto] m0.eqv_spec(t) implies m0.denom_nat() <= t.denom_nat() by {
            Self::lemma_eqv_symmetric(m0, t);
            assert(m0.eqv_spec(t) == t.eqv_spec(m0));
            assert(t.eqv_spec(m0));
            Self::lemma_eqv_transitive(t, m0, a);
            assert(t.eqv_spec(a));
            if t.denom_nat() <= a.denom_nat() {
                assert(m0.denom_nat() <= t.denom_nat());
            } else {
                assert((!(t.denom_nat() <= a.denom_nat())) ==> a.denom_nat() <= t.denom_nat())
                    by (nonlinear_arith);
                assert(a.denom_nat() <= t.denom_nat());
                assert((m0.denom_nat() <= a.denom_nat() && a.denom_nat() <= t.denom_nat())
                    ==> m0.denom_nat() <= t.denom_nat()) by (nonlinear_arith);
                assert(m0.denom_nat() <= t.denom_nat());
            }
        };
        assert(m0.normalized_spec());
        Self::lemma_normalized_implies_canonical_sign(m0);
        assert(m0.canonical_sign_spec());
        m0
    }

    pub proof fn lemma_eqv_neg_congruence(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.neg_spec().eqv_spec(b.neg_spec()),
    {
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.neg_spec().eqv_spec(b.neg_spec())
            == (a.neg_spec().num * b.neg_spec().denom() == b.neg_spec().num * a.neg_spec().denom()));
        assert(a.neg_spec().num == -a.num);
        assert(b.neg_spec().num == -b.num);
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().denom() == b.denom());
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((-a.num) * b.denom() == (-b.num) * a.denom())) by (nonlinear_arith);
        assert(a.neg_spec().eqv_spec(b.neg_spec()));
    }

    pub proof fn lemma_eqv_add_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.add_spec(c).eqv_spec(b.add_spec(c)),
    {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(b, c);
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(ac.eqv_spec(bc) == (ac.num * bc.denom() == bc.num * ac.denom()));
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
                == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
            == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        calc! {
            (==)
            ac.num * bc.denom();
            {
                assert(ac.num == a.num * c.denom() + c.num * a.denom());
                assert(bc.denom() == b.denom() * c.denom());
            }
            (a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom());
            { }
            (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom());
            {
                assert(bc.num == b.num * c.denom() + c.num * b.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            bc.num * ac.denom();
        }
        assert(ac.eqv_spec(bc));
    }

    pub proof fn lemma_eqv_add_congruence_right(a: Self, b: Self, c: Self)
        requires
            b.eqv_spec(c),
        ensures
            a.add_spec(b).eqv_spec(a.add_spec(c)),
    {
        let ab = a.add_spec(b);
        let ac = a.add_spec(c);
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(a, c);
        assert(ab.num == a.num * b.denom() + b.num * a.denom());
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(b.num * c.denom() == c.num * b.denom());
        assert(ab.eqv_spec(ac) == (ab.num * ac.denom() == ac.num * ab.denom()));
        assert((b.num * c.denom() == c.num * b.denom())
            ==> ((a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom())
                == (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom())))
            by (nonlinear_arith);
        assert((a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom())
            == (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom()));
        calc! {
            (==)
            ab.num * ac.denom();
            {
                assert(ab.num == a.num * b.denom() + b.num * a.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom());
            { }
            (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom());
            {
                assert(ac.num == a.num * c.denom() + c.num * a.denom());
                assert(ab.denom() == a.denom() * b.denom());
            }
            ac.num * ab.denom();
        }
        assert(ab.eqv_spec(ac));
    }

    pub proof fn lemma_eqv_add_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.add_spec(b1).eqv_spec(a2.add_spec(b2)),
    {
        Self::lemma_eqv_add_congruence_left(a1, a2, b1);
        Self::lemma_eqv_add_congruence_right(a2, b1, b2);
        Self::lemma_eqv_transitive(a1.add_spec(b1), a2.add_spec(b1), a2.add_spec(b2));
    }

    pub proof fn lemma_eqv_mul_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.mul_spec(c).eqv_spec(b.mul_spec(c)),
    {
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(ac.eqv_spec(bc) == (ac.num * bc.denom() == bc.num * ac.denom()));
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((a.num * c.num) * (b.denom() * c.denom())
                == (b.num * c.num) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.num) * (b.denom() * c.denom())
            == (b.num * c.num) * (a.denom() * c.denom()));
        calc! {
            (==)
            ac.num * bc.denom();
            {
                assert(ac.num == a.num * c.num);
                assert(bc.denom() == b.denom() * c.denom());
            }
            (a.num * c.num) * (b.denom() * c.denom());
            { }
            (b.num * c.num) * (a.denom() * c.denom());
            {
                assert(bc.num == b.num * c.num);
                assert(ac.denom() == a.denom() * c.denom());
            }
            bc.num * ac.denom();
        }
        assert(ac.eqv_spec(bc));
    }

    pub proof fn lemma_eqv_mul_congruence_right(a: Self, b: Self, c: Self)
        requires
            b.eqv_spec(c),
        ensures
            a.mul_spec(b).eqv_spec(a.mul_spec(c)),
    {
        let ab = a.mul_spec(b);
        let ac = a.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(a, c);
        assert(ab.num == a.num * b.num);
        assert(ac.num == a.num * c.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(b.num * c.denom() == c.num * b.denom());
        assert(ab.eqv_spec(ac) == (ab.num * ac.denom() == ac.num * ab.denom()));
        assert((b.num * c.denom() == c.num * b.denom())
            ==> ((a.num * b.num) * (a.denom() * c.denom())
                == (a.num * c.num) * (a.denom() * b.denom())))
            by (nonlinear_arith);
        assert((a.num * b.num) * (a.denom() * c.denom())
            == (a.num * c.num) * (a.denom() * b.denom()));
        calc! {
            (==)
            ab.num * ac.denom();
            {
                assert(ab.num == a.num * b.num);
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.num) * (a.denom() * c.denom());
            { }
            (a.num * c.num) * (a.denom() * b.denom());
            {
                assert(ac.num == a.num * c.num);
                assert(ab.denom() == a.denom() * b.denom());
            }
            ac.num * ab.denom();
        }
        assert(ab.eqv_spec(ac));
    }

    pub proof fn lemma_eqv_mul_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.mul_spec(b1).eqv_spec(a2.mul_spec(b2)),
    {
        Self::lemma_eqv_mul_congruence_left(a1, a2, b1);
        Self::lemma_eqv_mul_congruence_right(a2, b1, b2);
        Self::lemma_eqv_transitive(a1.mul_spec(b1), a2.mul_spec(b1), a2.mul_spec(b2));
    }

    pub proof fn lemma_eqv_sub_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.sub_spec(b1).eqv_spec(a2.sub_spec(b2)),
    {
        Self::lemma_eqv_neg_congruence(b1, b2);
        Self::lemma_eqv_add_congruence(a1, a2, b1.neg_spec(), b2.neg_spec());
        assert(a1.sub_spec(b1) == a1.add_spec(b1.neg_spec()));
        assert(a2.sub_spec(b2) == a2.add_spec(b2.neg_spec()));
        assert(a1.add_spec(b1.neg_spec()).eqv_spec(a2.add_spec(b2.neg_spec())));
        assert(a1.sub_spec(b1).eqv_spec(a2.sub_spec(b2)));
    }

    pub proof fn lemma_eqv_mul_distributive_left(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))),
    {
        let bc = b.add_spec(c);
        let lhs = a.mul_spec(bc);
        let ab = a.mul_spec(b);
        let ac = a.mul_spec(c);
        let rhs = ab.add_spec(ac);

        Self::lemma_add_denom_product_int(b, c);
        Self::lemma_mul_denom_product_int(a, bc);
        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(ab, ac);

        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(lhs.num == a.num * bc.num);
        assert(lhs.num == a.num * (b.num * c.denom() + c.num * b.denom()));
        assert(lhs.denom() == a.denom() * bc.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(lhs.denom() == a.denom() * (b.denom() * c.denom()));

        assert(ab.num == a.num * b.num);
        assert(ac.num == a.num * c.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(rhs.num == ab.num * ac.denom() + ac.num * ab.denom());
        calc! {
            (==)
            rhs.num;
            { }
            ab.num * ac.denom() + ac.num * ab.denom();
            {
                assert(ab.num == a.num * b.num);
                assert(ac.num == a.num * c.num);
                assert(ab.denom() == a.denom() * b.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.num) * (a.denom() * c.denom()) + (a.num * c.num) * (a.denom() * b.denom());
            {
                assert((a.num * b.num) * (a.denom() * c.denom())
                    == (a.num * a.denom()) * (b.num * c.denom())) by (nonlinear_arith);
                assert((a.num * c.num) * (a.denom() * b.denom())
                    == (a.num * a.denom()) * (c.num * b.denom())) by (nonlinear_arith);
                assert((a.num * a.denom()) * (b.num * c.denom()) + (a.num * a.denom()) * (c.num * b.denom())
                    == a.num * a.denom() * (b.num * c.denom() + c.num * b.denom())) by (nonlinear_arith);
            }
            a.num * a.denom() * (b.num * c.denom() + c.num * b.denom());
        }
        assert(rhs.denom() == ab.denom() * ac.denom());
        assert(rhs.denom() == (a.denom() * b.denom()) * (a.denom() * c.denom()));

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        calc! {
            (==)
            lhs.num * rhs.denom();
            {
                assert(lhs.num == a.num * (b.num * c.denom() + c.num * b.denom()));
                assert(rhs.denom() == (a.denom() * b.denom()) * (a.denom() * c.denom()));
            }
            (a.num * (b.num * c.denom() + c.num * b.denom()))
                * ((a.denom() * b.denom()) * (a.denom() * c.denom()));
        }
        calc! {
            (==)
            rhs.num * lhs.denom();
            {
                assert(rhs.num == a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()));
                assert(lhs.denom() == a.denom() * (b.denom() * c.denom()));
            }
            (a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()))
                * (a.denom() * (b.denom() * c.denom()));
        }
        assert(
            (a.num * (b.num * c.denom() + c.num * b.denom()))
                * ((a.denom() * b.denom()) * (a.denom() * c.denom()))
            ==
            (a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()))
                * (a.denom() * (b.denom() * c.denom()))
        ) by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_mul_distributive_right(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).mul_spec(c).eqv_spec(a.mul_spec(c).add_spec(b.mul_spec(c))),
    {
        let lhs = a.add_spec(b).mul_spec(c);
        let mid = c.mul_spec(a.add_spec(b));
        let mid_rhs = c.mul_spec(a).add_spec(c.mul_spec(b));
        let rhs = a.mul_spec(c).add_spec(b.mul_spec(c));

        Self::lemma_mul_commutative(a.add_spec(b), c);
        assert(lhs == mid);
        Self::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(mid));

        Self::lemma_eqv_mul_distributive_left(c, a, b);
        assert(mid.eqv_spec(mid_rhs));

        Self::lemma_mul_commutative(c, a);
        Self::lemma_mul_commutative(c, b);
        assert(mid_rhs == rhs);
        Self::lemma_eqv_reflexive(mid_rhs);
        assert(mid_rhs.eqv_spec(rhs));

        Self::lemma_eqv_transitive(lhs, mid, mid_rhs);
        Self::lemma_eqv_transitive(lhs, mid_rhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_sub_cancel_right(a: Self, b: Self, k: Self)
        ensures
            a.add_spec(k).sub_spec(b.add_spec(k)).eqv_spec(a.sub_spec(b)),
    {
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);
        let lhs = ak.sub_spec(bk);
        let rhs = a.sub_spec(b);

        Self::lemma_add_denom_product_int(a, k);
        Self::lemma_add_denom_product_int(b, k);
        Self::lemma_sub_denom_product_int(ak, bk);
        Self::lemma_sub_denom_product_int(a, b);

        assert(ak.num == a.num * k.denom() + k.num * a.denom());
        assert(bk.num == b.num * k.denom() + k.num * b.denom());
        assert(lhs.num == ak.num * bk.denom() + (-bk.num) * ak.denom());
        assert(rhs.num == a.num * b.denom() + (-b.num) * a.denom());

        assert(ak.denom() == a.denom() * k.denom());
        assert(bk.denom() == b.denom() * k.denom());
        assert(lhs.denom() == ak.denom() * bk.denom());
        assert(rhs.denom() == a.denom() * b.denom());

        calc! {
            (==)
            lhs.num;
            {
                assert(lhs.num == ak.num * bk.denom() + (-bk.num) * ak.denom());
            }
            ak.num * bk.denom() + (-bk.num) * ak.denom();
            {
                assert(ak.num == a.num * k.denom() + k.num * a.denom());
                assert(bk.num == b.num * k.denom() + k.num * b.denom());
                assert(ak.denom() == a.denom() * k.denom());
                assert(bk.denom() == b.denom() * k.denom());
            }
            (a.num * k.denom() + k.num * a.denom()) * (b.denom() * k.denom())
                + (-(b.num * k.denom() + k.num * b.denom())) * (a.denom() * k.denom());
            {
                assert((a.num * k.denom() + k.num * a.denom()) * (b.denom() * k.denom())
                    + (-(b.num * k.denom() + k.num * b.denom())) * (a.denom() * k.denom())
                    == ((a.num * k.denom() + k.num * a.denom()) * b.denom()
                        + (-(b.num * k.denom() + k.num * b.denom())) * a.denom()) * k.denom())
                    by (nonlinear_arith);
                assert(((a.num * k.denom() + k.num * a.denom()) * b.denom()
                        + (-(b.num * k.denom() + k.num * b.denom())) * a.denom())
                    == (a.num * b.denom() + (-b.num) * a.denom()) * k.denom())
                    by (nonlinear_arith);
            }
            ((a.num * b.denom() + (-b.num) * a.denom()) * k.denom()) * k.denom();
            {
                assert(((a.num * b.denom() + (-b.num) * a.denom()) * k.denom()) * k.denom()
                    == (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom()))
                    by (nonlinear_arith);
            }
            (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom());
        }

        calc! {
            (==)
            lhs.denom();
            {
                assert(lhs.denom() == ak.denom() * bk.denom());
                assert(ak.denom() == a.denom() * k.denom());
                assert(bk.denom() == b.denom() * k.denom());
            }
            (a.denom() * k.denom()) * (b.denom() * k.denom());
            {
                assert((a.denom() * k.denom()) * (b.denom() * k.denom())
                    == (a.denom() * b.denom()) * (k.denom() * k.denom()))
                    by (nonlinear_arith);
            }
            (a.denom() * b.denom()) * (k.denom() * k.denom());
        }

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(lhs.num == (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom()));
        assert(lhs.denom() == (a.denom() * b.denom()) * (k.denom() * k.denom()));
        assert(rhs.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(rhs.denom() == a.denom() * b.denom());
        assert(lhs.num * rhs.denom()
            == ((a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom())) * (a.denom() * b.denom()));
        assert(rhs.num * lhs.denom()
            == (a.num * b.denom() + (-b.num) * a.denom()) * ((a.denom() * b.denom()) * (k.denom() * k.denom())));
        assert(((a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom())) * (a.denom() * b.denom())
            == (a.num * b.denom() + (-b.num) * a.denom()) * ((a.denom() * b.denom()) * (k.denom() * k.denom())))
            by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_sub_chain(a: Self, b: Self, c: Self)
        ensures
            a.sub_spec(c).eqv_spec(a.sub_spec(b).add_spec(b.sub_spec(c))),
    {
        let lhs = a.sub_spec(c);
        let ab = a.sub_spec(b);
        let bc = b.sub_spec(c);
        let rhs = ab.add_spec(bc);

        Self::lemma_sub_denom_product_int(a, c);
        Self::lemma_sub_denom_product_int(a, b);
        Self::lemma_sub_denom_product_int(b, c);
        Self::lemma_add_denom_product_int(ab, bc);

        assert(lhs.num == a.num * c.denom() + (-c.num) * a.denom());
        assert(ab.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(bc.num == b.num * c.denom() + (-c.num) * b.denom());
        assert(rhs.num == ab.num * bc.denom() + bc.num * ab.denom());

        assert(lhs.denom() == a.denom() * c.denom());
        assert(ab.denom() == a.denom() * b.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(rhs.denom() == ab.denom() * bc.denom());

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(
            (a.num * b.denom() + (-b.num) * a.denom()) * c.denom()
            + (b.num * c.denom() + (-c.num) * b.denom()) * a.denom()
            == (a.num * c.denom() + (-c.num) * a.denom()) * b.denom()
        ) by (nonlinear_arith);

        calc! {
            (==)
            ab.num * c.denom() + bc.num * a.denom();
            {
                assert(ab.num == a.num * b.denom() + (-b.num) * a.denom());
                assert(bc.num == b.num * c.denom() + (-c.num) * b.denom());
            }
            (a.num * b.denom() + (-b.num) * a.denom()) * c.denom()
                + (b.num * c.denom() + (-c.num) * b.denom()) * a.denom();
            { }
            (a.num * c.denom() + (-c.num) * a.denom()) * b.denom();
            {
                assert(lhs.num == a.num * c.denom() + (-c.num) * a.denom());
            }
            lhs.num * b.denom();
        }

        calc! {
            (==)
            rhs.num;
            { assert(rhs.num == ab.num * bc.denom() + bc.num * ab.denom()); }
            ab.num * bc.denom() + bc.num * ab.denom();
            {
                assert(bc.denom() == b.denom() * c.denom());
                assert(ab.denom() == a.denom() * b.denom());
            }
            ab.num * (b.denom() * c.denom()) + bc.num * (a.denom() * b.denom());
            {
                assert(ab.num * (b.denom() * c.denom()) + bc.num * (a.denom() * b.denom())
                    == b.denom() * (ab.num * c.denom() + bc.num * a.denom())) by (nonlinear_arith);
            }
            b.denom() * (ab.num * c.denom() + bc.num * a.denom());
            {
                assert(ab.num * c.denom() + bc.num * a.denom() == lhs.num * b.denom());
            }
            b.denom() * (lhs.num * b.denom());
        }

        calc! {
            (==)
            rhs.num * lhs.denom();
            {
                assert(lhs.denom() == a.denom() * c.denom());
                assert(rhs.num == b.denom() * (lhs.num * b.denom()));
            }
            (b.denom() * (lhs.num * b.denom())) * (a.denom() * c.denom());
        }

        calc! {
            (==)
            lhs.num * rhs.denom();
            {
                assert(rhs.denom() == ab.denom() * bc.denom());
                assert(ab.denom() == a.denom() * b.denom());
                assert(bc.denom() == b.denom() * c.denom());
            }
            lhs.num * ((a.denom() * b.denom()) * (b.denom() * c.denom()));
        }

        assert((b.denom() * (lhs.num * b.denom())) * (a.denom() * c.denom())
            == lhs.num * ((a.denom() * b.denom()) * (b.denom() * c.denom()))) by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_signum(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.signum() == b.signum(),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());

        if a.num == 0 {
            assert(b.num * a.denom() == 0);
            assert((a.denom() != 0 && b.num * a.denom() == 0) ==> (b.num == 0)) by (nonlinear_arith);
            assert(a.denom() != 0);
            assert(b.num == 0);
            Self::lemma_signum_zero_iff(a);
            Self::lemma_signum_zero_iff(b);
            assert((a.signum() == 0) == (a.num == 0));
            assert((b.signum() == 0) == (b.num == 0));
            assert(a.signum() == 0);
            assert(b.signum() == 0);
        } else if a.num > 0 {
            assert((a.num > 0 && b.denom() > 0) ==> a.num * b.denom() > 0) by (nonlinear_arith);
            assert(a.num * b.denom() > 0);
            assert(b.num * a.denom() > 0);
            assert((a.denom() > 0 && b.num * a.denom() > 0) ==> b.num > 0) by (nonlinear_arith);
            assert(b.num > 0);
            Self::lemma_signum_positive_iff(a);
            Self::lemma_signum_positive_iff(b);
            assert((a.signum() == 1) == (a.num > 0));
            assert((b.signum() == 1) == (b.num > 0));
            assert(a.signum() == 1);
            assert(b.signum() == 1);
        } else {
            assert(a.num < 0);
            assert((a.num < 0 && b.denom() > 0) ==> a.num * b.denom() < 0) by (nonlinear_arith);
            assert(a.num * b.denom() < 0);
            assert(b.num * a.denom() < 0);
            assert((a.denom() > 0 && b.num * a.denom() < 0) ==> b.num < 0) by (nonlinear_arith);
            assert(b.num < 0);
            Self::lemma_signum_negative_iff(a);
            Self::lemma_signum_negative_iff(b);
            assert((a.signum() == -1) == (a.num < 0));
            assert((b.signum() == -1) == (b.num < 0));
            assert(a.signum() == -1);
            assert(b.signum() == -1);
        }
        assert(a.signum() == b.signum());
    }

    pub proof fn lemma_signum_positive_iff(a: Self)
        ensures
            (a.signum() == 1) == (a.num > 0),
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else {
            assert(a.signum() != 1);
        }
    }

    pub proof fn lemma_signum_neg(a: Self)
        ensures
            a.neg_spec().num == -a.num,
    {
        let n = a.neg_spec();
        assert(n.num == -a.num);
    }

    pub proof fn lemma_signum_negative_iff(a: Self)
        ensures
            (a.signum() == -1) == (a.num < 0),
    {
        if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() != -1);
        }
    }

    pub proof fn lemma_signum_zero_iff(a: Self)
        ensures
            (a.signum() == 0) == (a.num == 0),
    {
        if a.num == 0 {
            assert(a.signum() == 0);
        } else {
            assert(a.signum() != 0);
        }
    }

    pub proof fn lemma_signum_cases(a: Self)
        ensures
            a.signum() == 1 || a.signum() == -1 || a.signum() == 0,
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() == 0);
        }
    }

    pub proof fn lemma_signum_mul(a: Self, b: Self)
        ensures
            a.mul_spec(b).signum() == a.signum() * b.signum(),
    {
        let p = a.mul_spec(b);
        assert(p.num == a.num * b.num);

        if a.num == 0 {
            assert(a.signum() == 0);
            calc! {
                (==)
                p.num;
                { assert(p.num == a.num * b.num); assert(a.num == 0); }
                0 * b.num;
                {
                    lemma_mul_by_zero_is_zero(b.num);
                    assert(0 * b.num == 0);
                }
                0;
            }
            assert(p.signum() == 0);
            assert(a.signum() * b.signum() == 0);
        } else if a.num > 0 {
            assert(a.signum() == 1);
            if b.num == 0 {
                assert(b.signum() == 0);
                calc! {
                    (==)
                    p.num;
                    { assert(p.num == a.num * b.num); assert(b.num == 0); }
                    a.num * 0;
                    {
                        lemma_mul_by_zero_is_zero(a.num);
                        assert(a.num * 0 == 0);
                    }
                    0;
                }
                assert(p.signum() == 0);
                assert(a.signum() * b.signum() == 0);
            } else if b.num > 0 {
                assert(b.signum() == 1);
                lemma_mul_strict_inequality(0, a.num, b.num);
                lemma_mul_basics(b.num);
                assert(0 * b.num == 0);
                assert(0 < a.num * b.num);
                assert(p.num > 0);
                assert(p.signum() == 1);
                assert(a.signum() * b.signum() == 1);
            } else {
                assert(b.num < 0);
                assert(b.signum() == -1);
                lemma_mul_strict_inequality(b.num, 0, a.num);
                lemma_mul_is_commutative(a.num, b.num);
                lemma_mul_basics(a.num);
                assert(b.num * a.num < 0 * a.num);
                assert(0 * a.num == 0);
                assert(a.num * b.num == b.num * a.num);
                assert(p.num < 0);
                assert(p.signum() == -1);
                assert(a.signum() * b.signum() == -1);
            }
        } else {
            assert(a.num < 0);
            assert(a.signum() == -1);
            if b.num == 0 {
                assert(b.signum() == 0);
                calc! {
                    (==)
                    p.num;
                    { assert(p.num == a.num * b.num); assert(b.num == 0); }
                    a.num * 0;
                    {
                        lemma_mul_by_zero_is_zero(a.num);
                        assert(a.num * 0 == 0);
                    }
                    0;
                }
                assert(p.signum() == 0);
                assert(a.signum() * b.signum() == 0);
            } else if b.num > 0 {
                assert(b.signum() == 1);
                lemma_mul_strict_inequality(a.num, 0, b.num);
                lemma_mul_basics(b.num);
                assert(a.num * b.num < 0 * b.num);
                assert(0 * b.num == 0);
                assert(p.num < 0);
                assert(p.signum() == -1);
                assert(a.signum() * b.signum() == -1);
            } else {
                assert(b.num < 0);
                assert(b.signum() == -1);
                assert((a.num < 0) ==> (0 - a.num > 0)) by (nonlinear_arith);
                assert(0 - a.num > 0);
                assert(-a.num == 0 - a.num);
                assert(-a.num > 0);
                assert((b.num < 0) ==> (0 - b.num > 0)) by (nonlinear_arith);
                assert(0 - b.num > 0);
                assert(-b.num == 0 - b.num);
                assert(-b.num > 0);
                lemma_mul_strict_inequality(0, -a.num, -b.num);
                lemma_mul_basics(-b.num);
                assert(0 * (-b.num) == 0);
                assert(0 < (-a.num) * (-b.num));
                assert((-a.num) * (-b.num) == a.num * b.num) by (nonlinear_arith);
                assert(p.num > 0);
                assert(p.signum() == 1);
                assert(a.signum() * b.signum() == 1);
            }
        }
        assert(p.signum() == a.signum() * b.signum());
    }
}

/// Explicit name for the proof/spec scalar model.
///
/// This alias is the first step toward the "single runtime Scalar + model view"
/// refactor: proof-heavy modules can migrate to `ScalarModel` naming without
/// changing semantics.
pub type ScalarModel = Scalar;

} // verus!
