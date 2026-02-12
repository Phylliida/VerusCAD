use crate::quaternion::Quaternion;
use crate::runtime_quaternion::RuntimeQuaternion;
use crate::runtime_scalar::RuntimeScalar;
use crate::scalar::Scalar;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeQuaternion(RuntimeQuaternion);

impl View for RuntimeQuaternion {
    type V = Quaternion;

    uninterp spec fn view(&self) -> Quaternion;
}

pub assume_specification[ RuntimeQuaternion::new ](
    w: RuntimeScalar,
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == (Quaternion { w: w@, x: x@, y: y@, z: z@ }),
;

pub assume_specification[ RuntimeQuaternion::from_ints ](
    w: i64,
    x: i64,
    y: i64,
    z: i64,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::from_ints_spec(w as int, x as int, y as int, z as int),
;

pub assume_specification[ RuntimeQuaternion::zero ]() -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::zero_spec(),
;

pub assume_specification[ RuntimeQuaternion::one ]() -> (out: RuntimeQuaternion)
    ensures
        out@ == Quaternion::one_spec(),
;

pub assume_specification[ RuntimeQuaternion::add ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::sub ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::neg ](this: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeQuaternion::scale ](
    this: &RuntimeQuaternion,
    k: &RuntimeScalar,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.scale_spec(k@),
;

pub assume_specification[ RuntimeQuaternion::mul ](
    this: &RuntimeQuaternion,
    rhs: &RuntimeQuaternion,
) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.mul_spec(rhs@),
;

pub assume_specification[ RuntimeQuaternion::conjugate ](this: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == this@.conjugate_spec(),
;

pub assume_specification[ RuntimeQuaternion::norm2 ](this: &RuntimeQuaternion) -> (out: RuntimeScalar)
    ensures
        out@ == this@.norm2_spec(),
;

pub assume_specification[ RuntimeQuaternion::inverse ](this: &RuntimeQuaternion) -> (out: Option<RuntimeQuaternion>)
    ensures
        out.is_some() == (this@.norm2_spec().num > 0),
        match out {
            Option::None => true,
            Option::Some(inv) => inv@ == this@.inverse_spec(),
        },
;

#[allow(dead_code)]
pub fn runtime_quaternion_add_pair_commutative(a: &RuntimeQuaternion, b: &RuntimeQuaternion) -> (pair: (
    RuntimeQuaternion,
    RuntimeQuaternion,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        Quaternion::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

#[allow(dead_code)]
pub fn runtime_quaternion_add_associative(
    a: &RuntimeQuaternion,
    b: &RuntimeQuaternion,
    c: &RuntimeQuaternion,
) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.add_spec(b@).add_spec(c@),
        pair.1@ == a@.add_spec(b@.add_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let lhs = ab.add(c);
    let bc = b.add(c);
    let rhs = a.add(&bc);
    proof {
        Quaternion::lemma_add_associative(a@, b@, c@);
        assert(a@.add_spec(b@).add_spec(c@).eqv_spec(a@.add_spec(b@.add_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_add_zero_identity(
    a: &RuntimeQuaternion,
) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.add_spec(Quaternion::zero_spec()),
        pair.1@ == Quaternion::zero_spec().add_spec(a@),
        pair.0@ == a@,
        pair.1@ == a@,
{
    let z = RuntimeQuaternion::zero();
    let lhs = a.add(&z);
    let rhs = z.add(a);
    proof {
        Quaternion::lemma_add_zero_identity(a@);
        assert(a@.add_spec(Quaternion::zero_spec()) == a@);
        assert(Quaternion::zero_spec().add_spec(a@) == a@);
        assert(lhs@ == a@);
        assert(rhs@ == a@);
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_conjugate_involution(q: &RuntimeQuaternion) -> (out: RuntimeQuaternion)
    ensures
        out@ == q@,
{
    let c = q.conjugate();
    let out = c.conjugate();
    proof {
        Quaternion::lemma_conjugate_involution(q@);
        assert(q@.conjugate_spec().conjugate_spec() == q@);
        assert(out@ == q@);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_quaternion_sub_matches_add_neg(a: &RuntimeQuaternion, b: &RuntimeQuaternion) -> (pair: (
    RuntimeQuaternion,
    RuntimeQuaternion,
))
    ensures
        pair.0@ == a@.sub_spec(b@),
        pair.1@ == a@.add_spec(b@.neg_spec()),
        pair.0@ == pair.1@,
{
    let sub = a.sub(b);
    let negb = b.neg();
    let add_neg = a.add(&negb);
    proof {
        Quaternion::lemma_sub_is_add_neg(a@, b@);
        assert(a@.sub_spec(b@) == a@.add_spec(b@.neg_spec()));
        assert(sub@ == add_neg@);
    }
    (sub, add_neg)
}

#[allow(dead_code)]
pub fn runtime_quaternion_add_inverse(a: &RuntimeQuaternion) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.add_spec(a@.neg_spec()),
        pair.1@ == a@.neg_spec().add_spec(a@),
        pair.0@.eqv_spec(Quaternion::zero_spec()),
        pair.1@.eqv_spec(Quaternion::zero_spec()),
{
    let neg = a.neg();
    let lhs = a.add(&neg);
    let rhs = neg.add(a);
    proof {
        Quaternion::lemma_add_inverse(a@);
        assert(a@.add_spec(a@.neg_spec()).eqv_spec(Quaternion::zero_spec()));
        assert(a@.neg_spec().add_spec(a@).eqv_spec(Quaternion::zero_spec()));
        assert(lhs@.eqv_spec(Quaternion::zero_spec()));
        assert(rhs@.eqv_spec(Quaternion::zero_spec()));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_one_identity(a: &RuntimeQuaternion) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.mul_spec(Quaternion::one_spec()),
        pair.1@ == Quaternion::one_spec().mul_spec(a@),
        pair.0@.eqv_spec(a@),
        pair.1@.eqv_spec(a@),
{
    let one = RuntimeQuaternion::one();
    let lhs = a.mul(&one);
    let rhs = one.mul(a);
    proof {
        Quaternion::lemma_mul_one_identity(a@);
        assert(a@.mul_spec(Quaternion::one_spec()).eqv_spec(a@));
        assert(Quaternion::one_spec().mul_spec(a@).eqv_spec(a@));
        assert(lhs@.eqv_spec(a@));
        assert(rhs@.eqv_spec(a@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_associative(
    a: &RuntimeQuaternion,
    b: &RuntimeQuaternion,
    c: &RuntimeQuaternion,
) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.mul_spec(b@).mul_spec(c@),
        pair.1@ == a@.mul_spec(b@.mul_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.mul(b);
    let lhs = ab.mul(c);
    let bc = b.mul(c);
    let rhs = a.mul(&bc);
    proof {
        Quaternion::lemma_mul_associative(a@, b@, c@);
        assert(a@.mul_spec(b@).mul_spec(c@).eqv_spec(a@.mul_spec(b@.mul_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_distributes_over_add_left(
    a: &RuntimeQuaternion,
    b: &RuntimeQuaternion,
    c: &RuntimeQuaternion,
) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.add_spec(b@).mul_spec(c@),
        pair.1@ == a@.mul_spec(c@).add_spec(b@.mul_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let apb = a.add(b);
    let lhs = apb.mul(c);
    let ac = a.mul(c);
    let bc = b.mul(c);
    let rhs = ac.add(&bc);
    proof {
        Quaternion::lemma_mul_distributes_over_add_left(a@, b@, c@);
        assert(a@.add_spec(b@).mul_spec(c@).eqv_spec(a@.mul_spec(c@).add_spec(b@.mul_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_distributes_over_add_right(
    a: &RuntimeQuaternion,
    b: &RuntimeQuaternion,
    c: &RuntimeQuaternion,
) -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        pair.0@ == a@.mul_spec(b@.add_spec(c@)),
        pair.1@ == a@.mul_spec(b@).add_spec(a@.mul_spec(c@)),
        pair.0@.eqv_spec(pair.1@),
{
    let bpc = b.add(c);
    let lhs = a.mul(&bpc);
    let ab = a.mul(b);
    let ac = a.mul(c);
    let rhs = ab.add(&ac);
    proof {
        Quaternion::lemma_mul_distributes_over_add_right(a@, b@, c@);
        assert(a@.mul_spec(b@.add_spec(c@)).eqv_spec(a@.mul_spec(b@).add_spec(a@.mul_spec(c@))));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_noncommutative_witness() -> (pair: (RuntimeQuaternion, RuntimeQuaternion))
    ensures
        {
            let i = Quaternion::from_ints_spec(0, 1, 0, 0);
            let j = Quaternion::from_ints_spec(0, 0, 1, 0);
            pair.0@ == i.mul_spec(j)
        },
        {
            let i = Quaternion::from_ints_spec(0, 1, 0, 0);
            let j = Quaternion::from_ints_spec(0, 0, 1, 0);
            pair.1@ == j.mul_spec(i)
        },
        !pair.0@.eqv_spec(pair.1@),
{
    let i = RuntimeQuaternion::from_ints(0, 1, 0, 0);
    let j = RuntimeQuaternion::from_ints(0, 0, 1, 0);
    let ij = i.mul(&j);
    let ji = j.mul(&i);
    proof {
        Quaternion::lemma_mul_noncommutative_witness();
        let si = Quaternion::from_ints_spec(0, 1, 0, 0);
        let sj = Quaternion::from_ints_spec(0, 0, 1, 0);
        assert(!si.mul_spec(sj).eqv_spec(sj.mul_spec(si)));
        assert(!ij@.eqv_spec(ji@));
    }
    (ij, ji)
}

#[allow(dead_code)]
pub fn runtime_quaternion_norm2_nonnegative(q: &RuntimeQuaternion) -> (out: RuntimeScalar)
    ensures
        out@ == q@.norm2_spec(),
        Scalar::from_int_spec(0).le_spec(out@),
{
    let out = q.norm2();
    proof {
        Quaternion::lemma_norm2_nonnegative(q@);
        assert(Scalar::from_int_spec(0).le_spec(q@.norm2_spec()));
        assert(Scalar::from_int_spec(0).le_spec(out@));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_quaternion_norm2_zero_iff_zero(q: &RuntimeQuaternion) -> (out: RuntimeScalar)
    ensures
        out@ == q@.norm2_spec(),
        out@.eqv_spec(Scalar::from_int_spec(0)) == q@.eqv_spec(Quaternion::zero_spec()),
{
    let out = q.norm2();
    proof {
        Quaternion::lemma_norm2_zero_iff_zero(q@);
        assert(q@.norm2_spec().eqv_spec(Scalar::from_int_spec(0)) == q@.eqv_spec(Quaternion::zero_spec()));
        assert(out@.eqv_spec(Scalar::from_int_spec(0)) == q@.eqv_spec(Quaternion::zero_spec()));
    }
    out
}

#[allow(dead_code)]
pub fn runtime_quaternion_norm2_scale(
    q: &RuntimeQuaternion,
    k: &RuntimeScalar,
) -> (pair: (RuntimeScalar, RuntimeScalar))
    ensures
        pair.0@ == q@.scale_spec(k@).norm2_spec(),
        pair.1@ == k@.mul_spec(k@).mul_spec(q@.norm2_spec()),
        pair.0@.eqv_spec(pair.1@),
{
    let qs = q.scale(k);
    let lhs = qs.norm2();
    let n = q.norm2();
    let kk = k.mul(k);
    let rhs = kk.mul(&n);
    proof {
        Quaternion::lemma_norm2_scale(q@, k@);
        assert(q@.scale_spec(k@).norm2_spec().eqv_spec(k@.mul_spec(k@).mul_spec(q@.norm2_spec())));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_norm2_mul(
    a: &RuntimeQuaternion,
    b: &RuntimeQuaternion,
) -> (pair: (RuntimeScalar, RuntimeScalar))
    ensures
        pair.0@ == a@.mul_spec(b@).norm2_spec(),
        pair.1@ == a@.norm2_spec().mul_spec(b@.norm2_spec()),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.mul(b);
    let lhs = ab.norm2();
    let na = a.norm2();
    let nb = b.norm2();
    let rhs = na.mul(&nb);
    proof {
        Quaternion::lemma_norm2_mul(a@, b@);
        assert(a@.mul_spec(b@).norm2_spec().eqv_spec(a@.norm2_spec().mul_spec(b@.norm2_spec())));
        assert(lhs@.eqv_spec(rhs@));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_quaternion_norm2_conjugate_invariant(q: &RuntimeQuaternion) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == q@.norm2_spec(),
        pair.1@ == q@.conjugate_spec().norm2_spec(),
        pair.0@.eqv_spec(pair.1@),
{
    let n = q.norm2();
    let qc = q.conjugate();
    let nc = qc.norm2();
    proof {
        Quaternion::lemma_norm2_conjugate_invariant(q@);
        assert(q@.conjugate_spec().norm2_spec().eqv_spec(q@.norm2_spec()));
        Scalar::lemma_eqv_symmetric(q@.conjugate_spec().norm2_spec(), q@.norm2_spec());
        assert(q@.norm2_spec().eqv_spec(q@.conjugate_spec().norm2_spec()));
        assert(n@.eqv_spec(nc@));
    }
    (n, nc)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_conjugate_right_real_norm2(q: &RuntimeQuaternion) -> (pair: (
    RuntimeQuaternion,
    RuntimeScalar,
))
    ensures
        pair.0@ == q@.mul_spec(q@.conjugate_spec()),
        pair.1@ == q@.norm2_spec(),
        pair.0@.eqv_spec(Quaternion::real_spec(pair.1@)),
{
    let qc = q.conjugate();
    let prod = q.mul(&qc);
    let n = q.norm2();
    proof {
        Quaternion::lemma_mul_conjugate_right_real_norm2(q@);
        assert(q@.mul_spec(q@.conjugate_spec()).eqv_spec(Quaternion::real_spec(q@.norm2_spec())));
        assert(prod@.eqv_spec(Quaternion::real_spec(n@)));
    }
    (prod, n)
}

#[allow(dead_code)]
pub fn runtime_quaternion_mul_conjugate_left_real_norm2(q: &RuntimeQuaternion) -> (pair: (
    RuntimeQuaternion,
    RuntimeScalar,
))
    ensures
        pair.0@ == q@.conjugate_spec().mul_spec(q@),
        pair.1@ == q@.norm2_spec(),
        pair.0@.eqv_spec(Quaternion::real_spec(pair.1@)),
{
    let qc = q.conjugate();
    let prod = qc.mul(q);
    let n = q.norm2();
    proof {
        Quaternion::lemma_mul_conjugate_left_real_norm2(q@);
        assert(q@.conjugate_spec().mul_spec(q@).eqv_spec(Quaternion::real_spec(q@.norm2_spec())));
        assert(prod@.eqv_spec(Quaternion::real_spec(n@)));
    }
    (prod, n)
}

#[allow(dead_code)]
pub fn runtime_quaternion_inverse_identities(
    q: &RuntimeQuaternion,
) -> (out: Option<(RuntimeQuaternion, RuntimeQuaternion, RuntimeQuaternion)>)
    ensures
        match out {
            Option::None => q@.norm2_spec().num <= 0,
            Option::Some(t) => {
                &&& t.0@ == q@.inverse_spec()
                &&& t.1@ == q@.mul_spec(t.0@)
                &&& t.2@ == t.0@.mul_spec(q@)
                &&& t.1@.eqv_spec(Quaternion::one_spec())
                &&& t.2@.eqv_spec(Quaternion::one_spec())
            },
        },
{
    let inv_opt = q.inverse();
    match inv_opt {
        Option::None => {
            proof {
                assert(!inv_opt.is_some());
                assert(!(q@.norm2_spec().num > 0));
                assert(q@.norm2_spec().num <= 0);
            }
            Option::None
        },
        Option::Some(inv) => {
            let right = q.mul(&inv);
            let left = inv.mul(q);
            proof {
                assert(inv@ == q@.inverse_spec());
                Quaternion::lemma_inverse_right(q@);
                Quaternion::lemma_inverse_left(q@);
                assert(q@.mul_spec(q@.inverse_spec()).eqv_spec(Quaternion::one_spec()));
                assert(q@.inverse_spec().mul_spec(q@).eqv_spec(Quaternion::one_spec()));
                assert(right@.eqv_spec(Quaternion::one_spec()));
                assert(left@.eqv_spec(Quaternion::one_spec()));
            }
            Option::Some((inv, right, left))
        },
    }
}

} // verus!
