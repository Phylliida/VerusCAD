use crate::runtime_scalar::RuntimeScalar;
use crate::scalar::ScalarModel;
use rug::Integer;
use vstd::prelude::*;
use vstd::view::View;

verus! {

/// Verus-facing model view for the executable `RuntimeScalar`.
///
/// This is the trusted boundary for the `rug` backend:
/// runtime method bodies execute in Rust, while these contracts let proofs
/// reason about their mathematical `ScalarModel` behavior.
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeScalar(RuntimeScalar);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRugInteger(Integer);

/// Trusted model projection for `rug::Integer` at the runtime/proof boundary.
pub uninterp spec fn integer_view(i: Integer) -> int;

impl View for RuntimeScalar {
    type V = ScalarModel;

    uninterp spec fn view(&self) -> ScalarModel;
}

pub assume_specification[ RuntimeScalar::from_int ](value: i64) -> (out: RuntimeScalar)
    ensures
        out@ == ScalarModel::from_int_spec(value as int),
;

pub assume_specification[ RuntimeScalar::from_fraction ](
    num: Integer,
    den: Integer,
) -> (out: Option<RuntimeScalar>)
    ensures
        out.is_none() == (integer_view(den) == 0),
        match out {
            Option::None => true,
            Option::Some(s) => {
                &&& integer_view(den) != 0
                &&& s@.as_real() == integer_view(num) as real / integer_view(den) as real
            },
        },
;

pub assume_specification[ RuntimeScalar::add ](
    this: &RuntimeScalar,
    rhs: &RuntimeScalar,
) -> (out: RuntimeScalar)
    ensures
        out@ == this@.add_spec(rhs@),
;

pub assume_specification[ RuntimeScalar::sub ](
    this: &RuntimeScalar,
    rhs: &RuntimeScalar,
) -> (out: RuntimeScalar)
    ensures
        out@ == this@.sub_spec(rhs@),
;

pub assume_specification[ RuntimeScalar::mul ](
    this: &RuntimeScalar,
    rhs: &RuntimeScalar,
) -> (out: RuntimeScalar)
    ensures
        out@ == this@.mul_spec(rhs@),
;

pub assume_specification[ RuntimeScalar::neg ](this: &RuntimeScalar) -> (out: RuntimeScalar)
    ensures
        out@ == this@.neg_spec(),
;

pub assume_specification[ RuntimeScalar::normalize ](this: &RuntimeScalar) -> (out: RuntimeScalar)
    ensures
        out@.eqv_spec(this@),
        out@.canonical_sign_spec(),
;

/// Regression wrapper: verifies runtime `add` contracts are strong enough
/// to recover commutativity in model space.
#[allow(dead_code)]
pub fn runtime_add_pair_commutative(a: &RuntimeScalar, b: &RuntimeScalar) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == a@.add_spec(b@),
        pair.1@ == b@.add_spec(a@),
        pair.0@.eqv_spec(pair.1@),
{
    let ab = a.add(b);
    let ba = b.add(a);
    proof {
        ScalarModel::lemma_add_commutative(a@, b@);
        assert(a@.add_spec(b@).eqv_spec(b@.add_spec(a@)));
        assert(ab@.eqv_spec(ba@));
    }
    (ab, ba)
}

/// Regression wrapper: verifies runtime `mul` contracts recover
/// commutativity at model level.
#[allow(dead_code)]
pub fn runtime_mul_pair_commutative(a: &RuntimeScalar, b: &RuntimeScalar) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == a@.mul_spec(b@),
        pair.1@ == b@.mul_spec(a@),
        pair.0@ == pair.1@,
{
    let ab = a.mul(b);
    let ba = b.mul(a);
    proof {
        ScalarModel::lemma_mul_commutative(a@, b@);
        assert(a@.mul_spec(b@) == b@.mul_spec(a@));
        assert(ab@ == ba@);
    }
    (ab, ba)
}

/// Regression wrapper: verifies runtime `sub` + `neg` + `add` contracts
/// compose to the model theorem `sub == add(neg)`.
#[allow(dead_code)]
pub fn runtime_sub_matches_add_neg(a: &RuntimeScalar, b: &RuntimeScalar) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
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
        ScalarModel::lemma_sub_is_add_neg(a@, b@);
        assert(a@.sub_spec(b@) == a@.add_spec(b@.neg_spec()));
        assert(sub@ == add_neg@);
    }
    (sub, add_neg)
}

/// Regression wrapper: runtime `normalize` is semantically identity
/// on the model, while guaranteeing canonical sign placement.
#[allow(dead_code)]
pub fn runtime_normalize_is_eqv_identity(a: &RuntimeScalar) -> (out: RuntimeScalar)
    ensures
        out@.eqv_spec(a@),
        out@.canonical_sign_spec(),
{
    let n = a.normalize();
    n
}

} // verus!
