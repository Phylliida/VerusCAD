use crate::runtime_scalar::RuntimeScalar;
use crate::scalar::ScalarModel;
use rug::Integer;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExRuntimeScalar(RuntimeScalar);

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRugInteger(Integer);

impl View for RuntimeScalar {
    type V = ScalarModel;

    open spec fn view(&self) -> ScalarModel {
        self.model@
    }
}

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
