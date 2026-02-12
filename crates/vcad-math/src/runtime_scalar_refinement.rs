use crate::runtime_scalar::RuntimeScalar;
use crate::scalar::ScalarModel;
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

impl View for RuntimeScalar {
    type V = ScalarModel;

    uninterp spec fn view(&self) -> ScalarModel;
}

pub assume_specification[ RuntimeScalar::from_int ](value: i64) -> (out: RuntimeScalar)
    ensures
        out@ == ScalarModel::from_int_spec(value as int),
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

} // verus!
