use crate::orientation3::{orient3d_spec, orientation3_spec, scale_point_from_origin3_spec, Orientation3};
use crate::runtime_orientation3::{self, RuntimeOrientation3};
use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeOrientation3(RuntimeOrientation3);

impl View for RuntimeOrientation3 {
    type V = Orientation3;

    uninterp spec fn view(&self) -> Orientation3;
}

pub assume_specification[ runtime_orientation3::orient3d ](
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeScalar)
    ensures
        out@ == orient3d_spec(a@, b@, c@, d@),
;

pub assume_specification[ runtime_orientation3::scale_point_from_origin3 ](
    p: &RuntimePoint3,
    k: &RuntimeScalar,
) -> (out: RuntimePoint3)
    ensures
        out@ == scale_point_from_origin3_spec(p@, k@),
;

pub assume_specification[ runtime_orientation3::orientation3 ](
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeOrientation3)
    ensures
        out@ == orientation3_spec(a@, b@, c@, d@),
;

#[allow(dead_code)]
pub fn runtime_orientation3_translation_invariant(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    t: &RuntimeVec3,
) -> (pair: (
    RuntimeOrientation3,
    RuntimeOrientation3,
))
    ensures
        pair.0@ == orientation3_spec(
            a@.add_vec_spec(t@),
            b@.add_vec_spec(t@),
            c@.add_vec_spec(t@),
            d@.add_vec_spec(t@),
        ),
        pair.1@ == orientation3_spec(a@, b@, c@, d@),
        pair.0@ == pair.1@,
{
    let at = a.add_vec(t);
    let bt = b.add_vec(t);
    let ct = c.add_vec(t);
    let dt = d.add_vec(t);
    let lhs = runtime_orientation3::orientation3(&at, &bt, &ct, &dt);
    let rhs = runtime_orientation3::orientation3(a, b, c, d);
    proof {
        crate::orientation3::lemma_orientation3_spec_translation_invariant(a@, b@, c@, d@, t@);
        assert(
            orientation3_spec(
                a@.add_vec_spec(t@),
                b@.add_vec_spec(t@),
                c@.add_vec_spec(t@),
                d@.add_vec_spec(t@),
            ) == orientation3_spec(a@, b@, c@, d@)
        );
        assert(lhs@ == rhs@);
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_orientation3_exclusive(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeOrientation3)
    ensures
        out@ == orientation3_spec(a@, b@, c@, d@),
        (out@ is Positive) || (out@ is Negative) || (out@ is Coplanar),
{
    let out = runtime_orientation3::orientation3(a, b, c, d);
    proof {
        crate::orientation3::lemma_orientation3_spec_exclusive(a@, b@, c@, d@);
        assert((orientation3_spec(a@, b@, c@, d@) is Positive)
            || (orientation3_spec(a@, b@, c@, d@) is Negative)
            || (orientation3_spec(a@, b@, c@, d@) is Coplanar));
    }
    out
}

} // verus!
