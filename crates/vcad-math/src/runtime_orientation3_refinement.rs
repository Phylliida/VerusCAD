use crate::orientation3::{orient3d_spec, orientation3_spec, scale_point_from_origin3_spec, Orientation3};
use crate::runtime_orientation3::{self, RuntimeOrientation3};
use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
use crate::scalar::Scalar;
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

pub assume_specification[ runtime_orientation3::orientation3 ](
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (out: RuntimeOrientation3)
    ensures
        out@ == orientation3_spec(a@, b@, c@, d@),
;

pub assume_specification[ runtime_orientation3::scale_point_from_origin3 ](
    p: &RuntimePoint3,
    k: &RuntimeScalar,
) -> (out: RuntimePoint3)
    ensures
        out@ == scale_point_from_origin3_spec(p@, k@),
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

#[allow(dead_code)]
pub fn runtime_orientation3_swap_cd(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
) -> (pair: (RuntimeOrientation3, RuntimeOrientation3))
    ensures
        pair.0@ == orientation3_spec(a@, b@, c@, d@),
        pair.1@ == orientation3_spec(a@, b@, d@, c@),
        (pair.0@ is Positive) == (pair.1@ is Negative),
        (pair.0@ is Negative) == (pair.1@ is Positive),
        (pair.0@ is Coplanar) == (pair.1@ is Coplanar),
{
    let lhs = runtime_orientation3::orientation3(a, b, c, d);
    let rhs = runtime_orientation3::orientation3(a, b, d, c);
    proof {
        crate::orientation3::lemma_orientation3_spec_swap_cd(a@, b@, c@, d@);
        assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orientation3_spec(a@, b@, d@, c@) is Negative));
        assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orientation3_spec(a@, b@, d@, c@) is Positive));
        assert((orientation3_spec(a@, b@, c@, d@) is Coplanar) == (orientation3_spec(a@, b@, d@, c@) is Coplanar));
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_orientation3_scale_zero_coplanar(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    k: &RuntimeScalar,
) -> (out: RuntimeOrientation3)
    requires
        k@.eqv_spec(Scalar::from_int_spec(0)),
    ensures
        out@ == orientation3_spec(
            scale_point_from_origin3_spec(a@, k@),
            scale_point_from_origin3_spec(b@, k@),
            scale_point_from_origin3_spec(c@, k@),
            scale_point_from_origin3_spec(d@, k@),
        ),
        out@ is Coplanar,
{
    let sa = runtime_orientation3::scale_point_from_origin3(a, k);
    let sb = runtime_orientation3::scale_point_from_origin3(b, k);
    let sc = runtime_orientation3::scale_point_from_origin3(c, k);
    let sd = runtime_orientation3::scale_point_from_origin3(d, k);
    let out = runtime_orientation3::orientation3(&sa, &sb, &sc, &sd);
    proof {
        Scalar::lemma_eqv_zero_iff_num_zero(k@);
        assert(k@.eqv_spec(Scalar::from_int_spec(0)) == (k@.num == 0));
        assert(k@.num == 0);
        crate::orientation3::lemma_orientation3_spec_scale_zero_coplanar_strong(a@, b@, c@, d@, k@);
        assert(orientation3_spec(
            scale_point_from_origin3_spec(a@, k@),
            scale_point_from_origin3_spec(b@, k@),
            scale_point_from_origin3_spec(c@, k@),
            scale_point_from_origin3_spec(d@, k@),
        ) is Coplanar);
    }
    out
}

#[allow(dead_code)]
pub fn runtime_orientation3_scale_nonzero_behavior(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    k: &RuntimeScalar,
) -> (pair: (RuntimeOrientation3, RuntimeOrientation3))
    requires
        !k@.eqv_spec(Scalar::from_int_spec(0)),
    ensures
        pair.0@ == orientation3_spec(
            scale_point_from_origin3_spec(a@, k@),
            scale_point_from_origin3_spec(b@, k@),
            scale_point_from_origin3_spec(c@, k@),
            scale_point_from_origin3_spec(d@, k@),
        ),
        pair.1@ == orientation3_spec(a@, b@, c@, d@),
        (pair.0@ is Coplanar) == (pair.1@ is Coplanar),
        (k@.signum() == 1) ==> (pair.0@ == pair.1@),
        (k@.signum() == -1) ==> ((pair.0@ is Positive) == (pair.1@ is Negative)),
        (k@.signum() == -1) ==> ((pair.0@ is Negative) == (pair.1@ is Positive)),
        (k@.signum() == -1) ==> ((pair.0@ is Coplanar) == (pair.1@ is Coplanar)),
{
    let sa = runtime_orientation3::scale_point_from_origin3(a, k);
    let sb = runtime_orientation3::scale_point_from_origin3(b, k);
    let sc = runtime_orientation3::scale_point_from_origin3(c, k);
    let sd = runtime_orientation3::scale_point_from_origin3(d, k);
    let lhs = runtime_orientation3::orientation3(&sa, &sb, &sc, &sd);
    let rhs = runtime_orientation3::orientation3(a, b, c, d);
    proof {
        Scalar::lemma_eqv_zero_iff_num_zero(k@);
        assert(k@.eqv_spec(Scalar::from_int_spec(0)) == (k@.num == 0));
        assert(!k@.eqv_spec(Scalar::from_int_spec(0)));
        assert(!(k@.num == 0));
        assert(k@.num != 0);
        crate::orientation3::lemma_orientation3_spec_scale_nonzero_behavior_strong(a@, b@, c@, d@, k@);
        assert(
            (orientation3_spec(
                scale_point_from_origin3_spec(a@, k@),
                scale_point_from_origin3_spec(b@, k@),
                scale_point_from_origin3_spec(c@, k@),
                scale_point_from_origin3_spec(d@, k@),
            ) is Coplanar) == (orientation3_spec(a@, b@, c@, d@) is Coplanar)
        );
        if k@.signum() == 1 {
            assert(
                orientation3_spec(
                    scale_point_from_origin3_spec(a@, k@),
                    scale_point_from_origin3_spec(b@, k@),
                    scale_point_from_origin3_spec(c@, k@),
                    scale_point_from_origin3_spec(d@, k@),
                ) == orientation3_spec(a@, b@, c@, d@)
            );
        }
        if k@.signum() == -1 {
            assert(
                (orientation3_spec(
                    scale_point_from_origin3_spec(a@, k@),
                    scale_point_from_origin3_spec(b@, k@),
                    scale_point_from_origin3_spec(c@, k@),
                    scale_point_from_origin3_spec(d@, k@),
                ) is Positive) == (orientation3_spec(a@, b@, c@, d@) is Negative)
            );
            assert(
                (orientation3_spec(
                    scale_point_from_origin3_spec(a@, k@),
                    scale_point_from_origin3_spec(b@, k@),
                    scale_point_from_origin3_spec(c@, k@),
                    scale_point_from_origin3_spec(d@, k@),
                ) is Negative) == (orientation3_spec(a@, b@, c@, d@) is Positive)
            );
            assert(
                (orientation3_spec(
                    scale_point_from_origin3_spec(a@, k@),
                    scale_point_from_origin3_spec(b@, k@),
                    scale_point_from_origin3_spec(c@, k@),
                    scale_point_from_origin3_spec(d@, k@),
                ) is Coplanar) == (orientation3_spec(a@, b@, c@, d@) is Coplanar)
            );
        }
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_orientation3_degenerate_repeated_points(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (pair: (RuntimeOrientation3, RuntimeOrientation3))
    ensures
        pair.0@ == orientation3_spec(a@, a@, b@, c@),
        pair.1@ == orientation3_spec(a@, b@, c@, c@),
        pair.0@ is Coplanar,
        pair.1@ is Coplanar,
{
    let lhs = runtime_orientation3::orientation3(a, a, b, c);
    let rhs = runtime_orientation3::orientation3(a, b, c, c);
    proof {
        crate::orientation3::lemma_orientation3_spec_degenerate_repeated_points(a@, b@, c@);
        assert(orientation3_spec(a@, a@, b@, c@) is Coplanar);
        assert(orientation3_spec(a@, b@, c@, c@) is Coplanar);
    }
    (lhs, rhs)
}

} // verus!
