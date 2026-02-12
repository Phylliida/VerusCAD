use crate::orientation::{orient2d_spec, orientation_spec, scale_point_from_origin_spec, Orientation};
use crate::runtime_orientation::{self, RuntimeOrientation};
use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec2::RuntimeVec2;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExRuntimeOrientation(RuntimeOrientation);

impl View for RuntimeOrientation {
    type V = Orientation;

    uninterp spec fn view(&self) -> Orientation;
}

pub assume_specification[ runtime_orientation::orient2d ](
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: RuntimeScalar)
    ensures
        out@ == orient2d_spec(a@, b@, c@),
;

pub assume_specification[ runtime_orientation::scale_point_from_origin ](
    p: &RuntimePoint2,
    k: &RuntimeScalar,
) -> (out: RuntimePoint2)
    ensures
        out@ == scale_point_from_origin_spec(p@, k@),
;

pub assume_specification[ runtime_orientation::orientation ](
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (out: RuntimeOrientation)
    ensures
        out@ == orientation_spec(a@, b@, c@),
;

#[allow(dead_code)]
pub fn runtime_orientation_swap_pair(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (pair: (
    RuntimeOrientation,
    RuntimeOrientation,
))
    ensures
        pair.0@ == orientation_spec(a@, b@, c@),
        pair.1@ == orientation_spec(a@, c@, b@),
        (pair.0@ is Ccw) == (pair.1@ is Cw),
        (pair.0@ is Cw) == (pair.1@ is Ccw),
        (pair.0@ is Collinear) == (pair.1@ is Collinear),
{
    let abc = runtime_orientation::orientation(a, b, c);
    let acb = runtime_orientation::orientation(a, c, b);
    proof {
        crate::orientation::lemma_orientation_spec_swap(a@, b@, c@);
        assert((orientation_spec(a@, b@, c@) is Ccw) == (orientation_spec(a@, c@, b@) is Cw));
        assert((orientation_spec(a@, b@, c@) is Cw) == (orientation_spec(a@, c@, b@) is Ccw));
        assert(
            (orientation_spec(a@, b@, c@) is Collinear)
                == (orientation_spec(a@, c@, b@) is Collinear)
        );
    }
    (abc, acb)
}

#[allow(dead_code)]
pub fn runtime_orient2d_cyclic_pair(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> (pair: (
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        pair.0@ == orient2d_spec(a@, b@, c@),
        pair.1@ == orient2d_spec(b@, c@, a@),
        pair.0@.eqv_spec(pair.1@),
{
    let abc = runtime_orientation::orient2d(a, b, c);
    let bca = runtime_orientation::orient2d(b, c, a);
    proof {
        crate::orientation::lemma_orient2d_cyclic_eqv(a@, b@, c@);
        assert(orient2d_spec(a@, b@, c@).eqv_spec(orient2d_spec(b@, c@, a@)));
        assert(abc@.eqv_spec(bca@));
    }
    (abc, bca)
}

#[allow(dead_code)]
pub fn runtime_orient2d_permutation_table(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
) -> (vals: (
    RuntimeScalar,
    RuntimeScalar,
    RuntimeScalar,
    RuntimeScalar,
    RuntimeScalar,
    RuntimeScalar,
))
    ensures
        vals.0@ == orient2d_spec(a@, b@, c@),
        vals.1@ == orient2d_spec(b@, c@, a@),
        vals.2@ == orient2d_spec(c@, a@, b@),
        vals.3@ == orient2d_spec(a@, c@, b@),
        vals.4@ == orient2d_spec(b@, a@, c@),
        vals.5@ == orient2d_spec(c@, b@, a@),
        vals.0@.eqv_spec(vals.1@),
        vals.0@.eqv_spec(vals.2@),
        vals.3@.eqv_spec(vals.0@.neg_spec()),
        vals.4@.eqv_spec(vals.0@.neg_spec()),
        vals.5@.eqv_spec(vals.0@.neg_spec()),
{
    let abc = runtime_orientation::orient2d(a, b, c);
    let bca = runtime_orientation::orient2d(b, c, a);
    let cab = runtime_orientation::orient2d(c, a, b);
    let acb = runtime_orientation::orient2d(a, c, b);
    let bac = runtime_orientation::orient2d(b, a, c);
    let cba = runtime_orientation::orient2d(c, b, a);
    proof {
        crate::orientation::lemma_orient2d_permutation_table(a@, b@, c@);
        assert(orient2d_spec(a@, b@, c@).eqv_spec(orient2d_spec(b@, c@, a@)));
        assert(orient2d_spec(a@, b@, c@).eqv_spec(orient2d_spec(c@, a@, b@)));
        assert(orient2d_spec(a@, c@, b@).eqv_spec(orient2d_spec(a@, b@, c@).neg_spec()));
        assert(orient2d_spec(b@, a@, c@).eqv_spec(orient2d_spec(a@, b@, c@).neg_spec()));
        assert(orient2d_spec(c@, b@, a@).eqv_spec(orient2d_spec(a@, b@, c@).neg_spec()));
        assert(abc@.eqv_spec(bca@));
        assert(abc@.eqv_spec(cab@));
        assert(acb@.eqv_spec(abc@.neg_spec()));
        assert(bac@.eqv_spec(abc@.neg_spec()));
        assert(cba@.eqv_spec(abc@.neg_spec()));
    }
    (abc, bca, cab, acb, bac, cba)
}

#[allow(dead_code)]
pub fn runtime_orientation_translation_invariant(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    t: &RuntimeVec2,
) -> (pair: (
    RuntimeOrientation,
    RuntimeOrientation,
))
    ensures
        pair.0@ == orientation_spec(a@.add_vec_spec(t@), b@.add_vec_spec(t@), c@.add_vec_spec(t@)),
        pair.1@ == orientation_spec(a@, b@, c@),
        pair.0@ == pair.1@,
{
    let at = a.add_vec(t);
    let bt = b.add_vec(t);
    let ct = c.add_vec(t);
    let lhs = runtime_orientation::orientation(&at, &bt, &ct);
    let rhs = runtime_orientation::orientation(a, b, c);
    proof {
        crate::orientation::lemma_orientation_spec_translation_invariant(a@, b@, c@, t@);
        assert(
            orientation_spec(a@.add_vec_spec(t@), b@.add_vec_spec(t@), c@.add_vec_spec(t@))
                == orientation_spec(a@, b@, c@)
        );
        assert(lhs@ == rhs@);
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_orientation_scale_nonzero_preserves(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    k: &RuntimeScalar,
) -> (pair: (
    RuntimeOrientation,
    RuntimeOrientation,
))
    requires
        k@.num != 0,
    ensures
        pair.0@ == orientation_spec(
            scale_point_from_origin_spec(a@, k@),
            scale_point_from_origin_spec(b@, k@),
            scale_point_from_origin_spec(c@, k@),
        ),
        pair.1@ == orientation_spec(a@, b@, c@),
        pair.0@ == pair.1@,
{
    let sa = runtime_orientation::scale_point_from_origin(a, k);
    let sb = runtime_orientation::scale_point_from_origin(b, k);
    let sc = runtime_orientation::scale_point_from_origin(c, k);
    let lhs = runtime_orientation::orientation(&sa, &sb, &sc);
    let rhs = runtime_orientation::orientation(a, b, c);
    proof {
        crate::orientation::lemma_orientation_spec_scale_nonzero_preserves_strong(a@, b@, c@, k@);
        assert(
            orientation_spec(
                scale_point_from_origin_spec(a@, k@),
                scale_point_from_origin_spec(b@, k@),
                scale_point_from_origin_spec(c@, k@),
            ) == orientation_spec(a@, b@, c@)
        );
        assert(lhs@ == rhs@);
    }
    (lhs, rhs)
}

#[allow(dead_code)]
pub fn runtime_orientation_scale_zero_collinear(
    a: &RuntimePoint2,
    b: &RuntimePoint2,
    c: &RuntimePoint2,
    k: &RuntimeScalar,
) -> (out: RuntimeOrientation)
    requires
        k@.num == 0,
    ensures
        out@ == orientation_spec(
            scale_point_from_origin_spec(a@, k@),
            scale_point_from_origin_spec(b@, k@),
            scale_point_from_origin_spec(c@, k@),
        ),
        out@ is Collinear,
{
    let sa = runtime_orientation::scale_point_from_origin(a, k);
    let sb = runtime_orientation::scale_point_from_origin(b, k);
    let sc = runtime_orientation::scale_point_from_origin(c, k);
    let out = runtime_orientation::orientation(&sa, &sb, &sc);
    proof {
        crate::orientation::lemma_orientation_spec_scale_zero_collinear_strong(a@, b@, c@, k@);
        assert(
            orientation_spec(
                scale_point_from_origin_spec(a@, k@),
                scale_point_from_origin_spec(b@, k@),
                scale_point_from_origin_spec(c@, k@),
            ) is Collinear
        );
        assert(out@ is Collinear);
    }
    out
}

} // verus!
