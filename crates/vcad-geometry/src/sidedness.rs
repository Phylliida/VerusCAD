use crate::orientation_predicates::{orient3d_sign, orient3d_value};
use vcad_math::runtime_point3::RuntimePoint3;
use vcad_math::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use vcad_math::orientation3::{orient3d_spec, orientation3_spec};
#[cfg(verus_keep_ghost)]
use vcad_math::point3::Point3;
#[cfg(verus_keep_ghost)]
use vcad_math::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[cfg(not(verus_keep_ghost))]
pub fn point_above_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_sign(a, b, c, p) == 1
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_above_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == 1),
{
    orient3d_sign(a, b, c, p) == 1
}
}

#[cfg(not(verus_keep_ghost))]
pub fn point_below_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_sign(a, b, c, p) == -1
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_below_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == -1),
{
    orient3d_sign(a, b, c, p) == -1
}
}

#[cfg(not(verus_keep_ghost))]
pub fn point_on_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    orient3d_sign(a, b, c, p) == 0
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn point_on_plane(p: &RuntimePoint3, a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> (out: bool)
    ensures
        out == (orient3d_spec(a@, b@, c@, p@).signum() == 0),
{
    orient3d_sign(a, b, c, p) == 0
}
}

#[cfg(not(verus_keep_ghost))]
pub fn segment_crosses_plane_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> bool {
    let od = orient3d_sign(a, b, c, d);
    let oe = orient3d_sign(a, b, c, e);
    (od > 0 && oe < 0) || (od < 0 && oe > 0)
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn segment_crosses_plane_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: bool)
    ensures
        out == (((orientation3_spec(a@, b@, c@, d@) is Positive) && (orientation3_spec(a@, b@, c@, e@) is Negative))
            || ((orientation3_spec(a@, b@, c@, d@) is Negative) && (orientation3_spec(a@, b@, c@, e@) is Positive))),
{
    let od = orient3d_sign(a, b, c, d);
    let oe = orient3d_sign(a, b, c, e);
    let out = (od == 1 && oe == -1) || (od == -1 && oe == 1);
    proof {
        vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
        vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, e@);
        assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
        assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
        assert((orientation3_spec(a@, b@, c@, e@) is Positive) == (orient3d_spec(a@, b@, c@, e@).signum() == 1));
        assert((orientation3_spec(a@, b@, c@, e@) is Negative) == (orient3d_spec(a@, b@, c@, e@).signum() == -1));
    }
    out
}
}

#[cfg(not(verus_keep_ghost))]
pub fn segment_plane_intersection_parameter_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> Option<RuntimeScalar> {
    if !segment_crosses_plane_strict(d, e, a, b, c) {
        return None;
    }
    let od = orient3d_value(a, b, c, d);
    let oe = orient3d_value(a, b, c, e);
    let denom = od.sub(&oe); // od - oe
    let inv = denom.recip()?;
    Some(od.mul(&inv))
}

#[cfg(verus_keep_ghost)]
verus! {
pub fn segment_plane_intersection_parameter_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimeScalar>)
    ensures
        out.is_some() == (((orientation3_spec(a@, b@, c@, d@) is Positive) && (orientation3_spec(a@, b@, c@, e@) is Negative))
            || ((orientation3_spec(a@, b@, c@, d@) is Negative) && (orientation3_spec(a@, b@, c@, e@) is Positive))),
        match out {
            Option::None => true,
            Option::Some(t) => {
                let od = orient3d_spec(a@, b@, c@, d@);
                let oe = orient3d_spec(a@, b@, c@, e@);
                let den = od.sub_spec(oe);
                &&& t@.mul_spec(den).eqv_spec(od)
                &&& Scalar::from_int_spec(1).sub_spec(t@).mul_spec(den).eqv_spec(oe.neg_spec())
            },
        },
{
    let crosses = segment_crosses_plane_strict(d, e, a, b, c);
    if !crosses {
        return Option::None;
    }

    let od = orient3d_value(a, b, c, d);
    let oe = orient3d_value(a, b, c, e);
    let den = od.sub(&oe); // od - oe
    let inv_opt = den.recip();

    proof {
        vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, d@);
        vcad_math::orientation3::lemma_orientation3_spec_matches_predicates(a@, b@, c@, e@);

        assert(crosses);
        assert(crosses
            == (((orientation3_spec(a@, b@, c@, d@) is Positive)
                && (orientation3_spec(a@, b@, c@, e@) is Negative))
                || ((orientation3_spec(a@, b@, c@, d@) is Negative)
                && (orientation3_spec(a@, b@, c@, e@) is Positive))));

        assert((orientation3_spec(a@, b@, c@, d@) is Positive) == (orient3d_spec(a@, b@, c@, d@).signum() == 1));
        assert((orientation3_spec(a@, b@, c@, d@) is Negative) == (orient3d_spec(a@, b@, c@, d@).signum() == -1));
        assert((orientation3_spec(a@, b@, c@, e@) is Positive) == (orient3d_spec(a@, b@, c@, e@).signum() == 1));
        assert((orientation3_spec(a@, b@, c@, e@) is Negative) == (orient3d_spec(a@, b@, c@, e@).signum() == -1));
        assert(od@ == orient3d_spec(a@, b@, c@, d@));
        assert(oe@ == orient3d_spec(a@, b@, c@, e@));
        assert(den@ == od@.sub_spec(oe@));

        Scalar::lemma_sub_eqv_zero_iff_eqv(od@, oe@);
        if den@.eqv_spec(Scalar::from_int_spec(0)) {
            assert(od@.eqv_spec(oe@));
            Scalar::lemma_eqv_signum(od@, oe@);
            if (orientation3_spec(a@, b@, c@, d@) is Positive) && (orientation3_spec(a@, b@, c@, e@) is Negative) {
                assert(od@.signum() == 1);
                assert(oe@.signum() == -1);
            } else {
                assert((orientation3_spec(a@, b@, c@, d@) is Negative) && (orientation3_spec(a@, b@, c@, e@) is Positive));
                assert(od@.signum() == -1);
                assert(oe@.signum() == 1);
            }
            assert(od@.signum() == oe@.signum());
            assert(false);
        }
        assert(inv_opt.is_none() == den@.eqv_spec(Scalar::from_int_spec(0)));
        assert(!inv_opt.is_none());
    }

    match inv_opt {
        Option::None => {
            proof {
                assert(false);
            }
            Option::None
        }
        Option::Some(inv) => {
            let t = od.mul(&inv);
            proof {
                let one = Scalar::from_int_spec(1);

                assert(crosses
                    == (((orientation3_spec(a@, b@, c@, d@) is Positive)
                        && (orientation3_spec(a@, b@, c@, e@) is Negative))
                        || ((orientation3_spec(a@, b@, c@, d@) is Negative)
                        && (orientation3_spec(a@, b@, c@, e@) is Positive))));
                assert(crosses);
                assert(od@ == orient3d_spec(a@, b@, c@, d@));
                assert(oe@ == orient3d_spec(a@, b@, c@, e@));
                assert(den@ == od@.sub_spec(oe@));

                assert(inv_opt.is_some());
                assert(inv_opt.is_none() == den@.eqv_spec(Scalar::from_int_spec(0)));
                assert(!den@.eqv_spec(Scalar::from_int_spec(0)));
                assert(inv_opt == Option::Some(inv));
                assert(match inv_opt {
                    Option::None => true,
                    Option::Some(r) => {
                        &&& den@.mul_spec(r@).eqv_spec(one)
                        &&& r@.mul_spec(den@).eqv_spec(one)
                    }
                });
                assert(match Option::Some(inv) {
                    Option::None => true,
                    Option::Some(r) => {
                        &&& den@.mul_spec(r@).eqv_spec(one)
                        &&& r@.mul_spec(den@).eqv_spec(one)
                    }
                });
                assert(den@.mul_spec(inv@).eqv_spec(one));
                Scalar::lemma_mul_commutative(inv@, den@);
                assert(inv@.mul_spec(den@) == den@.mul_spec(inv@));

                assert(t@ == od@.mul_spec(inv@));
                Scalar::lemma_mul_associative(od@, inv@, den@);
                assert(od@.mul_spec(inv@).mul_spec(den@).eqv_spec(od@.mul_spec(inv@.mul_spec(den@))));
                assert(t@.mul_spec(den@) == od@.mul_spec(inv@).mul_spec(den@));
                assert(t@.mul_spec(den@).eqv_spec(od@.mul_spec(inv@.mul_spec(den@))));
                Scalar::lemma_eqv_reflexive(den@.mul_spec(inv@));
                assert(inv@.mul_spec(den@).eqv_spec(den@.mul_spec(inv@)));
                Scalar::lemma_eqv_mul_congruence_right(od@, inv@.mul_spec(den@), den@.mul_spec(inv@));
                assert(od@.mul_spec(inv@.mul_spec(den@)).eqv_spec(od@.mul_spec(den@.mul_spec(inv@))));
                Scalar::lemma_eqv_mul_congruence_right(od@, den@.mul_spec(inv@), one);
                assert(od@.mul_spec(den@.mul_spec(inv@)).eqv_spec(od@.mul_spec(one)));
                Scalar::lemma_mul_one_identity(od@);
                assert(od@.mul_spec(one) == od@);
                Scalar::lemma_eqv_transitive(
                    t@.mul_spec(den@),
                    od@.mul_spec(inv@.mul_spec(den@)),
                    od@.mul_spec(den@.mul_spec(inv@)),
                );
                Scalar::lemma_eqv_transitive(
                    t@.mul_spec(den@),
                    od@.mul_spec(den@.mul_spec(inv@)),
                    od@.mul_spec(one),
                );
                assert(t@.mul_spec(den@).eqv_spec(od@));

                Scalar::lemma_sub_mul_right(one, t@, den@);
                assert(one.sub_spec(t@).mul_spec(den@).eqv_spec(one.mul_spec(den@).sub_spec(t@.mul_spec(den@))));
                Scalar::lemma_mul_one_identity(den@);
                assert(one.mul_spec(den@) == den@);
                assert(one.mul_spec(den@).sub_spec(t@.mul_spec(den@)) == den@.sub_spec(t@.mul_spec(den@)));
                assert(one.sub_spec(t@).mul_spec(den@).eqv_spec(den@.sub_spec(t@.mul_spec(den@))));

                Scalar::lemma_eqv_reflexive(den@);
                Scalar::lemma_eqv_sub_congruence(den@, den@, t@.mul_spec(den@), od@);
                assert(den@.sub_spec(t@.mul_spec(den@)).eqv_spec(den@.sub_spec(od@)));
                Scalar::lemma_eqv_transitive(
                    one.sub_spec(t@).mul_spec(den@),
                    den@.sub_spec(t@.mul_spec(den@)),
                    den@.sub_spec(od@),
                );
                assert(one.sub_spec(t@).mul_spec(den@).eqv_spec(den@.sub_spec(od@)));

                Scalar::lemma_sub_is_add_neg(od@, oe@);
                assert(od@.sub_spec(oe@) == od@.add_spec(oe@.neg_spec()));
                assert(den@ == od@.add_spec(oe@.neg_spec()));
                assert(den@.sub_spec(od@) == od@.add_spec(oe@.neg_spec()).sub_spec(od@));
                Scalar::lemma_add_then_sub_cancel(od@, oe@.neg_spec());
                assert(od@.add_spec(oe@.neg_spec()).sub_spec(od@).eqv_spec(oe@.neg_spec()));
                Scalar::lemma_eqv_transitive(
                    den@.sub_spec(od@),
                    od@.add_spec(oe@.neg_spec()).sub_spec(od@),
                    oe@.neg_spec(),
                );
                assert(den@.sub_spec(od@).eqv_spec(oe@.neg_spec()));
                Scalar::lemma_eqv_transitive(
                    one.sub_spec(t@).mul_spec(den@),
                    den@.sub_spec(od@),
                    oe@.neg_spec(),
                );
                assert(one.sub_spec(t@).mul_spec(den@).eqv_spec(oe@.neg_spec()));
            }
            Option::Some(t)
        }
    }
}
}

#[cfg(not(verus_keep_ghost))]
pub fn segment_plane_intersection_point_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> Option<RuntimePoint3> {
    let t = segment_plane_intersection_parameter_strict(d, e, a, b, c)?;
    let dir = e.sub(d);
    let step = dir.scale(&t);
    Some(d.add_vec(&step))
}

#[cfg(verus_keep_ghost)]
verus! {
pub open spec fn segment_plane_t_valid_spec(t: Scalar, a: Point3, b: Point3, c: Point3, d: Point3, e: Point3) -> bool {
    let od = orient3d_spec(a, b, c, d);
    let oe = orient3d_spec(a, b, c, e);
    let den = od.sub_spec(oe);
    let one = Scalar::from_int_spec(1);
    &&& t.mul_spec(den).eqv_spec(od)
    &&& one.sub_spec(t).mul_spec(den).eqv_spec(oe.neg_spec())
}

pub open spec fn segment_plane_point_at_parameter_spec(p: Point3, t: Scalar, d: Point3, e: Point3) -> bool {
    p.eqv_spec(d.add_vec_spec(e.sub_spec(d).scale_spec(t)))
}

proof fn lemma_segment_plane_point_witness_from_t(
    p: Point3,
    t: Scalar,
    a: Point3,
    b: Point3,
    c: Point3,
    d: Point3,
    e: Point3,
)
    requires
        segment_plane_t_valid_spec(t, a, b, c, d, e),
        segment_plane_point_at_parameter_spec(p, t, d, e),
    ensures
        exists|tt: Scalar| {
            &&& segment_plane_t_valid_spec(tt, a, b, c, d, e)
            &&& #[trigger] segment_plane_point_at_parameter_spec(p, tt, d, e)
        },
{
    assert(exists|tt: Scalar| {
        &&& segment_plane_t_valid_spec(tt, a, b, c, d, e)
        &&& #[trigger] segment_plane_point_at_parameter_spec(p, tt, d, e)
    }) by {
        let tt = t;
    }
}

pub fn segment_plane_intersection_point_strict(
    d: &RuntimePoint3,
    e: &RuntimePoint3,
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
) -> (out: Option<RuntimePoint3>)
    ensures
        out.is_some() == (((orientation3_spec(a@, b@, c@, d@) is Positive) && (orientation3_spec(a@, b@, c@, e@) is Negative))
            || ((orientation3_spec(a@, b@, c@, d@) is Negative) && (orientation3_spec(a@, b@, c@, e@) is Positive))),
        match out {
            Option::None => true,
            Option::Some(p) => exists|t: Scalar| {
                &&& segment_plane_t_valid_spec(t, a@, b@, c@, d@, e@)
                &&& #[trigger] segment_plane_point_at_parameter_spec(p@, t, d@, e@)
            },
        },
{
    let t_opt = segment_plane_intersection_parameter_strict(d, e, a, b, c);
    match t_opt {
        Option::None => Option::None,
        Option::Some(t) => {
            let dir = e.sub(d);
            let step = dir.scale(&t);
            let p = d.add_vec(&step);
            let out = Option::Some(p);
            proof {
                assert(t_opt == Option::Some(t));
                assert(match Option::Some(t) {
                    Option::None => true,
                    Option::Some(tt) => {
                        let od = orient3d_spec(a@, b@, c@, d@);
                        let oe = orient3d_spec(a@, b@, c@, e@);
                        let den = od.sub_spec(oe);
                        let one = Scalar::from_int_spec(1);
                        &&& tt@.mul_spec(den).eqv_spec(od)
                        &&& one.sub_spec(tt@).mul_spec(den).eqv_spec(oe.neg_spec())
                    }
                });
                assert(segment_plane_t_valid_spec(t@, a@, b@, c@, d@, e@));
                assert(dir@ == e@.sub_spec(d@));
                assert(step@ == dir@.scale_spec(t@));
                assert(p@ == d@.add_vec_spec(step@));
                assert(p@ == d@.add_vec_spec(e@.sub_spec(d@).scale_spec(t@)));
                assert(segment_plane_point_at_parameter_spec(p@, t@, d@, e@));
                lemma_segment_plane_point_witness_from_t(p@, t@, a@, b@, c@, d@, e@);
                assert(out == Option::Some(p));
                assert(match out {
                    Option::None => true,
                    Option::Some(pp) => exists|tt: Scalar| {
                        &&& segment_plane_t_valid_spec(tt, a@, b@, c@, d@, e@)
                        &&& #[trigger] segment_plane_point_at_parameter_spec(pp@, tt, d@, e@)
                    },
                }) by {
                    match out {
                        Option::None => {
                            assert(false);
                        }
                        Option::Some(pp) => {
                            assert(pp == p);
                            lemma_segment_plane_point_witness_from_t(pp@, t@, a@, b@, c@, d@, e@);
                        }
                    }
                }
            }
            out
        }
    }
}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_crossing_and_t_on_simple_plane() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(0, 0, 1);
        let e = RuntimePoint3::from_ints(0, 0, -1);

        assert!(segment_crosses_plane_strict(&d, &e, &a, &b, &c));
        let t = segment_plane_intersection_parameter_strict(&d, &e, &a, &b, &c).unwrap();
        assert!(matches!(
            t.sign(),
            vcad_math::runtime_scalar::RuntimeSign::Positive
        ));

        let p = segment_plane_intersection_point_strict(&d, &e, &a, &b, &c).unwrap();
        assert_eq!(point_on_plane(&p, &a, &b, &c), true);
    }

    #[test]
    fn no_crossing_when_same_side() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(0, 0, 1);
        let e = RuntimePoint3::from_ints(0, 0, 2);

        assert!(!segment_crosses_plane_strict(&d, &e, &a, &b, &c));
        assert!(segment_plane_intersection_parameter_strict(&d, &e, &a, &b, &c).is_none());
    }
}
