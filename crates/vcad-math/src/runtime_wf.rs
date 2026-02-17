use crate::runtime_point2::RuntimePoint2;
use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::RuntimeScalar;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
verus! {

pub open spec fn point2_wf3_spec(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
}

pub open spec fn point2_wf4_spec(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2, d: &RuntimePoint2) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
    &&& d.witness_wf_spec()
}

pub open spec fn point3_wf3_spec(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
}

pub open spec fn point3_wf4_spec(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
    &&& d.witness_wf_spec()
}

pub open spec fn point3_wf5_spec(
    a: &RuntimePoint3,
    b: &RuntimePoint3,
    c: &RuntimePoint3,
    d: &RuntimePoint3,
    e: &RuntimePoint3,
) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
    &&& d.witness_wf_spec()
    &&& e.witness_wf_spec()
}

pub open spec fn scalar_wf2_spec(a: &RuntimeScalar, b: &RuntimeScalar) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
}

pub open spec fn scalar_wf4_spec(a: &RuntimeScalar, b: &RuntimeScalar, c: &RuntimeScalar, d: &RuntimeScalar) -> bool {
    &&& a.witness_wf_spec()
    &&& b.witness_wf_spec()
    &&& c.witness_wf_spec()
    &&& d.witness_wf_spec()
}

} // verus!
