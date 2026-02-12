use crate::runtime_point3::RuntimePoint3;
use crate::runtime_scalar::RuntimeScalar;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeOrientation3 {
    Negative,
    Coplanar,
    Positive,
}

pub fn orient3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> RuntimeScalar {
    let ba = b.sub(a);
    let ca = c.sub(a);
    let da = d.sub(a);
    let cad = ca.cross(&da);
    ba.dot(&cad)
}

pub fn scale_point_from_origin3(p: &RuntimePoint3, k: &RuntimeScalar) -> RuntimePoint3 {
    RuntimePoint3::new(p.x().mul(k), p.y().mul(k), p.z().mul(k))
}

pub fn orientation3(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> RuntimeOrientation3 {
    match orient3d(a, b, c, d).signum_i8() {
        1 => RuntimeOrientation3::Positive,
        -1 => RuntimeOrientation3::Negative,
        _ => RuntimeOrientation3::Coplanar,
    }
}
