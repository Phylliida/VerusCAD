use crate::runtime_point2::RuntimePoint2;
use crate::runtime_scalar::RuntimeScalar;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RuntimeOrientation {
    Cw,
    Collinear,
    Ccw,
}

pub fn orient2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeScalar {
    let ba = b.sub(a);
    let ca = c.sub(a);
    ba.cross(&ca)
}

pub fn scale_point_from_origin(p: &RuntimePoint2, k: &RuntimeScalar) -> RuntimePoint2 {
    RuntimePoint2::new(p.x().mul(k), p.y().mul(k))
}

pub fn orientation(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> RuntimeOrientation {
    match orient2d(a, b, c).signum_i8() {
        1 => RuntimeOrientation::Ccw,
        -1 => RuntimeOrientation::Cw,
        _ => RuntimeOrientation::Collinear,
    }
}
