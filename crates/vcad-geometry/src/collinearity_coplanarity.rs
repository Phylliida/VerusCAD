use crate::orientation_predicates::{orient2d_value, orient3d_value};
use vcad_math::runtime_point2::RuntimePoint2;
use vcad_math::runtime_point3::RuntimePoint3;

pub fn collinear2d(a: &RuntimePoint2, b: &RuntimePoint2, c: &RuntimePoint2) -> bool {
    orient2d_value(a, b, c).signum_i8() == 0
}

pub fn collinear3d(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3) -> bool {
    let ba = b.sub(a);
    let ca = c.sub(a);
    let cross = ba.cross(&ca);
    cross.x().signum_i8() == 0 && cross.y().signum_i8() == 0 && cross.z().signum_i8() == 0
}

pub fn coplanar(a: &RuntimePoint3, b: &RuntimePoint3, c: &RuntimePoint3, d: &RuntimePoint3) -> bool {
    orient3d_value(a, b, c, d).signum_i8() == 0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn collinear2d_basic() {
        let a = RuntimePoint2::from_ints(0, 0);
        let b = RuntimePoint2::from_ints(1, 1);
        let c = RuntimePoint2::from_ints(2, 2);
        assert!(collinear2d(&a, &b, &c));
    }

    #[test]
    fn coplanar_basic() {
        let a = RuntimePoint3::from_ints(0, 0, 0);
        let b = RuntimePoint3::from_ints(1, 0, 0);
        let c = RuntimePoint3::from_ints(0, 1, 0);
        let d = RuntimePoint3::from_ints(2, 3, 0);
        assert!(coplanar(&a, &b, &c, &d));
    }
}
