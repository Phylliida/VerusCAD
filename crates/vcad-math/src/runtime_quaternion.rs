use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeQuaternion {
    w: RuntimeScalar,
    x: RuntimeScalar,
    y: RuntimeScalar,
    z: RuntimeScalar,
}

impl RuntimeQuaternion {
    pub fn new(w: RuntimeScalar, x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> Self {
        Self { w, x, y, z }
    }

    pub fn from_ints(w: i64, x: i64, y: i64, z: i64) -> Self {
        Self {
            w: RuntimeScalar::from_int(w),
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
        }
    }

    pub fn zero() -> Self {
        Self::from_ints(0, 0, 0, 0)
    }

    pub fn one() -> Self {
        Self::from_ints(1, 0, 0, 0)
    }

    pub fn w(&self) -> &RuntimeScalar {
        &self.w
    }

    pub fn x(&self) -> &RuntimeScalar {
        &self.x
    }

    pub fn y(&self) -> &RuntimeScalar {
        &self.y
    }

    pub fn z(&self) -> &RuntimeScalar {
        &self.z
    }

    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            w: self.w.add(&rhs.w),
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            w: self.w.sub(&rhs.w),
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
        }
    }

    pub fn neg(&self) -> Self {
        Self {
            w: self.w.neg(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            w: self.w.mul(k),
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let ww = self.w.mul(&rhs.w);
        let xx = self.x.mul(&rhs.x);
        let yy = self.y.mul(&rhs.y);
        let zz = self.z.mul(&rhs.z);
        let w = ww.sub(&xx).sub(&yy).sub(&zz);

        let x0 = self.w.mul(&rhs.x);
        let x1 = self.x.mul(&rhs.w);
        let x2 = self.y.mul(&rhs.z);
        let x3 = self.z.mul(&rhs.y);
        let x = x0.add(&x1).add(&x2).sub(&x3);

        let y0 = self.w.mul(&rhs.y);
        let y1 = self.x.mul(&rhs.z);
        let y2 = self.y.mul(&rhs.w);
        let y3 = self.z.mul(&rhs.x);
        let y = y0.sub(&y1).add(&y2).add(&y3);

        let z0 = self.w.mul(&rhs.z);
        let z1 = self.x.mul(&rhs.y);
        let z2 = self.y.mul(&rhs.x);
        let z3 = self.z.mul(&rhs.w);
        let z = z0.add(&z1).sub(&z2).add(&z3);

        Self { w, x, y, z }
    }

    pub fn conjugate(&self) -> Self {
        Self {
            w: self.w.clone(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    pub fn norm2(&self) -> RuntimeScalar {
        let ww = self.w.mul(&self.w);
        let xx = self.x.mul(&self.x);
        let yy = self.y.mul(&self.y);
        let zz = self.z.mul(&self.z);
        ww.add(&xx).add(&yy).add(&zz)
    }

    pub fn inverse(&self) -> Option<Self> {
        let n = self.norm2();
        let inv_n = n.recip()?;
        Some(self.conjugate().scale(&inv_n))
    }

    pub fn rotate_vec3(&self, v: &RuntimeVec3) -> RuntimeVec3 {
        let pure_v = RuntimeQuaternion::new(
            RuntimeScalar::from_int(0),
            v.x().clone(),
            v.y().clone(),
            v.z().clone(),
        );
        let qc = self.conjugate();
        let tmp = self.mul(&pure_v);
        let rotated = tmp.mul(&qc);
        RuntimeVec3::new(rotated.x().clone(), rotated.y().clone(), rotated.z().clone())
    }
}

#[cfg(test)]
mod tests {
    use super::RuntimeQuaternion;

    fn small_quaternions() -> Vec<RuntimeQuaternion> {
        let vals = [-1, 0, 1];
        let mut out = Vec::new();
        for &w in &vals {
            for &x in &vals {
                for &y in &vals {
                    for &z in &vals {
                        out.push(RuntimeQuaternion::from_ints(w, x, y, z));
                    }
                }
            }
        }
        out
    }

    #[test]
    fn multiplication_is_associative_on_small_integer_grid() {
        let qs = small_quaternions();
        for a in &qs {
            for b in &qs {
                for c in &qs {
                    let lhs = a.mul(b).mul(c);
                    let rhs = a.mul(&b.mul(c));
                    assert_eq!(lhs, rhs);
                }
            }
        }
    }

    #[test]
    fn multiplication_distributes_over_addition_on_small_integer_grid() {
        let qs = small_quaternions();
        for a in &qs {
            for b in &qs {
                for c in &qs {
                    let left_lhs = a.add(b).mul(c);
                    let left_rhs = a.mul(c).add(&b.mul(c));
                    assert_eq!(left_lhs, left_rhs);

                    let right_lhs = a.mul(&b.add(c));
                    let right_rhs = a.mul(b).add(&a.mul(c));
                    assert_eq!(right_lhs, right_rhs);
                }
            }
        }
    }
}
