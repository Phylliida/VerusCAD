use crate::runtime_scalar::RuntimeScalar;
use crate::runtime_vec3::RuntimeVec3;
#[cfg(verus_keep_ghost)]
use crate::quaternion::Quaternion;
#[cfg(verus_keep_ghost)]
use crate::scalar::Scalar;
#[cfg(verus_keep_ghost)]
use crate::vec3::Vec3;
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RuntimeQuaternion {
    pub w: RuntimeScalar,
    pub x: RuntimeScalar,
    pub y: RuntimeScalar,
    pub z: RuntimeScalar,
}

impl RuntimeQuaternion {
    #[cfg(not(verus_keep_ghost))]
    pub fn new(w: RuntimeScalar, x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> Self {
        Self { w, x, y, z }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn from_ints(w: i64, x: i64, y: i64, z: i64) -> Self {
        Self {
            w: RuntimeScalar::from_int(w),
            x: RuntimeScalar::from_int(x),
            y: RuntimeScalar::from_int(y),
            z: RuntimeScalar::from_int(z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn zero() -> Self {
        Self::from_ints(0, 0, 0, 0)
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn add(&self, rhs: &Self) -> Self {
        Self {
            w: self.w.add(&rhs.w),
            x: self.x.add(&rhs.x),
            y: self.y.add(&rhs.y),
            z: self.z.add(&rhs.z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn sub(&self, rhs: &Self) -> Self {
        Self {
            w: self.w.sub(&rhs.w),
            x: self.x.sub(&rhs.x),
            y: self.y.sub(&rhs.y),
            z: self.z.sub(&rhs.z),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn neg(&self) -> Self {
        Self {
            w: self.w.neg(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn scale(&self, k: &RuntimeScalar) -> Self {
        Self {
            w: self.w.mul(k),
            x: self.x.mul(k),
            y: self.y.mul(k),
            z: self.z.mul(k),
        }
    }

    #[cfg(not(verus_keep_ghost))]
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

    #[cfg(not(verus_keep_ghost))]
    pub fn conjugate(&self) -> Self {
        Self {
            w: self.w.clone(),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        }
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn norm2(&self) -> RuntimeScalar {
        let ww = self.w.mul(&self.w);
        let xx = self.x.mul(&self.x);
        let yy = self.y.mul(&self.y);
        let zz = self.z.mul(&self.z);
        ww.add(&xx).add(&yy).add(&zz)
    }

    #[cfg(not(verus_keep_ghost))]
    pub fn inverse(&self) -> Option<Self> {
        let n = self.norm2();
        let inv_n = n.recip()?;
        Some(self.conjugate().scale(&inv_n))
    }

    #[cfg(not(verus_keep_ghost))]
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

#[cfg(verus_keep_ghost)]
verus! {
impl RuntimeQuaternion {
    pub fn new(w: RuntimeScalar, x: RuntimeScalar, y: RuntimeScalar, z: RuntimeScalar) -> (out: Self)
        ensures
            out@ == (Quaternion { w: w@, x: x@, y: y@, z: z@ }),
    {
        RuntimeQuaternion { w, x, y, z }
    }

    pub fn from_ints(w: i64, x: i64, y: i64, z: i64) -> (out: Self)
        ensures
            out@ == Quaternion::from_ints_spec(w as int, x as int, y as int, z as int),
    {
        let sw = RuntimeScalar::from_int(w);
        let sx = RuntimeScalar::from_int(x);
        let sy = RuntimeScalar::from_int(y);
        let sz = RuntimeScalar::from_int(z);
        let out = Self::new(sw, sx, sy, sz);
        proof {
            assert(out@ == Quaternion { w: sw@, x: sx@, y: sy@, z: sz@ });
            assert(sw@ == Scalar::from_int_spec(w as int));
            assert(sx@ == Scalar::from_int_spec(x as int));
            assert(sy@ == Scalar::from_int_spec(y as int));
            assert(sz@ == Scalar::from_int_spec(z as int));
            assert(out@ == Quaternion::from_ints_spec(w as int, x as int, y as int, z as int));
        }
        out
    }

    pub fn zero() -> (out: Self)
        ensures
            out@ == Quaternion::zero_spec(),
    {
        let out = Self::from_ints(0, 0, 0, 0);
        proof {
            assert(out@ == Quaternion::from_ints_spec(0, 0, 0, 0));
            assert(Quaternion::zero_spec() == Quaternion::from_ints_spec(0, 0, 0, 0));
        }
        out
    }

    pub fn one() -> (out: Self)
        ensures
            out@ == Quaternion::one_spec(),
    {
        let out = Self::from_ints(1, 0, 0, 0);
        proof {
            assert(out@ == Quaternion::from_ints_spec(1, 0, 0, 0));
            assert(Quaternion::one_spec() == Quaternion::from_ints_spec(1, 0, 0, 0));
        }
        out
    }

    pub fn add(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.add_spec(rhs@),
    {
        let w = self.w.add(&rhs.w);
        let x = self.x.add(&rhs.x);
        let y = self.y.add(&rhs.y);
        let z = self.z.add(&rhs.z);
        let out = Self { w, x, y, z };
        proof {
            assert(
                out@ == Quaternion {
                    w: self@.w.add_spec(rhs@.w),
                    x: self@.x.add_spec(rhs@.x),
                    y: self@.y.add_spec(rhs@.y),
                    z: self@.z.add_spec(rhs@.z),
                }
            );
            assert(out@ == self@.add_spec(rhs@));
        }
        out
    }

    pub fn sub(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.sub_spec(rhs@),
    {
        let w = self.w.sub(&rhs.w);
        let x = self.x.sub(&rhs.x);
        let y = self.y.sub(&rhs.y);
        let z = self.z.sub(&rhs.z);
        let out = Self { w, x, y, z };
        proof {
            assert(
                out@ == Quaternion {
                    w: self@.w.sub_spec(rhs@.w),
                    x: self@.x.sub_spec(rhs@.x),
                    y: self@.y.sub_spec(rhs@.y),
                    z: self@.z.sub_spec(rhs@.z),
                }
            );
            assert(out@ == self@.sub_spec(rhs@));
        }
        out
    }

    pub fn neg(&self) -> (out: Self)
        ensures
            out@ == self@.neg_spec(),
    {
        let w = self.w.neg();
        let x = self.x.neg();
        let y = self.y.neg();
        let z = self.z.neg();
        let out = Self { w, x, y, z };
        proof {
            assert(
                out@ == Quaternion {
                    w: self@.w.neg_spec(),
                    x: self@.x.neg_spec(),
                    y: self@.y.neg_spec(),
                    z: self@.z.neg_spec(),
                }
            );
            assert(out@ == self@.neg_spec());
        }
        out
    }

    pub fn scale(&self, k: &RuntimeScalar) -> (out: Self)
        ensures
            out@ == self@.scale_spec(k@),
    {
        let w = self.w.mul(k);
        let x = self.x.mul(k);
        let y = self.y.mul(k);
        let z = self.z.mul(k);
        let out = Self { w, x, y, z };
        proof {
            assert(
                out@ == Quaternion {
                    w: self@.w.mul_spec(k@),
                    x: self@.x.mul_spec(k@),
                    y: self@.y.mul_spec(k@),
                    z: self@.z.mul_spec(k@),
                }
            );
            assert(out@ == self@.scale_spec(k@));
        }
        out
    }

    pub fn mul(&self, rhs: &Self) -> (out: Self)
        ensures
            out@ == self@.mul_spec(rhs@),
    {
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

        let out = Self { w, x, y, z };
        proof {
            assert(ww@ == self@.w.mul_spec(rhs@.w));
            assert(xx@ == self@.x.mul_spec(rhs@.x));
            assert(yy@ == self@.y.mul_spec(rhs@.y));
            assert(zz@ == self@.z.mul_spec(rhs@.z));
            assert(w@ == ww@.sub_spec(xx@).sub_spec(yy@).sub_spec(zz@));

            assert(x0@ == self@.w.mul_spec(rhs@.x));
            assert(x1@ == self@.x.mul_spec(rhs@.w));
            assert(x2@ == self@.y.mul_spec(rhs@.z));
            assert(x3@ == self@.z.mul_spec(rhs@.y));
            assert(x@ == x0@.add_spec(x1@).add_spec(x2@).sub_spec(x3@));

            assert(y0@ == self@.w.mul_spec(rhs@.y));
            assert(y1@ == self@.x.mul_spec(rhs@.z));
            assert(y2@ == self@.y.mul_spec(rhs@.w));
            assert(y3@ == self@.z.mul_spec(rhs@.x));
            assert(y@ == y0@.sub_spec(y1@).add_spec(y2@).add_spec(y3@));

            assert(z0@ == self@.w.mul_spec(rhs@.z));
            assert(z1@ == self@.x.mul_spec(rhs@.y));
            assert(z2@ == self@.y.mul_spec(rhs@.x));
            assert(z3@ == self@.z.mul_spec(rhs@.w));
            assert(z@ == z0@.add_spec(z1@).sub_spec(z2@).add_spec(z3@));
            assert(out@ == self@.mul_spec(rhs@));
        }
        out
    }

    pub fn conjugate(&self) -> (out: Self)
        ensures
            out@ == self@.conjugate_spec(),
    {
        let z = RuntimeScalar::from_int(0);
        let out = Self {
            w: self.w.add(&z),
            x: self.x.neg(),
            y: self.y.neg(),
            z: self.z.neg(),
        };
        proof {
            Scalar::lemma_add_zero_identity(self@.w);
            assert(z@ == Scalar::from_int_spec(0));
            assert(out@.w == self@.w.add_spec(z@));
            assert(out@.w == self@.w);
            assert(out@ == Quaternion {
                w: self@.w,
                x: self@.x.neg_spec(),
                y: self@.y.neg_spec(),
                z: self@.z.neg_spec(),
            });
            assert(out@ == self@.conjugate_spec());
        }
        out
    }

    pub fn norm2(&self) -> (out: RuntimeScalar)
        ensures
            out@ == self@.norm2_spec(),
    {
        let ww = self.w.mul(&self.w);
        let xx = self.x.mul(&self.x);
        let yy = self.y.mul(&self.y);
        let zz = self.z.mul(&self.z);
        let out = ww.add(&xx).add(&yy).add(&zz);
        proof {
            assert(ww@ == self@.w.mul_spec(self@.w));
            assert(xx@ == self@.x.mul_spec(self@.x));
            assert(yy@ == self@.y.mul_spec(self@.y));
            assert(zz@ == self@.z.mul_spec(self@.z));
            assert(out@ == ww@.add_spec(xx@).add_spec(yy@).add_spec(zz@));
            assert(out@ == self@.norm2_spec());
        }
        out
    }

    pub fn inverse(&self) -> (out: Option<Self>)
        ensures
            out.is_some() == !self@.norm2_spec().eqv_spec(Scalar::from_int_spec(0)),
            match out {
                Option::None => true,
                Option::Some(inv) => inv@.eqv_spec(self@.inverse_spec()),
            },
    {
        let n = self.norm2();
        let inv_n_opt = n.recip();
        match inv_n_opt {
            Option::None => {
                proof {
                    assert(!inv_n_opt.is_some());
                    assert(inv_n_opt.is_none() == n@.eqv_spec(Scalar::from_int_spec(0)));
                    assert(n@.eqv_spec(Scalar::from_int_spec(0)));
                    assert(n@ == self@.norm2_spec());
                    assert(self@.norm2_spec().eqv_spec(Scalar::from_int_spec(0)));
                }
                Option::None
            },
            Option::Some(inv_n) => {
                let inv = self.conjugate().scale(&inv_n);
                proof {
                    let q = self@;
                    let qc = q.conjugate_spec();
                    let one = Quaternion::one_spec();
                    let z = Scalar::from_int_spec(0);
                    let inv_rt = qc.scale_spec(inv_n@);
                    let inv_spec = q.inverse_spec();

                    assert(inv_n_opt.is_some());
                    assert(!n@.eqv_spec(Scalar::from_int_spec(0)));
                    assert(n@ == q.norm2_spec());
                    assert(!q.norm2_spec().eqv_spec(Scalar::from_int_spec(0)));

                    assert(inv@ == inv_rt);

                    Quaternion::lemma_mul_scale_right(q, qc, inv_n@);
                    assert(q.mul_spec(inv_rt).eqv_spec(q.mul_spec(qc).scale_spec(inv_n@)));
                    Quaternion::lemma_mul_conjugate_right_real_norm2(q);
                    assert(q.mul_spec(qc).eqv_spec(Quaternion::real_spec(q.norm2_spec())));
                    Quaternion::lemma_scale_eqv_congruence(
                        q.mul_spec(qc),
                        Quaternion::real_spec(q.norm2_spec()),
                        inv_n@,
                    );
                    let rs_r = Quaternion::real_spec(q.norm2_spec()).scale_spec(inv_n@);
                    assert(q.mul_spec(qc).scale_spec(inv_n@).eqv_spec(rs_r));
                    assert(rs_r.w == q.norm2_spec().mul_spec(inv_n@));
                    assert(rs_r.x == z.mul_spec(inv_n@));
                    assert(rs_r.y == z.mul_spec(inv_n@));
                    assert(rs_r.z == z.mul_spec(inv_n@));
                    assert(n@.mul_spec(inv_n@).eqv_spec(Scalar::from_int_spec(1)));
                    assert(q.norm2_spec().mul_spec(inv_n@).eqv_spec(Scalar::from_int_spec(1)));
                    Scalar::lemma_mul_zero(inv_n@);
                    assert(z.mul_spec(inv_n@).eqv_spec(z));
                    assert(one.w == Scalar::from_int_spec(1));
                    assert(one.x == z);
                    assert(one.y == z);
                    assert(one.z == z);
                    assert(rs_r.w.eqv_spec(one.w));
                    assert(rs_r.x.eqv_spec(one.x));
                    assert(rs_r.y.eqv_spec(one.y));
                    assert(rs_r.z.eqv_spec(one.z));
                    Quaternion::lemma_eqv_from_components(rs_r, one);
                    assert(rs_r.eqv_spec(one));
                    Quaternion::lemma_eqv_transitive(q.mul_spec(inv_rt), q.mul_spec(qc).scale_spec(inv_n@), rs_r);
                    Quaternion::lemma_eqv_transitive(q.mul_spec(inv_rt), rs_r, one);
                    assert(q.mul_spec(inv_rt).eqv_spec(one));

                    Quaternion::lemma_mul_scale_left(qc, q, inv_n@);
                    assert(inv_rt.mul_spec(q).eqv_spec(qc.mul_spec(q).scale_spec(inv_n@)));
                    Quaternion::lemma_mul_conjugate_left_real_norm2(q);
                    assert(qc.mul_spec(q).eqv_spec(Quaternion::real_spec(q.norm2_spec())));
                    Quaternion::lemma_scale_eqv_congruence(
                        qc.mul_spec(q),
                        Quaternion::real_spec(q.norm2_spec()),
                        inv_n@,
                    );
                    let rs_l = Quaternion::real_spec(q.norm2_spec()).scale_spec(inv_n@);
                    assert(qc.mul_spec(q).scale_spec(inv_n@).eqv_spec(rs_l));
                    assert(rs_l.w == q.norm2_spec().mul_spec(inv_n@));
                    assert(rs_l.x == z.mul_spec(inv_n@));
                    assert(rs_l.y == z.mul_spec(inv_n@));
                    assert(rs_l.z == z.mul_spec(inv_n@));
                    assert(rs_l.w.eqv_spec(one.w));
                    assert(rs_l.x.eqv_spec(one.x));
                    assert(rs_l.y.eqv_spec(one.y));
                    assert(rs_l.z.eqv_spec(one.z));
                    Quaternion::lemma_eqv_from_components(rs_l, one);
                    assert(rs_l.eqv_spec(one));
                    Quaternion::lemma_eqv_transitive(inv_rt.mul_spec(q), qc.mul_spec(q).scale_spec(inv_n@), rs_l);
                    Quaternion::lemma_eqv_transitive(inv_rt.mul_spec(q), rs_l, one);
                    assert(inv_rt.mul_spec(q).eqv_spec(one));

                    Quaternion::lemma_inverse_right(q);
                    Quaternion::lemma_inverse_left(q);
                    assert(q.mul_spec(inv_spec).eqv_spec(one));
                    assert(inv_spec.mul_spec(q).eqv_spec(one));

                    Quaternion::lemma_mul_one_identity(inv_rt);
                    assert(inv_rt.mul_spec(one).eqv_spec(inv_rt));
                    Quaternion::lemma_eqv_symmetric(inv_rt.mul_spec(one), inv_rt);
                    assert(inv_rt.eqv_spec(inv_rt.mul_spec(one)));
                    Quaternion::lemma_mul_eqv_congruence_right(inv_rt, one, q.mul_spec(inv_spec));
                    assert(inv_rt.mul_spec(one).eqv_spec(inv_rt.mul_spec(q.mul_spec(inv_spec))));
                    Quaternion::lemma_mul_associative(inv_rt, q, inv_spec);
                    assert(inv_rt.mul_spec(q.mul_spec(inv_spec)).eqv_spec(inv_rt.mul_spec(q).mul_spec(inv_spec)));
                    Quaternion::lemma_mul_eqv_congruence_left(inv_rt.mul_spec(q), one, inv_spec);
                    assert(inv_rt.mul_spec(q).mul_spec(inv_spec).eqv_spec(one.mul_spec(inv_spec)));
                    Quaternion::lemma_mul_one_identity(inv_spec);
                    assert(one.mul_spec(inv_spec).eqv_spec(inv_spec));
                    Quaternion::lemma_eqv_transitive(inv_rt, inv_rt.mul_spec(one), inv_rt.mul_spec(q.mul_spec(inv_spec)));
                    Quaternion::lemma_eqv_transitive(inv_rt, inv_rt.mul_spec(q.mul_spec(inv_spec)), inv_rt.mul_spec(q).mul_spec(inv_spec));
                    Quaternion::lemma_eqv_transitive(inv_rt, inv_rt.mul_spec(q).mul_spec(inv_spec), one.mul_spec(inv_spec));
                    Quaternion::lemma_eqv_transitive(inv_rt, one.mul_spec(inv_spec), inv_spec);
                    assert(inv_rt.eqv_spec(inv_spec));

                    Quaternion::lemma_eqv_reflexive(inv@);
                    assert(inv@.eqv_spec(inv_rt));
                    Quaternion::lemma_eqv_transitive(inv@, inv_rt, inv_spec);
                    assert(inv@.eqv_spec(q.inverse_spec()));
                }
                Option::Some(inv)
            },
        }
    }

    pub fn rotate_vec3(&self, v: &RuntimeVec3) -> (out: RuntimeVec3)
        ensures
            out@ == Quaternion::rotate_vec3_spec(v@, self@),
    {
        let zero = RuntimeScalar::from_int(0);
        let vx = v.x.add(&zero);
        let vy = v.y.add(&zero);
        let vz = v.z.add(&zero);
        let pure_v = RuntimeQuaternion::new(
            zero,
            vx,
            vy,
            vz,
        );
        let qc = self.conjugate();
        let tmp = self.mul(&pure_v);
        let rotated = tmp.mul(&qc);
        let out = RuntimeVec3::new(rotated.x, rotated.y, rotated.z);
        proof {
            Scalar::lemma_add_zero_identity(v@.x);
            Scalar::lemma_add_zero_identity(v@.y);
            Scalar::lemma_add_zero_identity(v@.z);
            assert(zero@ == Scalar::from_int_spec(0));
            assert(vx@ == v@.x.add_spec(zero@));
            assert(vy@ == v@.y.add_spec(zero@));
            assert(vz@ == v@.z.add_spec(zero@));
            assert(vx@ == v@.x);
            assert(vy@ == v@.y);
            assert(vz@ == v@.z);
            assert(pure_v@ == Quaternion::pure_vec3_spec(v@));
            assert(qc@ == self@.conjugate_spec());
            assert(tmp@ == self@.mul_spec(pure_v@));
            assert(rotated@ == tmp@.mul_spec(qc@));
            assert(rotated@ == Quaternion::rotate_quat_spec(v@, self@));
            assert(out@ == Vec3 { x: rotated@.x, y: rotated@.y, z: rotated@.z });
            assert(out@ == Quaternion::rotate_quat_spec(v@, self@).vector_part_spec());
            assert(out@ == Quaternion::rotate_vec3_spec(v@, self@));
        }
        out
    }
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
