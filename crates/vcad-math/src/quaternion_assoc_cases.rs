use crate::quaternion::Quaternion;
use vstd::prelude::*;

verus! {

impl Quaternion {
    pub proof fn lemma_basis_assoc_case_0_0_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_0_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_0_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_0_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(0), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_1_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_1_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_1_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_1_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(1), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_2_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_2_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_2_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_2_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(2), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_3_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_3_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_3_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_0_3_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(0), Self::basis_spec(3), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_0_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_0_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_0_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_0_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(0), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_1_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_1_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_1_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_1_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(1), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_2_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_2_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_2_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_2_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(2), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_3_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_3_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_3_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_1_3_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(1), Self::basis_spec(3), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_0_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_0_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_0_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_0_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(0), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_1_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_1_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_1_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_1_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(1), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_2_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_2_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_2_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_2_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(2), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_3_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_3_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_3_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_2_3_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(2), Self::basis_spec(3), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_0_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_0_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_0_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_0_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(0), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_1_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_1_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_1_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_1_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(1), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_2_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_2_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_2_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_2_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(2), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_3_0()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(0)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(0))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_3_1()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(1)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(1))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_3_2()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(2)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(2))) by (compute);
    }

    pub proof fn lemma_basis_assoc_case_3_3_3()
        ensures
            Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(3)),
    {
        assert(Self::assoc_instance_spec(Self::basis_spec(3), Self::basis_spec(3), Self::basis_spec(3))) by (compute);
    }

    pub proof fn lemma_basis_assoc_indices(i: int, j: int, k: int)
        requires
            0 <= i < 4,
            0 <= j < 4,
            0 <= k < 4,
        ensures
            Self::assoc_instance_spec(Self::basis_spec(i), Self::basis_spec(j), Self::basis_spec(k)),
    {
        if i == 0 {
            if j == 0 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_0_0_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_0_0_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_0_0_2();
                } else {
                    Self::lemma_basis_assoc_case_0_0_3();
                }
            } else if j == 1 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_0_1_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_0_1_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_0_1_2();
                } else {
                    Self::lemma_basis_assoc_case_0_1_3();
                }
            } else if j == 2 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_0_2_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_0_2_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_0_2_2();
                } else {
                    Self::lemma_basis_assoc_case_0_2_3();
                }
            } else {
                if k == 0 {
                    Self::lemma_basis_assoc_case_0_3_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_0_3_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_0_3_2();
                } else {
                    Self::lemma_basis_assoc_case_0_3_3();
                }
            }
        } else if i == 1 {
            if j == 0 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_1_0_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_1_0_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_1_0_2();
                } else {
                    Self::lemma_basis_assoc_case_1_0_3();
                }
            } else if j == 1 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_1_1_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_1_1_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_1_1_2();
                } else {
                    Self::lemma_basis_assoc_case_1_1_3();
                }
            } else if j == 2 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_1_2_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_1_2_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_1_2_2();
                } else {
                    Self::lemma_basis_assoc_case_1_2_3();
                }
            } else {
                if k == 0 {
                    Self::lemma_basis_assoc_case_1_3_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_1_3_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_1_3_2();
                } else {
                    Self::lemma_basis_assoc_case_1_3_3();
                }
            }
        } else if i == 2 {
            if j == 0 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_2_0_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_2_0_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_2_0_2();
                } else {
                    Self::lemma_basis_assoc_case_2_0_3();
                }
            } else if j == 1 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_2_1_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_2_1_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_2_1_2();
                } else {
                    Self::lemma_basis_assoc_case_2_1_3();
                }
            } else if j == 2 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_2_2_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_2_2_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_2_2_2();
                } else {
                    Self::lemma_basis_assoc_case_2_2_3();
                }
            } else {
                if k == 0 {
                    Self::lemma_basis_assoc_case_2_3_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_2_3_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_2_3_2();
                } else {
                    Self::lemma_basis_assoc_case_2_3_3();
                }
            }
        } else {
            if j == 0 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_3_0_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_3_0_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_3_0_2();
                } else {
                    Self::lemma_basis_assoc_case_3_0_3();
                }
            } else if j == 1 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_3_1_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_3_1_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_3_1_2();
                } else {
                    Self::lemma_basis_assoc_case_3_1_3();
                }
            } else if j == 2 {
                if k == 0 {
                    Self::lemma_basis_assoc_case_3_2_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_3_2_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_3_2_2();
                } else {
                    Self::lemma_basis_assoc_case_3_2_3();
                }
            } else {
                if k == 0 {
                    Self::lemma_basis_assoc_case_3_3_0();
                } else if k == 1 {
                    Self::lemma_basis_assoc_case_3_3_1();
                } else if k == 2 {
                    Self::lemma_basis_assoc_case_3_3_2();
                } else {
                    Self::lemma_basis_assoc_case_3_3_3();
                }
            }
        }

        assert(Self::assoc_instance_spec(Self::basis_spec(i), Self::basis_spec(j), Self::basis_spec(k)));
    }
}

} // verus!
