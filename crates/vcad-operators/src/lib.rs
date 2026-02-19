pub fn placeholder() {}

#[cfg(feature = "verus-proofs")]
mod verified_stub {
    use vstd::prelude::*;

    verus! {
        pub proof fn phase6_stub_verifies() {
            assert(true);
        }
    }
}
