use crate::runtime_bigint_witness::RuntimeBigNatWitness;
use vstd::prelude::*;
use vstd::view::View;

verus! {

#[verifier::external_type_specification]
pub struct ExRuntimeBigNatWitness(RuntimeBigNatWitness);

impl View for RuntimeBigNatWitness {
    type V = nat;

    open spec fn view(&self) -> nat {
        self.model@
    }
}

} // verus!
