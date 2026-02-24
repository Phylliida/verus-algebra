use vstd::prelude::*;
use crate::traits::field::Field;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;

verus! {

/// Left multiplicative inverse: recip(a) * a ≡ 1 for nonzero a.
pub proof fn lemma_mul_recip_left<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.recip().mul(a).eqv(F::one()),
{
    F::axiom_mul_commutative(a.recip(), a);
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(a.recip().mul(a), a.mul(a.recip()), F::one());
}

/// Division by self: a / a ≡ 1 for nonzero a.
pub proof fn lemma_div_self<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.div(a).eqv(F::one()),
{
    F::axiom_div_is_mul_recip(a, a);
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(a.div(a), a.mul(a.recip()), F::one());
}

} // verus!
