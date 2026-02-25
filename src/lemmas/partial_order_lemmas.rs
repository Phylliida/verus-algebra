use vstd::prelude::*;
use crate::traits::partial_order::PartialOrder;

verus! {

/// Single-arg left congruence: a1 ≡ a2 and a1 ≤ b implies a2 ≤ b.
pub proof fn lemma_le_congruence_left<P: PartialOrder>(a1: P, a2: P, b: P)
    requires
        a1.eqv(a2),
        a1.le(b),
    ensures
        a2.le(b),
{
    P::axiom_eqv_reflexive(b);
    P::axiom_le_congruence(a1, a2, b, b);
}

/// Single-arg right congruence: a ≤ b1 and b1 ≡ b2 implies a ≤ b2.
pub proof fn lemma_le_congruence_right<P: PartialOrder>(a: P, b1: P, b2: P)
    requires
        b1.eqv(b2),
        a.le(b1),
    ensures
        a.le(b2),
{
    P::axiom_eqv_reflexive(a);
    P::axiom_le_congruence(a, a, b1, b2);
}

/// a ≡ b implies a ≤ b (from reflexivity + congruence).
pub proof fn lemma_le_eqv_implies_le<P: PartialOrder>(a: P, b: P)
    requires
        a.eqv(b),
    ensures
        a.le(b),
{
    P::axiom_le_reflexive(a);
    P::axiom_eqv_reflexive(a);
    P::axiom_le_congruence(a, a, a, b);
}

} // verus!
