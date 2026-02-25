use vstd::prelude::*;
use crate::traits::additive_commutative_monoid::AdditiveCommutativeMonoid;

verus! {

/// Left identity: 0 + a ≡ a.
/// Derived from right identity + commutativity.
pub proof fn lemma_add_zero_left<M: AdditiveCommutativeMonoid>(a: M)
    ensures
        M::zero().add(a).eqv(a),
{
    M::axiom_add_commutative(M::zero(), a);
    M::axiom_add_zero_right(a);
    M::axiom_eqv_transitive(M::zero().add(a), a.add(M::zero()), a);
}

/// Addition respects equivalence on the right:
/// if b ≡ c then a + b ≡ a + c.
/// Derived from commutativity + left congruence.
pub proof fn lemma_add_congruence_right<M: AdditiveCommutativeMonoid>(a: M, b: M, c: M)
    requires
        b.eqv(c),
    ensures
        a.add(b).eqv(a.add(c)),
{
    // a + b ≡ b + a ≡ c + a ≡ a + c
    M::axiom_add_commutative(a, b);
    M::axiom_add_congruence_left(b, c, a);
    M::axiom_add_commutative(c, a);
    M::axiom_eqv_transitive(a.add(b), b.add(a), c.add(a));
    M::axiom_eqv_transitive(a.add(b), c.add(a), a.add(c));
}

/// Full addition congruence: if a1 ≡ a2 and b1 ≡ b2 then a1 + b1 ≡ a2 + b2.
pub proof fn lemma_add_congruence<M: AdditiveCommutativeMonoid>(a1: M, a2: M, b1: M, b2: M)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        a1.add(b1).eqv(a2.add(b2)),
{
    M::axiom_add_congruence_left(a1, a2, b1);
    lemma_add_congruence_right::<M>(a2, b1, b2);
    M::axiom_eqv_transitive(a1.add(b1), a2.add(b1), a2.add(b2));
}

} // verus!
