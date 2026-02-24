use vstd::prelude::*;
use crate::traits::equivalence::Equivalence;

verus! {

/// Abelian group under addition with a compatible equivalence relation.
///
/// Provides zero, add, neg, and sub (defaulted to add + neg). Implementors
/// must prove the standard group axioms and that operations respect `eqv`.
pub trait AdditiveGroup: Equivalence {
    // ---- operations ----

    /// The additive identity element.
    spec fn zero() -> Self;

    /// Addition of two elements.
    spec fn add(self, other: Self) -> Self;

    /// Additive inverse (negation).
    spec fn neg(self) -> Self;

    /// Subtraction, defined as `self + (-other)`.
    /// Implementors may override with a more efficient definition, but must
    /// prove it equivalent via `axiom_sub_is_add_neg`.
    spec fn sub(self, other: Self) -> Self;

    // ---- axioms: group laws ----

    /// Commutativity: a + b ≡ b + a.
    proof fn axiom_add_commutative(a: Self, b: Self)
        ensures
            a.add(b).eqv(b.add(a)),
    ;

    /// Associativity: (a + b) + c ≡ a + (b + c).
    proof fn axiom_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add(b).add(c).eqv(a.add(b.add(c))),
    ;

    /// Right identity: a + 0 ≡ a.
    proof fn axiom_add_zero_right(a: Self)
        ensures
            a.add(Self::zero()).eqv(a),
    ;

    /// Right inverse: a + (-a) ≡ 0.
    proof fn axiom_add_inverse_right(a: Self)
        ensures
            a.add(a.neg()).eqv(Self::zero()),
    ;

    /// Subtraction is addition of the negation.
    proof fn axiom_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub(b).eqv(a.add(b.neg())),
    ;

    // ---- axioms: congruence ----

    /// Addition respects equivalence on the left.
    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv(b),
        ensures
            a.add(c).eqv(b.add(c)),
    ;

    /// Negation respects equivalence.
    proof fn axiom_neg_congruence(a: Self, b: Self)
        requires
            a.eqv(b),
        ensures
            a.neg().eqv(b.neg()),
    ;
}

} // verus!
