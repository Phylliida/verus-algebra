use vstd::prelude::*;
use crate::traits::ring::Ring;

verus! {

/// Totally ordered commutative ring.
///
/// Extends `Ring` with a total order (le, lt) compatible with the ring
/// operations: addition preserves order, and multiplication by a non-negative
/// element preserves order.
pub trait OrderedRing: Ring {
    // ---- operations ----

    /// Less-than-or-equal comparison.
    spec fn le(self, other: Self) -> bool;

    /// Strict less-than comparison.
    spec fn lt(self, other: Self) -> bool;

    // ---- axioms: total order ----

    /// Reflexivity: a <= a.
    proof fn axiom_le_reflexive(a: Self)
        ensures
            a.le(a),
    ;

    /// Antisymmetry: a <= b && b <= a implies a ≡ b.
    proof fn axiom_le_antisymmetric(a: Self, b: Self)
        requires
            a.le(b),
            b.le(a),
        ensures
            a.eqv(b),
    ;

    /// Transitivity: a <= b && b <= c implies a <= c.
    proof fn axiom_le_transitive(a: Self, b: Self, c: Self)
        requires
            a.le(b),
            b.le(c),
        ensures
            a.le(c),
    ;

    /// Totality: a <= b || b <= a.
    proof fn axiom_le_total(a: Self, b: Self)
        ensures
            a.le(b) || b.le(a),
    ;

    /// lt is equivalent to le and not eqv.
    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self)
        ensures
            a.lt(b) == (a.le(b) && !a.eqv(b)),
    ;

    // ---- axioms: compatibility with ring operations ----

    /// Addition preserves order: a <= b implies a + c <= b + c.
    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self)
        requires
            a.le(b),
        ensures
            a.add(c).le(b.add(c)),
    ;

    /// Multiplication by non-negative preserves order: a <= b && 0 <= c implies a*c <= b*c.
    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self)
        requires
            a.le(b),
            Self::zero().le(c),
        ensures
            a.mul(c).le(b.mul(c)),
    ;

    // ---- axioms: congruence ----

    /// Order respects equivalence.
    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv(a2),
            b1.eqv(b2),
            a1.le(b1),
        ensures
            a2.le(b2),
    ;
}

} // verus!
