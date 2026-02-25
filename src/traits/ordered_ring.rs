use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::partial_order::PartialOrder;

verus! {

/// Totally ordered commutative ring.
///
/// Extends `Ring + PartialOrder` with a total order (le, lt) compatible with
/// the ring operations: addition preserves order, and multiplication by a
/// non-negative element preserves order.
pub trait OrderedRing: Ring + PartialOrder {
    // ---- operations ----

    /// Strict less-than comparison.
    spec fn lt(self, other: Self) -> bool;

    // ---- axioms: total order ----

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
}

} // verus!
