use vstd::prelude::*;
use crate::traits::ordered_ring::OrderedRing;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;

verus! {

/// Minimum of two elements.
pub open spec fn min<R: OrderedRing>(a: R, b: R) -> R {
    if a.le(b) { a } else { b }
}

/// Maximum of two elements.
pub open spec fn max<R: OrderedRing>(a: R, b: R) -> R {
    if a.le(b) { b } else { a }
}

/// min(a, b) ≤ a.
pub proof fn lemma_min_le_left<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(a),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, need a ≤ a
        R::axiom_le_reflexive(a);
    } else {
        // min = b, and b ≤ a from totality
    }
}

/// min(a, b) ≤ b.
pub proof fn lemma_min_le_right<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(b),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, a ≤ b given
    } else {
        // min = b, need b ≤ b
        R::axiom_le_reflexive(b);
    }
}

/// a ≤ max(a, b).
pub proof fn lemma_max_ge_left<R: OrderedRing>(a: R, b: R)
    ensures
        a.le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // max = b, a ≤ b given
    } else {
        // max = a, need a ≤ a
        R::axiom_le_reflexive(a);
    }
}

/// b ≤ max(a, b).
pub proof fn lemma_max_ge_right<R: OrderedRing>(a: R, b: R)
    ensures
        b.le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // max = b, need b ≤ b
        R::axiom_le_reflexive(b);
    } else {
        // max = a, and b ≤ a from totality
    }
}

/// min(a, b) ≡ min(b, a).
pub proof fn lemma_min_commutative<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).eqv(min::<R>(b, a)),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, a);

    if a.le(b) && b.le(a) {
        // min(a,b) = a, min(b,a) = b, and a ≡ b by antisymmetry
        R::axiom_le_antisymmetric(a, b);
    } else if a.le(b) && !b.le(a) {
        // min(a,b) = a, min(b,a) = a (since ¬(b≤a), b is not min)
        R::axiom_eqv_reflexive(a);
    } else if !a.le(b) && b.le(a) {
        // min(a,b) = b, min(b,a) = b
        R::axiom_eqv_reflexive(b);
    } else {
        // Impossible by totality, but if both fail:
        R::axiom_eqv_reflexive(a);
    }
}

/// max(a, b) ≡ max(b, a).
pub proof fn lemma_max_commutative<R: OrderedRing>(a: R, b: R)
    ensures
        max::<R>(a, b).eqv(max::<R>(b, a)),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, a);

    if a.le(b) && b.le(a) {
        // max(a,b) = b, max(b,a) = a, and a ≡ b
        R::axiom_le_antisymmetric(a, b);
        R::axiom_eqv_symmetric(a, b);
    } else if a.le(b) && !b.le(a) {
        // max(a,b) = b, max(b,a) = b
        R::axiom_eqv_reflexive(b);
    } else if !a.le(b) && b.le(a) {
        // max(a,b) = a, max(b,a) = a
        R::axiom_eqv_reflexive(a);
    } else {
        R::axiom_eqv_reflexive(a);
    }
}

/// min(a, b) ≤ max(a, b).
pub proof fn lemma_min_le_max<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, max = b, a ≤ b given
    } else {
        // min = b, max = a, b ≤ a from totality
    }
}

/// min(a, b) + max(a, b) ≡ a + b.
pub proof fn lemma_min_max_sum<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).add(max::<R>(a, b)).eqv(a.add(b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, max = b, a + b ≡ a + b
        R::axiom_eqv_reflexive(a.add(b));
    } else {
        // min = b, max = a, b + a ≡ a + b
        R::axiom_add_commutative(b, a);
        R::axiom_eqv_symmetric(a.add(b), b.add(a));
    }
}

/// min(a, a) ≡ a.
pub proof fn lemma_min_self<R: OrderedRing>(a: R)
    ensures
        min::<R>(a, a).eqv(a),
{
    R::axiom_le_reflexive(a);
    R::axiom_eqv_reflexive(a);
}

/// max(a, a) ≡ a.
pub proof fn lemma_max_self<R: OrderedRing>(a: R)
    ensures
        max::<R>(a, a).eqv(a),
{
    R::axiom_le_reflexive(a);
    R::axiom_eqv_reflexive(a);
}

} // verus!
