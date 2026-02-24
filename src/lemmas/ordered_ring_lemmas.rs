use vstd::prelude::*;
use crate::traits::ordered_ring::OrderedRing;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;

verus! {

/// Strict order is irreflexive: !(a < a).
pub proof fn lemma_lt_irreflexive<R: OrderedRing>(a: R)
    ensures
        !a.lt(a),
{
    R::axiom_lt_iff_le_and_not_eqv(a, a);
    R::axiom_eqv_reflexive(a);
}

/// Strict order is asymmetric: a < b implies !(b < a).
pub proof fn lemma_lt_asymmetric<R: OrderedRing>(a: R, b: R)
    requires
        a.lt(b),
    ensures
        !b.lt(a),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_lt_iff_le_and_not_eqv(b, a);
    // a < b means a <= b and !a.eqv(b)
    // Suppose b < a, then b <= a.
    // a <= b and b <= a implies a.eqv(b) by antisymmetry. Contradiction.
    if b.lt(a) {
        R::axiom_le_antisymmetric(a, b);
    }
}

/// Strict order is transitive: a < b && b < c implies a < c.
pub proof fn lemma_lt_transitive<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.lt(b),
        b.lt(c),
    ensures
        a.lt(c),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_lt_iff_le_and_not_eqv(b, c);
    R::axiom_lt_iff_le_and_not_eqv(a, c);
    R::axiom_le_transitive(a, b, c);
    // a <= c. Need to show !a.eqv(c).
    // If a.eqv(c), then since a <= b and b <= c = a, we get b <= a.
    // Combined with a <= b, antisymmetry gives a.eqv(b). But a < b says !a.eqv(b). Contradiction.
    if a.eqv(c) {
        // a ≡ c, so c ≡ a (symmetric)
        R::axiom_eqv_symmetric(a, c);
        // b <= c and c ≡ a, so b <= a (congruence)
        R::axiom_eqv_reflexive(b);
        R::axiom_le_congruence(b, b, c, a);
        // a <= b and b <= a, so a ≡ b (antisymmetry)
        R::axiom_le_antisymmetric(a, b);
        // But a < b means !a.eqv(b). Contradiction.
    }
}

/// a <= b implies a + c <= b + c (restated for convenience; same as axiom).
pub proof fn lemma_le_add_compatible<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.le(b),
    ensures
        a.add(c).le(b.add(c)),
{
    R::axiom_le_add_monotone(a, b, c);
}

/// a < b implies a + c < b + c.
pub proof fn lemma_lt_add_compatible<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.lt(b),
    ensures
        a.add(c).lt(b.add(c)),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_le_add_monotone(a, b, c);
    R::axiom_lt_iff_le_and_not_eqv(a.add(c), b.add(c));
    // Need: !(a+c).eqv(b+c)
    // If (a+c).eqv(b+c), then by cancellation a.eqv(b), contradicting a < b.
    if a.add(c).eqv(b.add(c)) {
        lemma_add_right_cancel::<R>(a, b, c);
    }
}

/// 0 <= a and 0 <= b implies 0 <= a * b.
pub proof fn lemma_nonneg_mul_nonneg<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().le(a),
        R::zero().le(b),
    ensures
        R::zero().le(a.mul(b)),
{
    // 0 <= a and 0 <= b, so 0*b <= a*b by monotonicity
    R::axiom_le_mul_nonneg_monotone(R::zero(), a, b);
    // 0*b ≡ 0
    R::axiom_mul_zero_right(R::zero());
    lemma_mul_zero_left::<R>(b);
    // 0 <= 0*b <= a*b, and 0 ≡ 0*b, so 0 <= a*b
    R::axiom_eqv_reflexive(a.mul(b));
    R::axiom_eqv_symmetric(R::zero().mul(b), R::zero());
    R::axiom_le_congruence(R::zero().mul(b), R::zero(), a.mul(b), a.mul(b));
}

/// 0 <= a * a (squares are non-negative).
pub proof fn lemma_square_nonneg<R: OrderedRing>(a: R)
    ensures
        R::zero().le(a.mul(a)),
{
    R::axiom_le_total(R::zero(), a);
    if R::zero().le(a) {
        lemma_nonneg_mul_nonneg::<R>(a, a);
    } else {
        // a <= 0, so 0 <= -a
        // We need: a <= 0 implies 0 <= -a
        // a <= 0 means a + (-a) <= 0 + (-a)
        R::axiom_le_add_monotone(a, R::zero(), a.neg());
        // a + (-a) ≡ 0
        R::axiom_add_inverse_right(a);
        // 0 + (-a) ≡ -a
        lemma_add_zero_left::<R>(a.neg());
        // So: 0 ≡ a + (-a) <= 0 + (-a) ≡ -a
        // i.e. 0 <= -a
        R::axiom_eqv_symmetric(a.add(a.neg()), R::zero());
        R::axiom_eqv_reflexive(R::zero().add(a.neg()));
        R::axiom_le_congruence(
            a.add(a.neg()), R::zero(),
            R::zero().add(a.neg()), R::zero().add(a.neg()),
        );
        R::axiom_eqv_reflexive(R::zero());
        R::axiom_le_congruence(
            R::zero(), R::zero(),
            R::zero().add(a.neg()), a.neg(),
        );
        // Now 0 <= -a
        // So 0 <= (-a)*(-a) ≡ a*a
        lemma_nonneg_mul_nonneg::<R>(a.neg(), a.neg());
        lemma_neg_mul_neg::<R>(a, a);
        // (-a)*(-a) ≡ a*a and 0 <= (-a)*(-a)
        R::axiom_eqv_reflexive(R::zero());
        R::axiom_le_congruence(
            R::zero(), R::zero(),
            a.neg().mul(a.neg()), a.mul(a),
        );
    }
}

} // verus!
