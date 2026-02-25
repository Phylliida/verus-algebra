use vstd::prelude::*;
use crate::traits::field::OrderedField;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;

verus! {

/// 0 < a and 0 < b implies 0 < a*b.
pub proof fn lemma_mul_pos_pos<F: OrderedField>(a: F, b: F)
    requires
        F::zero().lt(a),
        F::zero().lt(b),
    ensures
        F::zero().lt(a.mul(b)),
{
    // 0 < a implies 0 ≤ a
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
    // 0 ≤ a*b
    lemma_nonneg_mul_nonneg::<F>(a, b);
    // Need: a*b ≢ 0
    // If a*b ≡ 0, then recip(b)*(a*b) ≡ 0 but also ≡ a, so a ≡ 0. Contradiction.
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
    F::axiom_eqv_symmetric(F::zero(), a.mul(b));
    if a.mul(b).eqv(F::zero()) {
        // a*b ≡ 0 and a ≢ 0 and b ≢ 0, but nonzero_product says a*b ≢ 0
        F::axiom_eqv_symmetric(F::zero(), a);
        F::axiom_eqv_symmetric(F::zero(), b);
        lemma_nonzero_product::<F>(a, b);
    }
}

/// a < 0 and b < 0 implies 0 < a*b.
pub proof fn lemma_mul_neg_neg<F: OrderedField>(a: F, b: F)
    requires
        a.lt(F::zero()),
        b.lt(F::zero()),
    ensures
        F::zero().lt(a.mul(b)),
{
    // a < 0 implies 0 < -a
    lemma_lt_neg_flip::<F>(a, F::zero());
    lemma_neg_zero::<F>();
    // -0 < -a, and -0 ≡ 0, so 0 < -a
    F::axiom_lt_iff_le_and_not_eqv(F::zero().neg(), a.neg());
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    lemma_le_congruence_left::<F>(F::zero().neg(), F::zero(), a.neg());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.neg());
    // Need !0.eqv(-a)
    if F::zero().eqv(a.neg()) {
        // 0 ≡ -a implies -0 ≡ -(-a) implies 0 ≡ a
        F::axiom_neg_congruence(F::zero(), a.neg());
        lemma_neg_involution::<F>(a);
        F::axiom_eqv_transitive(F::zero().neg(), a.neg().neg(), a);
        F::axiom_eqv_transitive(F::zero(), F::zero().neg(), a);
        // But a < 0 means !a.eqv(0)
        F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
        F::axiom_eqv_symmetric(F::zero(), a);
    }

    // Similarly 0 < -b
    lemma_lt_neg_flip::<F>(b, F::zero());
    F::axiom_lt_iff_le_and_not_eqv(F::zero().neg(), b.neg());
    lemma_le_congruence_left::<F>(F::zero().neg(), F::zero(), b.neg());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b.neg());
    if F::zero().eqv(b.neg()) {
        F::axiom_neg_congruence(F::zero(), b.neg());
        lemma_neg_involution::<F>(b);
        F::axiom_eqv_transitive(F::zero().neg(), b.neg().neg(), b);
        F::axiom_eqv_transitive(F::zero(), F::zero().neg(), b);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(F::zero(), b);
    }

    // 0 < (-a)*(-b)
    lemma_mul_pos_pos::<F>(a.neg(), b.neg());
    // (-a)*(-b) ≡ a*b
    lemma_neg_mul_neg::<F>(a, b);
    // 0 < a*b (by congruence on the right of <)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.neg().mul(b.neg()));
    lemma_le_congruence_right::<F>(F::zero(), a.neg().mul(b.neg()), a.mul(b));
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
    F::axiom_eqv_symmetric(F::zero(), a.mul(b));
    if F::zero().eqv(a.mul(b)) {
        // 0 ≡ a*b, then 0 ≡ (-a)*(-b) since a*b ≡ (-a)*(-b)
        F::axiom_eqv_symmetric(a.neg().mul(b.neg()), a.mul(b));
        F::axiom_eqv_transitive(F::zero(), a.mul(b), a.neg().mul(b.neg()));
    }
}

/// 0 < a and b < 0 implies a*b < 0.
pub proof fn lemma_mul_pos_neg<F: OrderedField>(a: F, b: F)
    requires
        F::zero().lt(a),
        b.lt(F::zero()),
    ensures
        a.mul(b).lt(F::zero()),
{
    // b < 0 implies 0 < -b
    lemma_lt_neg_flip::<F>(b, F::zero());
    lemma_neg_zero::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero().neg(), b.neg());
    F::axiom_eqv_symmetric(F::zero().neg(), F::zero());
    lemma_le_congruence_left::<F>(F::zero().neg(), F::zero(), b.neg());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b.neg());
    if F::zero().eqv(b.neg()) {
        F::axiom_neg_congruence(F::zero(), b.neg());
        lemma_neg_involution::<F>(b);
        F::axiom_eqv_transitive(F::zero().neg(), b.neg().neg(), b);
        F::axiom_eqv_transitive(F::zero(), F::zero().neg(), b);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(F::zero(), b);
    }

    // 0 < a*(-b)
    lemma_mul_pos_pos::<F>(a, b.neg());
    // a*(-b) ≡ -(a*b)
    lemma_mul_neg_right::<F>(a, b);
    // 0 < -(a*b)
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b.neg()));
    lemma_le_congruence_right::<F>(F::zero(), a.mul(b.neg()), a.mul(b).neg());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b).neg());
    if F::zero().eqv(a.mul(b).neg()) {
        F::axiom_eqv_symmetric(a.mul(b.neg()), a.mul(b).neg());
        F::axiom_eqv_transitive(F::zero(), a.mul(b).neg(), a.mul(b.neg()));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b.neg()));
    }

    // 0 < -(a*b) means -(a*b) > 0, so a*b < 0
    // Use neg_nonpos_iff: a*b ≤ 0 iff 0 ≤ -(a*b)
    lemma_neg_nonpos_iff::<F>(a.mul(b));
    F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
    // Need a*b ≢ 0
    if a.mul(b).eqv(F::zero()) {
        // a*b ≡ 0 contradicts nonzero_product
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(F::zero(), a);
        F::axiom_eqv_symmetric(b, F::zero());
        // need !a.eqv(0) and !b.eqv(0)
        // a < 0... wait, 0 < a means !0.eqv(a), which by symmetry is !a.eqv(0)... no.
        // 0 < a means 0.le(a) && !0.eqv(a). We need !a.eqv(0).
        // 0.eqv(a) == a.eqv(0) by symmetry
        // So !0.eqv(a) iff !a.eqv(0)
        lemma_nonzero_product::<F>(a, b);
    }
}

/// 0 < a implies 0 < recip(a).
pub proof fn lemma_recip_pos<F: OrderedField>(a: F)
    requires
        F::zero().lt(a),
    ensures
        F::zero().lt(a.recip()),
{
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
    F::axiom_eqv_symmetric(F::zero(), a);

    // Trichotomy on recip(a): recip(a) ≡ 0, 0 < recip(a), or recip(a) < 0
    lemma_trichotomy::<F>(F::zero(), a.recip());

    // Case 1: recip(a) ≡ 0. Then a*recip(a) ≡ a*0 ≡ 0. But a*recip(a) ≡ 1 ≢ 0.
    if F::zero().eqv(a.recip()) {
        F::axiom_eqv_symmetric(F::zero(), a.recip());
        lemma_mul_congruence_right::<F>(a, a.recip(), F::zero());
        F::axiom_mul_zero_right(a);
        F::axiom_mul_recip_right(a);
        // a*recip(a) ≡ a*0 ≡ 0 and a*recip(a) ≡ 1
        F::axiom_eqv_transitive(a.mul(a.recip()), a.mul(F::zero()), F::zero());
        F::axiom_eqv_symmetric(a.mul(a.recip()), F::one());
        F::axiom_eqv_transitive(F::one(), a.mul(a.recip()), F::zero());
        F::axiom_one_ne_zero();
    }

    // Case 2: recip(a) < 0. Then a*recip(a) < 0 by mul_pos_neg. But a*recip(a) ≡ 1 > 0.
    if a.recip().lt(F::zero()) {
        lemma_mul_pos_neg::<F>(a, a.recip());
        // a*recip(a) < 0, but a*recip(a) ≡ 1
        F::axiom_mul_recip_right(a);
        // 1 < 0?
        F::axiom_lt_iff_le_and_not_eqv(a.mul(a.recip()), F::zero());
        F::axiom_eqv_symmetric(a.mul(a.recip()), F::one());
        lemma_le_congruence_left::<F>(a.mul(a.recip()), F::one(), F::zero());
        // 1 ≤ 0. But also 0 < 1 from zero_lt_one.
        lemma_zero_lt_one::<F>();
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
        F::axiom_le_antisymmetric(F::zero(), F::one());
        F::axiom_one_ne_zero();
    }
}

/// 0 < a ≤ b implies recip(b) ≤ recip(a).
pub proof fn lemma_recip_reverses_le_pos<F: OrderedField>(a: F, b: F)
    requires
        F::zero().lt(a),
        a.le(b),
    ensures
        b.recip().le(a.recip()),
{
    // Establish !a.eqv(0) and 0 ≤ a
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
    F::axiom_eqv_symmetric(F::zero(), a);
    lemma_le_iff_lt_or_eqv::<F>(a, b);

    if a.eqv(b) {
        F::axiom_recip_congruence(a, b);
        F::axiom_eqv_symmetric(a.recip(), b.recip());
        // recip(b) ≡ recip(a), so recip(b) ≤ recip(a)
        F::axiom_le_reflexive(b.recip());
        lemma_le_congruence_right::<F>(b.recip(), b.recip(), a.recip());
    } else {
        // 0 < b (from 0 < a and a ≤ b, with a ≢ b so a < b)
        // a ≤ b and !a.eqv(b) give a < b
        F::axiom_lt_iff_le_and_not_eqv(a, b);
        // 0 < a and a < b give 0 < b
        lemma_lt_transitive::<F>(F::zero(), a, b);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        F::axiom_eqv_symmetric(F::zero(), b);

        // recip(a) > 0 and recip(b) > 0
        lemma_recip_pos::<F>(a);
        lemma_recip_pos::<F>(b);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.recip());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b.recip());

        // Multiply a ≤ b by recip(a)*recip(b) > 0
        // a * recip(a) * recip(b) ≤ b * recip(a) * recip(b)
        // First: a ≤ b, 0 ≤ recip(b) → a*recip(b) ≤ b*recip(b)
        F::axiom_le_mul_nonneg_monotone(a, b, b.recip());
        // b*recip(b) ≡ 1
        F::axiom_mul_recip_right(b);
        // a*recip(b) ≤ b*recip(b) ≡ 1
        lemma_le_congruence_right::<F>(a.mul(b.recip()), b.mul(b.recip()), F::one());

        // Now multiply a*recip(b) ≤ 1 by recip(a) ≥ 0:
        // a*recip(b)*recip(a) ≤ 1*recip(a)
        F::axiom_le_mul_nonneg_monotone(a.mul(b.recip()), F::one(), a.recip());
        // 1*recip(a) ≡ recip(a)
        lemma_mul_one_left::<F>(a.recip());
        // a*recip(b)*recip(a) ≤ recip(a)
        lemma_le_congruence_right::<F>(
            a.mul(b.recip()).mul(a.recip()),
            F::one().mul(a.recip()),
            a.recip(),
        );

        // a*recip(b)*recip(a) ≡ (a*recip(a))*recip(b) ... rearrange
        // a*recip(b)*recip(a) ≡ a*(recip(b)*recip(a))  [assoc]
        F::axiom_mul_associative(a, b.recip(), a.recip());
        // recip(b)*recip(a) ≡ recip(a)*recip(b) [comm]
        F::axiom_mul_commutative(b.recip(), a.recip());
        // a*(recip(b)*recip(a)) ≡ a*(recip(a)*recip(b)) [cong right]
        lemma_mul_congruence_right::<F>(a, b.recip().mul(a.recip()), a.recip().mul(b.recip()));
        F::axiom_eqv_transitive(
            a.mul(b.recip()).mul(a.recip()),
            a.mul(b.recip().mul(a.recip())),
            a.mul(a.recip().mul(b.recip())),
        );
        // a*(recip(a)*recip(b)) ≡ (a*recip(a))*recip(b) [assoc reversed]
        F::axiom_mul_associative(a, a.recip(), b.recip());
        F::axiom_eqv_symmetric(a.mul(a.recip()).mul(b.recip()), a.mul(a.recip().mul(b.recip())));
        F::axiom_eqv_transitive(
            a.mul(b.recip()).mul(a.recip()),
            a.mul(a.recip().mul(b.recip())),
            a.mul(a.recip()).mul(b.recip()),
        );
        // a*recip(a) ≡ 1
        F::axiom_mul_recip_right(a);
        // (a*recip(a))*recip(b) ≡ 1*recip(b) ≡ recip(b)
        F::axiom_mul_congruence_left(a.mul(a.recip()), F::one(), b.recip());
        lemma_mul_one_left::<F>(b.recip());
        F::axiom_eqv_transitive(
            a.mul(a.recip()).mul(b.recip()),
            F::one().mul(b.recip()),
            b.recip(),
        );
        // Full chain: a*recip(b)*recip(a) ≡ recip(b)
        F::axiom_eqv_transitive(
            a.mul(b.recip()).mul(a.recip()),
            a.mul(a.recip()).mul(b.recip()),
            b.recip(),
        );

        // recip(b) ≡ a*recip(b)*recip(a) ≤ recip(a)
        F::axiom_eqv_symmetric(a.mul(b.recip()).mul(a.recip()), b.recip());
        lemma_le_congruence_left::<F>(
            a.mul(b.recip()).mul(a.recip()),
            b.recip(),
            a.recip(),
        );
    }
}

/// 0 < a < b implies recip(b) < recip(a).
pub proof fn lemma_recip_reverses_lt_pos<F: OrderedField>(a: F, b: F)
    requires
        F::zero().lt(a),
        a.lt(b),
    ensures
        b.recip().lt(a.recip()),
{
    F::axiom_lt_iff_le_and_not_eqv(a, b);
    lemma_recip_reverses_le_pos::<F>(a, b);
    F::axiom_lt_iff_le_and_not_eqv(b.recip(), a.recip());
    // Establish !a.eqv(0) from 0 < a
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
    F::axiom_eqv_symmetric(F::zero(), a);
    // Need: !recip(b).eqv(recip(a))
    if b.recip().eqv(a.recip()) {
        // recip(a) ≢ 0 (if recip(a)≡0 then a*recip(a)≡a*0≡0 but also ≡1)
        if a.recip().eqv(F::zero()) {
            lemma_mul_congruence_right::<F>(a, a.recip(), F::zero());
            F::axiom_mul_zero_right(a);
            F::axiom_mul_recip_right(a);
            F::axiom_eqv_transitive(a.mul(a.recip()), a.mul(F::zero()), F::zero());
            F::axiom_eqv_symmetric(a.mul(a.recip()), F::one());
            F::axiom_eqv_transitive(F::one(), a.mul(a.recip()), F::zero());
            F::axiom_one_ne_zero();
        }
        // b*recip(b) ≡ b*recip(a) (congruence on recip(b) ≡ recip(a))
        lemma_mul_congruence_right::<F>(b, b.recip(), a.recip());
        // Need b ≢ 0: 0 < a ≤ b (from a < b), if b ≡ 0 then a ≤ 0 contradicting 0 < a
        // a ≤ b and 0 < a gives 0 < a ≤ b so 0 ≤ b
        // If b ≡ 0 then a ≤ 0 from le_congruence
        F::axiom_eqv_symmetric(F::zero(), b);
        if b.eqv(F::zero()) {
            F::axiom_eqv_symmetric(b, F::zero());
            lemma_le_congruence_right::<F>(a, b, F::zero());
            F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
            F::axiom_le_antisymmetric(F::zero(), a);
        }
        // b*recip(b) ≡ 1
        F::axiom_mul_recip_right(b);
        // So b*recip(a) ≡ b*recip(b) ≡ 1
        F::axiom_eqv_symmetric(b.mul(b.recip()), b.mul(a.recip()));
        F::axiom_eqv_transitive(b.mul(a.recip()), b.mul(b.recip()), F::one());
        // Also a*recip(a) ≡ 1
        F::axiom_mul_recip_right(a);
        // b*recip(a) ≡ 1 and a*recip(a) ≡ 1, so b*recip(a) ≡ a*recip(a)
        F::axiom_eqv_symmetric(a.mul(a.recip()), F::one());
        F::axiom_eqv_transitive(b.mul(a.recip()), F::one(), a.mul(a.recip()));
        // Cancel recip(a): b ≡ a
        lemma_mul_cancel_right::<F>(b, a, a.recip());
        // But a < b says !a.eqv(b)
        F::axiom_eqv_symmetric(b, a);
    }
}

/// a ≤ b and 0 < c implies a/c ≤ b/c.
pub proof fn lemma_le_div_monotone<F: OrderedField>(a: F, b: F, c: F)
    requires
        a.le(b),
        F::zero().lt(c),
    ensures
        a.div(c).le(b.div(c)),
{
    // recip(c) > 0
    lemma_recip_pos::<F>(c);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), c.recip());
    // a ≤ b and 0 ≤ recip(c) → a*recip(c) ≤ b*recip(c)
    F::axiom_le_mul_nonneg_monotone(a, b, c.recip());
    // a*recip(c) ≡ a/c
    F::axiom_div_is_mul_recip(a, c);
    F::axiom_eqv_symmetric(a.div(c), a.mul(c.recip()));
    // b*recip(c) ≡ b/c
    F::axiom_div_is_mul_recip(b, c);
    F::axiom_eqv_symmetric(b.div(c), b.mul(c.recip()));
    // a/c ≤ b/c
    F::axiom_le_congruence(a.mul(c.recip()), a.div(c), b.mul(c.recip()), b.div(c));
}

/// 0 < c and a*c ≤ b*c implies a ≤ b.
pub proof fn lemma_mul_le_cancel_pos<F: OrderedField>(a: F, b: F, c: F)
    requires
        F::zero().lt(c),
        a.mul(c).le(b.mul(c)),
    ensures
        a.le(b),
{
    F::axiom_le_total(a, b);
    if !a.le(b) {
        // b < a (from totality): b ≤ a and ¬b.eqv(a)
        // b ≤ a and 0 ≤ c → b*c ≤ a*c
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), c);
        F::axiom_le_mul_nonneg_monotone(b, a, c);
        // Now b*c ≤ a*c and a*c ≤ b*c, so a*c ≡ b*c
        F::axiom_le_antisymmetric(a.mul(c), b.mul(c));
        // By mul_cancel_right: a ≡ b
        F::axiom_eqv_symmetric(F::zero(), c);
        lemma_mul_cancel_right::<F>(a, b, c);
        // a ≡ b implies a ≤ b
        F::axiom_le_reflexive(a);
        F::axiom_eqv_reflexive(a);
        F::axiom_le_congruence(a, a, a, b);
    }
}

/// 0 < b and 0 < d implies: a/b ≤ c/d if and only if a*d ≤ c*b.
pub proof fn lemma_cross_mul_le<F: OrderedField>(a: F, b: F, c: F, d: F)
    requires
        F::zero().lt(b),
        F::zero().lt(d),
    ensures
        a.div(b).le(c.div(d)) == a.mul(d).le(c.mul(b)),
{
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), d);
    F::axiom_eqv_symmetric(F::zero(), b);
    F::axiom_eqv_symmetric(F::zero(), d);

    // Forward: a/b ≤ c/d ⟹ a*d ≤ c*b
    if a.div(b).le(c.div(d)) {
        // Multiply both sides by b (positive): (a/b)*b ≤ (c/d)*b
        F::axiom_le_mul_nonneg_monotone(a.div(b), c.div(d), b);
        // (a/b)*b ≡ a
        lemma_div_mul_cancel::<F>(a, b);
        // (c/d)*b: commute to b*(c/d)
        F::axiom_mul_commutative(c.div(d), b);
        // a ≤ b*(c/d)
        F::axiom_eqv_reflexive(c.div(d).mul(b));
        F::axiom_le_congruence(a.div(b).mul(b), a, c.div(d).mul(b), c.div(d).mul(b));
        lemma_le_congruence_right::<F>(a, c.div(d).mul(b), b.mul(c.div(d)));

        // Now multiply both sides of a ≤ b*(c/d) by d (positive): a*d ≤ b*(c/d)*d
        F::axiom_le_mul_nonneg_monotone(a, b.mul(c.div(d)), d);
        // b*(c/d)*d ≡ b*((c/d)*d) ≡ b*c
        F::axiom_mul_associative(b, c.div(d), d);
        lemma_div_mul_cancel::<F>(c, d);
        lemma_mul_congruence_right::<F>(b, c.div(d).mul(d), c);
        F::axiom_eqv_transitive(b.mul(c.div(d)).mul(d), b.mul(c.div(d).mul(d)), b.mul(c));
        // b*c ≡ c*b
        F::axiom_mul_commutative(b, c);
        F::axiom_eqv_transitive(b.mul(c.div(d)).mul(d), b.mul(c), c.mul(b));
        lemma_le_congruence_right::<F>(a.mul(d), b.mul(c.div(d)).mul(d), c.mul(b));
    }

    // Backward: a*d ≤ c*b ⟹ a/b ≤ c/d
    if a.mul(d).le(c.mul(b)) {
        // Multiply by recip(b): a*d*recip(b) ≤ c*b*recip(b)
        lemma_recip_pos::<F>(b);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b.recip());
        F::axiom_le_mul_nonneg_monotone(a.mul(d), c.mul(b), b.recip());
        // c*b*recip(b) ≡ c*(b*recip(b)) ≡ c*1 ≡ c
        F::axiom_mul_associative(c, b, b.recip());
        F::axiom_mul_recip_right(b);
        lemma_mul_congruence_right::<F>(c, b.mul(b.recip()), F::one());
        F::axiom_mul_one_right(c);
        F::axiom_eqv_transitive(c.mul(b).mul(b.recip()), c.mul(b.mul(b.recip())), c.mul(F::one()));
        F::axiom_eqv_transitive(c.mul(b).mul(b.recip()), c.mul(F::one()), c);
        // a*d*recip(b) ≤ c
        lemma_le_congruence_right::<F>(a.mul(d).mul(b.recip()), c.mul(b).mul(b.recip()), c);

        // Multiply by recip(d): a*d*recip(b)*recip(d) ≤ c*recip(d)
        lemma_recip_pos::<F>(d);
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), d.recip());
        F::axiom_le_mul_nonneg_monotone(a.mul(d).mul(b.recip()), c, d.recip());
        // c*recip(d) ≡ c/d
        F::axiom_div_is_mul_recip(c, d);
        F::axiom_eqv_symmetric(c.div(d), c.mul(d.recip()));
        lemma_le_congruence_right::<F>(a.mul(d).mul(b.recip()).mul(d.recip()), c.mul(d.recip()), c.div(d));

        // a*d*recip(b)*recip(d) ≡ a*(d*(recip(b)*recip(d)))  [assoc chain]
        F::axiom_mul_associative(a.mul(d), b.recip(), d.recip());
        F::axiom_mul_associative(a, d, b.recip().mul(d.recip()));
        F::axiom_eqv_transitive(
            a.mul(d).mul(b.recip()).mul(d.recip()),
            a.mul(d).mul(b.recip().mul(d.recip())),
            a.mul(d.mul(b.recip().mul(d.recip()))),
        );
        // d*(recip(b)*recip(d)) ≡ (d*recip(d))*recip(b)
        F::axiom_mul_associative(d, b.recip(), d.recip());
        F::axiom_eqv_symmetric(d.mul(b.recip()).mul(d.recip()), d.mul(b.recip().mul(d.recip())));
        F::axiom_mul_commutative(b.recip(), d.recip());
        lemma_mul_congruence_right::<F>(d, b.recip().mul(d.recip()), d.recip().mul(b.recip()));
        // d*(d.recip()*b.recip()) ≡ (d*d.recip())*b.recip()
        F::axiom_mul_associative(d, d.recip(), b.recip());
        F::axiom_eqv_symmetric(d.mul(d.recip()).mul(b.recip()), d.mul(d.recip().mul(b.recip())));
        F::axiom_eqv_transitive(
            d.mul(b.recip().mul(d.recip())),
            d.mul(d.recip().mul(b.recip())),
            d.mul(d.recip()).mul(b.recip()),
        );
        // d*recip(d) ≡ 1
        F::axiom_mul_recip_right(d);
        F::axiom_mul_congruence_left(d.mul(d.recip()), F::one(), b.recip());
        lemma_mul_one_left::<F>(b.recip());
        F::axiom_eqv_transitive(d.mul(d.recip()).mul(b.recip()), F::one().mul(b.recip()), b.recip());
        // d*(recip(b)*recip(d)) ≡ recip(b)
        F::axiom_eqv_transitive(d.mul(b.recip().mul(d.recip())), d.mul(d.recip()).mul(b.recip()), b.recip());
        // a*(d*(recip(b)*recip(d))) ≡ a*recip(b)
        lemma_mul_congruence_right::<F>(a, d.mul(b.recip().mul(d.recip())), b.recip());
        // a*recip(b) ≡ a/b
        F::axiom_div_is_mul_recip(a, b);
        F::axiom_eqv_symmetric(a.div(b), a.mul(b.recip()));
        F::axiom_eqv_transitive(a.mul(d.mul(b.recip().mul(d.recip()))), a.mul(b.recip()), a.div(b));
        // Chain from original to a/b
        F::axiom_eqv_transitive(
            a.mul(d).mul(b.recip()).mul(d.recip()),
            a.mul(d.mul(b.recip().mul(d.recip()))),
            a.div(b),
        );
        // a/b ≤ c/d via congruence
        F::axiom_eqv_symmetric(a.mul(d).mul(b.recip()).mul(d.recip()), a.div(b));
        lemma_le_congruence_left::<F>(a.mul(d).mul(b.recip()).mul(d.recip()), a.div(b), c.div(d));
    }
}

/// c < 0 and a < b implies b*c < a*c (strict multiplication by negative flips order).
pub proof fn lemma_lt_mul_nonpos_flip<F: OrderedField>(a: F, b: F, c: F)
    requires
        c.lt(F::zero()),
        a.lt(b),
    ensures
        b.mul(c).lt(a.mul(c)),
{
    // c < 0 → c ≤ 0
    F::axiom_lt_iff_le_and_not_eqv(c, F::zero());
    // a < b → a ≤ b
    F::axiom_lt_iff_le_and_not_eqv(a, b);
    // c ≤ 0 and a ≤ b → b*c ≤ a*c
    lemma_le_mul_nonpos_flip::<F>(a, b, c);
    // Need strict: b*c < a*c, i.e. b*c ≤ a*c and ¬(b*c ≡ a*c)
    F::axiom_lt_iff_le_and_not_eqv(b.mul(c), a.mul(c));
    // If b*c ≡ a*c, then by mul_cancel_right (since c ≢ 0): b ≡ a
    F::axiom_eqv_symmetric(c, F::zero());
    if b.mul(c).eqv(a.mul(c)) {
        lemma_mul_cancel_right::<F>(b, a, c);
        // b ≡ a, so a ≡ b
        F::axiom_eqv_symmetric(b, a);
        // But a < b means ¬(a ≡ b). Contradiction.
    }
}

} // verus!
