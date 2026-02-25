use vstd::prelude::*;
use crate::traits::ordered_ring::OrderedRing;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::partial_order_lemmas;

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

/// a ≤ b if and only if a < b or a ≡ b.
pub proof fn lemma_le_iff_lt_or_eqv<R: OrderedRing>(a: R, b: R)
    ensures
        a.le(b) == (a.lt(b) || a.eqv(b)),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_eqv_symmetric(a, b);
    if a.eqv(b) {
        // a ≡ b implies a ≤ b via reflexivity + congruence
        R::axiom_eqv_reflexive(a);
        R::axiom_le_reflexive(a);
        R::axiom_le_congruence(a, a, a, b);
    }
}

/// Single-arg left congruence: a1 ≡ a2 and a1 ≤ b implies a2 ≤ b.
pub proof fn lemma_le_congruence_left<R: OrderedRing>(a1: R, a2: R, b: R)
    requires
        a1.eqv(a2),
        a1.le(b),
    ensures
        a2.le(b),
{
    partial_order_lemmas::lemma_le_congruence_left::<R>(a1, a2, b);
}

/// Single-arg right congruence: a ≤ b1 and b1 ≡ b2 implies a ≤ b2.
pub proof fn lemma_le_congruence_right<R: OrderedRing>(a: R, b1: R, b2: R)
    requires
        b1.eqv(b2),
        a.le(b1),
    ensures
        a.le(b2),
{
    partial_order_lemmas::lemma_le_congruence_right::<R>(a, b1, b2);
}

/// a < b and b ≤ c implies a < c.
pub proof fn lemma_lt_le_transitive<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.lt(b),
        b.le(c),
    ensures
        a.lt(c),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_lt_iff_le_and_not_eqv(a, c);
    R::axiom_le_transitive(a, b, c);
    // Need !a.eqv(c). If a ≡ c, then c ≤ b (since a ≤ b and a ≡ c).
    // Combined with b ≤ c: b ≡ c. Then a ≡ c ≡ b, contradicting a < b.
    if a.eqv(c) {
        R::axiom_eqv_symmetric(a, c);
        lemma_le_congruence_left::<R>(a, c, b);
        R::axiom_le_antisymmetric(b, c);
        // b ≡ c, so c ≡ b (symmetric), then a ≡ c ≡ b
        R::axiom_eqv_symmetric(b, c);
        R::axiom_eqv_transitive(a, c, b);
    }
}

/// a ≤ b and b < c implies a < c.
pub proof fn lemma_le_lt_transitive<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.le(b),
        b.lt(c),
    ensures
        a.lt(c),
{
    R::axiom_lt_iff_le_and_not_eqv(b, c);
    R::axiom_lt_iff_le_and_not_eqv(a, c);
    R::axiom_le_transitive(a, b, c);
    // Need !a.eqv(c). If a ≡ c, then b ≤ c ≡ a ≤ b, so b ≡ a ≡ c, contradiction.
    if a.eqv(c) {
        R::axiom_eqv_symmetric(a, c);
        lemma_le_congruence_right::<R>(b, c, a);
        R::axiom_le_antisymmetric(a, b);
        // a ≡ b, so b ≡ c via b ≡ a ≡ c... but we need b.eqv(c) for contradiction
        R::axiom_eqv_symmetric(a, b);
        R::axiom_eqv_transitive(b, a, c);
    }
}

/// a ≤ b implies -b ≤ -a.
pub proof fn lemma_le_neg_flip<R: OrderedRing>(a: R, b: R)
    requires
        a.le(b),
    ensures
        b.neg().le(a.neg()),
{
    // a ≤ b implies a + (-b) ≤ b + (-b) [add_monotone with -b]
    R::axiom_le_add_monotone(a, b, b.neg());
    // b + (-b) ≡ 0
    R::axiom_add_inverse_right(b);
    // So a + (-b) ≤ 0
    lemma_le_congruence_right::<R>(a.add(b.neg()), b.add(b.neg()), R::zero());

    // Now: a + (-b) ≤ 0 implies (a + (-b)) + (-a) ≤ 0 + (-a)
    R::axiom_le_add_monotone(a.add(b.neg()), R::zero(), a.neg());

    // (a + (-b)) + (-a) ≡ (-b) + (a + (-a)) ... let's use rearrangement
    // (a + (-b)) + (-a) ≡ (a + (-a)) + (-b) ... by rearrange
    // Actually let's do it step by step:
    // (a + (-b)) + (-a) ≡ a + ((-b) + (-a))   [assoc]
    R::axiom_add_associative(a, b.neg(), a.neg());
    // (-b) + (-a) ≡ (-a) + (-b)               [comm]
    R::axiom_add_commutative(b.neg(), a.neg());
    // a + ((-b)+(-a)) ≡ a + ((-a)+(-b))       [cong right]
    lemma_add_congruence_right::<R>(a, b.neg().add(a.neg()), a.neg().add(b.neg()));
    // a + ((-a)+(-b)) ≡ (a+(-a))+(-b)         [assoc reversed]
    R::axiom_add_associative(a, a.neg(), b.neg());
    R::axiom_eqv_symmetric(a.add(a.neg()).add(b.neg()), a.add(a.neg().add(b.neg())));
    // a + (-a) ≡ 0
    R::axiom_add_inverse_right(a);
    // (a+(-a))+(-b) ≡ 0+(-b)
    R::axiom_add_congruence_left(a.add(a.neg()), R::zero(), b.neg());
    // 0 + (-b) ≡ -b
    lemma_add_zero_left::<R>(b.neg());

    // Full chain: (a+(-b))+(-a) ≡ a+((-b)+(-a)) ≡ a+((-a)+(-b)) ≡ (a+(-a))+(-b) ≡ 0+(-b) ≡ -b
    R::axiom_eqv_transitive(
        a.add(b.neg()).add(a.neg()),
        a.add(b.neg().add(a.neg())),
        a.add(a.neg().add(b.neg())),
    );
    R::axiom_eqv_transitive(
        a.add(b.neg()).add(a.neg()),
        a.add(a.neg().add(b.neg())),
        a.add(a.neg()).add(b.neg()),
    );
    R::axiom_eqv_transitive(
        a.add(b.neg()).add(a.neg()),
        a.add(a.neg()).add(b.neg()),
        R::zero().add(b.neg()),
    );
    R::axiom_eqv_transitive(
        a.add(b.neg()).add(a.neg()),
        R::zero().add(b.neg()),
        b.neg(),
    );

    // 0 + (-a) ≡ -a
    lemma_add_zero_left::<R>(a.neg());

    // Apply le_congruence: (a+(-b))+(-a) ≤ 0+(-a), and LHS ≡ -b, RHS ≡ -a
    R::axiom_le_congruence(
        a.add(b.neg()).add(a.neg()), b.neg(),
        R::zero().add(a.neg()), a.neg(),
    );
}

/// a < b implies -b < -a.
pub proof fn lemma_lt_neg_flip<R: OrderedRing>(a: R, b: R)
    requires
        a.lt(b),
    ensures
        b.neg().lt(a.neg()),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    lemma_le_neg_flip::<R>(a, b);
    R::axiom_lt_iff_le_and_not_eqv(b.neg(), a.neg());
    // Need !(-b).eqv(-a). If -b ≡ -a, then -(-b) ≡ -(-a), i.e. b ≡ a.
    if b.neg().eqv(a.neg()) {
        R::axiom_neg_congruence(b.neg(), a.neg());
        lemma_neg_involution::<R>(b);
        lemma_neg_involution::<R>(a);
        // -(-b) ≡ -(-a) and -(-b) ≡ b and -(-a) ≡ a
        R::axiom_eqv_symmetric(b.neg().neg(), b);
        R::axiom_eqv_transitive(b, b.neg().neg(), a.neg().neg());
        R::axiom_eqv_transitive(b, a.neg().neg(), a);
        R::axiom_eqv_symmetric(b, a);
        // a ≡ b, contradiction with a < b
    }
}

/// 0 ≤ a if and only if -a ≤ 0.
pub proof fn lemma_neg_nonneg_iff<R: OrderedRing>(a: R)
    ensures
        R::zero().le(a) == a.neg().le(R::zero()),
{
    if R::zero().le(a) {
        lemma_le_neg_flip::<R>(R::zero(), a);
        // -a ≤ -0
        lemma_neg_zero::<R>();
        // -0 ≡ 0
        lemma_le_congruence_right::<R>(a.neg(), R::zero().neg(), R::zero());
    }
    if a.neg().le(R::zero()) {
        lemma_le_neg_flip::<R>(a.neg(), R::zero());
        // -0 ≤ -(-a)
        lemma_neg_zero::<R>();
        lemma_neg_involution::<R>(a);
        // -0 ≡ 0 and -(-a) ≡ a
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
        lemma_le_congruence_left::<R>(R::zero().neg(), R::zero(), a.neg().neg());
        lemma_le_congruence_right::<R>(R::zero(), a.neg().neg(), a);
    }
}

/// a ≤ 0 if and only if 0 ≤ -a.
pub proof fn lemma_neg_nonpos_iff<R: OrderedRing>(a: R)
    ensures
        a.le(R::zero()) == R::zero().le(a.neg()),
{
    if a.le(R::zero()) {
        lemma_le_neg_flip::<R>(a, R::zero());
        lemma_neg_zero::<R>();
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
        lemma_le_congruence_left::<R>(R::zero().neg(), R::zero(), a.neg());
    }
    if R::zero().le(a.neg()) {
        lemma_le_neg_flip::<R>(R::zero(), a.neg());
        // -(-a) ≤ -0
        lemma_neg_involution::<R>(a);
        lemma_neg_zero::<R>();
        lemma_le_congruence_left::<R>(a.neg().neg(), a, R::zero().neg());
        lemma_le_congruence_right::<R>(a, R::zero().neg(), R::zero());
    }
}

/// a ≤ b implies a - c ≤ b - c.
pub proof fn lemma_le_sub_monotone<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.le(b),
    ensures
        a.sub(c).le(b.sub(c)),
{
    R::axiom_le_add_monotone(a, b, c.neg());
    // a + (-c) ≤ b + (-c)
    // a - c ≡ a + (-c)
    R::axiom_sub_is_add_neg(a, c);
    R::axiom_sub_is_add_neg(b, c);
    R::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    R::axiom_eqv_symmetric(b.sub(c), b.add(c.neg()));
    R::axiom_le_congruence(a.add(c.neg()), a.sub(c), b.add(c.neg()), b.sub(c));
}

/// a < b implies a - c < b - c.
pub proof fn lemma_lt_sub_monotone<R: OrderedRing>(a: R, b: R, c: R)
    requires
        a.lt(b),
    ensures
        a.sub(c).lt(b.sub(c)),
{
    lemma_lt_add_compatible::<R>(a, b, c.neg());
    // a + (-c) < b + (-c)
    R::axiom_lt_iff_le_and_not_eqv(a.add(c.neg()), b.add(c.neg()));
    R::axiom_sub_is_add_neg(a, c);
    R::axiom_sub_is_add_neg(b, c);
    R::axiom_eqv_symmetric(a.sub(c), a.add(c.neg()));
    R::axiom_eqv_symmetric(b.sub(c), b.add(c.neg()));
    // a.sub(c) ≤ b.sub(c)
    R::axiom_le_congruence(a.add(c.neg()), a.sub(c), b.add(c.neg()), b.sub(c));
    R::axiom_lt_iff_le_and_not_eqv(a.sub(c), b.sub(c));
    // Need: !a.sub(c).eqv(b.sub(c))
    // If a-c ≡ b-c then a+(-c) ≡ b+(-c) by congruence, contradiction
    if a.sub(c).eqv(b.sub(c)) {
        // a-c ≡ a+(-c) and b-c ≡ b+(-c)
        R::axiom_eqv_transitive(a.add(c.neg()), a.sub(c), b.sub(c));
        R::axiom_eqv_transitive(a.add(c.neg()), b.sub(c), b.add(c.neg()));
    }
}

/// Trichotomy: exactly one of a < b, a ≡ b, b < a holds.
pub proof fn lemma_trichotomy<R: OrderedRing>(a: R, b: R)
    ensures
        (a.lt(b) || a.eqv(b) || b.lt(a)),
        !(a.lt(b) && a.eqv(b)),
        !(a.lt(b) && b.lt(a)),
        !(a.eqv(b) && b.lt(a)),
{
    R::axiom_lt_iff_le_and_not_eqv(a, b);
    R::axiom_lt_iff_le_and_not_eqv(b, a);
    R::axiom_le_total(a, b);
    // At least one: if a ≤ b, then a < b or a ≡ b. If b ≤ a, then b < a or b ≡ a.
    if a.le(b) && !a.eqv(b) {
        // a < b
    } else if a.le(b) && a.eqv(b) {
        // a ≡ b
    } else {
        // b ≤ a
        if !b.eqv(a) {
            // b < a
        } else {
            R::axiom_eqv_symmetric(b, a);
        }
    }
    // Mutual exclusions:
    // a < b && a ≡ b: impossible by definition of <
    // a < b && b < a: impossible by lt_asymmetric
    if a.lt(b) {
        lemma_lt_asymmetric::<R>(a, b);
    }
    // a ≡ b && b < a: b < a means !b.eqv(a), but a ≡ b implies b ≡ a
    if a.eqv(b) {
        R::axiom_eqv_symmetric(a, b);
    }
}

/// 0 ≤ a ≤ c and 0 ≤ b ≤ d implies a*b ≤ c*d.
pub proof fn lemma_le_mul_nonneg_both<R: OrderedRing>(a: R, b: R, c: R, d: R)
    requires
        R::zero().le(a),
        a.le(c),
        R::zero().le(b),
        b.le(d),
    ensures
        a.mul(b).le(c.mul(d)),
{
    // Step 1: a*b ≤ c*b (a ≤ c and 0 ≤ b)
    R::axiom_le_mul_nonneg_monotone(a, c, b);

    // Step 2: b*c ≤ d*c (b ≤ d and 0 ≤ c, where 0 ≤ c from 0 ≤ a ≤ c)
    R::axiom_le_transitive(R::zero(), a, c);
    R::axiom_le_mul_nonneg_monotone(b, d, c);

    // Step 3: c*b ≡ b*c [comm]
    R::axiom_mul_commutative(c, b);
    // a*b ≤ c*b, and c*b ≡ b*c, so a*b ≤ b*c
    R::axiom_eqv_reflexive(a.mul(b));
    R::axiom_le_congruence(a.mul(b), a.mul(b), c.mul(b), b.mul(c));

    // Step 4: d*c ≡ c*d [comm]
    R::axiom_mul_commutative(d, c);
    // b*c ≤ d*c, and d*c ≡ c*d, so b*c ≤ c*d
    R::axiom_eqv_reflexive(b.mul(c));
    R::axiom_le_congruence(b.mul(c), b.mul(c), d.mul(c), c.mul(d));

    // Step 5: a*b ≤ b*c ≤ c*d
    R::axiom_le_transitive(a.mul(b), b.mul(c), c.mul(d));
}

/// 0 < 1.
pub proof fn lemma_zero_lt_one<R: OrderedRing>()
    ensures
        R::zero().lt(R::one()),
{
    // 0 ≤ 1*1 by square_nonneg
    lemma_square_nonneg::<R>(R::one());
    // 1*1 ≡ 1
    R::axiom_mul_one_right(R::one());
    // 0 ≤ 1
    lemma_le_congruence_right::<R>(R::zero(), R::one().mul(R::one()), R::one());
    // 1 ≢ 0, so 0 < 1
    R::axiom_one_ne_zero();
    R::axiom_eqv_symmetric(R::zero(), R::one());
    R::axiom_lt_iff_le_and_not_eqv(R::zero(), R::one());
}

/// 0 ≤ a and 0 < b implies 0 < a + b.
pub proof fn lemma_add_nonneg_pos<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().le(a),
        R::zero().lt(b),
    ensures
        R::zero().lt(a.add(b)),
{
    // 0 ≤ a implies 0 + b ≤ a + b [add_monotone(0, a, b)]
    R::axiom_le_add_monotone(R::zero(), a, b);
    // 0 + b ≡ b
    lemma_add_zero_left::<R>(b);
    // b ≤ a + b
    lemma_le_congruence_left::<R>(R::zero().add(b), b, a.add(b));
    // 0 < b and b ≤ a + b gives 0 < a + b
    lemma_lt_le_transitive::<R>(R::zero(), b, a.add(b));
}

/// 0 < a and 0 ≤ b implies 0 < a + b.
pub proof fn lemma_add_pos_nonneg<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().lt(a),
        R::zero().le(b),
    ensures
        R::zero().lt(a.add(b)),
{
    // a + b ≡ b + a, so use add_nonneg_pos(b, a)
    lemma_add_nonneg_pos::<R>(b, a);
    // 0 < b + a
    R::axiom_add_commutative(a, b);
    // a + b ≡ b + a, so congruence
    R::axiom_lt_iff_le_and_not_eqv(R::zero(), b.add(a));
    R::axiom_lt_iff_le_and_not_eqv(R::zero(), a.add(b));
    R::axiom_eqv_symmetric(a.add(b), b.add(a));
    lemma_le_congruence_right::<R>(R::zero(), b.add(a), a.add(b));
    if R::zero().eqv(a.add(b)) {
        R::axiom_eqv_transitive(R::zero(), a.add(b), b.add(a));
    }
}

/// a ≤ b and c ≤ d implies a + c ≤ b + d.
pub proof fn lemma_le_add_both<R: OrderedRing>(a: R, b: R, c: R, d: R)
    requires
        a.le(b),
        c.le(d),
    ensures
        a.add(c).le(b.add(d)),
{
    // a ≤ b → a + c ≤ b + c
    R::axiom_le_add_monotone(a, b, c);
    // c ≤ d → c + b ≤ d + b → b + c ≤ b + d
    R::axiom_le_add_monotone(c, d, b);
    // c + b ≡ b + c
    R::axiom_add_commutative(c, b);
    // d + b ≡ b + d
    R::axiom_add_commutative(d, b);
    R::axiom_le_congruence(c.add(b), b.add(c), d.add(b), b.add(d));
    // a + c ≤ b + c ≤ b + d
    R::axiom_le_transitive(a.add(c), b.add(c), b.add(d));
}

/// a < b and c < d implies a + c < b + d.
pub proof fn lemma_lt_add_both<R: OrderedRing>(a: R, b: R, c: R, d: R)
    requires
        a.lt(b),
        c.lt(d),
    ensures
        a.add(c).lt(b.add(d)),
{
    // a < b → a + c < b + c
    lemma_lt_add_compatible::<R>(a, b, c);
    // c < d → c + b < d + b
    lemma_lt_add_compatible::<R>(c, d, b);
    // c + b ≡ b + c and d + b ≡ b + d
    R::axiom_add_commutative(c, b);
    R::axiom_add_commutative(d, b);
    // c + b < d + b → b + c < b + d via congruence
    R::axiom_lt_iff_le_and_not_eqv(c.add(b), d.add(b));
    R::axiom_le_congruence(c.add(b), b.add(c), d.add(b), b.add(d));
    R::axiom_lt_iff_le_and_not_eqv(b.add(c), b.add(d));
    if b.add(c).eqv(b.add(d)) {
        // c + b ≡ b + c ≡ b + d ≡ d + b, contradiction with c+b < d+b
        R::axiom_add_commutative(c, b);
        R::axiom_eqv_transitive(c.add(b), b.add(c), b.add(d));
        R::axiom_add_commutative(d, b);
        R::axiom_eqv_symmetric(d.add(b), b.add(d));
        R::axiom_eqv_transitive(c.add(b), b.add(d), d.add(b));
    }
    // a + c < b + c < b + d
    lemma_lt_transitive::<R>(a.add(c), b.add(c), b.add(d));
}

/// 0 ≤ a ≤ b implies a*a ≤ b*b.
pub proof fn lemma_square_le_square<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().le(a),
        a.le(b),
    ensures
        a.mul(a).le(b.mul(b)),
{
    // Step 1: a*a ≤ b*a (from a ≤ b and 0 ≤ a)
    R::axiom_le_mul_nonneg_monotone(a, b, a);
    // Commute: a*a and b*a to get our terms
    // Actually axiom gives a*a ≤ b*a directly (a ≤ b, 0 ≤ a)

    // Step 2: a*b ≤ b*b (from a ≤ b and 0 ≤ b)
    R::axiom_le_transitive(R::zero(), a, b);
    R::axiom_le_mul_nonneg_monotone(a, b, b);
    // This gives a*b ≤ b*b

    // b*a ≡ a*b
    R::axiom_mul_commutative(b, a);
    // a*a ≤ b*a ≡ a*b ≤ b*b
    R::axiom_eqv_reflexive(a.mul(a));
    R::axiom_le_congruence(a.mul(a), a.mul(a), b.mul(a), a.mul(b));
    // a*a ≤ a*b ≤ b*b
    R::axiom_le_transitive(a.mul(a), a.mul(b), b.mul(b));
}

/// a ≤ b if and only if 0 ≤ b - a.
pub proof fn lemma_le_iff_sub_nonneg<R: OrderedRing>(a: R, b: R)
    ensures
        a.le(b) == R::zero().le(b.sub(a)),
{
    // Forward: a ≤ b → 0 ≤ b - a
    if a.le(b) {
        // a ≤ b → a + (-a) ≤ b + (-a)
        R::axiom_le_add_monotone(a, b, a.neg());
        // a + (-a) ≡ 0
        R::axiom_add_inverse_right(a);
        // b + (-a) ≡ b - a (symmetric)
        R::axiom_sub_is_add_neg(b, a);
        R::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
        // 0 ≡ a+(-a) and b-a ≡ b+(-a)
        R::axiom_eqv_symmetric(a.add(a.neg()), R::zero());
        R::axiom_le_congruence(a.add(a.neg()), R::zero(), b.add(a.neg()), b.sub(a));
    }
    // Backward: 0 ≤ b - a → a ≤ b
    if R::zero().le(b.sub(a)) {
        // 0 + a ≤ (b-a) + a
        R::axiom_le_add_monotone(R::zero(), b.sub(a), a);
        // 0 + a ≡ a
        lemma_add_zero_left::<R>(a);
        // (b-a) + a ≡ b
        lemma_sub_then_add_cancel::<R>(b, a);
        // a ≤ b
        R::axiom_le_congruence(R::zero().add(a), a, b.sub(a).add(a), b);
    }
}

/// c ≤ 0 and a ≤ b implies b*c ≤ a*c (multiplication by nonpositive flips order).
pub proof fn lemma_le_mul_nonpos_flip<R: OrderedRing>(a: R, b: R, c: R)
    requires
        c.le(R::zero()),
        a.le(b),
    ensures
        b.mul(c).le(a.mul(c)),
{
    // c ≤ 0 → 0 ≤ -c
    lemma_neg_nonpos_iff::<R>(c);
    // a ≤ b and 0 ≤ -c → a*(-c) ≤ b*(-c)
    R::axiom_le_mul_nonneg_monotone(a, b, c.neg());
    // a*(-c) ≡ -(a*c)
    lemma_mul_neg_right::<R>(a, c);
    // b*(-c) ≡ -(b*c)
    lemma_mul_neg_right::<R>(b, c);
    // -(a*c) ≤ -(b*c)  (via congruence from a*(-c) ≤ b*(-c))
    R::axiom_le_congruence(a.mul(c.neg()), a.mul(c).neg(), b.mul(c.neg()), b.mul(c).neg());
    // -(a*c) ≤ -(b*c) → b*c ≤ a*c  (le_neg_flip reversal)
    lemma_le_neg_flip::<R>(a.mul(c).neg(), b.mul(c).neg());
    // -(-( a*c )) ≡ a*c
    lemma_neg_involution::<R>(a.mul(c));
    // -(-(b*c)) ≡ b*c
    lemma_neg_involution::<R>(b.mul(c));
    // b*c ≡ -(-(b*c)) and a*c ≡ -(-(a*c))
    R::axiom_eqv_symmetric(b.mul(c).neg().neg(), b.mul(c));
    R::axiom_eqv_symmetric(a.mul(c).neg().neg(), a.mul(c));
    R::axiom_le_congruence(b.mul(c).neg().neg(), b.mul(c), a.mul(c).neg().neg(), a.mul(c));
}

} // verus!
