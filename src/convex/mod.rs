use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::{Field, OrderedField};
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;

verus! {

/// The element 1 + 1.
pub open spec fn two<R: Ring>() -> R {
    R::one().add(R::one())
}

/// Midpoint of two elements: (a + b) / 2.
pub open spec fn midpoint<F: OrderedField>(a: F, b: F) -> F {
    a.add(b).div(two::<F>())
}

/// Convex combination: t*a + (1-t)*b.
pub open spec fn convex<F: OrderedField>(a: F, b: F, t: F) -> F {
    t.mul(a).add(F::one().sub(t).mul(b))
}

/// two() ≢ 0.
pub proof fn lemma_two_nonzero<F: OrderedField>()
    ensures
        !two::<F>().eqv(F::zero()),
{
    // 0 < 1
    lemma_zero_lt_one::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
    // 0 < 1 and 0 ≤ 1 → 0 < 1+1 via add_nonneg_pos
    lemma_add_nonneg_pos::<F>(F::one(), F::one());
    // 0 < two(), so two() ≢ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), two::<F>());
    F::axiom_eqv_symmetric(F::zero(), two::<F>());
}

/// midpoint(a, a) ≡ a.
pub proof fn lemma_midpoint_self<F: OrderedField>(a: F)
    ensures
        midpoint::<F>(a, a).eqv(a),
{
    // midpoint(a,a) = (a+a) / 2
    // a+a ≡ 2*a [mul_two from ring_lemmas]
    lemma_mul_two::<F>(a);
    // (a+a) ≡ 2*a, so (a+a)/2 ≡ (2*a)/2
    // Show two() ≢ 0
    lemma_two_nonzero::<F>();
    // (2*a)/2 ≡ a [mul_div_cancel(a, 2)]
    // mul_div_cancel: (a*b)/b ≡ a for b ≢ 0
    lemma_mul_div_cancel::<F>(a, two::<F>());
    // Now chain: (a+a)/2 ≡ (2*a)/2 ≡ a
    // Need: div_congruence_left: x ≡ y → x/c ≡ y/c
    // div_is_mul_recip gives: x/c ≡ x*recip(c) and y/c ≡ y*recip(c)
    // So x ≡ y → x*recip(c) ≡ y*recip(c) → x/c ≡ y/c
    F::axiom_eqv_symmetric(a.add(a), two::<F>().mul(a));
    // two()*a ≡ a+a, flip: a+a ≡ two()*a... wait, mul_two gives a+a ≡ (1+1)*a = two()*a
    // So a.add(a).eqv(two::<F>().mul(a))
    // We need (a+a)/2 ≡ (2*a)/2
    F::axiom_div_is_mul_recip(a.add(a), two::<F>());
    F::axiom_div_is_mul_recip(two::<F>().mul(a), two::<F>());
    // a.add(a) ≡ two()*a
    lemma_mul_two::<F>(a);
    // (a+a)*recip(2) ≡ (2*a)*recip(2)
    F::axiom_mul_congruence_left(a.add(a), two::<F>().mul(a), two::<F>().recip());
    // (a+a)/2 ≡ (a+a)*recip(2) and (2*a)/2 ≡ (2*a)*recip(2)
    F::axiom_eqv_transitive(
        a.add(a).div(two::<F>()),
        a.add(a).mul(two::<F>().recip()),
        two::<F>().mul(a).mul(two::<F>().recip()),
    );
    F::axiom_eqv_symmetric(
        two::<F>().mul(a).div(two::<F>()),
        two::<F>().mul(a).mul(two::<F>().recip()),
    );
    F::axiom_eqv_transitive(
        a.add(a).div(two::<F>()),
        two::<F>().mul(a).mul(two::<F>().recip()),
        two::<F>().mul(a).div(two::<F>()),
    );
    // two()*a ≡ a*two() [commutative]
    F::axiom_mul_commutative(two::<F>(), a);
    // (two()*a)/two() ≡ (two()*a)*recip(two()) already established above
    // (a*two())/two() ≡ a [mul_div_cancel]
    // Need: (two()*a)/two() ≡ (a*two())/two() via div congruence
    F::axiom_div_is_mul_recip(a.mul(two::<F>()), two::<F>());
    F::axiom_mul_congruence_left(two::<F>().mul(a), a.mul(two::<F>()), two::<F>().recip());
    // (two()*a)*recip(two()) ≡ (a*two())*recip(two())
    // (two()*a)/two() ≡ (two()*a)*recip(two()) [already established]
    // (a*two())/two() ≡ (a*two())*recip(two()) [div_is_mul_recip]
    F::axiom_eqv_transitive(
        two::<F>().mul(a).div(two::<F>()),
        two::<F>().mul(a).mul(two::<F>().recip()),
        a.mul(two::<F>()).mul(two::<F>().recip()),
    );
    F::axiom_eqv_symmetric(
        a.mul(two::<F>()).div(two::<F>()),
        a.mul(two::<F>()).mul(two::<F>().recip()),
    );
    F::axiom_eqv_transitive(
        two::<F>().mul(a).div(two::<F>()),
        a.mul(two::<F>()).mul(two::<F>().recip()),
        a.mul(two::<F>()).div(two::<F>()),
    );
    // (a*two())/two() ≡ a [mul_div_cancel(a, two())]
    F::axiom_eqv_transitive(
        two::<F>().mul(a).div(two::<F>()),
        a.mul(two::<F>()).div(two::<F>()),
        a,
    );
    // Final chain: (a+a)/two() ≡ (two()*a)/two() ≡ a
    F::axiom_eqv_transitive(
        a.add(a).div(two::<F>()),
        two::<F>().mul(a).div(two::<F>()),
        a,
    );
}

/// midpoint(a, b) ≡ midpoint(b, a).
pub proof fn lemma_midpoint_commutative<F: OrderedField>(a: F, b: F)
    ensures
        midpoint::<F>(a, b).eqv(midpoint::<F>(b, a)),
{
    // midpoint(a,b) = (a+b)/2, midpoint(b,a) = (b+a)/2
    // a+b ≡ b+a
    F::axiom_add_commutative(a, b);
    // (a+b)/2 ≡ (b+a)/2 via div congruence
    F::axiom_div_is_mul_recip(a.add(b), two::<F>());
    F::axiom_div_is_mul_recip(b.add(a), two::<F>());
    F::axiom_mul_congruence_left(a.add(b), b.add(a), two::<F>().recip());
    // (a+b)/2 ≡ (a+b)*recip(2) ≡ (b+a)*recip(2) ≡ (b+a)/2
    F::axiom_eqv_transitive(
        a.add(b).div(two::<F>()),
        a.add(b).mul(two::<F>().recip()),
        b.add(a).mul(two::<F>().recip()),
    );
    F::axiom_eqv_symmetric(b.add(a).div(two::<F>()), b.add(a).mul(two::<F>().recip()));
    F::axiom_eqv_transitive(
        a.add(b).div(two::<F>()),
        b.add(a).mul(two::<F>().recip()),
        b.add(a).div(two::<F>()),
    );
}

/// a ≤ b implies a ≤ midpoint(a, b) ≤ b.
pub proof fn lemma_midpoint_between<F: OrderedField>(a: F, b: F)
    requires
        a.le(b),
    ensures
        a.le(midpoint::<F>(a, b)),
        midpoint::<F>(a, b).le(b),
{
    // 0 < 2
    lemma_zero_lt_one::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
    lemma_add_nonneg_pos::<F>(F::one(), F::one());

    // === Lower bound: a ≤ (a+b)/2 ===
    // a ≤ b → a+a ≤ b+a [add_monotone(a, b, a)]
    F::axiom_le_add_monotone(a, b, a);
    // b+a ≡ a+b [commutative]
    F::axiom_add_commutative(b, a);
    F::axiom_eqv_reflexive(a.add(a));
    F::axiom_eqv_symmetric(a.add(b), b.add(a));
    F::axiom_le_congruence(a.add(a), a.add(a), b.add(a), a.add(b));
    // a+a ≤ a+b → (a+a)/2 ≤ (a+b)/2
    lemma_le_div_monotone::<F>(a.add(a), a.add(b), two::<F>());
    // (a+a)/2 ≡ a [midpoint_self gives midpoint(a,a) = (a+a)/two() ≡ a]
    lemma_midpoint_self::<F>(a);
    // a ≡ (a+a)/2 [flip]
    F::axiom_eqv_symmetric(a.add(a).div(two::<F>()), a);
    // le_congruence to get a ≤ (a+b)/2
    F::axiom_eqv_reflexive(a.add(b).div(two::<F>()));
    F::axiom_le_congruence(
        a.add(a).div(two::<F>()),
        a,
        a.add(b).div(two::<F>()),
        a.add(b).div(two::<F>()),
    );

    // === Upper bound: (a+b)/2 ≤ b ===
    // a ≤ b → a+b ≤ b+b [add_monotone(a, b, b)]
    F::axiom_le_add_monotone(a, b, b);
    // (a+b)/2 ≤ (b+b)/2
    lemma_le_div_monotone::<F>(a.add(b), b.add(b), two::<F>());
    // (b+b)/2 ≡ b [midpoint_self]
    lemma_midpoint_self::<F>(b);
    // le_congruence to get (a+b)/2 ≤ b
    F::axiom_eqv_reflexive(a.add(b).div(two::<F>()));
    F::axiom_le_congruence(
        a.add(b).div(two::<F>()),
        a.add(b).div(two::<F>()),
        b.add(b).div(two::<F>()),
        b,
    );
}

/// convex(a, b, 0) ≡ b.
pub proof fn lemma_convex_at_zero<F: OrderedField>(a: F, b: F)
    ensures
        convex::<F>(a, b, F::zero()).eqv(b),
{
    // convex(a,b,0) = 0*a + (1-0)*b
    // 0*a ≡ 0
    lemma_mul_zero_left::<F>(a);
    // 1-0 ≡ 1: 1-0 = 1+(-0), -0 ≡ 0 [neg_zero], 1+0 ≡ 1 [add_zero_right axiom]
    F::axiom_sub_is_add_neg(F::one(), F::zero());
    lemma_neg_zero::<F>();
    lemma_add_congruence_right::<F>(F::one(), F::zero().neg(), F::zero());
    // 1+(-0) ≡ 1+0
    F::axiom_eqv_transitive(F::one().sub(F::zero()), F::one().add(F::zero().neg()), F::one().add(F::zero()));
    F::axiom_add_zero_right(F::one());
    F::axiom_eqv_transitive(F::one().sub(F::zero()), F::one().add(F::zero()), F::one());
    // (1-0)*b ≡ 1*b ≡ b
    F::axiom_mul_congruence_left(F::one().sub(F::zero()), F::one(), b);
    lemma_mul_one_left::<F>(b);
    F::axiom_eqv_transitive(F::one().sub(F::zero()).mul(b), F::one().mul(b), b);
    // 0*a + (1-0)*b ≡ 0 + b
    lemma_add_congruence::<F>(
        F::zero().mul(a), F::zero(),
        F::one().sub(F::zero()).mul(b), b,
    );
    // 0 + b ≡ b
    lemma_add_zero_left::<F>(b);
    // Chain
    F::axiom_eqv_transitive(
        F::zero().mul(a).add(F::one().sub(F::zero()).mul(b)),
        F::zero().add(b),
        b,
    );
}

/// convex(a, b, 1) ≡ a.
pub proof fn lemma_convex_at_one<F: OrderedField>(a: F, b: F)
    ensures
        convex::<F>(a, b, F::one()).eqv(a),
{
    // convex(a,b,1) = 1*a + (1-1)*b
    // 1*a ≡ a
    lemma_mul_one_left::<F>(a);
    // 1-1 ≡ 0 [sub_self]
    lemma_sub_self::<F>(F::one());
    // (1-1)*b ≡ 0*b ≡ 0
    F::axiom_mul_congruence_left(F::one().sub(F::one()), F::zero(), b);
    lemma_mul_zero_left::<F>(b);
    F::axiom_eqv_transitive(F::one().sub(F::one()).mul(b), F::zero().mul(b), F::zero());
    // 1*a + (1-1)*b ≡ a + 0
    lemma_add_congruence::<F>(
        F::one().mul(a), a,
        F::one().sub(F::one()).mul(b), F::zero(),
    );
    // a + 0 ≡ a [axiom_add_zero_right]
    F::axiom_add_zero_right(a);
    // Chain
    F::axiom_eqv_transitive(
        F::one().mul(a).add(F::one().sub(F::one()).mul(b)),
        a.add(F::zero()),
        a,
    );
}

/// convex(a, a, t) ≡ a.
pub proof fn lemma_convex_self<F: OrderedField>(a: F, t: F)
    ensures
        convex::<F>(a, a, t).eqv(a),
{
    // convex(a,a,t) = t*a + (1-t)*a
    // t*a + (1-t)*a ≡ (t + (1-t))*a [distributes_right reversed]
    lemma_mul_distributes_right::<F>(t, F::one().sub(t), a);
    F::axiom_eqv_symmetric(
        t.add(F::one().sub(t)).mul(a),
        t.mul(a).add(F::one().sub(t).mul(a)),
    );
    // t + (1-t) ≡ 1 [sub_then_add_cancel reversed: (1-t)+t ≡ 1, then commute]
    lemma_sub_then_add_cancel::<F>(F::one(), t);
    F::axiom_add_commutative(t, F::one().sub(t));
    F::axiom_eqv_symmetric(F::one().sub(t).add(t), t.add(F::one().sub(t)));
    F::axiom_eqv_transitive(t.add(F::one().sub(t)), F::one().sub(t).add(t), F::one());
    // (t+(1-t))*a ≡ 1*a
    F::axiom_mul_congruence_left(t.add(F::one().sub(t)), F::one(), a);
    // 1*a ≡ a
    lemma_mul_one_left::<F>(a);
    // Chain: t*a + (1-t)*a ≡ (t+(1-t))*a ≡ 1*a ≡ a
    F::axiom_eqv_transitive(
        t.mul(a).add(F::one().sub(t).mul(a)),
        t.add(F::one().sub(t)).mul(a),
        F::one().mul(a),
    );
    F::axiom_eqv_transitive(
        t.mul(a).add(F::one().sub(t).mul(a)),
        F::one().mul(a),
        a,
    );
}

/// convex(a, b, t) ≡ convex(b, a, 1-t).
pub proof fn lemma_convex_complement<F: OrderedField>(a: F, b: F, t: F)
    ensures
        convex::<F>(a, b, t).eqv(convex::<F>(b, a, F::one().sub(t))),
{
    // convex(a,b,t) = t*a + (1-t)*b
    // convex(b,a,1-t) = (1-t)*b + (1-(1-t))*a
    // Need: 1-(1-t) ≡ t
    // sub_then_add_cancel(1,t): (1-t)+t ≡ 1
    // So 1-(1-t) ≡ t by: 1-(1-t) = 1 + -(1-t). Also t = t.
    // Actually: sub is add_neg: 1-(1-t) = 1 + (-(1-t)).
    // neg(1-t) = neg(1) + neg(neg(t)) by neg_add... no, neg_add gives -(a+b) ≡ -a + -b.
    // 1-t = 1 + (-t) [sub_is_add_neg]
    // -(1-t) = -(1 + (-t)) ≡ -1 + -(-t) ≡ -1 + t [neg_add + neg_involution]
    // 1 + -(1-t) ≡ 1 + (-1 + t) ≡ (1 + -1) + t ≡ 0 + t ≡ t
    // This is complex. Let me use a simpler approach via add commutativity:
    // convex(a,b,t) = t*a + (1-t)*b
    // convex(b,a,1-t) = (1-t)*b + (1-(1-t))*a
    // These are the same if t*a ≡ (1-(1-t))*a and then commuted.
    // Actually just show 1-(1-t) ≡ t, then both sides have the same terms commuted.

    // Step 1: Show 1 - (1-t) ≡ t
    // (1-t) + t ≡ 1 [sub_then_add_cancel(1,t)]
    lemma_sub_then_add_cancel::<F>(F::one(), t);
    // So 1 - (1-t) ≡ (1-t+t) - (1-t) ... no, let's use a direct approach.
    // We know (1-t)+t ≡ 1. Subtract (1-t) from both sides:
    // ((1-t)+t) - (1-t) ≡ 1 - (1-t)
    // And (1-t)+t - (1-t) ≡ t by add_then_sub_cancel(t, 1-t)... hmm, order matters.
    // add_then_sub_cancel(a, b): a + b - b ≡ a
    // So t + (1-t) - (1-t) ≡ t
    // And t + (1-t) ≡ (1-t) + t [comm] ≡ 1 [sub_then_add_cancel]
    // Hmm, let me use add_then_sub_cancel(t, 1-t): t + (1-t) - (1-t) ≡ t
    lemma_add_then_sub_cancel::<F>(t, F::one().sub(t));
    // And t + (1-t) ≡ 1: commute and use sub_then_add_cancel
    F::axiom_add_commutative(t, F::one().sub(t));
    F::axiom_eqv_symmetric(F::one().sub(t).add(t), t.add(F::one().sub(t)));
    F::axiom_eqv_transitive(t.add(F::one().sub(t)), F::one().sub(t).add(t), F::one());
    // So (t + (1-t)) - (1-t) ≡ 1 - (1-t)
    // via sub_congruence(t+(1-t), 1, 1-t, 1-t)
    F::axiom_eqv_reflexive(F::one().sub(t));
    lemma_sub_congruence::<F>(t.add(F::one().sub(t)), F::one(), F::one().sub(t), F::one().sub(t));
    // t+(1-t)-(1-t) ≡ 1-(1-t), and t+(1-t)-(1-t) ≡ t [add_then_sub_cancel]
    // So t ≡ 1-(1-t)
    F::axiom_eqv_symmetric(
        t.add(F::one().sub(t)).sub(F::one().sub(t)),
        t,
    );
    F::axiom_eqv_transitive(
        t,
        t.add(F::one().sub(t)).sub(F::one().sub(t)),
        F::one().sub(F::one().sub(t)),
    );
    // Flip: 1-(1-t) ≡ t
    F::axiom_eqv_symmetric(t, F::one().sub(F::one().sub(t)));

    // Step 2: (1-(1-t))*a ≡ t*a
    F::axiom_mul_congruence_left(F::one().sub(F::one().sub(t)), t, a);
    // Flip: t*a ≡ (1-(1-t))*a
    F::axiom_eqv_symmetric(F::one().sub(F::one().sub(t)).mul(a), t.mul(a));

    // Step 3: convex(b,a,1-t) = (1-t)*b + (1-(1-t))*a ≡ (1-t)*b + t*a
    lemma_add_congruence_right::<F>(
        F::one().sub(t).mul(b),
        F::one().sub(F::one().sub(t)).mul(a),
        t.mul(a),
    );
    // (1-t)*b + (1-(1-t))*a ≡ (1-t)*b + t*a

    // Step 4: (1-t)*b + t*a ≡ t*a + (1-t)*b [add_commutative]
    F::axiom_add_commutative(F::one().sub(t).mul(b), t.mul(a));
    F::axiom_eqv_symmetric(t.mul(a).add(F::one().sub(t).mul(b)), F::one().sub(t).mul(b).add(t.mul(a)));

    // Step 5: Chain: convex(b,a,1-t) ≡ (1-t)*b + t*a ≡ t*a + (1-t)*b = convex(a,b,t)
    F::axiom_eqv_transitive(
        F::one().sub(t).mul(b).add(F::one().sub(F::one().sub(t)).mul(a)),
        F::one().sub(t).mul(b).add(t.mul(a)),
        t.mul(a).add(F::one().sub(t).mul(b)),
    );

    // convex(a,b,t) ≡ convex(b,a,1-t) by symmetry
    F::axiom_eqv_symmetric(
        F::one().sub(t).mul(b).add(F::one().sub(F::one().sub(t)).mul(a)),
        t.mul(a).add(F::one().sub(t).mul(b)),
    );
}

/// a ≤ b and 0 ≤ t ≤ 1 implies a ≤ convex(a, b, t) ≤ b.
pub proof fn lemma_convex_bounds<F: OrderedField>(a: F, b: F, t: F)
    requires
        a.le(b),
        F::zero().le(t),
        t.le(F::one()),
    ensures
        a.le(convex::<F>(a, b, t)),
        convex::<F>(a, b, t).le(b),
{
    // convex(a,b,t) = t*a + (1-t)*b

    // Step 0: Establish 0 ≤ 1-t
    // t ≤ 1 → t+(-t) ≤ 1+(-t) [add_monotone]
    F::axiom_le_add_monotone(t, F::one(), t.neg());
    // t+(-t) ≡ 0 [add_inverse_right], 1+(-t) ≡ 1-t [sub_is_add_neg reversed]
    F::axiom_add_inverse_right(t);
    F::axiom_sub_is_add_neg(F::one(), t);
    F::axiom_eqv_symmetric(F::one().sub(t), F::one().add(t.neg()));
    F::axiom_le_congruence(
        t.add(t.neg()), F::zero(),
        F::one().add(t.neg()), F::one().sub(t),
    );
    // Now 0 ≤ 1-t is established

    // === Lower bound: a ≤ t*a + (1-t)*b ===
    // a ≡ t*a + (1-t)*a [convex_self]
    lemma_convex_self::<F>(a, t);
    // a ≤ b and 0 ≤ (1-t) → (1-t)*a ≤ (1-t)*b
    // le_mul_nonneg_monotone: a ≤ b and 0 ≤ c → a*c ≤ b*c
    F::axiom_le_mul_nonneg_monotone(a, b, F::one().sub(t));
    // a*(1-t) ≤ b*(1-t), commute to (1-t)*a ≤ (1-t)*b
    F::axiom_mul_commutative(a, F::one().sub(t));
    F::axiom_mul_commutative(b, F::one().sub(t));
    F::axiom_eqv_symmetric(F::one().sub(t).mul(a), a.mul(F::one().sub(t)));
    F::axiom_eqv_symmetric(F::one().sub(t).mul(b), b.mul(F::one().sub(t)));
    F::axiom_le_congruence(
        a.mul(F::one().sub(t)), F::one().sub(t).mul(a),
        b.mul(F::one().sub(t)), F::one().sub(t).mul(b),
    );
    // (1-t)*a ≤ (1-t)*b → t*a + (1-t)*a ≤ t*a + (1-t)*b [add_monotone on left]
    F::axiom_le_add_monotone(F::one().sub(t).mul(a), F::one().sub(t).mul(b), t.mul(a));
    // t*a + (1-t)*a ≤ t*a + (1-t)*b — but add_monotone gives (1-t)*a+t*a ≤ (1-t)*b+t*a
    // Need to commute both sides
    F::axiom_add_commutative(F::one().sub(t).mul(a), t.mul(a));
    F::axiom_add_commutative(F::one().sub(t).mul(b), t.mul(a));
    F::axiom_eqv_symmetric(t.mul(a).add(F::one().sub(t).mul(a)), F::one().sub(t).mul(a).add(t.mul(a)));
    F::axiom_eqv_symmetric(t.mul(a).add(F::one().sub(t).mul(b)), F::one().sub(t).mul(b).add(t.mul(a)));
    F::axiom_le_congruence(
        F::one().sub(t).mul(a).add(t.mul(a)),
        t.mul(a).add(F::one().sub(t).mul(a)),
        F::one().sub(t).mul(b).add(t.mul(a)),
        t.mul(a).add(F::one().sub(t).mul(b)),
    );
    // a ≡ t*a + (1-t)*a [convex_self], so a ≤ t*a + (1-t)*b
    F::axiom_eqv_symmetric(
        t.mul(a).add(F::one().sub(t).mul(a)),
        a,
    );
    F::axiom_eqv_reflexive(t.mul(a).add(F::one().sub(t).mul(b)));
    F::axiom_le_congruence(
        t.mul(a).add(F::one().sub(t).mul(a)),
        a,
        t.mul(a).add(F::one().sub(t).mul(b)),
        t.mul(a).add(F::one().sub(t).mul(b)),
    );

    // === Upper bound: t*a + (1-t)*b ≤ b ===
    // b ≡ t*b + (1-t)*b [convex_self]
    lemma_convex_self::<F>(b, t);
    // a ≤ b and 0 ≤ t → t*a ≤ t*b
    // le_mul_nonneg_monotone: a ≤ b and 0 ≤ t → a*t ≤ b*t
    F::axiom_le_mul_nonneg_monotone(a, b, t);
    // a*t ≤ b*t, commute to t*a ≤ t*b
    F::axiom_mul_commutative(a, t);
    F::axiom_mul_commutative(b, t);
    F::axiom_eqv_symmetric(t.mul(a), a.mul(t));
    F::axiom_eqv_symmetric(t.mul(b), b.mul(t));
    F::axiom_le_congruence(
        a.mul(t), t.mul(a),
        b.mul(t), t.mul(b),
    );
    // t*a ≤ t*b → t*a + (1-t)*b ≤ t*b + (1-t)*b [add_monotone with (1-t)*b]
    F::axiom_le_add_monotone(t.mul(a), t.mul(b), F::one().sub(t).mul(b));
    // t*a + (1-t)*b and t*b + (1-t)*b
    // add_monotone gives: t*a + (1-t)*b ≤ t*b + (1-t)*b [since the add is on left]
    // Wait, axiom is: a ≤ b → a+c ≤ b+c
    // So t*a ≤ t*b → t*a+(1-t)*b ≤ t*b+(1-t)*b ✓

    // t*b + (1-t)*b ≡ b [convex_self]
    F::axiom_eqv_reflexive(t.mul(a).add(F::one().sub(t).mul(b)));
    F::axiom_le_congruence(
        t.mul(a).add(F::one().sub(t).mul(b)),
        t.mul(a).add(F::one().sub(t).mul(b)),
        t.mul(b).add(F::one().sub(t).mul(b)),
        b,
    );
}

} // verus!
