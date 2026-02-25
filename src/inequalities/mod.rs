use vstd::prelude::*;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::OrderedField;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;

verus! {

/// Absolute value: returns a if a ≥ 0, otherwise -a.
pub open spec fn abs<R: OrderedRing>(a: R) -> R {
    if R::zero().le(a) { a } else { a.neg() }
}

/// 0 ≤ a and 0 ≤ b implies 0 ≤ a + b.
pub proof fn lemma_nonneg_add<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().le(a),
        R::zero().le(b),
    ensures
        R::zero().le(a.add(b)),
{
    R::axiom_le_add_monotone(R::zero(), a, b);
    lemma_add_zero_left::<R>(b);
    lemma_le_congruence_left::<R>(R::zero().add(b), b, a.add(b));
    R::axiom_le_transitive(R::zero(), b, a.add(b));
}

/// 0 ≤ abs(a).
pub proof fn lemma_abs_nonneg<R: OrderedRing>(a: R)
    ensures
        R::zero().le(abs::<R>(a)),
{
    R::axiom_le_total(R::zero(), a);
    if !R::zero().le(a) {
        lemma_le_neg_flip::<R>(a, R::zero());
        lemma_neg_zero::<R>();
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
        lemma_le_congruence_left::<R>(R::zero().neg(), R::zero(), a.neg());
    }
}

/// abs(0) ≡ 0.
pub proof fn lemma_abs_zero<R: OrderedRing>()
    ensures
        abs::<R>(R::zero()).eqv(R::zero()),
{
    R::axiom_le_reflexive(R::zero());
    R::axiom_eqv_reflexive(R::zero());
}

/// abs(-a) ≡ abs(a).
pub proof fn lemma_abs_neg<R: OrderedRing>(a: R)
    ensures
        abs::<R>(a.neg()).eqv(abs::<R>(a)),
{
    R::axiom_le_total(R::zero(), a);
    R::axiom_le_total(R::zero(), a.neg());

    if R::zero().le(a) && R::zero().le(a.neg()) {
        lemma_neg_nonneg_iff::<R>(a);
        R::axiom_le_antisymmetric(a.neg(), R::zero());
        R::axiom_neg_congruence(a.neg(), R::zero());
        lemma_neg_involution::<R>(a);
        lemma_neg_zero::<R>();
        R::axiom_eqv_symmetric(a.neg().neg(), a);
        R::axiom_eqv_transitive(a, a.neg().neg(), R::zero().neg());
        R::axiom_eqv_transitive(a, R::zero().neg(), R::zero());
        R::axiom_eqv_symmetric(a, R::zero());
        R::axiom_eqv_transitive(a.neg(), R::zero(), a);
    } else if R::zero().le(a) && !R::zero().le(a.neg()) {
        lemma_neg_involution::<R>(a);
    } else if !R::zero().le(a) && R::zero().le(a.neg()) {
        R::axiom_eqv_reflexive(a.neg());
    } else {
        lemma_neg_nonpos_iff::<R>(a);
    }
}

/// abs(a * b) ≡ abs(a) * abs(b) for OrderedField.
pub proof fn lemma_abs_mul<F: OrderedField>(a: F, b: F)
    ensures
        abs::<F>(a.mul(b)).eqv(abs::<F>(a).mul(abs::<F>(b))),
{
    F::axiom_le_total(F::zero(), a);
    F::axiom_le_total(F::zero(), b);

    if F::zero().le(a) && F::zero().le(b) {
        lemma_nonneg_mul_nonneg::<F>(a, b);
        F::axiom_eqv_reflexive(a.mul(b));
    } else if F::zero().le(a) && !F::zero().le(b) {
        // abs(a)=a, abs(b)=-b, abs(a)*abs(b) = a*(-b)
        // a*(-b) ≡ -(a*b)
        lemma_mul_neg_right::<F>(a, b);
        // Show a*b ≤ 0: b ≤ 0 and 0 ≤ a → a*b ≤ a*0 = 0
        // Wait: le_mul_nonneg_monotone(b, 0, a) needs b ≤ 0 and 0 ≤ a → b*a ≤ 0*a
        F::axiom_le_mul_nonneg_monotone(b, F::zero(), a);
        lemma_mul_zero_left::<F>(a);
        F::axiom_mul_commutative(b, a);
        F::axiom_eqv_symmetric(b.mul(a), a.mul(b));
        // b*a ≤ 0*a, and b*a ≡ a*b, 0*a ≡ 0
        F::axiom_eqv_symmetric(b.mul(a), a.mul(b));
        F::axiom_le_congruence(b.mul(a), a.mul(b), F::zero().mul(a), F::zero());

        if F::zero().le(a.mul(b)) {
            // a*b ≡ 0, so abs(a*b) = a*b, abs(a)*abs(b) = a*(-b)
            F::axiom_le_antisymmetric(a.mul(b), F::zero());
            F::axiom_eqv_symmetric(a.mul(b), F::zero());
            F::axiom_neg_congruence(a.mul(b), F::zero());
            lemma_neg_zero::<F>();
            F::axiom_eqv_transitive(a.mul(b).neg(), F::zero().neg(), F::zero());
            F::axiom_eqv_transitive(a.mul(b.neg()), a.mul(b).neg(), F::zero());
            F::axiom_eqv_symmetric(a.mul(b.neg()), F::zero());
            F::axiom_eqv_transitive(a.mul(b), F::zero(), a.mul(b.neg()));
        } else {
            // abs(a*b) = -(a*b), and a*(-b) ≡ -(a*b), so -(a*b) ≡ a*(-b)
            F::axiom_eqv_symmetric(a.mul(b.neg()), a.mul(b).neg());
        }
    } else if !F::zero().le(a) && F::zero().le(b) {
        // abs(a)=-a, abs(b)=b, abs(a)*abs(b) = (-a)*b
        // (-a)*b ≡ -(a*b)
        lemma_mul_neg_left::<F>(a, b);
        // a*b ≤ 0: a ≤ 0 and 0 ≤ b → a*b ≤ 0*b = 0
        F::axiom_le_mul_nonneg_monotone(a, F::zero(), b);
        lemma_mul_zero_left::<F>(b);
        F::axiom_eqv_reflexive(a.mul(b));
        F::axiom_le_congruence(a.mul(b), a.mul(b), F::zero().mul(b), F::zero());

        if F::zero().le(a.mul(b)) {
            F::axiom_le_antisymmetric(a.mul(b), F::zero());
            F::axiom_eqv_symmetric(a.mul(b), F::zero());
            F::axiom_neg_congruence(a.mul(b), F::zero());
            lemma_neg_zero::<F>();
            F::axiom_eqv_transitive(a.mul(b).neg(), F::zero().neg(), F::zero());
            F::axiom_eqv_transitive(a.neg().mul(b), a.mul(b).neg(), F::zero());
            F::axiom_eqv_symmetric(a.neg().mul(b), F::zero());
            F::axiom_eqv_transitive(a.mul(b), F::zero(), a.neg().mul(b));
        } else {
            F::axiom_eqv_symmetric(a.neg().mul(b), a.mul(b).neg());
        }
    } else {
        // abs(a)=-a, abs(b)=-b, abs(a)*abs(b) = (-a)*(-b) ≡ a*b
        lemma_neg_nonpos_iff::<F>(a);
        lemma_neg_nonpos_iff::<F>(b);
        lemma_nonneg_mul_nonneg::<F>(a.neg(), b.neg());
        lemma_neg_mul_neg::<F>(a, b);
        lemma_le_congruence_right::<F>(F::zero(), a.neg().mul(b.neg()), a.mul(b));
        F::axiom_eqv_symmetric(a.neg().mul(b.neg()), a.mul(b));
    }
}

/// Triangle inequality: abs(a + b) ≤ abs(a) + abs(b).
pub proof fn lemma_triangle_inequality<R: OrderedRing>(a: R, b: R)
    ensures
        abs::<R>(a.add(b)).le(abs::<R>(a).add(abs::<R>(b))),
{
    R::axiom_le_total(R::zero(), a);
    R::axiom_le_total(R::zero(), b);

    if R::zero().le(a) && R::zero().le(b) {
        // abs = a+b, target = a+b, trivial
        lemma_nonneg_add::<R>(a, b);
        R::axiom_le_reflexive(a.add(b));
    } else if R::zero().le(a) && !R::zero().le(b) {
        // abs(a)=a, abs(b)=-b, target=a+(-b)
        if R::zero().le(a.add(b)) {
            // abs(a+b)=a+b, need: a+b ≤ a+(-b)
            // b ≤ -b (from b ≤ 0 ≤ -b)
            lemma_neg_nonpos_iff::<R>(b);
            R::axiom_le_transitive(b, R::zero(), b.neg());
            R::axiom_le_add_monotone(b, b.neg(), a);
            // b+a ≤ (-b)+a, commute both sides
            R::axiom_add_commutative(b, a);
            R::axiom_add_commutative(b.neg(), a);
            R::axiom_eqv_symmetric(a.add(b), b.add(a));
            R::axiom_eqv_symmetric(a.add(b.neg()), b.neg().add(a));
            R::axiom_le_congruence(b.add(a), a.add(b), b.neg().add(a), a.add(b.neg()));
        } else {
            // abs(a+b)=-(a+b), need: -(a+b) ≤ a+(-b)
            // -(a+b) ≡ (-a)+(-b)
            lemma_neg_add::<R>(a, b);
            // -a ≤ a (from -a ≤ 0 ≤ a)
            lemma_neg_nonneg_iff::<R>(a);
            R::axiom_le_transitive(a.neg(), R::zero(), a);
            // (-a)+(-b) ≤ a+(-b)
            R::axiom_le_add_monotone(a.neg(), a, b.neg());
            // -(a+b) ≡ (-a)+(-b) ≤ a+(-b)
            R::axiom_eqv_symmetric(a.add(b).neg(), a.neg().add(b.neg()));
            R::axiom_eqv_reflexive(a.add(b.neg()));
            R::axiom_le_congruence(
                a.neg().add(b.neg()), a.add(b).neg(),
                a.add(b.neg()), a.add(b.neg()),
            );
        }
    } else if !R::zero().le(a) && R::zero().le(b) {
        // abs(a)=-a, abs(b)=b, target=(-a)+b
        if R::zero().le(a.add(b)) {
            // abs(a+b)=a+b, need: a+b ≤ (-a)+b
            // a ≤ -a (from a ≤ 0 ≤ -a)
            lemma_neg_nonpos_iff::<R>(a);
            R::axiom_le_transitive(a, R::zero(), a.neg());
            R::axiom_le_add_monotone(a, a.neg(), b);
            // a+b ≤ (-a)+b
        } else {
            // abs(a+b)=-(a+b), need: -(a+b) ≤ (-a)+b
            // -(a+b) ≡ (-a)+(-b)
            lemma_neg_add::<R>(a, b);
            // -b ≤ b (from -b ≤ 0 ≤ b)
            lemma_neg_nonneg_iff::<R>(b);
            R::axiom_le_transitive(b.neg(), R::zero(), b);
            // (-b)+(-a) ≤ b+(-a) from add_monotone(-b, b, -a)
            R::axiom_le_add_monotone(b.neg(), b, a.neg());
            // (-b)+(-a) ≤ b+(-a), commute both sides
            R::axiom_add_commutative(b.neg(), a.neg());
            R::axiom_add_commutative(b, a.neg());
            R::axiom_eqv_symmetric(a.neg().add(b.neg()), b.neg().add(a.neg()));
            R::axiom_eqv_symmetric(a.neg().add(b), b.add(a.neg()));
            R::axiom_le_congruence(
                b.neg().add(a.neg()), a.neg().add(b.neg()),
                b.add(a.neg()), a.neg().add(b),
            );
            // -(a+b) ≡ (-a)+(-b) ≤ (-a)+b
            R::axiom_eqv_symmetric(a.add(b).neg(), a.neg().add(b.neg()));
            R::axiom_eqv_reflexive(a.neg().add(b));
            R::axiom_le_congruence(
                a.neg().add(b.neg()), a.add(b).neg(),
                a.neg().add(b), a.neg().add(b),
            );
        }
    } else {
        // a ≤ 0, b ≤ 0, abs(a)=-a, abs(b)=-b, target=(-a)+(-b)
        // a+b ≤ 0
        R::axiom_le_add_monotone(a, R::zero(), b);
        lemma_add_zero_left::<R>(b);
        lemma_le_congruence_right::<R>(a.add(b), R::zero().add(b), b);
        R::axiom_le_transitive(a.add(b), b, R::zero());

        if R::zero().le(a.add(b)) {
            // a+b ≡ 0 (from a+b ≤ 0 and 0 ≤ a+b)
            R::axiom_le_antisymmetric(a.add(b), R::zero());
            // abs(a+b) = a+b, need: a+b ≤ (-a)+(-b)
            lemma_neg_nonpos_iff::<R>(a);
            lemma_neg_nonpos_iff::<R>(b);
            lemma_nonneg_add::<R>(a.neg(), b.neg());
            // a+b ≡ 0 ≤ (-a)+(-b)
            R::axiom_eqv_symmetric(a.add(b), R::zero());
            R::axiom_eqv_reflexive(a.neg().add(b.neg()));
            R::axiom_le_congruence(
                R::zero(), a.add(b),
                a.neg().add(b.neg()), a.neg().add(b.neg()),
            );
        } else {
            // abs(a+b) = -(a+b) ≡ (-a)+(-b), done by reflexivity
            lemma_neg_add::<R>(a, b);
            R::axiom_eqv_symmetric(a.add(b).neg(), a.neg().add(b.neg()));
            R::axiom_le_reflexive(a.neg().add(b.neg()));
            lemma_le_congruence_left::<R>(
                a.neg().add(b.neg()),
                a.add(b).neg(),
                a.neg().add(b.neg()),
            );
        }
    }
}

/// 0 ≤ a*a + b*b.
pub proof fn lemma_sum_squares_nonneg_2d<R: OrderedRing>(a: R, b: R)
    ensures
        R::zero().le(a.mul(a).add(b.mul(b))),
{
    lemma_square_nonneg::<R>(a);
    lemma_square_nonneg::<R>(b);
    lemma_nonneg_add::<R>(a.mul(a), b.mul(b));
}

/// 0 ≤ a*a + b*b + c*c.
pub proof fn lemma_sum_squares_nonneg_3d<R: OrderedRing>(a: R, b: R, c: R)
    ensures
        R::zero().le(a.mul(a).add(b.mul(b)).add(c.mul(c))),
{
    lemma_sum_squares_nonneg_2d::<R>(a, b);
    lemma_square_nonneg::<R>(c);
    lemma_nonneg_add::<R>(a.mul(a).add(b.mul(b)), c.mul(c));
}

/// a ≡ b implies abs(a) ≡ abs(b).
pub proof fn lemma_abs_eqv<R: OrderedRing>(a: R, b: R)
    requires
        a.eqv(b),
    ensures
        abs::<R>(a).eqv(abs::<R>(b)),
{
    R::axiom_le_total(R::zero(), a);
    if R::zero().le(a) {
        // a ≡ b, 0 ≤ a → 0 ≤ b via congruence
        R::axiom_eqv_reflexive(R::zero());
        R::axiom_le_congruence(R::zero(), R::zero(), a, b);
        // abs(a) = a, abs(b) = b, a ≡ b
    } else {
        // ¬(0 ≤ a), show ¬(0 ≤ b) by contradiction
        if R::zero().le(b) {
            // 0 ≤ b and b ≡ a (symmetric) gives 0 ≤ a
            R::axiom_eqv_symmetric(a, b);
            R::axiom_eqv_reflexive(R::zero());
            R::axiom_le_congruence(R::zero(), R::zero(), b, a);
        }
        // abs(a) = -a, abs(b) = -b
        R::axiom_neg_congruence(a, b);
    }
}

/// abs(a - b) ≡ abs(b - a).
pub proof fn lemma_abs_sub_symmetric<R: OrderedRing>(a: R, b: R)
    ensures
        abs::<R>(a.sub(b)).eqv(abs::<R>(b.sub(a))),
{
    // a - b ≡ -(b - a) [sub_antisymmetric]
    lemma_sub_antisymmetric::<R>(a, b);
    // abs(a - b) ≡ abs(-(b - a)) [abs_eqv]
    lemma_abs_eqv::<R>(a.sub(b), b.sub(a).neg());
    // abs(-(b - a)) ≡ abs(b - a) [abs_neg]
    lemma_abs_neg::<R>(b.sub(a));
    R::axiom_eqv_transitive(abs::<R>(a.sub(b)), abs::<R>(b.sub(a).neg()), abs::<R>(b.sub(a)));
}

/// 0 ≤ b implies: abs(a) ≤ b if and only if b.neg() ≤ a and a ≤ b.
pub proof fn lemma_abs_le_iff<R: OrderedRing>(a: R, b: R)
    requires
        R::zero().le(b),
    ensures
        abs::<R>(a).le(b) == (b.neg().le(a) && a.le(b)),
{
    R::axiom_le_total(R::zero(), a);

    if R::zero().le(a) {
        // abs(a) = a
        if a.le(b) {
            // abs(a) ≤ b ✓, need -b ≤ a
            // -b ≤ 0 ≤ a
            lemma_neg_nonneg_iff::<R>(b);
            R::axiom_le_transitive(b.neg(), R::zero(), a);
        }
        if b.neg().le(a) && a.le(b) {
            // abs(a) = a ≤ b ✓
        }
    } else {
        // abs(a) = -a
        if a.neg().le(b) {
            // abs(a) ≤ b ✓, need -b ≤ a and a ≤ b
            // a ≤ 0 ≤ b
            R::axiom_le_total(a, R::zero());
            if !a.le(R::zero()) {
                // a > 0, contradiction with ¬(0 ≤ a)
                R::axiom_le_total(R::zero(), a);
            }
            R::axiom_le_transitive(a, R::zero(), b);
            // -a ≤ b → -b ≤ --a = a
            lemma_le_neg_flip::<R>(a.neg(), b);
            lemma_neg_involution::<R>(a);
            lemma_le_congruence_right::<R>(b.neg(), a.neg().neg(), a);
        }
        if b.neg().le(a) && a.le(b) {
            // need abs(a) = -a ≤ b
            // -b ≤ a → -a ≤ --b = b
            lemma_le_neg_flip::<R>(b.neg(), a);
            lemma_neg_involution::<R>(b);
            lemma_le_congruence_right::<R>(a.neg(), b.neg().neg(), b);
        }
    }
}

/// abs(abs(a) - abs(b)) ≤ abs(a - b)   (reverse triangle inequality).
pub proof fn lemma_reverse_triangle<R: OrderedRing>(a: R, b: R)
    ensures
        abs::<R>(abs::<R>(a).sub(abs::<R>(b))).le(abs::<R>(a.sub(b))),
{
    // Strategy: show both abs(a)-abs(b) ≤ abs(a-b) and abs(b)-abs(a) ≤ abs(a-b)
    // then case split on sign of abs(a)-abs(b).

    // --- Step 1: abs(a) - abs(b) ≤ abs(a-b) ---
    // Write a = (a - b) + b
    // Triangle: abs((a-b) + b) ≤ abs(a-b) + abs(b)
    // (a-b) + b ≡ a, so abs(a) ≡ abs((a-b)+b) ≤ abs(a-b) + abs(b)
    lemma_sub_then_add_cancel::<R>(a, b);
    R::axiom_eqv_symmetric(a.sub(b).add(b), a);
    lemma_abs_eqv::<R>(a, a.sub(b).add(b));
    lemma_triangle_inequality::<R>(a.sub(b), b);
    // abs(a) ≡ abs((a-b)+b) ≤ abs(a-b) + abs(b)
    R::axiom_eqv_symmetric(abs::<R>(a), abs::<R>(a.sub(b).add(b)));
    lemma_le_congruence_left::<R>(abs::<R>(a.sub(b).add(b)), abs::<R>(a), abs::<R>(a.sub(b)).add(abs::<R>(b)));
    // abs(a) ≤ abs(a-b) + abs(b)
    // → abs(a) - abs(b) ≤ abs(a-b)
    lemma_le_sub_monotone::<R>(abs::<R>(a), abs::<R>(a.sub(b)).add(abs::<R>(b)), abs::<R>(b));
    // abs(a-b) + abs(b) - abs(b) ≡ abs(a-b) [add_then_sub_cancel]
    lemma_add_then_sub_cancel::<R>(abs::<R>(a.sub(b)), abs::<R>(b));
    lemma_le_congruence_right::<R>(
        abs::<R>(a).sub(abs::<R>(b)),
        abs::<R>(a.sub(b)).add(abs::<R>(b)).sub(abs::<R>(b)),
        abs::<R>(a.sub(b)),
    );

    // --- Step 2: abs(b) - abs(a) ≤ abs(a-b) ---
    // Write b = (b - a) + a
    lemma_sub_then_add_cancel::<R>(b, a);
    R::axiom_eqv_symmetric(b.sub(a).add(a), b);
    lemma_abs_eqv::<R>(b, b.sub(a).add(a));
    lemma_triangle_inequality::<R>(b.sub(a), a);
    R::axiom_eqv_symmetric(abs::<R>(b), abs::<R>(b.sub(a).add(a)));
    lemma_le_congruence_left::<R>(abs::<R>(b.sub(a).add(a)), abs::<R>(b), abs::<R>(b.sub(a)).add(abs::<R>(a)));
    // abs(b) ≤ abs(b-a) + abs(a)
    // abs(b-a) ≡ abs(a-b)
    lemma_abs_sub_symmetric::<R>(b, a);
    R::axiom_add_congruence_left(abs::<R>(b.sub(a)), abs::<R>(a.sub(b)), abs::<R>(a));
    lemma_le_congruence_right::<R>(abs::<R>(b), abs::<R>(b.sub(a)).add(abs::<R>(a)), abs::<R>(a.sub(b)).add(abs::<R>(a)));
    // abs(b) ≤ abs(a-b) + abs(a)
    // abs(a-b) + abs(a) ≡ abs(a) + abs(a-b) [comm]
    R::axiom_add_commutative(abs::<R>(a.sub(b)), abs::<R>(a));
    lemma_le_congruence_right::<R>(abs::<R>(b), abs::<R>(a.sub(b)).add(abs::<R>(a)), abs::<R>(a).add(abs::<R>(a.sub(b))));
    // abs(b) ≤ abs(a) + abs(a-b)
    // → abs(b) - abs(a) ≤ abs(a-b)
    lemma_le_sub_monotone::<R>(abs::<R>(b), abs::<R>(a).add(abs::<R>(a.sub(b))), abs::<R>(a));
    lemma_add_then_sub_cancel::<R>(abs::<R>(a.sub(b)), abs::<R>(a));
    R::axiom_add_commutative(abs::<R>(a.sub(b)), abs::<R>(a));
    R::axiom_eqv_symmetric(abs::<R>(a.sub(b)).add(abs::<R>(a)), abs::<R>(a).add(abs::<R>(a.sub(b))));
    // abs(a) + abs(a-b) - abs(a) ≡ abs(a-b) + abs(a) - abs(a)
    R::axiom_eqv_reflexive(abs::<R>(a));
    lemma_sub_congruence::<R>(
        abs::<R>(a).add(abs::<R>(a.sub(b))),
        abs::<R>(a.sub(b)).add(abs::<R>(a)),
        abs::<R>(a),
        abs::<R>(a),
    );
    R::axiom_eqv_transitive(
        abs::<R>(a).add(abs::<R>(a.sub(b))).sub(abs::<R>(a)),
        abs::<R>(a.sub(b)).add(abs::<R>(a)).sub(abs::<R>(a)),
        abs::<R>(a.sub(b)),
    );
    lemma_le_congruence_right::<R>(
        abs::<R>(b).sub(abs::<R>(a)),
        abs::<R>(a).add(abs::<R>(a.sub(b))).sub(abs::<R>(a)),
        abs::<R>(a.sub(b)),
    );

    // --- Step 3: case split on sign of abs(a) - abs(b) ---
    R::axiom_le_total(R::zero(), abs::<R>(a).sub(abs::<R>(b)));
    if R::zero().le(abs::<R>(a).sub(abs::<R>(b))) {
        // abs(abs(a) - abs(b)) = abs(a) - abs(b) ≤ abs(a-b) [from step 1]
    } else {
        // abs(abs(a) - abs(b)) = -(abs(a) - abs(b))
        // We know from step 2: abs(b)-abs(a) ≤ abs(a-b)
        // Show -(abs(a)-abs(b)) ≡ abs(b)-abs(a) via sub_antisymmetric
        lemma_sub_antisymmetric::<R>(abs::<R>(a), abs::<R>(b));
        // abs(a)-abs(b) ≡ -(abs(b)-abs(a))
        R::axiom_neg_congruence(abs::<R>(a).sub(abs::<R>(b)), abs::<R>(b).sub(abs::<R>(a)).neg());
        // -(abs(a)-abs(b)) ≡ -(-(abs(b)-abs(a)))
        lemma_neg_involution::<R>(abs::<R>(b).sub(abs::<R>(a)));
        // -(-(abs(b)-abs(a))) ≡ abs(b)-abs(a)
        R::axiom_eqv_transitive(
            abs::<R>(a).sub(abs::<R>(b)).neg(),
            abs::<R>(b).sub(abs::<R>(a)).neg().neg(),
            abs::<R>(b).sub(abs::<R>(a)),
        );
        // abs(b)-abs(a) ≡ -(abs(a)-abs(b))
        R::axiom_eqv_symmetric(
            abs::<R>(a).sub(abs::<R>(b)).neg(),
            abs::<R>(b).sub(abs::<R>(a)),
        );
        // abs(b)-abs(a) ≤ abs(a-b) [from step 2] + congruence:
        // -(abs(a)-abs(b)) ≤ abs(a-b)
        lemma_le_congruence_left::<R>(
            abs::<R>(b).sub(abs::<R>(a)),
            abs::<R>(a).sub(abs::<R>(b)).neg(),
            abs::<R>(a.sub(b)),
        );
    }
}

/// Signum function: returns 1 if a > 0, -1 if a < 0, 0 if a ≡ 0.
pub open spec fn signum<R: OrderedRing>(a: R) -> R {
    if R::zero().lt(a) { R::one() }
    else if a.lt(R::zero()) { R::one().neg() }
    else { R::zero() }
}

/// 0 < a implies signum(a) ≡ 1.
pub proof fn lemma_signum_pos<R: OrderedRing>(a: R)
    requires
        R::zero().lt(a),
    ensures
        signum::<R>(a).eqv(R::one()),
{
    R::axiom_eqv_reflexive(R::one());
}

/// a < 0 implies signum(a) ≡ -1.
pub proof fn lemma_signum_neg<R: OrderedRing>(a: R)
    requires
        a.lt(R::zero()),
    ensures
        signum::<R>(a).eqv(R::one().neg()),
{
    // Need to show ¬(0 < a) so spec unfolds to second branch
    lemma_lt_asymmetric::<R>(a, R::zero());
    R::axiom_eqv_reflexive(R::one().neg());
}

/// signum(0) ≡ 0.
pub proof fn lemma_signum_zero<R: OrderedRing>()
    ensures
        signum::<R>(R::zero()).eqv(R::zero()),
{
    lemma_lt_irreflexive::<R>(R::zero());
    R::axiom_eqv_reflexive(R::zero());
}

/// signum(-a) ≡ -signum(a).
pub proof fn lemma_signum_neg_flip<R: OrderedRing>(a: R)
    ensures
        signum::<R>(a.neg()).eqv(signum::<R>(a).neg()),
{
    lemma_trichotomy::<R>(R::zero(), a);

    if R::zero().lt(a) {
        // 0 < a implies -a < 0
        lemma_lt_neg_flip::<R>(R::zero(), a);
        lemma_neg_zero::<R>();
        // -a < -0, unpack to get -a ≤ -0
        R::axiom_lt_iff_le_and_not_eqv(a.neg(), R::zero().neg());
        // -a ≤ -0 and -0 ≡ 0, so -a ≤ 0
        lemma_le_congruence_right::<R>(a.neg(), R::zero().neg(), R::zero());
        // Establish a.neg().lt(R::zero())
        R::axiom_lt_iff_le_and_not_eqv(a.neg(), R::zero());
        if a.neg().eqv(R::zero()) {
            R::axiom_neg_congruence(a.neg(), R::zero());
            lemma_neg_involution::<R>(a);
            lemma_neg_zero::<R>();
            R::axiom_eqv_symmetric(a.neg().neg(), a);
            R::axiom_eqv_transitive(a, a.neg().neg(), R::zero().neg());
            R::axiom_eqv_transitive(a, R::zero().neg(), R::zero());
            R::axiom_eqv_symmetric(a, R::zero());
            R::axiom_lt_iff_le_and_not_eqv(R::zero(), a);
        }
        // Now a.neg().lt(R::zero()) is established
        // Establish ¬(R::zero().lt(a.neg())): since a.neg().lt(R::zero()), asymmetry gives ¬(R::zero().lt(a.neg()))
        lemma_lt_asymmetric::<R>(a.neg(), R::zero());
        // signum(a) = 1 (first branch, since 0 < a)
        // signum(-a) = -1 (second branch, since ¬(0 < -a) and -a < 0)
        // Need: -1 ≡ -(1), which is reflexivity
        R::axiom_eqv_reflexive(R::one().neg());
    } else if R::zero().eqv(a) {
        // 0 ≡ a
        R::axiom_eqv_symmetric(R::zero(), a);
        // Now a.eqv(R::zero())
        // Establish ¬(0 < a) and ¬(a < 0)
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a);
        R::axiom_lt_iff_le_and_not_eqv(a, R::zero());
        // signum(a) = 0 (third branch)

        // -a ≡ -0 ≡ 0
        R::axiom_neg_congruence(a, R::zero());
        lemma_neg_zero::<R>();
        R::axiom_eqv_transitive(a.neg(), R::zero().neg(), R::zero());
        // Establish ¬(0 < -a) and ¬(-a < 0)
        R::axiom_eqv_symmetric(a.neg(), R::zero());
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a.neg());
        R::axiom_eqv_symmetric(R::zero(), a.neg());
        R::axiom_lt_iff_le_and_not_eqv(a.neg(), R::zero());
        // signum(-a) = 0 (third branch)

        // Need: 0 ≡ -(0), i.e. 0 ≡ 0.neg()
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
    } else {
        // a < 0
        // -a > 0 via lt_neg_flip
        lemma_lt_neg_flip::<R>(a, R::zero());
        lemma_neg_zero::<R>();
        // -0.lt(-a), i.e. R::zero().neg().lt(a.neg())
        R::axiom_lt_iff_le_and_not_eqv(R::zero().neg(), a.neg());
        R::axiom_eqv_symmetric(R::zero().neg(), R::zero());
        lemma_le_congruence_left::<R>(R::zero().neg(), R::zero(), a.neg());
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a.neg());
        if R::zero().eqv(a.neg()) {
            R::axiom_neg_congruence(R::zero(), a.neg());
            lemma_neg_involution::<R>(a);
            R::axiom_eqv_transitive(R::zero().neg(), a.neg().neg(), a);
            R::axiom_eqv_transitive(R::zero(), R::zero().neg(), a);
            R::axiom_eqv_symmetric(R::zero(), a);
            R::axiom_lt_iff_le_and_not_eqv(a, R::zero());
            R::axiom_eqv_symmetric(a, R::zero());
        }
        // Now R::zero().lt(a.neg())
        // Establish ¬(a < 0)... wait, we have a.lt(R::zero()) from else branch.
        // For signum(a): ¬(0 < a) from lt_asymmetric
        lemma_lt_asymmetric::<R>(a, R::zero());
        // signum(a) = -1 (second branch: ¬(0 < a) and a < 0)
        // signum(-a) = 1 (first branch: 0 < -a)
        // Need: 1 ≡ -(-1), i.e. R::one().eqv(R::one().neg().neg())
        lemma_neg_involution::<R>(R::one());
        R::axiom_eqv_symmetric(R::one().neg().neg(), R::one());
    }
}

/// signum(a) * abs(a) ≡ a.
pub proof fn lemma_signum_abs<R: OrderedRing>(a: R)
    ensures
        signum::<R>(a).mul(abs::<R>(a)).eqv(a),
{
    lemma_trichotomy::<R>(R::zero(), a);

    if R::zero().lt(a) {
        // signum(a) = 1, abs(a) = a (since 0 ≤ a from 0 < a)
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a);
        // 1 * a ≡ a
        lemma_mul_one_left::<R>(a);
    } else if R::zero().eqv(a) {
        // signum(a) = 0, abs(a) = 0 or a
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a);
        R::axiom_lt_iff_le_and_not_eqv(a, R::zero());
        R::axiom_eqv_symmetric(R::zero(), a);
        // Both branches give signum = 0
        // 0 * abs(a) ≡ 0 ≡ a
        R::axiom_le_reflexive(R::zero());
        R::axiom_eqv_reflexive(R::zero());
        // 0 ≤ 0 ≡ a, so 0 ≤ a, so abs(a) = a
        R::axiom_le_congruence(R::zero(), R::zero(), R::zero(), a);
        // abs(a) = a, signum(a) = 0
        // 0 * a ≡ 0 ≡ a
        lemma_mul_zero_left::<R>(a);
        R::axiom_eqv_transitive(R::zero().mul(a), R::zero(), a);
    } else {
        // a < 0, signum(a) = -1, abs(a) = -a (since ¬(0 ≤ a))
        lemma_lt_asymmetric::<R>(a, R::zero());
        // ¬(0 < a) ✓
        // Need ¬(0 ≤ a) for abs to be -a
        R::axiom_lt_iff_le_and_not_eqv(a, R::zero());
        if R::zero().le(a) {
            R::axiom_le_antisymmetric(a, R::zero());
            R::axiom_eqv_symmetric(a, R::zero());
        }
        // (-1) * (-a) ≡ -((-a)) ... no, let's use neg_mul_neg
        // (-1) * (-a) ≡ 1 * a [neg_mul_neg(1, a)]
        lemma_neg_mul_neg::<R>(R::one(), a);
        // 1 * a ≡ a [mul_one_left]
        lemma_mul_one_left::<R>(a);
        R::axiom_eqv_transitive(R::one().neg().mul(a.neg()), R::one().mul(a), a);
    }
}

/// signum(a*b) ≡ signum(a) * signum(b) (for OrderedField).
pub proof fn lemma_signum_mul<F: OrderedField>(a: F, b: F)
    ensures
        signum::<F>(a.mul(b)).eqv(signum::<F>(a).mul(signum::<F>(b))),
{
    lemma_trichotomy::<F>(F::zero(), a);
    lemma_trichotomy::<F>(F::zero(), b);

    if F::zero().lt(a) && F::zero().lt(b) {
        lemma_mul_pos_pos::<F>(a, b);
        // 1≡1*1
        F::axiom_mul_one_right(F::one());
        F::axiom_eqv_symmetric(F::one().mul(F::one()), F::one());
    } else if F::zero().lt(a) && F::zero().eqv(b) {
        F::axiom_eqv_symmetric(F::zero(), b);
        lemma_mul_congruence_right::<F>(a, b, F::zero());
        F::axiom_mul_zero_right(a);
        F::axiom_eqv_transitive(a.mul(b), a.mul(F::zero()), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(b, F::zero());
        // 0≡1*0
        F::axiom_mul_zero_right(F::one());
        F::axiom_eqv_symmetric(F::one().mul(F::zero()), F::zero());
    } else if F::zero().lt(a) && b.lt(F::zero()) {
        lemma_mul_pos_neg::<F>(a, b);
        lemma_lt_asymmetric::<F>(a.mul(b), F::zero());
        // (-1)≡1*(-1)
        lemma_mul_one_left::<F>(F::one().neg());
        F::axiom_eqv_symmetric(F::one().mul(F::one().neg()), F::one().neg());
    } else if F::zero().eqv(a) && F::zero().lt(b) {
        F::axiom_eqv_symmetric(F::zero(), a);
        F::axiom_mul_congruence_left(a, F::zero(), b);
        lemma_mul_zero_left::<F>(b);
        F::axiom_eqv_transitive(a.mul(b), F::zero().mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
        F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
        F::axiom_eqv_symmetric(a, F::zero());
        // 0≡0*1
        lemma_mul_zero_left::<F>(F::one());
        F::axiom_eqv_symmetric(F::zero().mul(F::one()), F::zero());
    } else if F::zero().eqv(a) && F::zero().eqv(b) {
        F::axiom_eqv_symmetric(F::zero(), a);
        F::axiom_mul_congruence_left(a, F::zero(), b);
        lemma_mul_zero_left::<F>(b);
        F::axiom_eqv_transitive(a.mul(b), F::zero().mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
        F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
        F::axiom_eqv_symmetric(a, F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(b, F::zero());
        // 0≡0*0
        F::axiom_mul_zero_right(F::zero());
        F::axiom_eqv_symmetric(F::zero().mul(F::zero()), F::zero());
    } else if F::zero().eqv(a) && b.lt(F::zero()) {
        F::axiom_eqv_symmetric(F::zero(), a);
        F::axiom_mul_congruence_left(a, F::zero(), b);
        lemma_mul_zero_left::<F>(b);
        F::axiom_eqv_transitive(a.mul(b), F::zero().mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a);
        F::axiom_lt_iff_le_and_not_eqv(a, F::zero());
        F::axiom_eqv_symmetric(a, F::zero());
        // 0≡0*(-1)
        lemma_mul_zero_left::<F>(F::one().neg());
        F::axiom_eqv_symmetric(F::zero().mul(F::one().neg()), F::zero());
    } else if a.lt(F::zero()) && F::zero().lt(b) {
        F::axiom_mul_commutative(a, b);
        lemma_mul_pos_neg::<F>(b, a);
        F::axiom_lt_iff_le_and_not_eqv(b.mul(a), F::zero());
        F::axiom_eqv_symmetric(a.mul(b), b.mul(a));
        lemma_le_congruence_left::<F>(b.mul(a), a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        if a.mul(b).eqv(F::zero()) {
            F::axiom_eqv_transitive(b.mul(a), a.mul(b), F::zero());
        }
        lemma_lt_asymmetric::<F>(a.mul(b), F::zero());
        // (-1)≡(-1)*1
        F::axiom_mul_one_right(F::one().neg());
        F::axiom_eqv_symmetric(F::one().neg().mul(F::one()), F::one().neg());
    } else if a.lt(F::zero()) && F::zero().eqv(b) {
        F::axiom_eqv_symmetric(F::zero(), b);
        lemma_mul_congruence_right::<F>(a, b, F::zero());
        F::axiom_mul_zero_right(a);
        F::axiom_eqv_transitive(a.mul(b), a.mul(F::zero()), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(b));
        F::axiom_eqv_symmetric(F::zero(), a.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(a.mul(b), F::zero());
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), b);
        F::axiom_lt_iff_le_and_not_eqv(b, F::zero());
        F::axiom_eqv_symmetric(b, F::zero());
        lemma_lt_asymmetric::<F>(a, F::zero());
        // 0≡(-1)*0
        F::axiom_mul_zero_right(F::one().neg());
        F::axiom_eqv_symmetric(F::one().neg().mul(F::zero()), F::zero());
    } else {
        lemma_mul_neg_neg::<F>(a, b);
        lemma_lt_asymmetric::<F>(a, F::zero());
        lemma_lt_asymmetric::<F>(b, F::zero());
        // 1≡(-1)*(-1)
        lemma_neg_mul_neg::<F>(F::one(), F::one());
        F::axiom_mul_one_right(F::one());
        F::axiom_eqv_transitive(F::one().neg().mul(F::one().neg()), F::one().mul(F::one()), F::one());
        F::axiom_eqv_symmetric(F::one().neg().mul(F::one().neg()), F::one());
    }
}

} // verus!
