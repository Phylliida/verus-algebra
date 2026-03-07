use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::OrderedField;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;
use crate::convex::two;

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

/// AM-GM inequality: 0 ≤ a and 0 ≤ b implies a*b ≤ (a*a + b*b) / two().
pub proof fn lemma_am_gm<F: OrderedField>(a: F, b: F)
    requires
        F::zero().le(a),
        F::zero().le(b),
    ensures
        a.mul(b).le(a.mul(a).add(b.mul(b)).div(two::<F>())),
{
    // 0 ≤ (a-b)^2 = a^2 - 2*a*b + b^2
    lemma_square_nonneg::<F>(a.sub(b));
    // (a-b)*(a-b) ≡ a*a - (1+1)*a*b + b*b
    lemma_square_sub_expand::<F>(a, b);
    // 0 ≤ (a-b)*(a-b) ≡ a*a - (1+1)*a*b + b*b
    lemma_le_congruence_right::<F>(F::zero(), a.sub(b).mul(a.sub(b)), a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)));

    // Rearrange: 0 ≤ a^2 - 2ab + b^2 → 2ab ≤ a^2 + b^2
    // a^2 - 2ab + b^2 + 2ab ≡ a^2 + b^2 (via cancellation)
    // First: (a^2 - 2ab) + 2ab ≡ a^2 (sub_then_add_cancel)
    lemma_sub_then_add_cancel::<F>(a.mul(a), two::<F>().mul(a.mul(b)));
    // (a^2 - 2ab + b^2) + 2ab ≡ ((a^2 - 2ab) + 2ab) + b^2... no, let's be more direct.
    // 0 ≤ a^2 - 2ab + b^2
    // Add 2ab to both sides: 2ab ≤ a^2 - 2ab + b^2 + 2ab
    F::axiom_le_add_monotone(F::zero(), a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)), two::<F>().mul(a.mul(b)));
    // LHS: 0 + 2ab ≡ 2ab
    lemma_add_zero_left::<F>(two::<F>().mul(a.mul(b)));
    lemma_le_congruence_left::<F>(
        F::zero().add(two::<F>().mul(a.mul(b))),
        two::<F>().mul(a.mul(b)),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)).add(two::<F>().mul(a.mul(b))),
    );

    // RHS: (a^2 - 2ab + b^2) + 2ab ≡ (a^2 - 2ab) + (b^2 + 2ab)  [assoc]
    F::axiom_add_associative(a.mul(a).sub(two::<F>().mul(a.mul(b))), b.mul(b), two::<F>().mul(a.mul(b)));
    // b^2 + 2ab ≡ 2ab + b^2  [comm]
    F::axiom_add_commutative(b.mul(b), two::<F>().mul(a.mul(b)));
    // (a^2 - 2ab) + (2ab + b^2) [assoc inner reversed to get (a^2-2ab+2ab)+b^2]
    lemma_add_congruence_right::<F>(
        a.mul(a).sub(two::<F>().mul(a.mul(b))),
        b.mul(b).add(two::<F>().mul(a.mul(b))),
        two::<F>().mul(a.mul(b)).add(b.mul(b)),
    );
    F::axiom_eqv_transitive(
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)).add(two::<F>().mul(a.mul(b))),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b).add(two::<F>().mul(a.mul(b)))),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b)).add(b.mul(b))),
    );

    // (a^2-2ab) + (2ab + b^2) ≡ ((a^2-2ab)+2ab) + b^2  [assoc reversed]
    F::axiom_add_associative(a.mul(a).sub(two::<F>().mul(a.mul(b))), two::<F>().mul(a.mul(b)), b.mul(b));
    F::axiom_eqv_symmetric(
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b))).add(b.mul(b)),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b)).add(b.mul(b))),
    );
    F::axiom_eqv_transitive(
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)).add(two::<F>().mul(a.mul(b))),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b)).add(b.mul(b))),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b))).add(b.mul(b)),
    );

    // (a^2-2ab)+2ab ≡ a^2  [sub_then_add_cancel]
    F::axiom_add_congruence_left(
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b))),
        a.mul(a),
        b.mul(b),
    );
    F::axiom_eqv_transitive(
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)).add(two::<F>().mul(a.mul(b))),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(two::<F>().mul(a.mul(b))).add(b.mul(b)),
        a.mul(a).add(b.mul(b)),
    );

    // So: 2ab ≤ a^2 + b^2
    lemma_le_congruence_right::<F>(
        two::<F>().mul(a.mul(b)),
        a.mul(a).sub(two::<F>().mul(a.mul(b))).add(b.mul(b)).add(two::<F>().mul(a.mul(b))),
        a.mul(a).add(b.mul(b)),
    );

    // Now divide by 2: 2 > 0, so ab ≤ (a^2+b^2)/2
    // 2ab ≤ a^2+b^2 and 0 < 2 → 2ab/2 ≤ (a^2+b^2)/2
    lemma_zero_lt_one::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
    lemma_add_nonneg_pos::<F>(F::one(), F::one());
    // 0 < two()

    lemma_le_div_monotone::<F>(two::<F>().mul(a.mul(b)), a.mul(a).add(b.mul(b)), two::<F>());

    // 2*ab / 2 ≡ ab
    F::axiom_eqv_symmetric(F::zero(), two::<F>());
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), two::<F>());
    lemma_mul_div_cancel::<F>(a.mul(b), two::<F>());
    // 2*ab ≡ ab*2... actually mul_div_cancel gives (ab*2)/2 ≡ ab
    // We need (2*ab)/2 ≡ ab. Use commutativity.
    F::axiom_mul_commutative(two::<F>(), a.mul(b));
    // 2*ab ≡ ab*2
    // (2*ab)/2 ≡ (ab*2)/2  [div congruence... need to go through div_is_mul_recip]
    F::axiom_div_is_mul_recip(two::<F>().mul(a.mul(b)), two::<F>());
    F::axiom_div_is_mul_recip(a.mul(b).mul(two::<F>()), two::<F>());
    F::axiom_mul_congruence_left(two::<F>().mul(a.mul(b)), a.mul(b).mul(two::<F>()), two::<F>().recip());
    F::axiom_eqv_symmetric(a.mul(b).mul(two::<F>()).div(two::<F>()), a.mul(b).mul(two::<F>()).mul(two::<F>().recip()));
    F::axiom_eqv_transitive(
        two::<F>().mul(a.mul(b)).mul(two::<F>().recip()),
        a.mul(b).mul(two::<F>()).mul(two::<F>().recip()),
        a.mul(b).mul(two::<F>()).div(two::<F>()),
    );
    F::axiom_eqv_symmetric(two::<F>().mul(a.mul(b)).div(two::<F>()), two::<F>().mul(a.mul(b)).mul(two::<F>().recip()));
    F::axiom_eqv_transitive(
        two::<F>().mul(a.mul(b)).div(two::<F>()),
        two::<F>().mul(a.mul(b)).mul(two::<F>().recip()),
        a.mul(b).mul(two::<F>()).div(two::<F>()),
    );
    // (ab*2)/2 ≡ ab
    F::axiom_eqv_transitive(two::<F>().mul(a.mul(b)).div(two::<F>()), a.mul(b).mul(two::<F>()).div(two::<F>()), a.mul(b));

    // ab ≡ (2*ab)/2 ≤ (a^2+b^2)/2
    F::axiom_eqv_symmetric(two::<F>().mul(a.mul(b)).div(two::<F>()), a.mul(b));
    lemma_le_congruence_left::<F>(
        two::<F>().mul(a.mul(b)).div(two::<F>()),
        a.mul(b),
        a.mul(a).add(b.mul(b)).div(two::<F>()),
    );
}

/// abs(a) * abs(a) ≡ a * a.
pub proof fn lemma_abs_mul_self<R: OrderedRing>(a: R)
    ensures
        abs::<R>(a).mul(abs::<R>(a)).eqv(a.mul(a)),
{
    R::axiom_le_total(R::zero(), a);
    if R::zero().le(a) {
        // abs(a) = a, trivial
        R::axiom_eqv_reflexive(a.mul(a));
    } else {
        // abs(a) = -a
        // (-a)*(-a) ≡ a*a [neg_mul_neg]
        lemma_neg_mul_neg::<R>(a, a);
    }
}

/// 0 < abs(a) if and only if ¬(a ≡ 0).
pub proof fn lemma_abs_pos_iff<R: OrderedRing>(a: R)
    ensures
        R::zero().lt(abs::<R>(a)) == !a.eqv(R::zero()),
{
    R::axiom_le_total(R::zero(), a);
    R::axiom_lt_iff_le_and_not_eqv(R::zero(), abs::<R>(a));

    if R::zero().le(a) {
        // abs(a) = a
        // 0 < a ⟺ ¬(a ≡ 0): 0 < a means 0 ≤ a ∧ ¬(0 ≡ a)
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), a);
        R::axiom_eqv_symmetric(R::zero(), a);
        // 0 < abs(a) = 0 < a = (0 ≤ a ∧ ¬(a ≡ 0))
        // And ¬(a ≡ 0) is what we want
    } else {
        // abs(a) = -a
        // a < 0 (since ¬(0 ≤ a) and totality gives a ≤ 0)
        // ¬(a ≡ 0): if a ≡ 0 then 0 ≤ a via congruence, contradiction
        if a.eqv(R::zero()) {
            R::axiom_le_reflexive(R::zero());
            R::axiom_eqv_symmetric(a, R::zero());
            lemma_le_congruence_right::<R>(R::zero(), R::zero(), a);
        }
        // 0 ≤ -a: from neg_nonpos_iff or directly from a < 0
        lemma_neg_nonpos_iff::<R>(a);
        // Need !0.eqv(-a)
        R::axiom_eqv_symmetric(R::zero(), a.neg());
        if a.neg().eqv(R::zero()) {
            // -a ≡ 0 implies --a ≡ -0 ≡ 0, i.e. a ≡ 0
            R::axiom_neg_congruence(a.neg(), R::zero());
            lemma_neg_involution::<R>(a);
            lemma_neg_zero::<R>();
            R::axiom_eqv_symmetric(a.neg().neg(), a);
            R::axiom_eqv_transitive(a, a.neg().neg(), R::zero().neg());
            R::axiom_eqv_transitive(a, R::zero().neg(), R::zero());
            // But a ≡ 0 contradicts ¬(0 ≤ a)
            R::axiom_le_reflexive(R::zero());
            R::axiom_eqv_symmetric(a, R::zero());
            lemma_le_congruence_right::<R>(R::zero(), R::zero(), a);
        }
    }
}

/// a*a + b*b ≡ 0 implies a ≡ 0 and b ≡ 0 (for OrderedField).
pub proof fn lemma_sum_squares_zero_2d<F: OrderedField>(a: F, b: F)
    requires
        a.mul(a).add(b.mul(b)).eqv(F::zero()),
    ensures
        a.eqv(F::zero()),
        b.eqv(F::zero()),
{
    // 0 ≤ a² and 0 ≤ b²
    lemma_square_nonneg::<F>(a);
    lemma_square_nonneg::<F>(b);

    // If a² > 0, then a² + b² > 0 (by add_pos_nonneg), contradicting a²+b² ≡ 0
    // So a² ≡ 0.
    // Establish a² ≡ 0: if ¬(a² ≡ 0), then 0 < a² (from 0 ≤ a² and ¬(0 ≡ a²))
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a));
    F::axiom_eqv_symmetric(F::zero(), a.mul(a));
    if !a.mul(a).eqv(F::zero()) {
        // 0 < a²
        lemma_add_pos_nonneg::<F>(a.mul(a), b.mul(b));
        // 0 < a² + b², but a²+b² ≡ 0, contradiction
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a).add(b.mul(b)));
        F::axiom_eqv_symmetric(F::zero(), a.mul(a).add(b.mul(b)));
    }
    // a² ≡ 0

    // Similarly b² ≡ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), b.mul(b));
    F::axiom_eqv_symmetric(F::zero(), b.mul(b));
    if !b.mul(b).eqv(F::zero()) {
        lemma_add_nonneg_pos::<F>(a.mul(a), b.mul(b));
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a).add(b.mul(b)));
        F::axiom_eqv_symmetric(F::zero(), a.mul(a).add(b.mul(b)));
    }
    // b² ≡ 0

    // a² ≡ 0 and ¬a≡0 would give ¬(a²≡0) by nonzero_product. So a ≡ 0.
    F::axiom_eqv_symmetric(a.mul(a), F::zero());
    if !a.eqv(F::zero()) {
        lemma_nonzero_product::<F>(a, a);
    }

    F::axiom_eqv_symmetric(b.mul(b), F::zero());
    if !b.eqv(F::zero()) {
        lemma_nonzero_product::<F>(b, b);
    }
}

/// a*a + b*b + c*c ≡ 0 implies a ≡ 0 and b ≡ 0 and c ≡ 0 (for OrderedField).
pub proof fn lemma_sum_squares_zero_3d<F: OrderedField>(a: F, b: F, c: F)
    requires
        a.mul(a).add(b.mul(b)).add(c.mul(c)).eqv(F::zero()),
    ensures
        a.eqv(F::zero()),
        b.eqv(F::zero()),
        c.eqv(F::zero()),
{
    // 0 ≤ a²+b² and 0 ≤ c²
    lemma_sum_squares_nonneg_2d::<F>(a, b);
    lemma_square_nonneg::<F>(c);

    // If a²+b² > 0, then (a²+b²)+c² > 0, contradicting the hypothesis
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a).add(b.mul(b)));
    F::axiom_eqv_symmetric(F::zero(), a.mul(a).add(b.mul(b)));
    if !a.mul(a).add(b.mul(b)).eqv(F::zero()) {
        lemma_add_pos_nonneg::<F>(a.mul(a).add(b.mul(b)), c.mul(c));
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a).add(b.mul(b)).add(c.mul(c)));
        F::axiom_eqv_symmetric(F::zero(), a.mul(a).add(b.mul(b)).add(c.mul(c)));
    }
    // a²+b² ≡ 0
    // By sum_squares_zero_2d: a ≡ 0 and b ≡ 0
    F::axiom_eqv_symmetric(a.mul(a).add(b.mul(b)), F::zero());
    lemma_sum_squares_zero_2d::<F>(a, b);

    // Similarly c² ≡ 0
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), c.mul(c));
    F::axiom_eqv_symmetric(F::zero(), c.mul(c));
    if !c.mul(c).eqv(F::zero()) {
        lemma_add_nonneg_pos::<F>(a.mul(a).add(b.mul(b)), c.mul(c));
        F::axiom_lt_iff_le_and_not_eqv(F::zero(), a.mul(a).add(b.mul(b)).add(c.mul(c)));
        F::axiom_eqv_symmetric(F::zero(), a.mul(a).add(b.mul(b)).add(c.mul(c)));
    }

    F::axiom_eqv_symmetric(c.mul(c), F::zero());
    if !c.eqv(F::zero()) {
        lemma_nonzero_product::<F>(c, c);
    }
}

/// Helper: (x*y)*(x*y) ≡ (x*x)*(y*y), i.e. (xy)² ≡ x²y².
pub proof fn lemma_square_mul<R: Ring>(x: R, y: R)
    ensures
        x.mul(y).mul(x.mul(y)).eqv(x.mul(x).mul(y.mul(y))),
{
    // (xy)(xy) ≡ x(y(xy))  [assoc]
    R::axiom_mul_associative(x, y, x.mul(y));
    // y(xy) chain: y(xy) ≡ (yx)y ≡ (xy)y ≡ x(yy)
    R::axiom_mul_associative(y, x, y);
    R::axiom_eqv_symmetric(y.mul(x).mul(y), y.mul(x.mul(y)));
    R::axiom_mul_commutative(y, x);
    R::axiom_mul_congruence_left(y.mul(x), x.mul(y), y);
    R::axiom_mul_associative(x, y, y);
    R::axiom_eqv_transitive(y.mul(x.mul(y)), y.mul(x).mul(y), x.mul(y).mul(y));
    R::axiom_eqv_transitive(y.mul(x.mul(y)), x.mul(y).mul(y), x.mul(y.mul(y)));
    // x(y(xy)) ≡ x(x(yy))
    lemma_mul_congruence_right::<R>(x, y.mul(x.mul(y)), x.mul(y.mul(y)));
    R::axiom_eqv_transitive(
        x.mul(y).mul(x.mul(y)),
        x.mul(y.mul(x.mul(y))),
        x.mul(x.mul(y.mul(y))),
    );
    // x(x(yy)) ≡ (xx)(yy)  [assoc reversed]
    R::axiom_mul_associative(x, x, y.mul(y));
    R::axiom_eqv_symmetric(x.mul(x).mul(y.mul(y)), x.mul(x.mul(y.mul(y))));
    R::axiom_eqv_transitive(
        x.mul(y).mul(x.mul(y)),
        x.mul(x.mul(y.mul(y))),
        x.mul(x).mul(y.mul(y)),
    );
}

/// Helper: (a*c)*(b*d) ≡ (a*d)*(b*c) — four-way product rearrangement.
/// Both sides equal a*(b*(c*d)) via associativity and commutativity.
proof fn lemma_mul_four_commute<R: Ring>(a: R, b: R, c: R, d: R)
    ensures
        a.mul(c).mul(b.mul(d)).eqv(a.mul(d).mul(b.mul(c))),
{
    // (ac)(bd) ≡ a(c(bd)) ≡ a(b(cd)):
    R::axiom_mul_associative(a, c, b.mul(d));
    // c(bd) ≡ (cb)d ≡ (bc)d ≡ b(cd)
    R::axiom_mul_associative(c, b, d);
    R::axiom_eqv_symmetric(c.mul(b).mul(d), c.mul(b.mul(d)));
    R::axiom_mul_commutative(c, b);
    R::axiom_mul_congruence_left(c.mul(b), b.mul(c), d);
    R::axiom_mul_associative(b, c, d);
    R::axiom_eqv_transitive(c.mul(b.mul(d)), c.mul(b).mul(d), b.mul(c).mul(d));
    R::axiom_eqv_transitive(c.mul(b.mul(d)), b.mul(c).mul(d), b.mul(c.mul(d)));
    lemma_mul_congruence_right::<R>(a, c.mul(b.mul(d)), b.mul(c.mul(d)));
    R::axiom_eqv_transitive(
        a.mul(c).mul(b.mul(d)),
        a.mul(c.mul(b.mul(d))),
        a.mul(b.mul(c.mul(d))),
    );

    // (ad)(bc) ≡ a(d(bc)) ≡ a(b(cd)):
    R::axiom_mul_associative(a, d, b.mul(c));
    // d(bc) ≡ (db)c ≡ (bd)c ≡ b(dc) ≡ b(cd)
    R::axiom_mul_associative(d, b, c);
    R::axiom_eqv_symmetric(d.mul(b).mul(c), d.mul(b.mul(c)));
    R::axiom_mul_commutative(d, b);
    R::axiom_mul_congruence_left(d.mul(b), b.mul(d), c);
    R::axiom_mul_associative(b, d, c);
    R::axiom_eqv_transitive(d.mul(b.mul(c)), d.mul(b).mul(c), b.mul(d).mul(c));
    R::axiom_eqv_transitive(d.mul(b.mul(c)), b.mul(d).mul(c), b.mul(d.mul(c)));
    R::axiom_mul_commutative(d, c);
    lemma_mul_congruence_right::<R>(b, d.mul(c), c.mul(d));
    R::axiom_eqv_transitive(d.mul(b.mul(c)), b.mul(d.mul(c)), b.mul(c.mul(d)));
    lemma_mul_congruence_right::<R>(a, d.mul(b.mul(c)), b.mul(c.mul(d)));
    R::axiom_eqv_transitive(
        a.mul(d).mul(b.mul(c)),
        a.mul(d.mul(b.mul(c))),
        a.mul(b.mul(c.mul(d))),
    );

    // Both ≡ a(b(cd)), so (ac)(bd) ≡ (ad)(bc)
    R::axiom_eqv_symmetric(a.mul(d).mul(b.mul(c)), a.mul(b.mul(c.mul(d))));
    R::axiom_eqv_transitive(
        a.mul(c).mul(b.mul(d)),
        a.mul(b.mul(c.mul(d))),
        a.mul(d).mul(b.mul(c)),
    );
}

/// Helper: distribute (x²+y²)*(u²+v²) ≡ (xu)²+(xv)²+(yu)²+(yv)².
/// Returns in the form ((xu)²+(xv)²) + ((yu)²+(yv)²).
proof fn lemma_expand_product_of_sums_of_squares<R: Ring>(x: R, y: R, u: R, v: R)
    ensures
        x.mul(x).add(y.mul(y)).mul(u.mul(u).add(v.mul(v))).eqv(
            x.mul(u).mul(x.mul(u)).add(x.mul(v).mul(x.mul(v)))
                .add(y.mul(u).mul(y.mul(u)).add(y.mul(v).mul(y.mul(v))))
        ),
{
    let xx = x.mul(x);
    let yy = y.mul(y);
    let uu = u.mul(u);
    let vv = v.mul(v);
    // (x²+y²)(u²+v²) ≡ x²(u²+v²) + y²(u²+v²)  [right distrib]
    lemma_mul_distributes_right::<R>(xx, yy, uu.add(vv));

    // x²(u²+v²) ≡ x²u² + x²v²  [left distrib]
    R::axiom_mul_distributes_left(xx, uu, vv);
    // x²u² ≡ (xu)² and x²v² ≡ (xv)²
    lemma_square_mul::<R>(x, u);
    R::axiom_eqv_symmetric(x.mul(u).mul(x.mul(u)), xx.mul(uu));
    lemma_square_mul::<R>(x, v);
    R::axiom_eqv_symmetric(x.mul(v).mul(x.mul(v)), xx.mul(vv));
    lemma_add_congruence::<R>(
        xx.mul(uu), x.mul(u).mul(x.mul(u)),
        xx.mul(vv), x.mul(v).mul(x.mul(v)),
    );
    R::axiom_eqv_transitive(
        xx.mul(uu.add(vv)),
        xx.mul(uu).add(xx.mul(vv)),
        x.mul(u).mul(x.mul(u)).add(x.mul(v).mul(x.mul(v))),
    );

    // y²(u²+v²) ≡ y²u² + y²v²  [left distrib]
    R::axiom_mul_distributes_left(yy, uu, vv);
    // y²u² ≡ (yu)² and y²v² ≡ (yv)²
    lemma_square_mul::<R>(y, u);
    R::axiom_eqv_symmetric(y.mul(u).mul(y.mul(u)), yy.mul(uu));
    lemma_square_mul::<R>(y, v);
    R::axiom_eqv_symmetric(y.mul(v).mul(y.mul(v)), yy.mul(vv));
    lemma_add_congruence::<R>(
        yy.mul(uu), y.mul(u).mul(y.mul(u)),
        yy.mul(vv), y.mul(v).mul(y.mul(v)),
    );
    R::axiom_eqv_transitive(
        yy.mul(uu.add(vv)),
        yy.mul(uu).add(yy.mul(vv)),
        y.mul(u).mul(y.mul(u)).add(y.mul(v).mul(y.mul(v))),
    );

    // Combine: (x²+y²)(u²+v²) ≡ x²(u²+v²) + y²(u²+v²) ≡ ((xu)²+(xv)²) + ((yu)²+(yv)²)
    lemma_add_congruence::<R>(
        xx.mul(uu.add(vv)), x.mul(u).mul(x.mul(u)).add(x.mul(v).mul(x.mul(v))),
        yy.mul(uu.add(vv)), y.mul(u).mul(y.mul(u)).add(y.mul(v).mul(y.mul(v))),
    );
    R::axiom_eqv_transitive(
        xx.add(yy).mul(uu.add(vv)),
        xx.mul(uu.add(vv)).add(yy.mul(uu.add(vv))),
        x.mul(u).mul(x.mul(u)).add(x.mul(v).mul(x.mul(v)))
            .add(y.mul(u).mul(y.mul(u)).add(y.mul(v).mul(y.mul(v)))),
    );
}

/// Cauchy-Schwarz in 2D: (a*c + b*d)² ≤ (a²+b²)*(c²+d²) (for OrderedRing).
/// Uses the Lagrange identity: (a²+b²)(c²+d²) = (ac+bd)² + (ad-bc)² ≥ (ac+bd)².
pub proof fn lemma_cauchy_schwarz_2d<R: OrderedRing>(a: R, b: R, c: R, d: R)
    ensures
        a.mul(c).add(b.mul(d)).mul(a.mul(c).add(b.mul(d))).le(
            a.mul(a).add(b.mul(b)).mul(c.mul(c).add(d.mul(d)))
        ),
{
    let ac = a.mul(c);
    let bd = b.mul(d);
    let ad = a.mul(d);
    let bc = b.mul(c);
    let two = R::one().add(R::one());

    // ══════════════════════════════════════════════════════════════════
    // Part A: Show 2*(ac)(bd) ≤ (ad)² + (bc)²
    // ══════════════════════════════════════════════════════════════════

    // 0 ≤ (ad-bc)²
    lemma_square_nonneg::<R>(ad.sub(bc));
    // (ad-bc)² ≡ (ad)² - 2*(ad)*(bc) + (bc)²
    lemma_square_sub_expand::<R>(ad, bc);
    // 0 ≤ (ad)² - 2*(ad)*(bc) + (bc)²
    lemma_le_congruence_right::<R>(
        R::zero(),
        ad.sub(bc).mul(ad.sub(bc)),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)),
    );

    // Add 2*(ad)*(bc) to both sides:
    // 2*(ad)*(bc) ≤ (ad)² - 2*(ad)*(bc) + (bc)² + 2*(ad)*(bc)
    R::axiom_le_add_monotone(
        R::zero(),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)),
        two.mul(ad.mul(bc)),
    );
    // LHS: 0 + 2*(ad)*(bc) ≡ 2*(ad)*(bc)
    lemma_add_zero_left::<R>(two.mul(ad.mul(bc)));
    lemma_le_congruence_left::<R>(
        R::zero().add(two.mul(ad.mul(bc))),
        two.mul(ad.mul(bc)),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)).add(two.mul(ad.mul(bc))),
    );

    // RHS: ((ad)²-2xy+bc²) + 2xy ≡ (ad)² + (bc)²
    // Rearrange via assoc: ((ad)²-2xy) + (bc²+2xy) → ((ad)²-2xy) + (2xy+bc²)
    R::axiom_add_associative(
        ad.mul(ad).sub(two.mul(ad.mul(bc))),
        bc.mul(bc),
        two.mul(ad.mul(bc)),
    );
    R::axiom_add_commutative(bc.mul(bc), two.mul(ad.mul(bc)));
    lemma_add_congruence_right::<R>(
        ad.mul(ad).sub(two.mul(ad.mul(bc))),
        bc.mul(bc).add(two.mul(ad.mul(bc))),
        two.mul(ad.mul(bc)).add(bc.mul(bc)),
    );
    R::axiom_eqv_transitive(
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)).add(two.mul(ad.mul(bc))),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc).add(two.mul(ad.mul(bc)))),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc)).add(bc.mul(bc))),
    );
    // ((ad)²-2xy) + (2xy+bc²) ≡ ((ad)²-2xy+2xy) + bc²  [assoc reversed]
    R::axiom_add_associative(
        ad.mul(ad).sub(two.mul(ad.mul(bc))),
        two.mul(ad.mul(bc)),
        bc.mul(bc),
    );
    R::axiom_eqv_symmetric(
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc))).add(bc.mul(bc)),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc)).add(bc.mul(bc))),
    );
    R::axiom_eqv_transitive(
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)).add(two.mul(ad.mul(bc))),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc)).add(bc.mul(bc))),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc))).add(bc.mul(bc)),
    );
    // (ad)²-2xy+2xy ≡ (ad)²  [sub_then_add_cancel]
    lemma_sub_then_add_cancel::<R>(ad.mul(ad), two.mul(ad.mul(bc)));
    R::axiom_add_congruence_left(
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc))),
        ad.mul(ad),
        bc.mul(bc),
    );
    R::axiom_eqv_transitive(
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)).add(two.mul(ad.mul(bc))),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(two.mul(ad.mul(bc))).add(bc.mul(bc)),
        ad.mul(ad).add(bc.mul(bc)),
    );

    // So: 2*(ad)*(bc) ≤ (ad)² + (bc)²
    lemma_le_congruence_right::<R>(
        two.mul(ad.mul(bc)),
        ad.mul(ad).sub(two.mul(ad.mul(bc))).add(bc.mul(bc)).add(two.mul(ad.mul(bc))),
        ad.mul(ad).add(bc.mul(bc)),
    );

    // Use (ac)(bd) ≡ (ad)(bc) to get: 2*(ac)*(bd) ≤ (ad)²+(bc)²
    lemma_mul_four_commute::<R>(a, b, c, d);
    lemma_mul_congruence_right::<R>(two, ac.mul(bd), ad.mul(bc));
    R::axiom_eqv_symmetric(two.mul(ac.mul(bd)), two.mul(ad.mul(bc)));
    lemma_le_congruence_left::<R>(
        two.mul(ad.mul(bc)),
        two.mul(ac.mul(bd)),
        ad.mul(ad).add(bc.mul(bc)),
    );
    // Now: 2*(ac)*(bd) ≤ (ad)² + (bc)²

    // ══════════════════════════════════════════════════════════════════
    // Part B: Add (ac)²+(bd)² to both sides
    // ══════════════════════════════════════════════════════════════════

    // (ac)²+(bd)² + 2*(ac)(bd) ≤ (ac)²+(bd)² + (ad)²+(bc)²
    R::axiom_le_reflexive(ac.mul(ac).add(bd.mul(bd)));
    lemma_le_add_both::<R>(
        two.mul(ac.mul(bd)),
        ad.mul(ad).add(bc.mul(bc)),
        ac.mul(ac).add(bd.mul(bd)),
        ac.mul(ac).add(bd.mul(bd)),
    );
    // Commute LHS: 2*(ac)(bd) + (ac)²+(bd)² ≡ (ac)²+(bd)² + 2*(ac)(bd)
    R::axiom_add_commutative(two.mul(ac.mul(bd)), ac.mul(ac).add(bd.mul(bd)));
    // Commute RHS: (ad)²+(bc)² + (ac)²+(bd)² ≡ (ac)²+(bd)² + (ad)²+(bc)²
    R::axiom_add_commutative(ad.mul(ad).add(bc.mul(bc)), ac.mul(ac).add(bd.mul(bd)));
    R::axiom_le_congruence(
        two.mul(ac.mul(bd)).add(ac.mul(ac).add(bd.mul(bd))),
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
        ad.mul(ad).add(bc.mul(bc)).add(ac.mul(ac).add(bd.mul(bd))),
        ac.mul(ac).add(bd.mul(bd)).add(ad.mul(ad).add(bc.mul(bc))),
    );
    // So: (ac)²+(bd)² + 2*(ac)(bd) ≤ (ac)²+(bd)² + (ad)²+(bc)²

    // ══════════════════════════════════════════════════════════════════
    // Part C: LHS ≡ (ac+bd)²
    // ══════════════════════════════════════════════════════════════════

    // (ac+bd)² ≡ (ac)² + 2*(ac)*(bd) + (bd)²  [square_expand]
    lemma_square_expand::<R>(ac, bd);
    // Grouping: ((ac)² + 2*(ac)(bd)) + (bd)²
    // Rearrange to: (ac)² + (bd)² + 2*(ac)(bd)
    // via: ((ac)²+2xy)+(bd)² ≡ (ac)²+(2xy+(bd)²) ≡ (ac)²+((bd)²+2xy) ≡ ((ac)²+(bd)²)+2xy
    R::axiom_add_associative(ac.mul(ac), two.mul(ac.mul(bd)), bd.mul(bd));
    R::axiom_add_commutative(two.mul(ac.mul(bd)), bd.mul(bd));
    lemma_add_congruence_right::<R>(
        ac.mul(ac),
        two.mul(ac.mul(bd)).add(bd.mul(bd)),
        bd.mul(bd).add(two.mul(ac.mul(bd))),
    );
    R::axiom_eqv_transitive(
        ac.mul(ac).add(two.mul(ac.mul(bd))).add(bd.mul(bd)),
        ac.mul(ac).add(two.mul(ac.mul(bd)).add(bd.mul(bd))),
        ac.mul(ac).add(bd.mul(bd).add(two.mul(ac.mul(bd)))),
    );
    R::axiom_add_associative(ac.mul(ac), bd.mul(bd), two.mul(ac.mul(bd)));
    R::axiom_eqv_symmetric(
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
        ac.mul(ac).add(bd.mul(bd).add(two.mul(ac.mul(bd)))),
    );
    R::axiom_eqv_transitive(
        ac.mul(ac).add(two.mul(ac.mul(bd))).add(bd.mul(bd)),
        ac.mul(ac).add(bd.mul(bd).add(two.mul(ac.mul(bd)))),
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
    );
    // (ac+bd)² ≡ (ac)²+(bd)² + 2*(ac)(bd)
    R::axiom_eqv_transitive(
        ac.add(bd).mul(ac.add(bd)),
        ac.mul(ac).add(two.mul(ac.mul(bd))).add(bd.mul(bd)),
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
    );
    // Apply congruence: (ac+bd)² ≤ RHS
    R::axiom_eqv_symmetric(
        ac.add(bd).mul(ac.add(bd)),
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
    );
    lemma_le_congruence_left::<R>(
        ac.mul(ac).add(bd.mul(bd)).add(two.mul(ac.mul(bd))),
        ac.add(bd).mul(ac.add(bd)),
        ac.mul(ac).add(bd.mul(bd)).add(ad.mul(ad).add(bc.mul(bc))),
    );

    // ══════════════════════════════════════════════════════════════════
    // Part D: RHS ≡ (a²+b²)(c²+d²)
    // ══════════════════════════════════════════════════════════════════

    // Expand (a²+b²)(c²+d²) ≡ ((ac)²+(ad)²) + ((bc)²+(bd)²)
    lemma_expand_product_of_sums_of_squares::<R>(a, b, c, d);

    // Rearrange: ((ac)²+(ad)²)+((bc)²+(bd)²) ≡ ((ac)²+(bd)²)+((ad)²+(bc)²)
    lemma_add_rearrange_2x2::<R>(ac.mul(ac), ad.mul(ad), bc.mul(bc), bd.mul(bd));
    // rearrange_2x2 gives: ((ac)²+(ad)²)+((bc)²+(bd)²) ≡ ((ac)²+(bc)²)+((ad)²+(bd)²)
    // But we need: ≡ ((ac)²+(bd)²)+((ad)²+(bc)²)
    // So we need a different rearrangement.
    // Let me use rearrange_2x2 with different grouping:
    // We have ((ac)²+(ad)²)+((bc)²+(bd)²) from the expansion.
    // We want ((ac)²+(bd)²)+((ad)²+(bc)²).
    // Apply rearrange_2x2 to the expansion:
    // (p+q)+(r+s) ≡ (p+r)+(q+s) where p=(ac)², q=(ad)², r=(bc)², s=(bd)²
    // gives ((ac)²+(bc)²)+((ad)²+(bd)²)
    // Then we need to swap the two inner sums:
    // ((ac)²+(bc)²)+((ad)²+(bd)²) and we want ((ac)²+(bd)²)+((ad)²+(bc)²)
    // These are different groupings. Let me use a different approach.

    // From expansion: (a²+b²)(c²+d²) ≡ ((ac)²+(ad)²)+((bc)²+(bd)²)
    // We want to show this ≡ ((ac)²+(bd)²)+((ad)²+(bc)²)
    // Use rearrange_2x2 on ((ac)²+(ad)²)+((bc)²+(bd)²):
    // With a1=(ac)², b1=(ad)², c1=(bc)², d1=(bd)²:
    // (a1+b1)+(c1+d1) ≡ (a1+c1)+(b1+d1)
    R::axiom_eqv_transitive(
        a.mul(a).add(b.mul(b)).mul(c.mul(c).add(d.mul(d))),
        ac.mul(ac).add(ad.mul(ad)).add(bc.mul(bc).add(bd.mul(bd))),
        ac.mul(ac).add(bc.mul(bc)).add(ad.mul(ad).add(bd.mul(bd))),
    );
    // Now swap the two pairs in each sum to get our target form.
    // We have ((ac)²+(bc)²) + ((ad)²+(bd)²).
    // We want ((ac)²+(bd)²) + ((ad)²+(bc)²).
    // Apply rearrange_2x2 again: (a1+c1)+(b1+d1) ≡ (a1+b1)+(c1+d1)
    // Wait, that just reverses it. Let me think...
    // Actually: ((ac)²+(bc)²)+((ad)²+(bd)²) = ((ac)²+(bc)²)+((ad)²+(bd)²)
    // Apply rearrange_2x2 with a1=(ac)², b1=(bc)², c1=(ad)², d1=(bd)²:
    // ((ac)²+(bc)²)+((ad)²+(bd)²) ≡ ((ac)²+(ad)²)+((bc)²+(bd)²)
    // That goes back to the original. Not helpful.

    // Different approach: rearrange the inner sums.
    // From ((ac)²+(bc)²)+((ad)²+(bd)²), swap bc² and bd² between groups:
    // We can use: ((ac)²+(bc)²)+((ad)²+(bd)²) via assoc+comm:
    // ≡ (ac)²+(bc)²+(ad)²+(bd)² [flatten]
    // ≡ (ac)²+(bd)²+(ad)²+(bc)² [rearrange inner]
    // ≡ ((ac)²+(bd)²)+((ad)²+(bc)²) [regroup]
    // This requires showing a 4-element rearrangement. Let me use two applications.

    // Step D1: ((ac)²+(bc)²)+((ad)²+(bd)²) ≡ (ac)²+((bc)²+((ad)²+(bd)²))  [assoc]
    R::axiom_add_associative(ac.mul(ac), bc.mul(bc), ad.mul(ad).add(bd.mul(bd)));
    // Step D2: (bc)²+((ad)²+(bd)²) ≡ ((bc)²+(ad)²)+(bd)²  [assoc reversed]
    R::axiom_add_associative(bc.mul(bc), ad.mul(ad), bd.mul(bd));
    R::axiom_eqv_symmetric(
        bc.mul(bc).add(ad.mul(ad)).add(bd.mul(bd)),
        bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd))),
    );
    // Step D3: (bc)²+(ad)² ≡ (ad)²+(bc)²  [comm]
    R::axiom_add_commutative(bc.mul(bc), ad.mul(ad));
    R::axiom_add_congruence_left(
        bc.mul(bc).add(ad.mul(ad)),
        ad.mul(ad).add(bc.mul(bc)),
        bd.mul(bd),
    );
    // Chain: (bc)²+((ad)²+(bd)²) ≡ ((bc)²+(ad)²)+(bd)² ≡ ((ad)²+(bc)²)+(bd)²
    R::axiom_eqv_transitive(
        bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd))),
        bc.mul(bc).add(ad.mul(ad)).add(bd.mul(bd)),
        ad.mul(ad).add(bc.mul(bc)).add(bd.mul(bd)),
    );
    // Step D4: ((ad)²+(bc)²)+(bd)² ≡ (ad)²+((bc)²+(bd)²)  [assoc]
    R::axiom_add_associative(ad.mul(ad), bc.mul(bc), bd.mul(bd));
    R::axiom_eqv_transitive(
        bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd))),
        ad.mul(ad).add(bc.mul(bc)).add(bd.mul(bd)),
        ad.mul(ad).add(bc.mul(bc).add(bd.mul(bd))),
    );
    // Step D5: (bc)²+(bd)² ≡ (bd)²+(bc)²  [comm]
    R::axiom_add_commutative(bc.mul(bc), bd.mul(bd));
    lemma_add_congruence_right::<R>(
        ad.mul(ad),
        bc.mul(bc).add(bd.mul(bd)),
        bd.mul(bd).add(bc.mul(bc)),
    );
    R::axiom_eqv_transitive(
        bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd))),
        ad.mul(ad).add(bc.mul(bc).add(bd.mul(bd))),
        ad.mul(ad).add(bd.mul(bd).add(bc.mul(bc))),
    );
    // Step D6: (ad)²+((bd)²+(bc)²) ≡ ((ad)²+(bd)²)+(bc)²  [assoc reversed]... wait, wrong direction.
    // Actually we want: (bc)²+((ad)²+(bd)²) was our starting point, and we've shown it ≡ (ad)²+((bd)²+(bc)²)
    // Now I need (ac)²+(this) ≡ ((ac)²+(bd)²)+((ad)²+(bc)²)

    // Let me take: (ac)²+((bc)²+((ad)²+(bd)²))) from Step D1
    // ≡ (ac)²+((ad)²+((bd)²+(bc)²)))  via our chain
    lemma_add_congruence_right::<R>(
        ac.mul(ac),
        bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd))),
        ad.mul(ad).add(bd.mul(bd).add(bc.mul(bc))),
    );
    R::axiom_eqv_transitive(
        ac.mul(ac).add(bc.mul(bc)).add(ad.mul(ad).add(bd.mul(bd))),
        ac.mul(ac).add(bc.mul(bc).add(ad.mul(ad).add(bd.mul(bd)))),
        ac.mul(ac).add(ad.mul(ad).add(bd.mul(bd).add(bc.mul(bc)))),
    );
    // Now: (ac)²+((ad)²+((bd)²+(bc)²)) ≡ ((ac)²+(ad)²)+((bd)²+(bc)²)... no.
    // Actually: (ac)²+(x+(y+z)) ≡ ((ac)²+x)+(y+z)  [assoc reversed]
    // where x=(ad)², y=(bd)², z=(bc)²
    // ≡ ((ac)²+(ad)²)+((bd)²+(bc)²)
    // Hmm, this is getting complicated. Let me try a completely different rearrangement.

    // Actually, the simplest approach: just apply rearrange_2x2 to our final inequality.
    // We have: (ac+bd)² ≤ ((ac)²+(bd)²)+((ad)²+(bc)²)
    // And (a²+b²)(c²+d²) ≡ ((ac)²+(ad)²)+((bc)²+(bd)²)
    // So we need ((ac)²+(bd)²)+((ad)²+(bc)²) ≡ ((ac)²+(ad)²)+((bc)²+(bd)²)
    // This is just rearrange_2x2 with a=(ac)², b=(bd)², c=(ad)², d=(bc)²:
    lemma_add_rearrange_2x2::<R>(ac.mul(ac), bd.mul(bd), ad.mul(ad), bc.mul(bc));
    // ((ac)²+(bd)²)+((ad)²+(bc)²) ≡ ((ac)²+(ad)²)+((bd)²+(bc)²)
    // Need to fix: ((bd)²+(bc)²) ≡ ((bc)²+(bd)²) [comm]
    R::axiom_add_commutative(bd.mul(bd), bc.mul(bc));
    lemma_add_congruence_right::<R>(
        ac.mul(ac).add(ad.mul(ad)),
        bd.mul(bd).add(bc.mul(bc)),
        bc.mul(bc).add(bd.mul(bd)),
    );
    R::axiom_eqv_transitive(
        ac.mul(ac).add(bd.mul(bd)).add(ad.mul(ad).add(bc.mul(bc))),
        ac.mul(ac).add(ad.mul(ad)).add(bd.mul(bd).add(bc.mul(bc))),
        ac.mul(ac).add(ad.mul(ad)).add(bc.mul(bc).add(bd.mul(bd))),
    );

    // So ((ac)²+(bd)²)+((ad)²+(bc)²) ≡ ((ac)²+(ad)²)+((bc)²+(bd)²) ≡ (a²+b²)(c²+d²)
    R::axiom_eqv_symmetric(
        a.mul(a).add(b.mul(b)).mul(c.mul(c).add(d.mul(d))),
        ac.mul(ac).add(ad.mul(ad)).add(bc.mul(bc).add(bd.mul(bd))),
    );
    R::axiom_eqv_transitive(
        ac.mul(ac).add(bd.mul(bd)).add(ad.mul(ad).add(bc.mul(bc))),
        ac.mul(ac).add(ad.mul(ad)).add(bc.mul(bc).add(bd.mul(bd))),
        a.mul(a).add(b.mul(b)).mul(c.mul(c).add(d.mul(d))),
    );

    // Final: (ac+bd)² ≤ ((ac)²+(bd)²)+((ad)²+(bc)²) ≡ (a²+b²)(c²+d²)
    lemma_le_congruence_right::<R>(
        ac.add(bd).mul(ac.add(bd)),
        ac.mul(ac).add(bd.mul(bd)).add(ad.mul(ad).add(bc.mul(bc))),
        a.mul(a).add(b.mul(b)).mul(c.mul(c).add(d.mul(d))),
    );
}

/// 0 ≤ a*a + b*b + c*c + d*d.
pub proof fn lemma_sum_squares_nonneg_4d<R: OrderedRing>(a: R, b: R, c: R, d: R)
    ensures
        R::zero().le(a.mul(a).add(b.mul(b)).add(c.mul(c)).add(d.mul(d))),
{
    lemma_sum_squares_nonneg_3d::<R>(a, b, c);
    lemma_square_nonneg::<R>(d);
    lemma_nonneg_add::<R>(a.mul(a).add(b.mul(b)).add(c.mul(c)), d.mul(d));
}

/// Helper: 2*x*y ≤ x*x + y*y for any x, y in an ordered ring.
/// Follows from (x - y)² ≥ 0.
proof fn lemma_two_mul_le_sum_sq<R: OrderedRing>(x: R, y: R)
    ensures
        R::one().add(R::one()).mul(x.mul(y)).le(x.mul(x).add(y.mul(y))),
{
    let two = R::one().add(R::one());

    // 0 ≤ (x-y)²
    lemma_square_nonneg::<R>(x.sub(y));
    // (x-y)² ≡ x² - 2xy + y²
    lemma_square_sub_expand::<R>(x, y);
    // 0 ≤ x² - 2xy + y²
    lemma_le_congruence_right::<R>(
        R::zero(),
        x.sub(y).mul(x.sub(y)),
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)),
    );

    // Add 2xy to both sides: 2xy ≤ (x² - 2xy + y²) + 2xy
    R::axiom_le_add_monotone(
        R::zero(),
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)),
        two.mul(x.mul(y)),
    );
    // LHS: 0 + 2xy ≡ 2xy
    lemma_add_zero_left::<R>(two.mul(x.mul(y)));
    lemma_le_congruence_left::<R>(
        R::zero().add(two.mul(x.mul(y))),
        two.mul(x.mul(y)),
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)).add(two.mul(x.mul(y))),
    );

    // RHS: (x² - 2xy + y²) + 2xy ≡ x² + y²
    // Use the same rearrangement as the 2D CS proof.
    // ((x²-2xy) + y²) + 2xy
    // ≡ (x²-2xy) + (y² + 2xy)     [assoc]
    R::axiom_add_associative(
        x.mul(x).sub(two.mul(x.mul(y))),
        y.mul(y),
        two.mul(x.mul(y)),
    );
    // y² + 2xy ≡ 2xy + y²         [comm]
    R::axiom_add_commutative(y.mul(y), two.mul(x.mul(y)));
    lemma_add_congruence_right::<R>(
        x.mul(x).sub(two.mul(x.mul(y))),
        y.mul(y).add(two.mul(x.mul(y))),
        two.mul(x.mul(y)).add(y.mul(y)),
    );
    R::axiom_eqv_transitive(
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)).add(two.mul(x.mul(y))),
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y).add(two.mul(x.mul(y)))),
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y)).add(y.mul(y))),
    );
    // (x²-2xy) + (2xy + y²) ≡ ((x²-2xy)+2xy) + y²  [assoc reversed]
    R::axiom_add_associative(
        x.mul(x).sub(two.mul(x.mul(y))),
        two.mul(x.mul(y)),
        y.mul(y),
    );
    R::axiom_eqv_symmetric(
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y))).add(y.mul(y)),
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y)).add(y.mul(y))),
    );
    R::axiom_eqv_transitive(
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)).add(two.mul(x.mul(y))),
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y)).add(y.mul(y))),
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y))).add(y.mul(y)),
    );
    // (x²-2xy)+2xy ≡ x²  [sub_then_add_cancel]
    lemma_sub_then_add_cancel::<R>(x.mul(x), two.mul(x.mul(y)));
    R::axiom_add_congruence_left(
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y))),
        x.mul(x),
        y.mul(y),
    );
    R::axiom_eqv_transitive(
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)).add(two.mul(x.mul(y))),
        x.mul(x).sub(two.mul(x.mul(y))).add(two.mul(x.mul(y))).add(y.mul(y)),
        x.mul(x).add(y.mul(y)),
    );

    // So: 2xy ≤ x² + y²
    lemma_le_congruence_right::<R>(
        two.mul(x.mul(y)),
        x.mul(x).sub(two.mul(x.mul(y))).add(y.mul(y)).add(two.mul(x.mul(y))),
        x.mul(x).add(y.mul(y)),
    );
}

/// Cross-term bound for 4D Cauchy-Schwarz:
/// 2*(a1*b1+a2*b2)*(a3*b3+a4*b4) ≤ (a1²+a2²)(b3²+b4²) + (a3²+a4²)(b1²+b2²)
///
/// Proof: expand the product, apply mul_four_commute to each of the 4 terms
/// to get cross products, then apply 2xy ≤ x²+y² to each cross product,
/// sum, convert squares with square_mul, and factor via distributivity.
proof fn lemma_cross_term_bound_4d<R: OrderedRing>(
    a1: R, a2: R, a3: R, a4: R,
    b1: R, b2: R, b3: R, b4: R,
)
    ensures
        R::one().add(R::one()).mul(
            a1.mul(b1).add(a2.mul(b2)).mul(a3.mul(b3).add(a4.mul(b4)))
        ).le(
            a1.mul(a1).add(a2.mul(a2)).mul(b3.mul(b3).add(b4.mul(b4)))
                .add(a3.mul(a3).add(a4.mul(a4)).mul(b1.mul(b1).add(b2.mul(b2))))
        ),
{
    let two = R::one().add(R::one());
    let p12 = a1.mul(b1).add(a2.mul(b2));
    let p34 = a3.mul(b3).add(a4.mul(b4));

    // Abbreviations for squared norms
    let alpha = a1.mul(a1).add(a2.mul(a2));  // a1²+a2²
    let beta  = b1.mul(b1).add(b2.mul(b2));  // b1²+b2²
    let gamma = a3.mul(a3).add(a4.mul(a4));  // a3²+a4²
    let delta = b3.mul(b3).add(b4.mul(b4));  // b3²+b4²

    // ══════════════════════════════════════════════════════════════
    // Step 1: Expand p12 * p34 via distributivity
    // (a1b1+a2b2)(a3b3+a4b4)
    //   ≡ (a1b1)(a3b3) + (a1b1)(a4b4) + (a2b2)(a3b3) + (a2b2)(a4b4)
    // ══════════════════════════════════════════════════════════════

    // Left distrib: p12 * p34 ≡ p12*a3b3 + p12*a4b4
    R::axiom_mul_distributes_left(p12, a3.mul(b3), a4.mul(b4));

    // Right distrib on p12*a3b3: (a1b1+a2b2)*a3b3 ≡ (a1b1)(a3b3) + (a2b2)(a3b3)
    lemma_mul_distributes_right::<R>(a1.mul(b1), a2.mul(b2), a3.mul(b3));

    // Right distrib on p12*a4b4: (a1b1+a2b2)*a4b4 ≡ (a1b1)(a4b4) + (a2b2)(a4b4)
    lemma_mul_distributes_right::<R>(a1.mul(b1), a2.mul(b2), a4.mul(b4));

    // Combine: p12*p34 ≡ ((a1b1)(a3b3)+(a2b2)(a3b3)) + ((a1b1)(a4b4)+(a2b2)(a4b4))
    let t13 = a1.mul(b1).mul(a3.mul(b3));
    let t23 = a2.mul(b2).mul(a3.mul(b3));
    let t14 = a1.mul(b1).mul(a4.mul(b4));
    let t24 = a2.mul(b2).mul(a4.mul(b4));

    lemma_add_congruence::<R>(
        p12.mul(a3.mul(b3)), t13.add(t23),
        p12.mul(a4.mul(b4)), t14.add(t24),
    );
    R::axiom_eqv_transitive(
        p12.mul(p34),
        p12.mul(a3.mul(b3)).add(p12.mul(a4.mul(b4))),
        t13.add(t23).add(t14.add(t24)),
    );

    // Rearrange to t13+t14+t23+t24 via rearrange_2x2
    // (t13+t23)+(t14+t24) ≡ (t13+t14)+(t23+t24)
    lemma_add_rearrange_2x2::<R>(t13, t23, t14, t24);
    R::axiom_eqv_transitive(
        p12.mul(p34),
        t13.add(t23).add(t14.add(t24)),
        t13.add(t14).add(t23.add(t24)),
    );

    // ══════════════════════════════════════════════════════════════
    // Step 2: Apply mul_four_commute to each term
    // (a1b1)(a3b3) ≡ (a1b3)(a3b1), etc.
    // ══════════════════════════════════════════════════════════════

    let c13 = a1.mul(b3).mul(a3.mul(b1));
    let c14 = a1.mul(b4).mul(a4.mul(b1));
    let c23 = a2.mul(b3).mul(a3.mul(b2));
    let c24 = a2.mul(b4).mul(a4.mul(b2));

    lemma_mul_four_commute::<R>(a1, a3, b1, b3);  // t13 ≡ c13
    lemma_mul_four_commute::<R>(a1, a4, b1, b4);  // t14 ≡ c14
    lemma_mul_four_commute::<R>(a2, a3, b2, b3);  // t23 ≡ c23
    lemma_mul_four_commute::<R>(a2, a4, b2, b4);  // t24 ≡ c24

    // Propagate congruences through the sums
    lemma_add_congruence::<R>(t13, c13, t14, c14);
    lemma_add_congruence::<R>(t23, c23, t24, c24);
    lemma_add_congruence::<R>(
        t13.add(t14), c13.add(c14),
        t23.add(t24), c23.add(c24),
    );
    R::axiom_eqv_transitive(
        p12.mul(p34),
        t13.add(t14).add(t23.add(t24)),
        c13.add(c14).add(c23.add(c24)),
    );

    // ══════════════════════════════════════════════════════════════
    // Step 3: Apply 2xy ≤ x²+y² to each cross product
    // ══════════════════════════════════════════════════════════════

    lemma_two_mul_le_sum_sq::<R>(a1.mul(b3), a3.mul(b1));
    lemma_two_mul_le_sum_sq::<R>(a1.mul(b4), a4.mul(b1));
    lemma_two_mul_le_sum_sq::<R>(a2.mul(b3), a3.mul(b2));
    lemma_two_mul_le_sum_sq::<R>(a2.mul(b4), a4.mul(b2));

    // Sum the first two: 2*c13 + 2*c14 ≤ (sq13+sq31) + (sq14+sq41)
    let sq13 = a1.mul(b3).mul(a1.mul(b3));
    let sq31 = a3.mul(b1).mul(a3.mul(b1));
    let sq14 = a1.mul(b4).mul(a1.mul(b4));
    let sq41 = a4.mul(b1).mul(a4.mul(b1));
    let sq23 = a2.mul(b3).mul(a2.mul(b3));
    let sq32 = a3.mul(b2).mul(a3.mul(b2));
    let sq24 = a2.mul(b4).mul(a2.mul(b4));
    let sq42 = a4.mul(b2).mul(a4.mul(b2));

    lemma_le_add_both::<R>(
        two.mul(c13), sq13.add(sq31),
        two.mul(c14), sq14.add(sq41),
    );
    lemma_le_add_both::<R>(
        two.mul(c23), sq23.add(sq32),
        two.mul(c24), sq24.add(sq42),
    );
    lemma_le_add_both::<R>(
        two.mul(c13).add(two.mul(c14)),
        sq13.add(sq31).add(sq14.add(sq41)),
        two.mul(c23).add(two.mul(c24)),
        sq23.add(sq32).add(sq24.add(sq42)),
    );

    // ══════════════════════════════════════════════════════════════
    // Step 4: LHS ≡ 2*(p12*p34), show:
    // 2*c13+2*c14+2*c23+2*c24 ≡ 2*(c13+c14+c23+c24) ≡ 2*(p12*p34)
    // ══════════════════════════════════════════════════════════════

    // 2*(c13+c14) ≡ 2*c13 + 2*c14  [left distrib]
    R::axiom_mul_distributes_left(two, c13, c14);
    R::axiom_eqv_symmetric(two.mul(c13).add(two.mul(c14)), two.mul(c13.add(c14)));

    // 2*(c23+c24) ≡ 2*c23 + 2*c24  [left distrib]
    R::axiom_mul_distributes_left(two, c23, c24);
    R::axiom_eqv_symmetric(two.mul(c23).add(two.mul(c24)), two.mul(c23.add(c24)));

    // (2*c13+2*c14) + (2*c23+2*c24) ≡ 2*(c13+c14) + 2*(c23+c24)
    lemma_add_congruence::<R>(
        two.mul(c13).add(two.mul(c14)), two.mul(c13.add(c14)),
        two.mul(c23).add(two.mul(c24)), two.mul(c23.add(c24)),
    );

    // 2*(c13+c14) + 2*(c23+c24) ≡ 2*((c13+c14)+(c23+c24))  [left distrib]
    R::axiom_mul_distributes_left(two, c13.add(c14), c23.add(c24));
    R::axiom_eqv_symmetric(
        two.mul(c13.add(c14)).add(two.mul(c23.add(c24))),
        two.mul(c13.add(c14).add(c23.add(c24))),
    );

    R::axiom_eqv_transitive(
        two.mul(c13).add(two.mul(c14)).add(two.mul(c23).add(two.mul(c24))),
        two.mul(c13.add(c14)).add(two.mul(c23.add(c24))),
        two.mul(c13.add(c14).add(c23.add(c24))),
    );

    // c13+c14+c23+c24 ≡ p12*p34
    R::axiom_eqv_symmetric(p12.mul(p34), c13.add(c14).add(c23.add(c24)));
    lemma_mul_congruence_right::<R>(
        two,
        c13.add(c14).add(c23.add(c24)),
        p12.mul(p34),
    );
    R::axiom_eqv_transitive(
        two.mul(c13).add(two.mul(c14)).add(two.mul(c23).add(two.mul(c24))),
        two.mul(c13.add(c14).add(c23.add(c24))),
        two.mul(p12.mul(p34)),
    );

    // Apply congruence to LHS of inequality
    R::axiom_eqv_symmetric(
        two.mul(c13).add(two.mul(c14)).add(two.mul(c23).add(two.mul(c24))),
        two.mul(p12.mul(p34)),
    );
    lemma_le_congruence_left::<R>(
        two.mul(c13).add(two.mul(c14)).add(two.mul(c23).add(two.mul(c24))),
        two.mul(p12.mul(p34)),
        sq13.add(sq31).add(sq14.add(sq41)).add(sq23.add(sq32).add(sq24.add(sq42))),
    );

    // ══════════════════════════════════════════════════════════════
    // Step 5: RHS ≡ αδ + γβ, show:
    // (sq13+sq31+sq14+sq41) + (sq23+sq32+sq24+sq42)
    //   ≡ (a1²+a2²)(b3²+b4²) + (a3²+a4²)(b1²+b2²)
    //
    // Using square_mul: (xy)² ≡ x²y², then factor via distrib.
    // ══════════════════════════════════════════════════════════════

    // Convert each (xy)² to x²y²
    lemma_square_mul::<R>(a1, b3);  // sq13 ≡ a1²·b3²
    lemma_square_mul::<R>(a3, b1);  // sq31 ≡ a3²·b1²
    lemma_square_mul::<R>(a1, b4);  // sq14 ≡ a1²·b4²
    lemma_square_mul::<R>(a4, b1);  // sq41 ≡ a4²·b1²
    lemma_square_mul::<R>(a2, b3);  // sq23 ≡ a2²·b3²
    lemma_square_mul::<R>(a3, b2);  // sq32 ≡ a3²·b2²
    lemma_square_mul::<R>(a2, b4);  // sq24 ≡ a2²·b4²
    lemma_square_mul::<R>(a4, b2);  // sq42 ≡ a4²·b2²

    let a1s = a1.mul(a1);
    let a2s = a2.mul(a2);
    let a3s = a3.mul(a3);
    let a4s = a4.mul(a4);
    let b1s = b1.mul(b1);
    let b2s = b2.mul(b2);
    let b3s = b3.mul(b3);
    let b4s = b4.mul(b4);

    // Group first 4: sq13+sq31+sq14+sq41 ≡ a1²b3²+a3²b1²+a1²b4²+a4²b1²
    lemma_add_congruence::<R>(sq13, a1s.mul(b3s), sq31, a3s.mul(b1s));
    lemma_add_congruence::<R>(sq14, a1s.mul(b4s), sq41, a4s.mul(b1s));
    lemma_add_congruence::<R>(
        sq13.add(sq31), a1s.mul(b3s).add(a3s.mul(b1s)),
        sq14.add(sq41), a1s.mul(b4s).add(a4s.mul(b1s)),
    );

    // Group second 4: sq23+sq32+sq24+sq42 ≡ a2²b3²+a3²b2²+a2²b4²+a4²b2²
    lemma_add_congruence::<R>(sq23, a2s.mul(b3s), sq32, a3s.mul(b2s));
    lemma_add_congruence::<R>(sq24, a2s.mul(b4s), sq42, a4s.mul(b2s));
    lemma_add_congruence::<R>(
        sq23.add(sq32), a2s.mul(b3s).add(a3s.mul(b2s)),
        sq24.add(sq42), a2s.mul(b4s).add(a4s.mul(b2s)),
    );

    // Full RHS congruence
    lemma_add_congruence::<R>(
        sq13.add(sq31).add(sq14.add(sq41)),
        a1s.mul(b3s).add(a3s.mul(b1s)).add(a1s.mul(b4s).add(a4s.mul(b1s))),
        sq23.add(sq32).add(sq24.add(sq42)),
        a2s.mul(b3s).add(a3s.mul(b2s)).add(a2s.mul(b4s).add(a4s.mul(b2s))),
    );

    // Now rearrange a1²b3²+a3²b1²+a1²b4²+a4²b1² to a1²(b3²+b4²)+a4²b1²+a3²b1²
    // Actually, let's factor directly:
    // a1²b3²+a1²b4² = a1²(b3²+b4²)    [left distrib reversed]
    // a3²b1²+a4²b1² = (a3²+a4²)b1²... wait, = b1²(a3²+a4²)... hmm,
    // a3²b1² + a4²b1² — this is adding two terms. Use right distrib:
    // (a3²+a4²)*b1² = a3²*b1² + a4²*b1²  [right distrib reversed]

    // First group: rearrange (a1²b3²+a3²b1²)+(a1²b4²+a4²b1²) to (a1²b3²+a1²b4²)+(a3²b1²+a4²b1²)
    lemma_add_rearrange_2x2::<R>(a1s.mul(b3s), a3s.mul(b1s), a1s.mul(b4s), a4s.mul(b1s));
    // ≡ (a1²b3²+a1²b4²)+(a3²b1²+a4²b1²)

    // a1²b3²+a1²b4² ≡ a1²(b3²+b4²) [left distrib reversed]
    R::axiom_mul_distributes_left(a1s, b3s, b4s);
    R::axiom_eqv_symmetric(a1s.mul(b3s).add(a1s.mul(b4s)), a1s.mul(b3s.add(b4s)));

    // a3²b1²+a4²b1² ≡ (a3²+a4²)b1² [right distrib reversed]
    lemma_mul_distributes_right::<R>(a3s, a4s, b1s);
    R::axiom_eqv_symmetric(a3s.mul(b1s).add(a4s.mul(b1s)), a3s.add(a4s).mul(b1s));

    lemma_add_congruence::<R>(
        a1s.mul(b3s).add(a1s.mul(b4s)), a1s.mul(b3s.add(b4s)),
        a3s.mul(b1s).add(a4s.mul(b1s)), a3s.add(a4s).mul(b1s),
    );
    R::axiom_eqv_transitive(
        a1s.mul(b3s).add(a3s.mul(b1s)).add(a1s.mul(b4s).add(a4s.mul(b1s))),
        a1s.mul(b3s).add(a1s.mul(b4s)).add(a3s.mul(b1s).add(a4s.mul(b1s))),
        a1s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b1s)),
    );

    // Second group: rearrange (a2²b3²+a3²b2²)+(a2²b4²+a4²b2²) similarly
    lemma_add_rearrange_2x2::<R>(a2s.mul(b3s), a3s.mul(b2s), a2s.mul(b4s), a4s.mul(b2s));

    R::axiom_mul_distributes_left(a2s, b3s, b4s);
    R::axiom_eqv_symmetric(a2s.mul(b3s).add(a2s.mul(b4s)), a2s.mul(b3s.add(b4s)));

    lemma_mul_distributes_right::<R>(a3s, a4s, b2s);
    R::axiom_eqv_symmetric(a3s.mul(b2s).add(a4s.mul(b2s)), a3s.add(a4s).mul(b2s));

    lemma_add_congruence::<R>(
        a2s.mul(b3s).add(a2s.mul(b4s)), a2s.mul(b3s.add(b4s)),
        a3s.mul(b2s).add(a4s.mul(b2s)), a3s.add(a4s).mul(b2s),
    );
    R::axiom_eqv_transitive(
        a2s.mul(b3s).add(a3s.mul(b2s)).add(a2s.mul(b4s).add(a4s.mul(b2s))),
        a2s.mul(b3s).add(a2s.mul(b4s)).add(a3s.mul(b2s).add(a4s.mul(b2s))),
        a2s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b2s)),
    );

    // Combine: (a1²δ + γ·b1²) + (a2²δ + γ·b2²) ≡ (a1²+a2²)δ + γ(b1²+b2²)
    // First: a1²δ + a2²δ ≡ (a1²+a2²)δ
    lemma_mul_distributes_right::<R>(a1s, a2s, b3s.add(b4s));
    R::axiom_eqv_symmetric(
        a1s.mul(b3s.add(b4s)).add(a2s.mul(b3s.add(b4s))),
        a1s.add(a2s).mul(b3s.add(b4s)),
    );

    // γ·b1² + γ·b2² ≡ γ·(b1²+b2²)
    R::axiom_mul_distributes_left(a3s.add(a4s), b1s, b2s);
    R::axiom_eqv_symmetric(
        a3s.add(a4s).mul(b1s).add(a3s.add(a4s).mul(b2s)),
        a3s.add(a4s).mul(b1s.add(b2s)),
    );

    // (a1²δ+γb1²)+(a2²δ+γb2²) ≡ (a1²δ+a2²δ)+(γb1²+γb2²)
    lemma_add_rearrange_2x2::<R>(
        a1s.mul(b3s.add(b4s)), a3s.add(a4s).mul(b1s),
        a2s.mul(b3s.add(b4s)), a3s.add(a4s).mul(b2s),
    );

    // Chain to (a1²+a2²)δ + γ(b1²+b2²) = αδ + γβ
    lemma_add_congruence::<R>(
        a1s.mul(b3s.add(b4s)).add(a2s.mul(b3s.add(b4s))),
        a1s.add(a2s).mul(b3s.add(b4s)),
        a3s.add(a4s).mul(b1s).add(a3s.add(a4s).mul(b2s)),
        a3s.add(a4s).mul(b1s.add(b2s)),
    );
    R::axiom_eqv_transitive(
        a1s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b1s))
            .add(a2s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b2s))),
        a1s.mul(b3s.add(b4s)).add(a2s.mul(b3s.add(b4s)))
            .add(a3s.add(a4s).mul(b1s).add(a3s.add(a4s).mul(b2s))),
        a1s.add(a2s).mul(b3s.add(b4s))
            .add(a3s.add(a4s).mul(b1s.add(b2s))),
    );

    // Chain full RHS: sq-sums ≡ x²y²-sums (via add_congruence on the 8 sq terms)
    lemma_add_congruence::<R>(
        sq13.add(sq31).add(sq14.add(sq41)),
        a1s.mul(b3s).add(a3s.mul(b1s)).add(a1s.mul(b4s).add(a4s.mul(b1s))),
        sq23.add(sq32).add(sq24.add(sq42)),
        a2s.mul(b3s).add(a3s.mul(b2s)).add(a2s.mul(b4s).add(a4s.mul(b2s))),
    );

    // Lift per-group equivalences to sum: x²y²-sums ≡ factored-sums
    lemma_add_congruence::<R>(
        a1s.mul(b3s).add(a3s.mul(b1s)).add(a1s.mul(b4s).add(a4s.mul(b1s))),
        a1s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b1s)),
        a2s.mul(b3s).add(a3s.mul(b2s)).add(a2s.mul(b4s).add(a4s.mul(b2s))),
        a2s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b2s)),
    );

    // Chain: sq-sums ≡ x²y²-sums ≡ factored-sums
    R::axiom_eqv_transitive(
        sq13.add(sq31).add(sq14.add(sq41))
            .add(sq23.add(sq32).add(sq24.add(sq42))),
        a1s.mul(b3s).add(a3s.mul(b1s)).add(a1s.mul(b4s).add(a4s.mul(b1s)))
            .add(a2s.mul(b3s).add(a3s.mul(b2s)).add(a2s.mul(b4s).add(a4s.mul(b2s)))),
        a1s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b1s))
            .add(a2s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b2s))),
    );

    // Chain: factored-sums ≡ αδ + γβ
    R::axiom_eqv_transitive(
        sq13.add(sq31).add(sq14.add(sq41))
            .add(sq23.add(sq32).add(sq24.add(sq42))),
        a1s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b1s))
            .add(a2s.mul(b3s.add(b4s)).add(a3s.add(a4s).mul(b2s))),
        alpha.mul(delta).add(gamma.mul(beta)),
    );

    // Apply RHS congruence to inequality
    lemma_le_congruence_right::<R>(
        two.mul(p12.mul(p34)),
        sq13.add(sq31).add(sq14.add(sq41))
            .add(sq23.add(sq32).add(sq24.add(sq42))),
        alpha.mul(delta).add(gamma.mul(beta)),
    );
}

/// Cauchy-Schwarz in 4D: (a1*b1+a2*b2+a3*b3+a4*b4)² ≤ (a1²+a2²+a3²+a4²)*(b1²+b2²+b3²+b4²).
///
/// Proof: split the dot product as p12+p34 where p12=a1b1+a2b2, p34=a3b3+a4b4.
/// Apply 2D CS to bound p12² and p34², and lemma_cross_term_bound_4d for 2*p12*p34.
/// Sum and factor to get the result.
pub proof fn lemma_cauchy_schwarz_4d<R: OrderedRing>(
    a1: R, a2: R, a3: R, a4: R,
    b1: R, b2: R, b3: R, b4: R,
)
    ensures
        a1.mul(b1).add(a2.mul(b2)).add(a3.mul(b3)).add(a4.mul(b4))
            .mul(a1.mul(b1).add(a2.mul(b2)).add(a3.mul(b3)).add(a4.mul(b4)))
            .le(
                a1.mul(a1).add(a2.mul(a2)).add(a3.mul(a3)).add(a4.mul(a4))
                    .mul(b1.mul(b1).add(b2.mul(b2)).add(b3.mul(b3)).add(b4.mul(b4)))
            ),
{
    let two = R::one().add(R::one());
    let p12 = a1.mul(b1).add(a2.mul(b2));
    let p34 = a3.mul(b3).add(a4.mul(b4));

    // Left-associated form of the dot product
    let s_left = p12.add(a3.mul(b3)).add(a4.mul(b4));
    // Right-grouped form
    let s_right = p12.add(p34);

    let alpha = a1.mul(a1).add(a2.mul(a2));  // a1²+a2²
    let beta  = b1.mul(b1).add(b2.mul(b2));  // b1²+b2²
    let gamma = a3.mul(a3).add(a4.mul(a4));  // a3²+a4²
    let delta = b3.mul(b3).add(b4.mul(b4));  // b3²+b4²

    // ══════════════════════════════════════════════════════════════
    // Part A: s_left ≡ s_right (via associativity)
    // ((a1b1+a2b2)+a3b3)+a4b4 ≡ (a1b1+a2b2)+(a3b3+a4b4)
    // ══════════════════════════════════════════════════════════════

    R::axiom_add_associative(p12, a3.mul(b3), a4.mul(b4));

    // s_left² ≡ s_right² (by congruence)
    lemma_mul_congruence::<R>(s_left, s_right, s_left, s_right);

    // ══════════════════════════════════════════════════════════════
    // Part B: s_right² ≡ p12² + 2·p12·p34 + p34²
    // ══════════════════════════════════════════════════════════════

    lemma_square_expand::<R>(p12, p34);
    // s_right² ≡ p12² + two·(p12·p34) + p34²

    // ══════════════════════════════════════════════════════════════
    // Part C: Bound each term
    // ══════════════════════════════════════════════════════════════

    // C1: p12² ≤ α·β (by 2D CS)
    lemma_cauchy_schwarz_2d::<R>(a1, a2, b1, b2);

    // C2: p34² ≤ γ·δ (by 2D CS)
    lemma_cauchy_schwarz_2d::<R>(a3, a4, b3, b4);

    // C3: 2·p12·p34 ≤ α·δ + γ·β (by cross-term bound)
    lemma_cross_term_bound_4d::<R>(a1, a2, a3, a4, b1, b2, b3, b4);

    // ══════════════════════════════════════════════════════════════
    // Part D: Sum the bounds
    // p12² + (2·p12·p34) ≤ αβ + (αδ+γβ)
    // ══════════════════════════════════════════════════════════════

    lemma_le_add_both::<R>(
        p12.mul(p12), alpha.mul(beta),
        two.mul(p12.mul(p34)), alpha.mul(delta).add(gamma.mul(beta)),
    );
    // + p34² ≤ + γδ
    lemma_le_add_both::<R>(
        p12.mul(p12).add(two.mul(p12.mul(p34))),
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))),
        p34.mul(p34),
        gamma.mul(delta),
    );

    // ══════════════════════════════════════════════════════════════
    // Part E: LHS ≡ s_left², connect via congruence
    // s_left² ≡ s_right² ≡ p12²+2·p12·p34+p34²
    // ══════════════════════════════════════════════════════════════

    // s_right² ≡ p12²+two·(p12·p34)+p34² (from square_expand above)
    // s_left² ≡ s_right² (from Part A)
    R::axiom_eqv_transitive(
        s_left.mul(s_left),
        s_right.mul(s_right),
        p12.mul(p12).add(two.mul(p12.mul(p34))).add(p34.mul(p34)),
    );

    // Apply congruence to LHS of inequality
    R::axiom_eqv_symmetric(
        s_left.mul(s_left),
        p12.mul(p12).add(two.mul(p12.mul(p34))).add(p34.mul(p34)),
    );
    lemma_le_congruence_left::<R>(
        p12.mul(p12).add(two.mul(p12.mul(p34))).add(p34.mul(p34)),
        s_left.mul(s_left),
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))).add(gamma.mul(delta)),
    );

    // ══════════════════════════════════════════════════════════════
    // Part F: RHS ≡ (Σaᵢ²)·(Σbⱼ²), i.e.,
    // αβ + (αδ+γβ) + γδ ≡ (α+γ)(β+δ)
    // and (α+γ) ≡ Σaᵢ² (left-associated), (β+δ) ≡ Σbⱼ² (left-associated)
    // ══════════════════════════════════════════════════════════════

    // F1: (α+γ)(β+δ) ≡ αβ+αδ+γβ+γδ
    // Expand via right distrib then left distrib:
    // (α+γ)(β+δ) ≡ α(β+δ) + γ(β+δ)
    lemma_mul_distributes_right::<R>(alpha, gamma, beta.add(delta));
    // α(β+δ) ≡ αβ + αδ
    R::axiom_mul_distributes_left(alpha, beta, delta);
    // γ(β+δ) ≡ γβ + γδ
    R::axiom_mul_distributes_left(gamma, beta, delta);

    // (α+γ)(β+δ) ≡ (αβ+αδ) + (γβ+γδ)
    lemma_add_congruence::<R>(
        alpha.mul(beta.add(delta)), alpha.mul(beta).add(alpha.mul(delta)),
        gamma.mul(beta.add(delta)), gamma.mul(beta).add(gamma.mul(delta)),
    );
    R::axiom_eqv_transitive(
        alpha.add(gamma).mul(beta.add(delta)),
        alpha.mul(beta.add(delta)).add(gamma.mul(beta.add(delta))),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta).add(gamma.mul(delta))),
    );

    // Now show our bound sum ≡ (α+γ)(β+δ):
    // αβ + (αδ+γβ) + γδ ≡ (αβ+αδ) + (γβ+γδ)
    // LHS is left-assoc: (αβ + (αδ+γβ)) + γδ
    // via rearrange: αβ+(αδ+γβ) ≡ (αβ+αδ)+γβ [assoc reversed in inner]
    R::axiom_add_associative(alpha.mul(beta), alpha.mul(delta), gamma.mul(beta));
    R::axiom_eqv_symmetric(
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta)),
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))),
    );
    // So αβ+(αδ+γβ) ≡ (αβ+αδ)+γβ
    // Then ((αβ+αδ)+γβ)+γδ ≡ (αβ+αδ)+(γβ+γδ) [assoc]
    R::axiom_add_associative(
        alpha.mul(beta).add(alpha.mul(delta)),
        gamma.mul(beta),
        gamma.mul(delta),
    );
    // Chain: (αβ+(αδ+γβ))+γδ ≡ ((αβ+αδ)+γβ)+γδ ≡ (αβ+αδ)+(γβ+γδ)
    R::axiom_add_congruence_left(
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta)),
        gamma.mul(delta),
    );
    R::axiom_eqv_transitive(
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))).add(gamma.mul(delta)),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta)).add(gamma.mul(delta)),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta).add(gamma.mul(delta))),
    );
    // bound_sum ≡ (αβ+αδ)+(γβ+γδ) ≡ (α+γ)(β+δ)
    R::axiom_eqv_symmetric(
        alpha.add(gamma).mul(beta.add(delta)),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta).add(gamma.mul(delta))),
    );
    R::axiom_eqv_transitive(
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))).add(gamma.mul(delta)),
        alpha.mul(beta).add(alpha.mul(delta)).add(gamma.mul(beta).add(gamma.mul(delta))),
        alpha.add(gamma).mul(beta.add(delta)),
    );

    // F2: α+γ ≡ Σaᵢ² (left-associated)
    // alpha.add(gamma) = (a1²+a2²)+(a3²+a4²)
    // left-associated: ((a1²+a2²)+a3²)+a4²
    R::axiom_add_associative(alpha, a3.mul(a3), a4.mul(a4));
    // (α+γ) ≡ (α+a3²)+a4² [assoc reversed... no]
    // α + (a3²+a4²) ≡ (α+a3²)+a4²... wait, assoc gives (α+a3²)+a4² ≡ α+(a3²+a4²)
    // So α+(a3²+a4²) ≡ reversed is (α+a3²)+a4²
    R::axiom_eqv_symmetric(
        alpha.add(a3.mul(a3)).add(a4.mul(a4)),
        alpha.add(a3.mul(a3).add(a4.mul(a4))),
    );

    // F3: β+δ ≡ Σbⱼ² (left-associated)
    R::axiom_add_associative(beta, b3.mul(b3), b4.mul(b4));
    R::axiom_eqv_symmetric(
        beta.add(b3.mul(b3)).add(b4.mul(b4)),
        beta.add(b3.mul(b3).add(b4.mul(b4))),
    );

    // F4: (α+γ)(β+δ) ≡ (Σaᵢ²)(Σbⱼ²)
    lemma_mul_congruence::<R>(
        alpha.add(gamma),
        alpha.add(a3.mul(a3)).add(a4.mul(a4)),
        beta.add(delta),
        beta.add(b3.mul(b3)).add(b4.mul(b4)),
    );

    // Chain bound_sum to (Σaᵢ²)(Σbⱼ²)
    R::axiom_eqv_transitive(
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))).add(gamma.mul(delta)),
        alpha.add(gamma).mul(beta.add(delta)),
        alpha.add(a3.mul(a3)).add(a4.mul(a4))
            .mul(beta.add(b3.mul(b3)).add(b4.mul(b4))),
    );

    // Apply RHS congruence to complete the proof
    lemma_le_congruence_right::<R>(
        s_left.mul(s_left),
        alpha.mul(beta).add(alpha.mul(delta).add(gamma.mul(beta))).add(gamma.mul(delta)),
        alpha.add(a3.mul(a3)).add(a4.mul(a4))
            .mul(beta.add(b3.mul(b3)).add(b4.mul(b4))),
    );
}

} // verus!
