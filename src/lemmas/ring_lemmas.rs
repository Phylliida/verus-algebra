use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::lemmas::additive_group_lemmas::*;

verus! {

/// Left identity: 1 * a ≡ a.
/// Derived from right identity + commutativity.
pub proof fn lemma_mul_one_left<R: Ring>(a: R)
    ensures
        R::one().mul(a).eqv(a),
{
    R::axiom_mul_commutative(R::one(), a);
    R::axiom_mul_one_right(a);
    R::axiom_eqv_transitive(R::one().mul(a), a.mul(R::one()), a);
}

/// Left zero: 0 * a ≡ 0.
/// Derived from right zero + commutativity.
pub proof fn lemma_mul_zero_left<R: Ring>(a: R)
    ensures
        R::zero().mul(a).eqv(R::zero()),
{
    R::axiom_mul_commutative(R::zero(), a);
    R::axiom_mul_zero_right(a);
    R::axiom_eqv_transitive(R::zero().mul(a), a.mul(R::zero()), R::zero());
}

/// Right distributivity: (a + b) * c ≡ a*c + b*c.
/// Derived from left distributivity + commutativity.
pub proof fn lemma_mul_distributes_right<R: Ring>(a: R, b: R, c: R)
    ensures
        a.add(b).mul(c).eqv(a.mul(c).add(b.mul(c))),
{
    // (a + b) * c ≡ c * (a + b) ≡ c*a + c*b ≡ a*c + b*c
    R::axiom_mul_commutative(a.add(b), c);
    R::axiom_mul_distributes_left(c, a, b);
    R::axiom_eqv_transitive(a.add(b).mul(c), c.mul(a.add(b)), c.mul(a).add(c.mul(b)));

    // c*a ≡ a*c
    R::axiom_mul_commutative(c, a);
    // c*b ≡ b*c
    R::axiom_mul_commutative(c, b);

    // c*a + c*b ≡ a*c + b*c
    R::axiom_add_congruence_left(c.mul(a), a.mul(c), c.mul(b));
    lemma_add_congruence_right::<R>(a.mul(c), c.mul(b), b.mul(c));
    R::axiom_eqv_transitive(c.mul(a).add(c.mul(b)), a.mul(c).add(c.mul(b)), a.mul(c).add(b.mul(c)));

    R::axiom_eqv_transitive(
        a.add(b).mul(c),
        c.mul(a).add(c.mul(b)),
        a.mul(c).add(b.mul(c)),
    );
}

/// Multiplication respects equivalence on the right:
/// if b ≡ c then a * b ≡ a * c.
pub proof fn lemma_mul_congruence_right<R: Ring>(a: R, b: R, c: R)
    requires
        b.eqv(c),
    ensures
        a.mul(b).eqv(a.mul(c)),
{
    // a*b ≡ b*a ≡ c*a ≡ a*c
    R::axiom_mul_commutative(a, b);
    R::axiom_mul_congruence_left(b, c, a);
    R::axiom_mul_commutative(c, a);
    R::axiom_eqv_transitive(a.mul(b), b.mul(a), c.mul(a));
    R::axiom_eqv_transitive(a.mul(b), c.mul(a), a.mul(c));
}

/// Full multiplication congruence: if a1 ≡ a2 and b1 ≡ b2 then a1*b1 ≡ a2*b2.
pub proof fn lemma_mul_congruence<R: Ring>(a1: R, a2: R, b1: R, b2: R)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        a1.mul(b1).eqv(a2.mul(b2)),
{
    R::axiom_mul_congruence_left(a1, a2, b1);
    lemma_mul_congruence_right::<R>(a2, b1, b2);
    R::axiom_eqv_transitive(a1.mul(b1), a2.mul(b1), a2.mul(b2));
}

/// Multiplication by -1: (-1) * a ≡ -a.
pub proof fn lemma_mul_neg_one<R: Ring>(a: R)
    ensures
        R::one().neg().mul(a).eqv(a.neg()),
{
    // (-1)*a + a ≡ (-1)*a + 1*a ≡ (-1 + 1)*a ≡ 0*a ≡ 0
    // So (-1)*a ≡ -a by uniqueness of inverse.

    // 1*a ≡ a
    lemma_mul_one_left::<R>(a);

    // (-1 + 1) ≡ 0
    lemma_add_inverse_left::<R>(R::one());

    // (-1 + 1)*a ≡ 0*a
    R::axiom_mul_congruence_left(R::one().neg().add(R::one()), R::zero(), a);

    // (-1 + 1)*a ≡ (-1)*a + 1*a   [right distributivity]
    lemma_mul_distributes_right::<R>(R::one().neg(), R::one(), a);
    // flip: (-1)*a + 1*a ≡ (-1 + 1)*a
    R::axiom_eqv_symmetric(
        R::one().neg().add(R::one()).mul(a),
        R::one().neg().mul(a).add(R::one().mul(a)),
    );

    // 0*a ≡ 0
    lemma_mul_zero_left::<R>(a);

    // (-1)*a + 1*a ≡ (-1 + 1)*a ≡ 0*a ≡ 0
    R::axiom_eqv_transitive(
        R::one().neg().mul(a).add(R::one().mul(a)),
        R::one().neg().add(R::one()).mul(a),
        R::zero().mul(a),
    );
    R::axiom_eqv_transitive(
        R::one().neg().mul(a).add(R::one().mul(a)),
        R::zero().mul(a),
        R::zero(),
    );

    // (-1)*a + a ≡ (-1)*a + 1*a   [congruence: a ≡ 1*a]
    R::axiom_eqv_symmetric(R::one().mul(a), a);
    lemma_add_congruence_right::<R>(R::one().neg().mul(a), a, R::one().mul(a));
    R::axiom_eqv_symmetric(
        R::one().neg().mul(a).add(a),
        R::one().neg().mul(a).add(R::one().mul(a)),
    );

    // So: (-1)*a + a ≡ 0
    R::axiom_eqv_transitive(
        R::one().neg().mul(a).add(a),
        R::one().neg().mul(a).add(R::one().mul(a)),
        R::zero(),
    );

    // Also: (-a) + a ≡ 0
    lemma_add_inverse_left::<R>(a);

    // Both (-1)*a and (-a) are left inverses of a.
    // (-1)*a + a ≡ 0 ≡ (-a) + a
    // By right cancellation: (-1)*a ≡ -a
    R::axiom_eqv_symmetric(a.neg().add(a), R::zero());
    R::axiom_eqv_transitive(
        R::one().neg().mul(a).add(a),
        R::zero(),
        a.neg().add(a),
    );
    lemma_add_right_cancel::<R>(R::one().neg().mul(a), a.neg(), a);
}

/// a * (-b) ≡ -(a * b).
pub proof fn lemma_mul_neg_right<R: Ring>(a: R, b: R)
    ensures
        a.mul(b.neg()).eqv(a.mul(b).neg()),
{
    // a*(-b) + a*b ≡ a*(-b + b) ≡ a*0 ≡ 0
    // So a*(-b) is the additive inverse of a*b.

    // (-b) + b ≡ 0
    lemma_add_inverse_left::<R>(b);

    // a*((-b) + b) ≡ a*0
    lemma_mul_congruence_right::<R>(a, b.neg().add(b), R::zero());

    // a*((-b) + b) ≡ a*(-b) + a*b  [left distributivity]
    R::axiom_mul_distributes_left(a, b.neg(), b);

    // a*0 ≡ 0
    R::axiom_mul_zero_right(a);

    // a*(-b) + a*b ≡ a*((-b) + b) ≡ a*0 ≡ 0
    R::axiom_eqv_symmetric(a.mul(b.neg().add(b)), a.mul(b.neg()).add(a.mul(b)));
    R::axiom_eqv_transitive(
        a.mul(b.neg()).add(a.mul(b)),
        a.mul(b.neg().add(b)),
        a.mul(R::zero()),
    );
    R::axiom_eqv_transitive(
        a.mul(b.neg()).add(a.mul(b)),
        a.mul(R::zero()),
        R::zero(),
    );

    // Also: -(a*b) + a*b ≡ 0
    lemma_add_inverse_left::<R>(a.mul(b));

    // Both are left inverses of a*b, so they're equivalent.
    R::axiom_eqv_symmetric(a.mul(b).neg().add(a.mul(b)), R::zero());
    R::axiom_eqv_transitive(
        a.mul(b.neg()).add(a.mul(b)),
        R::zero(),
        a.mul(b).neg().add(a.mul(b)),
    );
    lemma_add_right_cancel::<R>(a.mul(b.neg()), a.mul(b).neg(), a.mul(b));
}

/// (-a) * b ≡ -(a * b).
pub proof fn lemma_mul_neg_left<R: Ring>(a: R, b: R)
    ensures
        a.neg().mul(b).eqv(a.mul(b).neg()),
{
    // (-a)*b ≡ b*(-a) ≡ -(b*a) ≡ -(a*b)
    R::axiom_mul_commutative(a.neg(), b);
    lemma_mul_neg_right::<R>(b, a);
    R::axiom_eqv_transitive(a.neg().mul(b), b.mul(a.neg()), b.mul(a).neg());

    R::axiom_mul_commutative(b, a);
    R::axiom_neg_congruence(b.mul(a), a.mul(b));
    R::axiom_eqv_transitive(a.neg().mul(b), b.mul(a).neg(), a.mul(b).neg());
}

/// (-a) * (-b) ≡ a * b.
pub proof fn lemma_neg_mul_neg<R: Ring>(a: R, b: R)
    ensures
        a.neg().mul(b.neg()).eqv(a.mul(b)),
{
    // (-a)*(-b) ≡ -(a*(-b)) ≡ -(-(a*b)) ≡ a*b
    lemma_mul_neg_left::<R>(a, b.neg());
    // a*(-b) ≡ -(a*b)
    lemma_mul_neg_right::<R>(a, b);
    // -(a*(-b)) ≡ -(-(a*b))
    R::axiom_neg_congruence(a.mul(b.neg()), a.mul(b).neg());
    // -(-(a*b)) ≡ a*b
    lemma_neg_involution::<R>(a.mul(b));

    // Chain: (-a)*(-b) ≡ -(a*(-b)) ≡ -(-(a*b)) ≡ a*b
    R::axiom_eqv_transitive(
        a.neg().mul(b.neg()),
        a.mul(b.neg()).neg(),
        a.mul(b).neg().neg(),
    );
    R::axiom_eqv_transitive(
        a.neg().mul(b.neg()),
        a.mul(b).neg().neg(),
        a.mul(b),
    );
}

/// a * (b - c) ≡ a*b - a*c.
pub proof fn lemma_mul_distributes_over_sub<R: Ring>(a: R, b: R, c: R)
    ensures
        a.mul(b.sub(c)).eqv(a.mul(b).sub(a.mul(c))),
{
    // b - c ≡ b + (-c)
    R::axiom_sub_is_add_neg(b, c);
    // a*(b-c) ≡ a*(b+(-c))
    lemma_mul_congruence_right::<R>(a, b.sub(c), b.add(c.neg()));
    // a*(b+(-c)) ≡ a*b + a*(-c)
    R::axiom_mul_distributes_left(a, b, c.neg());
    R::axiom_eqv_transitive(a.mul(b.sub(c)), a.mul(b.add(c.neg())), a.mul(b).add(a.mul(c.neg())));
    // a*(-c) ≡ -(a*c)
    lemma_mul_neg_right::<R>(a, c);
    // a*b + a*(-c) ≡ a*b + (-(a*c))
    lemma_add_congruence_right::<R>(a.mul(b), a.mul(c.neg()), a.mul(c).neg());
    R::axiom_eqv_transitive(
        a.mul(b.sub(c)),
        a.mul(b).add(a.mul(c.neg())),
        a.mul(b).add(a.mul(c).neg()),
    );
    // a*b + (-(a*c)) ≡ a*b - a*c
    R::axiom_sub_is_add_neg(a.mul(b), a.mul(c));
    R::axiom_eqv_symmetric(a.mul(b).sub(a.mul(c)), a.mul(b).add(a.mul(c).neg()));
    R::axiom_eqv_transitive(
        a.mul(b.sub(c)),
        a.mul(b).add(a.mul(c).neg()),
        a.mul(b).sub(a.mul(c)),
    );
}

/// (a - b) * k ≡ a*k - b*k.
pub proof fn lemma_sub_mul_right<R: Ring>(a: R, b: R, k: R)
    ensures
        a.sub(b).mul(k).eqv(a.mul(k).sub(b.mul(k))),
{
    // (a-b)*k ≡ k*(a-b)
    R::axiom_mul_commutative(a.sub(b), k);
    // k*(a-b) ≡ k*a - k*b
    lemma_mul_distributes_over_sub::<R>(k, a, b);
    R::axiom_eqv_transitive(a.sub(b).mul(k), k.mul(a.sub(b)), k.mul(a).sub(k.mul(b)));
    // k*a ≡ a*k
    R::axiom_mul_commutative(k, a);
    // k*b ≡ b*k
    R::axiom_mul_commutative(k, b);
    // k*a - k*b ≡ a*k - b*k
    lemma_sub_congruence::<R>(k.mul(a), a.mul(k), k.mul(b), b.mul(k));
    R::axiom_eqv_transitive(
        a.sub(b).mul(k),
        k.mul(a).sub(k.mul(b)),
        a.mul(k).sub(b.mul(k)),
    );
}

/// a + a ≡ (1 + 1) * a.
pub proof fn lemma_mul_two<R: Ring>(a: R)
    ensures
        a.add(a).eqv(R::one().add(R::one()).mul(a)),
{
    // (1+1)*a ≡ 1*a + 1*a  [right distributivity]
    lemma_mul_distributes_right::<R>(R::one(), R::one(), a);
    // 1*a ≡ a
    lemma_mul_one_left::<R>(a);
    // 1*a + 1*a ≡ a + 1*a
    R::axiom_add_congruence_left(R::one().mul(a), a, R::one().mul(a));
    // a + 1*a ≡ a + a
    lemma_add_congruence_right::<R>(a, R::one().mul(a), a);
    // Chain: (1+1)*a ≡ 1*a + 1*a ≡ a + 1*a ≡ a + a
    R::axiom_eqv_transitive(
        R::one().add(R::one()).mul(a),
        R::one().mul(a).add(R::one().mul(a)),
        a.add(R::one().mul(a)),
    );
    R::axiom_eqv_transitive(
        R::one().add(R::one()).mul(a),
        a.add(R::one().mul(a)),
        a.add(a),
    );
    // Flip: a + a ≡ (1+1)*a
    R::axiom_eqv_symmetric(R::one().add(R::one()).mul(a), a.add(a));
}

/// (a - b) * (a + b) ≡ a*a - b*b.
pub proof fn lemma_square_sub<R: Ring>(a: R, b: R)
    ensures
        a.sub(b).mul(a.add(b)).eqv(a.mul(a).sub(b.mul(b))),
{
    // (a-b)*(a+b)
    // ≡ (a-b)*a + (a-b)*b              [left distributivity, but we use right dist]
    // Use: (a-b)*(a+b) ≡ (a+b)*(a-b) ≡ (a+b)*a - (a+b)*b ... no, let's use mul_distributes_left
    // Actually mul_distributes_left: x*(y+z) ≡ x*y + x*z
    // We want (a-b)*(a+b). Let's first use commutativity.
    R::axiom_mul_commutative(a.sub(b), a.add(b));
    // (a+b)*(a-b) via a+b = x, a-b = y+z where y=a, z=-b
    // (a+b)*(a-b) ≡ (a+b)*(a+(-b))
    R::axiom_sub_is_add_neg(a, b);
    lemma_mul_congruence_right::<R>(a.add(b), a.sub(b), a.add(b.neg()));
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.add(b).mul(a.sub(b)),
        a.add(b).mul(a.add(b.neg())),
    );
    // (a+b)*(a+(-b)) ≡ (a+b)*a + (a+b)*(-b)
    R::axiom_mul_distributes_left(a.add(b), a, b.neg());
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.add(b).mul(a.add(b.neg())),
        a.add(b).mul(a).add(a.add(b).mul(b.neg())),
    );

    // (a+b)*a ≡ a*a + b*a [right dist]
    lemma_mul_distributes_right::<R>(a, b, a);

    // (a+b)*(-b) ≡ a*(-b) + b*(-b) [right dist]
    lemma_mul_distributes_right::<R>(a, b, b.neg());

    // b*a ≡ a*b [comm]
    R::axiom_mul_commutative(b, a);

    // a*(-b) ≡ -(a*b) [mul_neg_right]
    lemma_mul_neg_right::<R>(a, b);

    // b*(-b) ≡ -(b*b) [mul_neg_right]
    lemma_mul_neg_right::<R>(b, b);

    // (a+b)*a + (a+b)*(-b) ≡ (a*a + b*a) + (a*(-b) + b*(-b))
    lemma_add_congruence::<R>(
        a.add(b).mul(a), a.mul(a).add(b.mul(a)),
        a.add(b).mul(b.neg()), a.mul(b.neg()).add(b.mul(b.neg())),
    );
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.add(b).mul(a).add(a.add(b).mul(b.neg())),
        a.mul(a).add(b.mul(a)).add(a.mul(b.neg()).add(b.mul(b.neg()))),
    );

    // Rearrange using add_rearrange_2x2:
    // (a*a + b*a) + (a*(-b) + b*(-b)) ≡ (a*a + a*(-b)) + (b*a + b*(-b))
    lemma_add_rearrange_2x2::<R>(a.mul(a), b.mul(a), a.mul(b.neg()), b.mul(b.neg()));
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.mul(a).add(b.mul(a)).add(a.mul(b.neg()).add(b.mul(b.neg()))),
        a.mul(a).add(a.mul(b.neg())).add(b.mul(a).add(b.mul(b.neg()))),
    );

    // b*a ≡ a*b, and a*(-b) ≡ -(a*b), so b*a + a*(-b) ≡ a*b + -(a*b) ≡ 0
    // Actually we have a*(-b) in one position and b*a in another.
    // a*a + a*(-b) ≡ a*a + -(a*b)
    lemma_add_congruence_right::<R>(a.mul(a), a.mul(b.neg()), a.mul(b).neg());

    // b*a + b*(-b) ≡ a*b + -(b*b)
    lemma_add_congruence::<R>(b.mul(a), a.mul(b), b.mul(b.neg()), b.mul(b).neg());

    // (a*a + a*(-b)) + (b*a + b*(-b)) ≡ (a*a + -(a*b)) + (a*b + -(b*b))
    lemma_add_congruence::<R>(
        a.mul(a).add(a.mul(b.neg())), a.mul(a).add(a.mul(b).neg()),
        b.mul(a).add(b.mul(b.neg())), a.mul(b).add(b.mul(b).neg()),
    );
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.mul(a).add(a.mul(b.neg())).add(b.mul(a).add(b.mul(b.neg()))),
        a.mul(a).add(a.mul(b).neg()).add(a.mul(b).add(b.mul(b).neg())),
    );

    // -(a*b) + a*b ≡ 0
    lemma_add_inverse_left::<R>(a.mul(b));
    // a*a + -(a*b) + (a*b + -(b*b))
    // Use associativity to regroup:
    // (a*a + -(a*b)) + (a*b + -(b*b))
    // ≡ a*a + (-(a*b) + (a*b + -(b*b)))  [assoc]
    R::axiom_add_associative(a.mul(a), a.mul(b).neg(), a.mul(b).add(b.mul(b).neg()));
    // -(a*b) + (a*b + -(b*b)) ≡ (-(a*b) + a*b) + -(b*b)  [assoc reversed]
    R::axiom_add_associative(a.mul(b).neg(), a.mul(b), b.mul(b).neg());
    R::axiom_eqv_symmetric(
        a.mul(b).neg().add(a.mul(b)).add(b.mul(b).neg()),
        a.mul(b).neg().add(a.mul(b).add(b.mul(b).neg())),
    );
    // -(a*b) + a*b ≡ 0
    // (-(a*b) + a*b) + -(b*b) ≡ 0 + -(b*b) ≡ -(b*b)
    R::axiom_add_congruence_left(a.mul(b).neg().add(a.mul(b)), R::zero(), b.mul(b).neg());
    lemma_add_zero_left::<R>(b.mul(b).neg());
    R::axiom_eqv_transitive(
        a.mul(b).neg().add(a.mul(b)).add(b.mul(b).neg()),
        R::zero().add(b.mul(b).neg()),
        b.mul(b).neg(),
    );
    // Chain: -(a*b) + (a*b + -(b*b)) ≡ (-(a*b) + a*b) + -(b*b) ≡ -(b*b)
    R::axiom_eqv_transitive(
        a.mul(b).neg().add(a.mul(b).add(b.mul(b).neg())),
        a.mul(b).neg().add(a.mul(b)).add(b.mul(b).neg()),
        b.mul(b).neg(),
    );

    // a*a + (-(a*b) + (a*b + -(b*b))) ≡ a*a + -(b*b)
    lemma_add_congruence_right::<R>(
        a.mul(a),
        a.mul(b).neg().add(a.mul(b).add(b.mul(b).neg())),
        b.mul(b).neg(),
    );

    // (a*a + -(a*b)) + (a*b + -(b*b)) ≡ a*a + (-(a*b) + (a*b + -(b*b))) ≡ a*a + -(b*b)
    R::axiom_eqv_transitive(
        a.mul(a).add(a.mul(b).neg()).add(a.mul(b).add(b.mul(b).neg())),
        a.mul(a).add(a.mul(b).neg().add(a.mul(b).add(b.mul(b).neg()))),
        a.mul(a).add(b.mul(b).neg()),
    );

    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.mul(a).add(a.mul(b).neg()).add(a.mul(b).add(b.mul(b).neg())),
        a.mul(a).add(b.mul(b).neg()),
    );

    // a*a + -(b*b) ≡ a*a - b*b
    R::axiom_sub_is_add_neg(a.mul(a), b.mul(b));
    R::axiom_eqv_symmetric(a.mul(a).sub(b.mul(b)), a.mul(a).add(b.mul(b).neg()));
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.add(b)),
        a.mul(a).add(b.mul(b).neg()),
        a.mul(a).sub(b.mul(b)),
    );
}

/// (a + b) * (a + b) ≡ a*a + (1+1)*a*b + b*b.
pub proof fn lemma_square_expand<R: Ring>(a: R, b: R)
    ensures
        a.add(b).mul(a.add(b)).eqv(
            a.mul(a).add(R::one().add(R::one()).mul(a.mul(b))).add(b.mul(b))
        ),
{
    // (a+b)*(a+b) ≡ (a+b)*a + (a+b)*b  [left distributivity]
    R::axiom_mul_distributes_left(a.add(b), a, b);

    // (a+b)*a ≡ a*a + b*a [right dist]
    lemma_mul_distributes_right::<R>(a, b, a);

    // (a+b)*b ≡ a*b + b*b [right dist]
    lemma_mul_distributes_right::<R>(a, b, b);

    // So: (a+b)*(a+b) ≡ (a*a + b*a) + (a*b + b*b)
    lemma_add_congruence::<R>(
        a.add(b).mul(a), a.mul(a).add(b.mul(a)),
        a.add(b).mul(b), a.mul(b).add(b.mul(b)),
    );
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.add(b).mul(a).add(a.add(b).mul(b)),
        a.mul(a).add(b.mul(a)).add(a.mul(b).add(b.mul(b))),
    );

    // Rearrange: (a*a + b*a) + (a*b + b*b) ≡ (a*a + a*b) + (b*a + b*b)
    lemma_add_rearrange_2x2::<R>(a.mul(a), b.mul(a), a.mul(b), b.mul(b));
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.mul(a).add(b.mul(a)).add(a.mul(b).add(b.mul(b))),
        a.mul(a).add(a.mul(b)).add(b.mul(a).add(b.mul(b))),
    );

    // b*a ≡ a*b [comm]
    R::axiom_mul_commutative(b, a);
    // b*a + b*b ≡ a*b + b*b
    R::axiom_add_congruence_left(b.mul(a), a.mul(b), b.mul(b));

    // (a*a + a*b) + (b*a + b*b) ≡ (a*a + a*b) + (a*b + b*b)
    R::axiom_eqv_reflexive(a.mul(a).add(a.mul(b)));
    lemma_add_congruence::<R>(
        a.mul(a).add(a.mul(b)), a.mul(a).add(a.mul(b)),
        b.mul(a).add(b.mul(b)), a.mul(b).add(b.mul(b)),
    );
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.mul(a).add(a.mul(b)).add(b.mul(a).add(b.mul(b))),
        a.mul(a).add(a.mul(b)).add(a.mul(b).add(b.mul(b))),
    );

    // Reassociate: (a*a + a*b) + (a*b + b*b) ≡ a*a + (a*b + (a*b + b*b))
    R::axiom_add_associative(a.mul(a), a.mul(b), a.mul(b).add(b.mul(b)));
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.mul(a).add(a.mul(b)).add(a.mul(b).add(b.mul(b))),
        a.mul(a).add(a.mul(b).add(a.mul(b).add(b.mul(b)))),
    );

    // a*b + (a*b + b*b) ≡ (a*b + a*b) + b*b [assoc reversed]
    R::axiom_add_associative(a.mul(b), a.mul(b), b.mul(b));
    R::axiom_eqv_symmetric(
        a.mul(b).add(a.mul(b)).add(b.mul(b)),
        a.mul(b).add(a.mul(b).add(b.mul(b))),
    );

    // a*b + a*b ≡ (1+1)*(a*b) [mul_two]
    lemma_mul_two::<R>(a.mul(b));

    // (a*b + a*b) + b*b ≡ (1+1)*(a*b) + b*b
    R::axiom_add_congruence_left(a.mul(b).add(a.mul(b)), R::one().add(R::one()).mul(a.mul(b)), b.mul(b));

    // Chain: a*b + (a*b + b*b) ≡ (a*b + a*b) + b*b ≡ (1+1)*(a*b) + b*b
    R::axiom_eqv_transitive(
        a.mul(b).add(a.mul(b).add(b.mul(b))),
        a.mul(b).add(a.mul(b)).add(b.mul(b)),
        R::one().add(R::one()).mul(a.mul(b)).add(b.mul(b)),
    );

    // a*a + (a*b + (a*b + b*b)) ≡ a*a + ((1+1)*(a*b) + b*b)
    lemma_add_congruence_right::<R>(
        a.mul(a),
        a.mul(b).add(a.mul(b).add(b.mul(b))),
        R::one().add(R::one()).mul(a.mul(b)).add(b.mul(b)),
    );
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.mul(a).add(a.mul(b).add(a.mul(b).add(b.mul(b)))),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b)).add(b.mul(b))),
    );

    // a*a + ((1+1)*(a*b) + b*b) ≡ (a*a + (1+1)*(a*b)) + b*b [assoc reversed]
    R::axiom_add_associative(a.mul(a), R::one().add(R::one()).mul(a.mul(b)), b.mul(b));
    R::axiom_eqv_symmetric(
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b))).add(b.mul(b)),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b)).add(b.mul(b))),
    );
    R::axiom_eqv_transitive(
        a.add(b).mul(a.add(b)),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b)).add(b.mul(b))),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b))).add(b.mul(b)),
    );
}

/// (a - b) * (a - b) ≡ a*a - (1+1)*a*b + b*b.
pub proof fn lemma_square_sub_expand<R: Ring>(a: R, b: R)
    ensures
        a.sub(b).mul(a.sub(b)).eqv(
            a.mul(a).sub(R::one().add(R::one()).mul(a.mul(b))).add(b.mul(b))
        ),
{
    // a - b ≡ a + (-b)
    R::axiom_sub_is_add_neg(a, b);

    // (a-b)*(a-b) ≡ (a+(-b))*(a+(-b)) [congruence]
    lemma_mul_congruence::<R>(a.sub(b), a.add(b.neg()), a.sub(b), a.add(b.neg()));

    // Apply square_expand to (a+(-b))*(a+(-b)):
    // ≡ a*a + (1+1)*a*(-b) + (-b)*(-b)
    lemma_square_expand::<R>(a, b.neg());
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.sub(b)),
        a.add(b.neg()).mul(a.add(b.neg())),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b.neg()))).add(b.neg().mul(b.neg())),
    );

    // a*(-b) ≡ -(a*b) [mul_neg_right]
    lemma_mul_neg_right::<R>(a, b);

    // (1+1)*a*(-b) ≡ (1+1)*(-(a*b))
    lemma_mul_congruence_right::<R>(R::one().add(R::one()), a.mul(b.neg()), a.mul(b).neg());

    // (1+1)*(-(a*b)) ≡ -((1+1)*(a*b)) [mul_neg_right]
    lemma_mul_neg_right::<R>(R::one().add(R::one()), a.mul(b));

    // Chain: (1+1)*a*(-b) ≡ (1+1)*(-(a*b)) ≡ -((1+1)*(a*b))
    R::axiom_eqv_transitive(
        R::one().add(R::one()).mul(a.mul(b.neg())),
        R::one().add(R::one()).mul(a.mul(b).neg()),
        R::one().add(R::one()).mul(a.mul(b)).neg(),
    );

    // (-b)*(-b) ≡ b*b [neg_mul_neg]
    lemma_neg_mul_neg::<R>(b, b);

    // a*a + (1+1)*a*(-b) ≡ a*a + (-((1+1)*(a*b)))
    lemma_add_congruence_right::<R>(
        a.mul(a),
        R::one().add(R::one()).mul(a.mul(b.neg())),
        R::one().add(R::one()).mul(a.mul(b)).neg(),
    );

    // a*a + (-((1+1)*(a*b))) ≡ a*a - (1+1)*(a*b)
    R::axiom_sub_is_add_neg(a.mul(a), R::one().add(R::one()).mul(a.mul(b)));
    R::axiom_eqv_symmetric(
        a.mul(a).sub(R::one().add(R::one()).mul(a.mul(b))),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b)).neg()),
    );
    R::axiom_eqv_transitive(
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b.neg()))),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b)).neg()),
        a.mul(a).sub(R::one().add(R::one()).mul(a.mul(b))),
    );

    // Full: (a*a + (1+1)*a*(-b)) + (-b)*(-b) ≡ (a*a - (1+1)*(a*b)) + b*b
    lemma_add_congruence::<R>(
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b.neg()))),
        a.mul(a).sub(R::one().add(R::one()).mul(a.mul(b))),
        b.neg().mul(b.neg()),
        b.mul(b),
    );
    R::axiom_eqv_transitive(
        a.sub(b).mul(a.sub(b)),
        a.mul(a).add(R::one().add(R::one()).mul(a.mul(b.neg()))).add(b.neg().mul(b.neg())),
        a.mul(a).sub(R::one().add(R::one()).mul(a.mul(b))).add(b.mul(b)),
    );
}

/// If 1 * e ≡ 1, then e ≡ 1.
pub proof fn lemma_mul_identity_unique<R: Ring>(e: R)
    requires
        R::one().mul(e).eqv(R::one()),
    ensures
        e.eqv(R::one()),
{
    // 1 * e ≡ e  [mul_one_left]
    lemma_mul_one_left::<R>(e);
    // 1 * e ≡ 1  [given]
    // e ≡ 1*e ≡ 1
    R::axiom_eqv_symmetric(R::one().mul(e), e);
    R::axiom_eqv_transitive(e, R::one().mul(e), R::one());
}

} // verus!
