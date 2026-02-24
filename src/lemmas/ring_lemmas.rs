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

} // verus!
