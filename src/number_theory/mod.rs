use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;

verus! {

/// a divides b if there exists k such that a * k ≡ b.
pub open spec fn divides<R: Ring>(a: R, b: R) -> bool {
    exists|k: R| a.mul(k).eqv(b)
}

/// Every element divides itself: divides(a, a), witness: one().
pub proof fn lemma_divides_reflexive<R: Ring>(a: R)
    ensures
        divides::<R>(a, a),
{
    R::axiom_mul_one_right(a);
    // a * 1 ≡ a, so witness k = 1
}

/// Every element divides zero: divides(a, 0), witness: zero().
pub proof fn lemma_divides_zero<R: Ring>(a: R)
    ensures
        divides::<R>(a, R::zero()),
{
    R::axiom_mul_zero_right(a);
    // a * 0 ≡ 0, so witness k = 0
}

/// One divides everything: divides(1, a), witness: a.
pub proof fn lemma_one_divides<R: Ring>(a: R)
    ensures
        divides::<R>(R::one(), a),
{
    lemma_mul_one_left::<R>(a);
    // 1 * a ≡ a, so witness k = a
}

/// Divisibility is transitive: divides(a,b) and divides(b,c) implies divides(a,c).
pub proof fn lemma_divides_transitive<R: Ring>(a: R, b: R, c: R)
    requires
        divides::<R>(a, b),
        divides::<R>(b, c),
    ensures
        divides::<R>(a, c),
{
    // Exists k1: a*k1 ≡ b and k2: b*k2 ≡ c
    // Then a*(k1*k2) ≡ (a*k1)*k2 ≡ b*k2 ≡ c
    let k1 = choose|k: R| a.mul(k).eqv(b);
    let k2 = choose|k: R| b.mul(k).eqv(c);
    // a*k1 ≡ b
    // b*k2 ≡ c
    // (a*k1)*k2 ≡ b*k2 ≡ c
    R::axiom_mul_congruence_left(a.mul(k1), b, k2);
    R::axiom_eqv_transitive(a.mul(k1).mul(k2), b.mul(k2), c);
    // a*(k1*k2) ≡ (a*k1)*k2
    R::axiom_mul_associative(a, k1, k2);
    R::axiom_eqv_symmetric(a.mul(k1).mul(k2), a.mul(k1.mul(k2)));
    // a*(k1*k2) ≡ (a*k1)*k2 ≡ c
    R::axiom_eqv_symmetric(a.mul(k1.mul(k2)), a.mul(k1).mul(k2));
    R::axiom_eqv_transitive(a.mul(k1.mul(k2)), a.mul(k1).mul(k2), c);
}

/// If a divides b and a divides c, then a divides b + c.
pub proof fn lemma_divides_add<R: Ring>(a: R, b: R, c: R)
    requires
        divides::<R>(a, b),
        divides::<R>(a, c),
    ensures
        divides::<R>(a, b.add(c)),
{
    // Witnesses: a*k1 ≡ b and a*k2 ≡ c
    let k1 = choose|k: R| a.mul(k).eqv(b);
    let k2 = choose|k: R| a.mul(k).eqv(c);
    // a*(k1+k2) ≡ a*k1 + a*k2  [left distributivity]
    R::axiom_mul_distributes_left(a, k1, k2);
    // a*k1 + a*k2 ≡ b + a*k2   [add congruence left]
    R::axiom_add_congruence_left(a.mul(k1), b, a.mul(k2));
    // b + a*k2 ≡ b + c          [add congruence right]
    lemma_add_congruence_right::<R>(b, a.mul(k2), c);
    // Chain: a*(k1+k2) ≡ a*k1 + a*k2 ≡ b + a*k2 ≡ b + c
    R::axiom_eqv_transitive(
        a.mul(k1.add(k2)),
        a.mul(k1).add(a.mul(k2)),
        b.add(a.mul(k2)),
    );
    R::axiom_eqv_transitive(
        a.mul(k1.add(k2)),
        b.add(a.mul(k2)),
        b.add(c),
    );
}

/// If a divides b, then a divides b * c.
pub proof fn lemma_divides_mul_right<R: Ring>(a: R, b: R, c: R)
    requires
        divides::<R>(a, b),
    ensures
        divides::<R>(a, b.mul(c)),
{
    // Witness: a*k ≡ b, so a*(k*c) ≡ (a*k)*c ≡ b*c
    let k = choose|k: R| a.mul(k).eqv(b);
    // (a*k)*c ≡ b*c  [congruence left]
    R::axiom_mul_congruence_left(a.mul(k), b, c);
    // (a*k)*c ≡ a*(k*c)  [associativity]
    R::axiom_mul_associative(a, k, c);
    // a*(k*c) ≡ (a*k)*c  [symmetric]
    R::axiom_eqv_symmetric(a.mul(k).mul(c), a.mul(k.mul(c)));
    // Chain: a*(k*c) ≡ (a*k)*c ≡ b*c
    R::axiom_eqv_transitive(a.mul(k.mul(c)), a.mul(k).mul(c), b.mul(c));
}

/// If a divides b, then a divides -b.
pub proof fn lemma_divides_neg<R: Ring>(a: R, b: R)
    requires
        divides::<R>(a, b),
    ensures
        divides::<R>(a, b.neg()),
{
    // Witness: a*k ≡ b, so a*(-k) ≡ -(a*k) ≡ -b
    let k = choose|k: R| a.mul(k).eqv(b);
    // a*(-k) ≡ -(a*k)  [mul_neg_right]
    lemma_mul_neg_right::<R>(a, k);
    // -(a*k) ≡ -b       [neg_congruence]
    R::axiom_neg_congruence(a.mul(k), b);
    // Chain: a*(-k) ≡ -(a*k) ≡ -b
    R::axiom_eqv_transitive(a.mul(k.neg()), a.mul(k).neg(), b.neg());
}

} // verus!
