use vstd::prelude::*;
use crate::traits::ring::Ring;
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

} // verus!
