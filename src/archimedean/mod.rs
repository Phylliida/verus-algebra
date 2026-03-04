use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::{Field, OrderedField};
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;
use crate::inequalities;

verus! {

// ============================================================
//  Natural-number multiplication (repeated addition)
// ============================================================

/// n-fold addition: nat_mul(n, a) = a + a + ... + a (n times).
/// nat_mul(0, a) = 0, nat_mul(n+1, a) = a + nat_mul(n, a).
pub open spec fn nat_mul<R: Ring>(n: nat, a: R) -> R
    decreases n,
{
    if n == 0 { R::zero() }
    else { a.add(nat_mul::<R>((n - 1) as nat, a)) }
}

// ============================================================
//  Basic nat_mul lemmas
// ============================================================

/// nat_mul(0, a) ≡ 0.
pub proof fn lemma_nat_mul_zero<R: Ring>(a: R)
    ensures
        nat_mul::<R>(0, a).eqv(R::zero()),
{
    R::axiom_eqv_reflexive(R::zero());
}

/// nat_mul(1, a) ≡ a.
pub proof fn lemma_nat_mul_one<R: Ring>(a: R)
    ensures
        nat_mul::<R>(1, a).eqv(a),
{
    // Help Verus unfold the recursion
    assert(nat_mul::<R>(1, a) == a.add(nat_mul::<R>(0, a)));
    assert(nat_mul::<R>(0, a) == R::zero());
    // nat_mul(1, a) = a + 0 ≡ a
    R::axiom_add_zero_right(a);
}

/// nat_mul(n+1, a) ≡ a + nat_mul(n, a).
pub proof fn lemma_nat_mul_succ<R: Ring>(n: nat, a: R)
    ensures
        nat_mul::<R>(n + 1, a).eqv(a.add(nat_mul::<R>(n, a))),
{
    R::axiom_eqv_reflexive(a.add(nat_mul::<R>(n, a)));
}

/// nat_mul(2, a) ≡ a + a.
pub proof fn lemma_nat_mul_two<R: Ring>(a: R)
    ensures
        nat_mul::<R>(2, a).eqv(a.add(a)),
{
    // nat_mul(2, a) = a + nat_mul(1, a)
    // nat_mul(1, a) ≡ a
    lemma_nat_mul_one::<R>(a);
    lemma_add_congruence_right::<R>(a, nat_mul::<R>(1, a), a);
}

/// nat_mul(m + n, a) ≡ nat_mul(m, a) + nat_mul(n, a).
pub proof fn lemma_nat_mul_add<R: Ring>(m: nat, n: nat, a: R)
    ensures
        nat_mul::<R>(m + n, a).eqv(nat_mul::<R>(m, a).add(nat_mul::<R>(n, a))),
    decreases m,
{
    if m == 0 {
        // nat_mul(n, a) and 0 + nat_mul(n, a) ≡ nat_mul(n, a)
        lemma_add_zero_left::<R>(nat_mul::<R>(n, a));
        R::axiom_eqv_symmetric(R::zero().add(nat_mul::<R>(n, a)), nat_mul::<R>(n, a));
    } else {
        // nat_mul(m+n, a) = a + nat_mul(m-1+n, a)
        // IH: nat_mul(m-1+n, a) ≡ nat_mul(m-1, a) + nat_mul(n, a)
        lemma_nat_mul_add::<R>((m - 1) as nat, n, a);

        // a + nat_mul(m-1+n, a) ≡ a + (nat_mul(m-1,a) + nat_mul(n,a))
        lemma_add_congruence_right::<R>(
            a,
            nat_mul::<R>(((m - 1) as nat) + n, a),
            nat_mul::<R>((m - 1) as nat, a).add(nat_mul::<R>(n, a)),
        );

        // a + (nat_mul(m-1,a) + nat_mul(n,a)) ≡ (a + nat_mul(m-1,a)) + nat_mul(n,a) [assoc rev]
        R::axiom_add_associative(a, nat_mul::<R>((m - 1) as nat, a), nat_mul::<R>(n, a));
        R::axiom_eqv_symmetric(
            a.add(nat_mul::<R>((m - 1) as nat, a).add(nat_mul::<R>(n, a))),
            a.add(nat_mul::<R>((m - 1) as nat, a)).add(nat_mul::<R>(n, a)),
        );

        // Chain: nat_mul(m+n, a) ≡ a + (nat_mul(m-1,a)+nat_mul(n,a))
        //                        ≡ (a+nat_mul(m-1,a)) + nat_mul(n,a)
        //                        = nat_mul(m,a) + nat_mul(n,a)
        R::axiom_eqv_transitive(
            a.add(nat_mul::<R>(((m - 1) as nat) + n, a)),
            a.add(nat_mul::<R>((m - 1) as nat, a).add(nat_mul::<R>(n, a))),
            a.add(nat_mul::<R>((m - 1) as nat, a)).add(nat_mul::<R>(n, a)),
        );
    }
}

/// nat_mul respects equivalence: a ≡ b implies nat_mul(n, a) ≡ nat_mul(n, b).
pub proof fn lemma_nat_mul_congruence<R: Ring>(n: nat, a: R, b: R)
    requires
        a.eqv(b),
    ensures
        nat_mul::<R>(n, a).eqv(nat_mul::<R>(n, b)),
    decreases n,
{
    if n == 0 {
        R::axiom_eqv_reflexive(R::zero());
    } else {
        lemma_nat_mul_congruence::<R>((n - 1) as nat, a, b);
        lemma_add_congruence::<R>(
            a, b,
            nat_mul::<R>((n - 1) as nat, a), nat_mul::<R>((n - 1) as nat, b),
        );
    }
}

/// 0 ≤ a implies 0 ≤ nat_mul(n, a).
pub proof fn lemma_nat_mul_nonneg<R: OrderedRing>(n: nat, a: R)
    requires
        R::zero().le(a),
    ensures
        R::zero().le(nat_mul::<R>(n, a)),
    decreases n,
{
    if n == 0 {
        R::axiom_le_reflexive(R::zero());
    } else {
        lemma_nat_mul_nonneg::<R>((n - 1) as nat, a);
        // 0 ≤ a and 0 ≤ nat_mul(n-1, a)
        // → 0 ≤ a + nat_mul(n-1, a) = nat_mul(n, a)
        inequalities::lemma_nonneg_add::<R>(a, nat_mul::<R>((n - 1) as nat, a));
    }
}

/// a ≤ b implies nat_mul(n, a) ≤ nat_mul(n, b).
pub proof fn lemma_nat_mul_monotone<R: OrderedRing>(n: nat, a: R, b: R)
    requires
        a.le(b),
    ensures
        nat_mul::<R>(n, a).le(nat_mul::<R>(n, b)),
    decreases n,
{
    if n == 0 {
        R::axiom_le_reflexive(R::zero());
    } else {
        // IH: nat_mul(n-1, a) ≤ nat_mul(n-1, b)
        lemma_nat_mul_monotone::<R>((n - 1) as nat, a, b);
        // a ≤ b → a + nat_mul(n-1,a) ≤ b + nat_mul(n-1,a) [add_monotone]
        R::axiom_le_add_monotone(a, b, nat_mul::<R>((n - 1) as nat, a));
        // b + nat_mul(n-1,a) ≤ b + nat_mul(n-1,b) [add_monotone on right via comm]
        R::axiom_add_commutative(b, nat_mul::<R>((n - 1) as nat, a));
        R::axiom_add_commutative(b, nat_mul::<R>((n - 1) as nat, b));
        R::axiom_le_add_monotone(
            nat_mul::<R>((n - 1) as nat, a),
            nat_mul::<R>((n - 1) as nat, b),
            b,
        );
        // nat_mul(n-1,a)+b ≤ nat_mul(n-1,b)+b, commute both
        R::axiom_eqv_symmetric(b.add(nat_mul::<R>((n - 1) as nat, a)), nat_mul::<R>((n - 1) as nat, a).add(b));
        R::axiom_eqv_symmetric(b.add(nat_mul::<R>((n - 1) as nat, b)), nat_mul::<R>((n - 1) as nat, b).add(b));
        R::axiom_le_congruence(
            nat_mul::<R>((n - 1) as nat, a).add(b), b.add(nat_mul::<R>((n - 1) as nat, a)),
            nat_mul::<R>((n - 1) as nat, b).add(b), b.add(nat_mul::<R>((n - 1) as nat, b)),
        );
        // Transitivity
        R::axiom_le_transitive(
            a.add(nat_mul::<R>((n - 1) as nat, a)),
            b.add(nat_mul::<R>((n - 1) as nat, a)),
            b.add(nat_mul::<R>((n - 1) as nat, b)),
        );
    }
}

/// nat_mul(n, a) ≡ a * nat_mul_ring(n) where nat_mul_ring(n) = nat_mul(n, 1).
/// That is, nat_mul distributes through ring multiplication.
pub proof fn lemma_nat_mul_as_ring_mul<R: Ring>(n: nat, a: R)
    ensures
        nat_mul::<R>(n, a).eqv(a.mul(nat_mul::<R>(n, R::one()))),
    decreases n,
{
    if n == 0 {
        // nat_mul(0, a) = 0, a * nat_mul(0, 1) = a * 0 ≡ 0
        R::axiom_mul_zero_right(a);
        R::axiom_eqv_symmetric(a.mul(R::zero()), R::zero());
    } else {
        // nat_mul(n, a) = a + nat_mul(n-1, a)
        // IH: nat_mul(n-1, a) ≡ a * nat_mul(n-1, 1)
        lemma_nat_mul_as_ring_mul::<R>((n - 1) as nat, a);

        // a + nat_mul(n-1, a) ≡ a + a*nat_mul(n-1, 1)
        lemma_add_congruence_right::<R>(
            a,
            nat_mul::<R>((n - 1) as nat, a),
            a.mul(nat_mul::<R>((n - 1) as nat, R::one())),
        );

        // a + a*nat_mul(n-1,1) ≡ a*1 + a*nat_mul(n-1,1)
        R::axiom_mul_one_right(a);
        R::axiom_eqv_symmetric(a.mul(R::one()), a);
        R::axiom_add_congruence_left(a, a.mul(R::one()), a.mul(nat_mul::<R>((n - 1) as nat, R::one())));

        // a*1 + a*nat_mul(n-1,1) ≡ a*(1 + nat_mul(n-1,1))  [distributes reversed]
        R::axiom_mul_distributes_left(a, R::one(), nat_mul::<R>((n - 1) as nat, R::one()));
        R::axiom_eqv_symmetric(
            a.mul(R::one().add(nat_mul::<R>((n - 1) as nat, R::one()))),
            a.mul(R::one()).add(a.mul(nat_mul::<R>((n - 1) as nat, R::one()))),
        );

        // 1 + nat_mul(n-1, 1) = nat_mul(n, 1)  [definitional]
        R::axiom_eqv_reflexive(R::one().add(nat_mul::<R>((n - 1) as nat, R::one())));

        // Chain: nat_mul(n, a) = a + nat_mul(n-1,a) ≡ a + a*nat_mul(n-1,1)
        //        ≡ a*1 + a*nat_mul(n-1,1) ≡ a*(1+nat_mul(n-1,1)) = a*nat_mul(n,1)
        R::axiom_eqv_transitive(
            a.add(nat_mul::<R>((n - 1) as nat, a)),
            a.add(a.mul(nat_mul::<R>((n - 1) as nat, R::one()))),
            a.mul(R::one()).add(a.mul(nat_mul::<R>((n - 1) as nat, R::one()))),
        );
        R::axiom_eqv_transitive(
            a.add(nat_mul::<R>((n - 1) as nat, a)),
            a.mul(R::one()).add(a.mul(nat_mul::<R>((n - 1) as nat, R::one()))),
            a.mul(R::one().add(nat_mul::<R>((n - 1) as nat, R::one()))),
        );
    }
}

// ============================================================
//  Archimedean property trait
// ============================================================

/// An Archimedean ordered field: for any a > 0 and any b, there
/// exists a natural number n such that n*a > b.
///
/// This axiom guarantees there are no infinitesimals or infinitely
/// large elements. All sub-fields of the real numbers are Archimedean.
pub trait Archimedean: OrderedField {

    /// For any positive a and any b, there exists n with nat_mul(n, a) > b.
    proof fn axiom_archimedean(a: Self, b: Self)
        requires
            Self::zero().lt(a),
        ensures
            exists|n: nat| b.lt(nat_mul::<Self>(n, a));
}

// ============================================================
//  Archimedean lemmas
// ============================================================

/// nat_mul(n, a) can exceed any target b (simple restatement of the axiom).
pub proof fn lemma_archimedean_exceed<F: Archimedean>(a: F, target: F)
    requires
        F::zero().lt(a),
    ensures
        exists|n: nat| target.lt(nat_mul::<F>(n, a)),
{
    F::axiom_archimedean(a, target);
}

} // verus!
