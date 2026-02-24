use vstd::prelude::*;
use crate::traits::additive_group::AdditiveGroup;

verus! {

/// Left identity: 0 + a ≡ a.
/// Derived from right identity + commutativity.
pub proof fn lemma_add_zero_left<A: AdditiveGroup>(a: A)
    ensures
        A::zero().add(a).eqv(a),
{
    A::axiom_add_commutative(A::zero(), a);
    A::axiom_add_zero_right(a);
    A::axiom_eqv_transitive(A::zero().add(a), a.add(A::zero()), a);
}

/// Left inverse: (-a) + a ≡ 0.
/// Derived from right inverse + commutativity.
pub proof fn lemma_add_inverse_left<A: AdditiveGroup>(a: A)
    ensures
        a.neg().add(a).eqv(A::zero()),
{
    A::axiom_add_commutative(a.neg(), a);
    A::axiom_add_inverse_right(a);
    A::axiom_eqv_transitive(a.neg().add(a), a.add(a.neg()), A::zero());
}

/// Addition respects equivalence on the right:
/// if b ≡ c then a + b ≡ a + c.
/// Derived from commutativity + left congruence.
pub proof fn lemma_add_congruence_right<A: AdditiveGroup>(a: A, b: A, c: A)
    requires
        b.eqv(c),
    ensures
        a.add(b).eqv(a.add(c)),
{
    // a + b ≡ b + a ≡ c + a ≡ a + c
    A::axiom_add_commutative(a, b);
    A::axiom_add_congruence_left(b, c, a);
    A::axiom_add_commutative(c, a);
    A::axiom_eqv_transitive(a.add(b), b.add(a), c.add(a));
    A::axiom_eqv_transitive(a.add(b), c.add(a), a.add(c));
}

/// Full addition congruence: if a1 ≡ a2 and b1 ≡ b2 then a1 + b1 ≡ a2 + b2.
pub proof fn lemma_add_congruence<A: AdditiveGroup>(a1: A, a2: A, b1: A, b2: A)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        a1.add(b1).eqv(a2.add(b2)),
{
    A::axiom_add_congruence_left(a1, a2, b1);
    lemma_add_congruence_right::<A>(a2, b1, b2);
    A::axiom_eqv_transitive(a1.add(b1), a2.add(b1), a2.add(b2));
}

/// Right cancellation: if a + k ≡ b + k then a ≡ b.
pub proof fn lemma_add_right_cancel<A: AdditiveGroup>(a: A, b: A, k: A)
    requires
        a.add(k).eqv(b.add(k)),
    ensures
        a.eqv(b),
{
    // (a + k) + (-k) ≡ (b + k) + (-k)   [congruence on given]
    A::axiom_add_congruence_left(a.add(k), b.add(k), k.neg());

    // k + (-k) ≡ 0
    A::axiom_add_inverse_right(k);

    // --- Chain for a: (a + k) + (-k) ≡ a ---
    // (a + k) + (-k) ≡ a + (k + (-k))   [associativity]
    A::axiom_add_associative(a, k, k.neg());
    // a + (k + (-k)) ≡ a + 0             [congruence_right]
    lemma_add_congruence_right::<A>(a, k.add(k.neg()), A::zero());
    // a + 0 ≡ a                           [right identity]
    A::axiom_add_zero_right(a);
    // (a+k)+(-k) ≡ a+(k+(-k)) ≡ a+0 ≡ a
    A::axiom_eqv_transitive(a.add(k).add(k.neg()), a.add(k.add(k.neg())), a.add(A::zero()));
    A::axiom_eqv_transitive(a.add(k).add(k.neg()), a.add(A::zero()), a);

    // --- Chain for b: (b + k) + (-k) ≡ b ---
    A::axiom_add_associative(b, k, k.neg());
    lemma_add_congruence_right::<A>(b, k.add(k.neg()), A::zero());
    A::axiom_add_zero_right(b);
    A::axiom_eqv_transitive(b.add(k).add(k.neg()), b.add(k.add(k.neg())), b.add(A::zero()));
    A::axiom_eqv_transitive(b.add(k).add(k.neg()), b.add(A::zero()), b);

    // a ≡ (a+k)+(-k) ≡ (b+k)+(-k) ≡ b
    A::axiom_eqv_symmetric(a.add(k).add(k.neg()), a);
    A::axiom_eqv_transitive(a, a.add(k).add(k.neg()), b.add(k).add(k.neg()));
    A::axiom_eqv_transitive(a, b.add(k).add(k.neg()), b);
}

/// Left cancellation: if k + a ≡ k + b then a ≡ b.
pub proof fn lemma_add_left_cancel<A: AdditiveGroup>(a: A, b: A, k: A)
    requires
        k.add(a).eqv(k.add(b)),
    ensures
        a.eqv(b),
{
    // k + a ≡ a + k   [comm]
    A::axiom_add_commutative(k, a);
    // k + b ≡ b + k   [comm]
    A::axiom_add_commutative(k, b);
    // a + k ≡ k + a ≡ k + b ≡ b + k
    A::axiom_eqv_symmetric(k.add(a), a.add(k));
    A::axiom_eqv_transitive(a.add(k), k.add(a), k.add(b));
    A::axiom_eqv_transitive(a.add(k), k.add(b), b.add(k));
    lemma_add_right_cancel::<A>(a, b, k);
}

/// Double negation: -(-a) ≡ a.
pub proof fn lemma_neg_involution<A: AdditiveGroup>(a: A)
    ensures
        a.neg().neg().eqv(a),
{
    // -a + (-(-a)) ≡ 0   [right inverse of -a]
    A::axiom_add_inverse_right(a.neg());
    // -a + a ≡ 0          [left inverse of a]
    lemma_add_inverse_left::<A>(a);
    // So: -a + (-(-a)) ≡ 0 ≡ -a + a
    A::axiom_eqv_symmetric(a.neg().add(a), A::zero());
    A::axiom_eqv_transitive(
        a.neg().add(a.neg().neg()),
        A::zero(),
        a.neg().add(a),
    );
    // By left cancellation (cancel -a): (-(-a)) ≡ a
    lemma_add_left_cancel::<A>(a.neg().neg(), a, a.neg());
}

/// Negation of zero: -0 ≡ 0.
pub proof fn lemma_neg_zero<A: AdditiveGroup>()
    ensures
        A::zero().neg().eqv(A::zero()),
{
    // 0 + (-0) ≡ 0   [right inverse]
    A::axiom_add_inverse_right(A::zero());
    // 0 + (-0) ≡ (-0) [left identity]
    lemma_add_zero_left::<A>(A::zero().neg());
    // (-0) ≡ 0 + (-0) ≡ 0
    A::axiom_eqv_symmetric(A::zero().add(A::zero().neg()), A::zero().neg());
    A::axiom_eqv_transitive(
        A::zero().neg(),
        A::zero().add(A::zero().neg()),
        A::zero(),
    );
}

} // verus!
