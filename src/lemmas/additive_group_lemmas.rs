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

/// a - a ≡ 0.
pub proof fn lemma_sub_self<A: AdditiveGroup>(a: A)
    ensures
        a.sub(a).eqv(A::zero()),
{
    A::axiom_sub_is_add_neg(a, a);
    A::axiom_add_inverse_right(a);
    A::axiom_eqv_transitive(a.sub(a), a.add(a.neg()), A::zero());
}

/// Full subtraction congruence: if a1 ≡ a2 and b1 ≡ b2 then a1 - b1 ≡ a2 - b2.
pub proof fn lemma_sub_congruence<A: AdditiveGroup>(a1: A, a2: A, b1: A, b2: A)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
    ensures
        a1.sub(b1).eqv(a2.sub(b2)),
{
    // a1 - b1 ≡ a1 + (-b1)
    A::axiom_sub_is_add_neg(a1, b1);
    // a2 - b2 ≡ a2 + (-b2)
    A::axiom_sub_is_add_neg(a2, b2);
    // -b1 ≡ -b2
    A::axiom_neg_congruence(b1, b2);
    // a1 + (-b1) ≡ a2 + (-b2)
    lemma_add_congruence::<A>(a1, a2, b1.neg(), b2.neg());
    // chain: a1 - b1 ≡ a1 + (-b1) ≡ a2 + (-b2)
    A::axiom_eqv_transitive(a1.sub(b1), a1.add(b1.neg()), a2.add(b2.neg()));
    // a2 + (-b2) ≡ a2 - b2 (symmetric)
    A::axiom_eqv_symmetric(a2.sub(b2), a2.add(b2.neg()));
    A::axiom_eqv_transitive(a1.sub(b1), a2.add(b2.neg()), a2.sub(b2));
}

/// (a + b) - b ≡ a.
pub proof fn lemma_add_then_sub_cancel<A: AdditiveGroup>(a: A, b: A)
    ensures
        a.add(b).sub(b).eqv(a),
{
    // (a+b) - b ≡ (a+b) + (-b)
    A::axiom_sub_is_add_neg(a.add(b), b);
    // (a+b) + (-b) ≡ a + (b + (-b))
    A::axiom_add_associative(a, b, b.neg());
    A::axiom_eqv_transitive(a.add(b).sub(b), a.add(b).add(b.neg()), a.add(b.add(b.neg())));
    // b + (-b) ≡ 0
    A::axiom_add_inverse_right(b);
    // a + (b + (-b)) ≡ a + 0
    lemma_add_congruence_right::<A>(a, b.add(b.neg()), A::zero());
    // a + 0 ≡ a
    A::axiom_add_zero_right(a);
    // chain
    A::axiom_eqv_transitive(a.add(b).sub(b), a.add(b.add(b.neg())), a.add(A::zero()));
    A::axiom_eqv_transitive(a.add(b).sub(b), a.add(A::zero()), a);
}

/// (a - b) + b ≡ a.
pub proof fn lemma_sub_then_add_cancel<A: AdditiveGroup>(a: A, b: A)
    ensures
        a.sub(b).add(b).eqv(a),
{
    // (a-b) + b ≡ (a + (-b)) + b
    A::axiom_sub_is_add_neg(a, b);
    A::axiom_add_congruence_left(a.sub(b), a.add(b.neg()), b);
    // (a + (-b)) + b ≡ a + ((-b) + b)
    A::axiom_add_associative(a, b.neg(), b);
    A::axiom_eqv_transitive(a.sub(b).add(b), a.add(b.neg()).add(b), a.add(b.neg().add(b)));
    // (-b) + b ≡ 0
    lemma_add_inverse_left::<A>(b);
    // a + ((-b) + b) ≡ a + 0
    lemma_add_congruence_right::<A>(a, b.neg().add(b), A::zero());
    // a + 0 ≡ a
    A::axiom_add_zero_right(a);
    // chain
    A::axiom_eqv_transitive(a.sub(b).add(b), a.add(b.neg().add(b)), a.add(A::zero()));
    A::axiom_eqv_transitive(a.sub(b).add(b), a.add(A::zero()), a);
}

/// -(a + b) ≡ (-a) + (-b).
pub proof fn lemma_neg_add<A: AdditiveGroup>(a: A, b: A)
    ensures
        a.add(b).neg().eqv(a.neg().add(b.neg())),
{
    // Show (a+b) + ((-a)+(-b)) ≡ 0, then use left_cancel against the inverse.
    // (a+b) + ((-a)+(-b))
    // ≡ a + (b + ((-a)+(-b)))    [assoc]
    // ≡ a + ((b + (-a)) + (-b))  [assoc inner]
    // ≡ a + (((-a) + b) + (-b))  [comm b, -a]
    // ≡ a + ((-a) + (b + (-b)))  [assoc]
    // ≡ a + ((-a) + 0)           [inverse]
    // ≡ a + (-a)                 [identity]
    // ≡ 0                        [inverse]

    // Step 1: b + (-a) ≡ (-a) + b
    A::axiom_add_commutative(b, a.neg());

    // Step 2: b + ((-a) + (-b)) ≡ (b + (-a)) + (-b)
    A::axiom_add_associative(b, a.neg(), b.neg());
    A::axiom_eqv_symmetric(b.add(a.neg()).add(b.neg()), b.add(a.neg().add(b.neg())));

    // Step 3: (b + (-a)) + (-b) ≡ ((-a) + b) + (-b)
    A::axiom_add_congruence_left(b.add(a.neg()), a.neg().add(b), b.neg());

    // Step 4: ((-a) + b) + (-b) ≡ (-a) + (b + (-b))
    A::axiom_add_associative(a.neg(), b, b.neg());

    // Step 5: b + (-b) ≡ 0
    A::axiom_add_inverse_right(b);

    // Step 6: (-a) + (b + (-b)) ≡ (-a) + 0
    lemma_add_congruence_right::<A>(a.neg(), b.add(b.neg()), A::zero());

    // Step 7: (-a) + 0 ≡ -a
    A::axiom_add_zero_right(a.neg());

    // Chain: ((-a)+b)+(-b) ≡ (-a)+(b+(-b)) ≡ (-a)+0 ≡ -a
    A::axiom_eqv_transitive(
        a.neg().add(b).add(b.neg()),
        a.neg().add(b.add(b.neg())),
        a.neg().add(A::zero()),
    );
    A::axiom_eqv_transitive(
        a.neg().add(b).add(b.neg()),
        a.neg().add(A::zero()),
        a.neg(),
    );

    // Chain: (b+(-a))+(-b) ≡ ((-a)+b)+(-b) ≡ -a
    A::axiom_eqv_transitive(
        b.add(a.neg()).add(b.neg()),
        a.neg().add(b).add(b.neg()),
        a.neg(),
    );

    // b + ((-a)+(-b)) ≡ (b+(-a))+(-b) [from step 2 reversed]
    // Chain: b + ((-a)+(-b)) ≡ (b+(-a))+(-b) ≡ -a
    A::axiom_eqv_transitive(
        b.add(a.neg().add(b.neg())),
        b.add(a.neg()).add(b.neg()),
        a.neg(),
    );

    // Now: (a+b) + ((-a)+(-b)) ≡ a + (b + ((-a)+(-b)))
    A::axiom_add_associative(a, b, a.neg().add(b.neg()));
    // a + (b + ((-a)+(-b))) ≡ a + (-a)
    lemma_add_congruence_right::<A>(a, b.add(a.neg().add(b.neg())), a.neg());
    A::axiom_eqv_transitive(
        a.add(b).add(a.neg().add(b.neg())),
        a.add(b.add(a.neg().add(b.neg()))),
        a.add(a.neg()),
    );
    // a + (-a) ≡ 0
    A::axiom_add_inverse_right(a);
    A::axiom_eqv_transitive(
        a.add(b).add(a.neg().add(b.neg())),
        a.add(a.neg()),
        A::zero(),
    );

    // Also: (a+b) + (-(a+b)) ≡ 0
    A::axiom_add_inverse_right(a.add(b));

    // So (a+b) + ((-a)+(-b)) ≡ 0 ≡ (a+b) + (-(a+b))
    A::axiom_eqv_symmetric(a.add(b).add(a.add(b).neg()), A::zero());
    A::axiom_eqv_transitive(
        a.add(b).add(a.neg().add(b.neg())),
        A::zero(),
        a.add(b).add(a.add(b).neg()),
    );

    // By left cancellation: (-a)+(-b) ≡ -(a+b)
    lemma_add_left_cancel::<A>(a.neg().add(b.neg()), a.add(b).neg(), a.add(b));
    A::axiom_eqv_symmetric(a.neg().add(b.neg()), a.add(b).neg());
}

/// a - b ≡ -(b - a).
pub proof fn lemma_sub_antisymmetric<A: AdditiveGroup>(a: A, b: A)
    ensures
        a.sub(b).eqv(b.sub(a).neg()),
{
    // a - b ≡ a + (-b)
    A::axiom_sub_is_add_neg(a, b);
    // b - a ≡ b + (-a)
    A::axiom_sub_is_add_neg(b, a);
    // -(b - a) ≡ -(b + (-a))
    A::axiom_neg_congruence(b.sub(a), b.add(a.neg()));
    // -(b + (-a)) ≡ (-b) + (-(-a))
    lemma_neg_add::<A>(b, a.neg());
    A::axiom_eqv_transitive(b.sub(a).neg(), b.add(a.neg()).neg(), b.neg().add(a.neg().neg()));
    // -(-a) ≡ a
    lemma_neg_involution::<A>(a);
    // (-b) + (-(-a)) ≡ (-b) + a
    lemma_add_congruence_right::<A>(b.neg(), a.neg().neg(), a);
    A::axiom_eqv_transitive(b.sub(a).neg(), b.neg().add(a.neg().neg()), b.neg().add(a));
    // (-b) + a ≡ a + (-b)
    A::axiom_add_commutative(b.neg(), a);
    A::axiom_eqv_transitive(b.sub(a).neg(), b.neg().add(a), a.add(b.neg()));
    // a + (-b) ≡ a - b (symmetric)
    A::axiom_eqv_symmetric(a.sub(b), a.add(b.neg()));
    // chain: a - b ≡ a + (-b) ≡ -(b - a) ... but let's use the other direction
    // -(b-a) ≡ a + (-b) and a - b ≡ a + (-b)
    // So a - b ≡ a + (-b) and -(b-a) ≡ a + (-b)
    // Thus: a - b ≡ -(b - a)
    A::axiom_eqv_symmetric(b.sub(a).neg(), a.add(b.neg()));
    A::axiom_eqv_transitive(a.sub(b), a.add(b.neg()), b.sub(a).neg());
}

/// a - b ≡ 0 implies a ≡ b.
pub proof fn lemma_sub_eqv_zero_implies_eqv<A: AdditiveGroup>(a: A, b: A)
    requires
        a.sub(b).eqv(A::zero()),
    ensures
        a.eqv(b),
{
    // (a - b) + b ≡ a
    lemma_sub_then_add_cancel::<A>(a, b);
    // (a - b) + b ≡ 0 + b
    A::axiom_add_congruence_left(a.sub(b), A::zero(), b);
    // 0 + b ≡ b
    lemma_add_zero_left::<A>(b);
    // a ≡ (a-b)+b ≡ 0+b ≡ b
    A::axiom_eqv_symmetric(a.sub(b).add(b), a);
    A::axiom_eqv_transitive(a, a.sub(b).add(b), A::zero().add(b));
    A::axiom_eqv_transitive(a, A::zero().add(b), b);
}

/// a ≡ b implies a - b ≡ 0.
pub proof fn lemma_eqv_implies_sub_eqv_zero<A: AdditiveGroup>(a: A, b: A)
    requires
        a.eqv(b),
    ensures
        a.sub(b).eqv(A::zero()),
{
    A::axiom_eqv_reflexive(b);
    lemma_sub_congruence::<A>(a, b, b, b);
    // a - b ≡ b - b
    lemma_sub_self::<A>(b);
    A::axiom_eqv_transitive(a.sub(b), b.sub(b), A::zero());
}

/// (-a) - (-b) ≡ b - a.
pub proof fn lemma_sub_neg_both<A: AdditiveGroup>(a: A, b: A)
    ensures
        a.neg().sub(b.neg()).eqv(b.sub(a)),
{
    // (-a) - (-b) ≡ (-a) + (-(-b))
    A::axiom_sub_is_add_neg(a.neg(), b.neg());
    // -(-b) ≡ b
    lemma_neg_involution::<A>(b);
    // (-a) + (-(-b)) ≡ (-a) + b
    lemma_add_congruence_right::<A>(a.neg(), b.neg().neg(), b);
    A::axiom_eqv_transitive(a.neg().sub(b.neg()), a.neg().add(b.neg().neg()), a.neg().add(b));
    // (-a) + b ≡ b + (-a)
    A::axiom_add_commutative(a.neg(), b);
    A::axiom_eqv_transitive(a.neg().sub(b.neg()), a.neg().add(b), b.add(a.neg()));
    // b + (-a) ≡ b - a (symmetric of sub_is_add_neg)
    A::axiom_sub_is_add_neg(b, a);
    A::axiom_eqv_symmetric(b.sub(a), b.add(a.neg()));
    A::axiom_eqv_transitive(a.neg().sub(b.neg()), b.add(a.neg()), b.sub(a));
}

/// (a + b) + (c + d) ≡ (a + c) + (b + d).
pub proof fn lemma_add_rearrange_2x2<A: AdditiveGroup>(a: A, b: A, c: A, d: A)
    ensures
        a.add(b).add(c.add(d)).eqv(a.add(c).add(b.add(d))),
{
    // (a+b)+(c+d) ≡ a+(b+(c+d))     [assoc]
    A::axiom_add_associative(a, b, c.add(d));

    // b+(c+d) ≡ (b+c)+d             [assoc reversed]
    A::axiom_add_associative(b, c, d);
    A::axiom_eqv_symmetric(b.add(c).add(d), b.add(c.add(d)));

    // b+c ≡ c+b                     [comm]
    A::axiom_add_commutative(b, c);

    // (b+c)+d ≡ (c+b)+d             [cong]
    A::axiom_add_congruence_left(b.add(c), c.add(b), d);

    // (c+b)+d ≡ c+(b+d)             [assoc]
    A::axiom_add_associative(c, b, d);

    // Chain: b+(c+d) ≡ (b+c)+d ≡ (c+b)+d ≡ c+(b+d)
    A::axiom_eqv_transitive(b.add(c.add(d)), b.add(c).add(d), c.add(b).add(d));
    A::axiom_eqv_transitive(b.add(c.add(d)), c.add(b).add(d), c.add(b.add(d)));

    // a+(b+(c+d)) ≡ a+(c+(b+d))     [cong right]
    lemma_add_congruence_right::<A>(a, b.add(c.add(d)), c.add(b.add(d)));

    // a+(c+(b+d)) ≡ (a+c)+(b+d)     [assoc reversed]
    A::axiom_add_associative(a, c, b.add(d));
    A::axiom_eqv_symmetric(a.add(c).add(b.add(d)), a.add(c.add(b.add(d))));

    // Chain: (a+b)+(c+d) ≡ a+(b+(c+d)) ≡ a+(c+(b+d)) ≡ (a+c)+(b+d)
    A::axiom_eqv_transitive(
        a.add(b).add(c.add(d)),
        a.add(b.add(c.add(d))),
        a.add(c.add(b.add(d))),
    );
    A::axiom_eqv_transitive(
        a.add(b).add(c.add(d)),
        a.add(c.add(b.add(d))),
        a.add(c).add(b.add(d)),
    );
}

} // verus!
