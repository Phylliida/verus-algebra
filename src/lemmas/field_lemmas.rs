use vstd::prelude::*;
use crate::traits::field::Field;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;

verus! {

/// Left multiplicative inverse: recip(a) * a ≡ 1 for nonzero a.
pub proof fn lemma_mul_recip_left<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.recip().mul(a).eqv(F::one()),
{
    F::axiom_mul_commutative(a.recip(), a);
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(a.recip().mul(a), a.mul(a.recip()), F::one());
}

/// Division by self: a / a ≡ 1 for nonzero a.
pub proof fn lemma_div_self<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.div(a).eqv(F::one()),
{
    F::axiom_div_is_mul_recip(a, a);
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(a.div(a), a.mul(a.recip()), F::one());
}

/// If a ≢ 0 and b ≢ 0 then a*b ≢ 0.
pub proof fn lemma_nonzero_product<F: Field>(a: F, b: F)
    requires
        !a.eqv(F::zero()),
        !b.eqv(F::zero()),
    ensures
        !a.mul(b).eqv(F::zero()),
{
    if a.mul(b).eqv(F::zero()) {
        // Step 1: recip(a) * (a*b) ≡ recip(a) * 0  [cong right, a*b ≡ 0]
        lemma_mul_congruence_right::<F>(a.recip(), a.mul(b), F::zero());
        // Step 2: recip(a) * 0 ≡ 0
        F::axiom_mul_zero_right(a.recip());
        // Step 3: recip(a) * (a*b) ≡ 0
        F::axiom_eqv_transitive(a.recip().mul(a.mul(b)), a.recip().mul(F::zero()), F::zero());

        // Step 4: recip(a) * (a*b) ≡ (recip(a)*a)*b  [assoc reversed]
        F::axiom_mul_associative(a.recip(), a, b);
        F::axiom_eqv_symmetric(a.recip().mul(a).mul(b), a.recip().mul(a.mul(b)));

        // Step 5: recip(a)*a ≡ 1
        lemma_mul_recip_left::<F>(a);
        // Step 6: (recip(a)*a)*b ≡ 1*b
        F::axiom_mul_congruence_left(a.recip().mul(a), F::one(), b);
        // Step 7: 1*b ≡ b
        lemma_mul_one_left::<F>(b);

        // Step 8: recip(a)*(a*b) ≡ (recip(a)*a)*b ≡ 1*b ≡ b
        F::axiom_eqv_transitive(a.recip().mul(a.mul(b)), a.recip().mul(a).mul(b), F::one().mul(b));
        F::axiom_eqv_transitive(a.recip().mul(a.mul(b)), F::one().mul(b), b);

        // Step 9: b ≡ recip(a)*(a*b) ≡ 0
        F::axiom_eqv_symmetric(a.recip().mul(a.mul(b)), b);
        F::axiom_eqv_transitive(b, a.recip().mul(a.mul(b)), F::zero());
    }
}

/// Right cancellation: a*c ≡ b*c and c ≢ 0 implies a ≡ b.
pub proof fn lemma_mul_cancel_right<F: Field>(a: F, b: F, c: F)
    requires
        a.mul(c).eqv(b.mul(c)),
        !c.eqv(F::zero()),
    ensures
        a.eqv(b),
{
    // Multiply both sides by recip(c):
    // (a*c)*recip(c) ≡ (b*c)*recip(c)
    F::axiom_mul_congruence_left(a.mul(c), b.mul(c), c.recip());

    // (a*c)*recip(c) ≡ a*(c*recip(c)) ≡ a*1 ≡ a
    F::axiom_mul_associative(a, c, c.recip());
    F::axiom_mul_recip_right(c);
    lemma_mul_congruence_right::<F>(a, c.mul(c.recip()), F::one());
    F::axiom_mul_one_right(a);
    F::axiom_eqv_transitive(a.mul(c).mul(c.recip()), a.mul(c.mul(c.recip())), a.mul(F::one()));
    F::axiom_eqv_transitive(a.mul(c).mul(c.recip()), a.mul(F::one()), a);

    // (b*c)*recip(c) ≡ b*(c*recip(c)) ≡ b*1 ≡ b
    F::axiom_mul_associative(b, c, c.recip());
    lemma_mul_congruence_right::<F>(b, c.mul(c.recip()), F::one());
    F::axiom_mul_one_right(b);
    F::axiom_eqv_transitive(b.mul(c).mul(c.recip()), b.mul(c.mul(c.recip())), b.mul(F::one()));
    F::axiom_eqv_transitive(b.mul(c).mul(c.recip()), b.mul(F::one()), b);

    // a ≡ (a*c)*recip(c) ≡ (b*c)*recip(c) ≡ b
    F::axiom_eqv_symmetric(a.mul(c).mul(c.recip()), a);
    F::axiom_eqv_transitive(a, a.mul(c).mul(c.recip()), b.mul(c).mul(c.recip()));
    F::axiom_eqv_transitive(a, b.mul(c).mul(c.recip()), b);
}

/// Left cancellation: c*a ≡ c*b and c ≢ 0 implies a ≡ b.
pub proof fn lemma_mul_cancel_left<F: Field>(a: F, b: F, c: F)
    requires
        c.mul(a).eqv(c.mul(b)),
        !c.eqv(F::zero()),
    ensures
        a.eqv(b),
{
    // c*a ≡ a*c and c*b ≡ b*c
    F::axiom_mul_commutative(c, a);
    F::axiom_mul_commutative(c, b);
    // a*c ≡ c*a ≡ c*b ≡ b*c
    F::axiom_eqv_symmetric(c.mul(a), a.mul(c));
    F::axiom_eqv_transitive(a.mul(c), c.mul(a), c.mul(b));
    F::axiom_eqv_transitive(a.mul(c), c.mul(b), b.mul(c));
    lemma_mul_cancel_right::<F>(a, b, c);
}

/// a / 1 ≡ a.
pub proof fn lemma_div_one<F: Field>(a: F)
    ensures
        a.div(F::one()).eqv(a),
{
    // a/1 ≡ a * recip(1)
    F::axiom_div_is_mul_recip(a, F::one());

    // Show recip(1) ≡ 1:
    // 1 * recip(1) ≡ 1 [axiom, since 1 ≢ 0]
    F::axiom_one_ne_zero();
    F::axiom_mul_recip_right(F::one());
    // 1 * recip(1) ≡ recip(1) [left identity]
    lemma_mul_one_left::<F>(F::one().recip());
    // recip(1) ≡ 1*recip(1) ≡ 1
    F::axiom_eqv_symmetric(F::one().mul(F::one().recip()), F::one().recip());
    F::axiom_eqv_transitive(F::one().recip(), F::one().mul(F::one().recip()), F::one());

    // a * recip(1) ≡ a * 1
    lemma_mul_congruence_right::<F>(a, F::one().recip(), F::one());
    // a * 1 ≡ a
    F::axiom_mul_one_right(a);

    // a/1 ≡ a*recip(1) ≡ a*1 ≡ a
    F::axiom_eqv_transitive(a.div(F::one()), a.mul(F::one().recip()), a.mul(F::one()));
    F::axiom_eqv_transitive(a.div(F::one()), a.mul(F::one()), a);
}

/// recip(recip(a)) ≡ a for nonzero a.
pub proof fn lemma_recip_involution<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.recip().recip().eqv(a),
{
    // Both a and recip(recip(a)) are right-inverses of recip(a).
    // recip(a) * a ≡ 1 [mul_recip_left]
    lemma_mul_recip_left::<F>(a);

    // recip(a) ≢ 0 (otherwise a*recip(a)≡a*0≡0≢1)
    // Proof by contradiction: if recip(a) ≡ 0, then
    // a * recip(a) ≡ a * 0 ≡ 0, but a * recip(a) ≡ 1, so 1 ≡ 0. Contradiction.
    if a.recip().eqv(F::zero()) {
        lemma_mul_congruence_right::<F>(a, a.recip(), F::zero());
        F::axiom_mul_zero_right(a);
        F::axiom_mul_recip_right(a);
        // a*recip(a) ≡ a*0 ≡ 0 and a*recip(a) ≡ 1
        F::axiom_eqv_transitive(a.mul(a.recip()), a.mul(F::zero()), F::zero());
        F::axiom_eqv_symmetric(a.mul(a.recip()), F::one());
        F::axiom_eqv_transitive(F::one(), a.mul(a.recip()), F::zero());
        F::axiom_one_ne_zero();
    }

    // recip(a) * recip(recip(a)) ≡ 1 [axiom on recip(a)]
    F::axiom_mul_recip_right(a.recip());

    // Both: recip(a)*a ≡ 1 and recip(a)*recip(recip(a)) ≡ 1
    // So recip(a)*a ≡ recip(a)*recip(recip(a))
    F::axiom_eqv_symmetric(a.recip().mul(a.recip().recip()), F::one());
    F::axiom_eqv_transitive(a.recip().mul(a), F::one(), a.recip().mul(a.recip().recip()));

    // By left cancellation: a ≡ recip(recip(a))
    lemma_mul_cancel_left::<F>(a, a.recip().recip(), a.recip());
    F::axiom_eqv_symmetric(a, a.recip().recip());
}

/// (a / b) * b ≡ a for nonzero b.
pub proof fn lemma_div_mul_cancel<F: Field>(a: F, b: F)
    requires
        !b.eqv(F::zero()),
    ensures
        a.div(b).mul(b).eqv(a),
{
    // a/b ≡ a*recip(b)
    F::axiom_div_is_mul_recip(a, b);
    // (a/b)*b ≡ (a*recip(b))*b
    F::axiom_mul_congruence_left(a.div(b), a.mul(b.recip()), b);
    // (a*recip(b))*b ≡ a*(recip(b)*b)
    F::axiom_mul_associative(a, b.recip(), b);
    // recip(b)*b ≡ 1
    lemma_mul_recip_left::<F>(b);
    // a*(recip(b)*b) ≡ a*1
    lemma_mul_congruence_right::<F>(a, b.recip().mul(b), F::one());
    // a*1 ≡ a
    F::axiom_mul_one_right(a);
    // Chain: (a/b)*b ≡ (a*recip(b))*b ≡ a*(recip(b)*b) ≡ a*1 ≡ a
    F::axiom_eqv_transitive(a.div(b).mul(b), a.mul(b.recip()).mul(b), a.mul(b.recip().mul(b)));
    F::axiom_eqv_transitive(a.div(b).mul(b), a.mul(b.recip().mul(b)), a.mul(F::one()));
    F::axiom_eqv_transitive(a.div(b).mul(b), a.mul(F::one()), a);
}

/// (a * b) / b ≡ a for nonzero b.
pub proof fn lemma_mul_div_cancel<F: Field>(a: F, b: F)
    requires
        !b.eqv(F::zero()),
    ensures
        a.mul(b).div(b).eqv(a),
{
    // (a*b)/b ≡ (a*b)*recip(b)
    F::axiom_div_is_mul_recip(a.mul(b), b);
    // (a*b)*recip(b) ≡ a*(b*recip(b))
    F::axiom_mul_associative(a, b, b.recip());
    // b*recip(b) ≡ 1
    F::axiom_mul_recip_right(b);
    // a*(b*recip(b)) ≡ a*1
    lemma_mul_congruence_right::<F>(a, b.mul(b.recip()), F::one());
    // a*1 ≡ a
    F::axiom_mul_one_right(a);
    // Chain
    F::axiom_eqv_transitive(a.mul(b).div(b), a.mul(b).mul(b.recip()), a.mul(b.mul(b.recip())));
    F::axiom_eqv_transitive(a.mul(b).div(b), a.mul(b.mul(b.recip())), a.mul(F::one()));
    F::axiom_eqv_transitive(a.mul(b).div(b), a.mul(F::one()), a);
}

/// (a + b) / c ≡ a/c + b/c for nonzero c.
pub proof fn lemma_div_distributes_over_add<F: Field>(a: F, b: F, c: F)
    requires
        !c.eqv(F::zero()),
    ensures
        a.add(b).div(c).eqv(a.div(c).add(b.div(c))),
{
    // (a+b)/c ≡ (a+b)*recip(c)
    F::axiom_div_is_mul_recip(a.add(b), c);
    // (a+b)*recip(c) ≡ a*recip(c) + b*recip(c)  [right distributivity]
    lemma_mul_distributes_right::<F>(a, b, c.recip());
    F::axiom_eqv_transitive(
        a.add(b).div(c),
        a.add(b).mul(c.recip()),
        a.mul(c.recip()).add(b.mul(c.recip())),
    );
    // a/c ≡ a*recip(c)
    F::axiom_div_is_mul_recip(a, c);
    // b/c ≡ b*recip(c)
    F::axiom_div_is_mul_recip(b, c);
    // a*recip(c) + b*recip(c) ≡ a/c + b/c (reverse congruence)
    F::axiom_eqv_symmetric(a.div(c), a.mul(c.recip()));
    F::axiom_eqv_symmetric(b.div(c), b.mul(c.recip()));
    lemma_add_congruence::<F>(a.mul(c.recip()), a.div(c), b.mul(c.recip()), b.div(c));
    F::axiom_eqv_transitive(
        a.add(b).div(c),
        a.mul(c.recip()).add(b.mul(c.recip())),
        a.div(c).add(b.div(c)),
    );
}

/// recip(a * b) ≡ recip(a) * recip(b) for nonzero a, b.
pub proof fn lemma_recip_mul<F: Field>(a: F, b: F)
    requires
        !a.eqv(F::zero()),
        !b.eqv(F::zero()),
    ensures
        a.mul(b).recip().eqv(a.recip().mul(b.recip())),
{
    // Show (a*b)*(recip(a)*recip(b)) ≡ 1 via rearrangement.
    // (a*b)*(recip(a)*recip(b))
    // ≡ a*(b*(recip(a)*recip(b)))        [assoc]
    F::axiom_mul_associative(a, b, a.recip().mul(b.recip()));
    // ≡ a*((b*recip(a))*recip(b))        [assoc inner, reversed]
    F::axiom_mul_associative(b, a.recip(), b.recip());
    F::axiom_eqv_symmetric(b.mul(a.recip()).mul(b.recip()), b.mul(a.recip().mul(b.recip())));
    lemma_mul_congruence_right::<F>(a, b.mul(a.recip().mul(b.recip())), b.mul(a.recip()).mul(b.recip()));
    F::axiom_eqv_transitive(
        a.mul(b).mul(a.recip().mul(b.recip())),
        a.mul(b.mul(a.recip().mul(b.recip()))),
        a.mul(b.mul(a.recip()).mul(b.recip())),
    );
    // b*recip(a) ≡ recip(a)*b           [comm]
    F::axiom_mul_commutative(b, a.recip());
    // (recip(a)*b)*recip(b) ≡ recip(a)*(b*recip(b)) [assoc]
    F::axiom_mul_associative(a.recip(), b, b.recip());
    // (b*recip(a))*recip(b) ≡ (recip(a)*b)*recip(b) [cong]
    F::axiom_mul_congruence_left(b.mul(a.recip()), a.recip().mul(b), b.recip());
    // (recip(a)*b)*recip(b) ≡ recip(a)*(b*recip(b))
    F::axiom_eqv_transitive(
        b.mul(a.recip()).mul(b.recip()),
        a.recip().mul(b).mul(b.recip()),
        a.recip().mul(b.mul(b.recip())),
    );
    // b*recip(b) ≡ 1
    F::axiom_mul_recip_right(b);
    // recip(a)*(b*recip(b)) ≡ recip(a)*1
    lemma_mul_congruence_right::<F>(a.recip(), b.mul(b.recip()), F::one());
    // recip(a)*1 ≡ recip(a)
    F::axiom_mul_one_right(a.recip());
    // Chain: (b*recip(a))*recip(b) ≡ recip(a)*(b*recip(b)) ≡ recip(a)*1 ≡ recip(a)
    F::axiom_eqv_transitive(
        b.mul(a.recip()).mul(b.recip()),
        a.recip().mul(b.mul(b.recip())),
        a.recip().mul(F::one()),
    );
    F::axiom_eqv_transitive(
        b.mul(a.recip()).mul(b.recip()),
        a.recip().mul(F::one()),
        a.recip(),
    );

    // So: a*(b*recip(a))*recip(b) ≡ a*recip(a) [cong right on a]
    lemma_mul_congruence_right::<F>(a, b.mul(a.recip()).mul(b.recip()), a.recip());
    F::axiom_eqv_transitive(
        a.mul(b).mul(a.recip().mul(b.recip())),
        a.mul(b.mul(a.recip()).mul(b.recip())),
        a.mul(a.recip()),
    );
    // a*recip(a) ≡ 1
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(
        a.mul(b).mul(a.recip().mul(b.recip())),
        a.mul(a.recip()),
        F::one(),
    );

    // a*b ≢ 0
    lemma_nonzero_product::<F>(a, b);

    // Also: (a*b)*recip(a*b) ≡ 1
    F::axiom_mul_recip_right(a.mul(b));

    // (a*b)*(recip(a)*recip(b)) ≡ 1 ≡ (a*b)*recip(a*b)
    F::axiom_eqv_symmetric(a.mul(b).mul(a.mul(b).recip()), F::one());
    F::axiom_eqv_transitive(
        a.mul(b).mul(a.recip().mul(b.recip())),
        F::one(),
        a.mul(b).mul(a.mul(b).recip()),
    );
    // By left cancellation with (a*b): recip(a)*recip(b) ≡ recip(a*b)
    lemma_mul_cancel_left::<F>(a.recip().mul(b.recip()), a.mul(b).recip(), a.mul(b));
    F::axiom_eqv_symmetric(a.recip().mul(b.recip()), a.mul(b).recip());
}

/// recip(-a) ≡ -recip(a) for nonzero a.
pub proof fn lemma_recip_neg<F: Field>(a: F)
    requires
        !a.eqv(F::zero()),
    ensures
        a.neg().recip().eqv(a.recip().neg()),
{
    // Show (-a)*(-recip(a)) ≡ 1
    lemma_neg_mul_neg::<F>(a, a.recip());
    // (-a)*(-recip(a)) ≡ a*recip(a) ≡ 1
    F::axiom_mul_recip_right(a);
    F::axiom_eqv_transitive(a.neg().mul(a.recip().neg()), a.mul(a.recip()), F::one());

    // -a ≢ 0 (if -a ≡ 0, then -(-a) ≡ -0 ≡ 0, i.e. a ≡ 0)
    if a.neg().eqv(F::zero()) {
        F::axiom_neg_congruence(a.neg(), F::zero());
        lemma_neg_involution::<F>(a);
        lemma_neg_zero::<F>();
        F::axiom_eqv_symmetric(a.neg().neg(), a);
        F::axiom_eqv_transitive(a, a.neg().neg(), F::zero().neg());
        F::axiom_eqv_transitive(a, F::zero().neg(), F::zero());
    }

    // Also: (-a)*recip(-a) ≡ 1
    F::axiom_mul_recip_right(a.neg());

    // (-a)*(-recip(a)) ≡ 1 ≡ (-a)*recip(-a)
    F::axiom_eqv_symmetric(a.neg().mul(a.neg().recip()), F::one());
    F::axiom_eqv_transitive(
        a.neg().mul(a.recip().neg()),
        F::one(),
        a.neg().mul(a.neg().recip()),
    );
    // By left cancellation: -recip(a) ≡ recip(-a)
    lemma_mul_cancel_left::<F>(a.recip().neg(), a.neg().recip(), a.neg());
    F::axiom_eqv_symmetric(a.recip().neg(), a.neg().recip());
}

/// (a / b) / c ≡ a / (b * c) for nonzero b, c.
pub proof fn lemma_div_div<F: Field>(a: F, b: F, c: F)
    requires
        !b.eqv(F::zero()),
        !c.eqv(F::zero()),
    ensures
        a.div(b).div(c).eqv(a.div(b.mul(c))),
{
    // (a/b)/c ≡ (a/b)*recip(c)
    F::axiom_div_is_mul_recip(a.div(b), c);
    // a/b ≡ a*recip(b)
    F::axiom_div_is_mul_recip(a, b);
    // (a/b)*recip(c) ≡ (a*recip(b))*recip(c)
    F::axiom_mul_congruence_left(a.div(b), a.mul(b.recip()), c.recip());
    F::axiom_eqv_transitive(
        a.div(b).div(c),
        a.div(b).mul(c.recip()),
        a.mul(b.recip()).mul(c.recip()),
    );
    // (a*recip(b))*recip(c) ≡ a*(recip(b)*recip(c))
    F::axiom_mul_associative(a, b.recip(), c.recip());
    // recip(b)*recip(c) ≡ recip(b*c)
    lemma_recip_mul::<F>(b, c);
    F::axiom_eqv_symmetric(b.mul(c).recip(), b.recip().mul(c.recip()));
    // a*(recip(b)*recip(c)) ≡ a*recip(b*c)
    lemma_mul_congruence_right::<F>(a, b.recip().mul(c.recip()), b.mul(c).recip());
    // a*recip(b*c) ≡ a/(b*c)
    F::axiom_div_is_mul_recip(a, b.mul(c));
    F::axiom_eqv_symmetric(a.div(b.mul(c)), a.mul(b.mul(c).recip()));

    // Chain: (a/b)/c ≡ (a*recip(b))*recip(c) ≡ a*(recip(b)*recip(c)) ≡ a*recip(b*c) ≡ a/(b*c)
    F::axiom_eqv_transitive(
        a.div(b).div(c),
        a.mul(b.recip()).mul(c.recip()),
        a.mul(b.recip().mul(c.recip())),
    );
    F::axiom_eqv_transitive(
        a.div(b).div(c),
        a.mul(b.recip().mul(c.recip())),
        a.mul(b.mul(c).recip()),
    );
    F::axiom_eqv_transitive(
        a.div(b).div(c),
        a.mul(b.mul(c).recip()),
        a.div(b.mul(c)),
    );
}

} // verus!
