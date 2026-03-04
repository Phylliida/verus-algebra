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
//  Sqrt trait
// ============================================================

/// An ordered field equipped with a square root operation for non-negative elements.
///
/// Not all ordered fields have square roots (e.g. the rationals), so this is a
/// separate trait that types opt into. The two axioms state that sqrt(a) is the
/// unique non-negative element whose square equals a.
pub trait Sqrt: OrderedField {

    /// Square root of a non-negative element.
    spec fn sqrt(self) -> Self;

    /// Defining property: sqrt(a)² ≡ a for a ≥ 0.
    proof fn axiom_sqrt_square(a: Self)
        requires
            Self::zero().le(a),
        ensures
            a.sqrt().mul(a.sqrt()).eqv(a);

    /// Non-negativity: sqrt(a) ≥ 0 for a ≥ 0.
    proof fn axiom_sqrt_nonneg(a: Self)
        requires
            Self::zero().le(a),
        ensures
            Self::zero().le(a.sqrt());
}

// ============================================================
//  Uniqueness of non-negative square root
// ============================================================

/// Uniqueness: if x ≥ 0 and x*x ≡ a with a ≥ 0, then x ≡ sqrt(a).
///
/// Proof sketch: x² ≡ a ≡ sqrt(a)², so x² - sqrt(a)² ≡ 0.
/// By difference of squares, (x - sqrt(a))*(x + sqrt(a)) ≡ 0.
/// Since x ≥ 0 and sqrt(a) ≥ 0, either x + sqrt(a) > 0 (use field
/// cancellation) or x + sqrt(a) ≡ 0 (both must be zero).
pub proof fn lemma_sqrt_unique<F: Sqrt>(x: F, a: F)
    requires
        F::zero().le(x),
        x.mul(x).eqv(a),
        F::zero().le(a),
    ensures
        x.eqv(a.sqrt()),
{
    let s = a.sqrt();

    // Establish: 0 ≤ s, s*s ≡ a
    F::axiom_sqrt_nonneg(a);
    F::axiom_sqrt_square(a);

    // Step 1: x*x ≡ s*s
    // x*x ≡ a [given], a ≡ s*s [symmetric of axiom]
    F::axiom_eqv_symmetric(s.mul(s), a);
    F::axiom_eqv_transitive(x.mul(x), a, s.mul(s));

    // Step 2: (x-s)*(x+s) ≡ x*x - s*s [square_sub]
    lemma_square_sub::<F>(x, s);

    // Step 3: x*x - s*s ≡ 0
    // sub_congruence(x*x, s*s, s*s, s*s) needs: x*x ≡ s*s ✓, s*s ≡ s*s
    F::axiom_eqv_reflexive(s.mul(s));
    lemma_sub_congruence::<F>(x.mul(x), s.mul(s), s.mul(s), s.mul(s));
    // gives: x*x - s*s ≡ s*s - s*s
    lemma_sub_self::<F>(s.mul(s));
    // chain: x*x - s*s ≡ s*s - s*s ≡ 0
    F::axiom_eqv_transitive(
        x.mul(x).sub(s.mul(s)),
        s.mul(s).sub(s.mul(s)),
        F::zero(),
    );

    // Step 4: (x-s)*(x+s) ≡ 0
    F::axiom_eqv_transitive(
        x.sub(s).mul(x.add(s)),
        x.mul(x).sub(s.mul(s)),
        F::zero(),
    );

    // Step 5: 0 ≤ x + s
    inequalities::lemma_nonneg_add::<F>(x, s);

    // Either x+s ≡ 0 or x+s ≢ 0
    F::axiom_le_total(F::zero(), x.add(s));

    if !x.add(s).eqv(F::zero()) {
        // Case A: x+s ≢ 0
        // We need (x-s)*(x+s) ≡ 0*(x+s) for mul_cancel_right
        F::axiom_eqv_symmetric(x.add(s), F::zero());
        lemma_mul_zero_left::<F>(x.add(s));
        F::axiom_eqv_symmetric(F::zero().mul(x.add(s)), F::zero());
        F::axiom_eqv_transitive(
            x.sub(s).mul(x.add(s)),
            F::zero(),
            F::zero().mul(x.add(s)),
        );
        // mul_cancel_right: (x-s)*(x+s) ≡ 0*(x+s) and x+s ≢ 0 → x-s ≡ 0
        lemma_mul_cancel_right::<F>(x.sub(s), F::zero(), x.add(s));
        // x-s ≡ 0 → x ≡ s
        lemma_sub_eqv_zero_implies_eqv::<F>(x, s);
    } else {
        // Case B: x+s ≡ 0, so both x and s must be 0 (sum of nonneg is 0)

        // Show x ≤ 0: from 0 ≤ s, add_monotone gives 0+x ≤ s+x
        F::axiom_le_add_monotone(F::zero(), s, x);
        // 0+x ≡ x
        lemma_add_zero_left::<F>(x);
        // s+x ≡ x+s
        F::axiom_add_commutative(s, x);
        // le_congruence: 0+x ≤ s+x → x ≤ x+s
        F::axiom_le_congruence(
            F::zero().add(x), x,
            s.add(x), x.add(s),
        );
        // x ≤ x+s and x+s ≡ 0 → x ≤ 0
        F::axiom_eqv_reflexive(x);
        F::axiom_le_congruence(x, x, x.add(s), F::zero());
        // 0 ≤ x and x ≤ 0 → x ≡ 0
        F::axiom_le_antisymmetric(x, F::zero());

        // Show s ≤ 0: from 0 ≤ x, add_monotone gives 0+s ≤ x+s
        F::axiom_le_add_monotone(F::zero(), x, s);
        // 0+s ≡ s
        lemma_add_zero_left::<F>(s);
        // le_congruence: 0+s ≤ x+s → s ≤ x+s
        F::axiom_eqv_reflexive(x.add(s));
        F::axiom_le_congruence(
            F::zero().add(s), s,
            x.add(s), x.add(s),
        );
        // s ≤ x+s and x+s ≡ 0 → s ≤ 0
        F::axiom_eqv_reflexive(s);
        F::axiom_le_congruence(s, s, x.add(s), F::zero());
        // 0 ≤ s and s ≤ 0 → s ≡ 0
        F::axiom_le_antisymmetric(s, F::zero());

        // x ≡ 0 and s ≡ 0 → x ≡ s
        F::axiom_eqv_symmetric(s, F::zero());
        F::axiom_eqv_transitive(x, F::zero(), s);
    }
}

// ============================================================
//  Derived lemmas
// ============================================================

/// sqrt(0) ≡ 0.
pub proof fn lemma_sqrt_zero<F: Sqrt>()
    ensures
        F::zero().sqrt().eqv(F::zero()),
{
    F::axiom_le_reflexive(F::zero());
    // 0 * 0 ≡ 0
    lemma_mul_zero_left::<F>(F::zero());
    // 0 is a nonneg square root of 0
    lemma_sqrt_unique::<F>(F::zero(), F::zero());
    F::axiom_eqv_symmetric(F::zero(), F::zero().sqrt());
}

/// sqrt(1) ≡ 1.
pub proof fn lemma_sqrt_one<F: Sqrt>()
    ensures
        F::one().sqrt().eqv(F::one()),
{
    lemma_zero_lt_one::<F>();
    F::axiom_lt_iff_le_and_not_eqv(F::zero(), F::one());
    // 1 * 1 ≡ 1
    F::axiom_mul_one_right(F::one());
    lemma_sqrt_unique::<F>(F::one(), F::one());
    F::axiom_eqv_symmetric(F::one(), F::one().sqrt());
}

/// For a ≥ 0: sqrt(a*a) ≡ a.
pub proof fn lemma_sqrt_of_square<F: Sqrt>(a: F)
    requires
        F::zero().le(a),
    ensures
        a.mul(a).sqrt().eqv(a),
{
    lemma_square_nonneg::<F>(a);
    F::axiom_eqv_reflexive(a.mul(a));
    lemma_sqrt_unique::<F>(a, a.mul(a));
    F::axiom_eqv_symmetric(a, a.mul(a).sqrt());
}

/// Monotonicity: 0 ≤ a ≤ b implies sqrt(a) ≤ sqrt(b).
pub proof fn lemma_sqrt_monotone<F: Sqrt>(a: F, b: F)
    requires
        F::zero().le(a),
        a.le(b),
    ensures
        a.sqrt().le(b.sqrt()),
{
    F::axiom_le_transitive(F::zero(), a, b);
    F::axiom_sqrt_nonneg(a);
    F::axiom_sqrt_nonneg(b);
    F::axiom_sqrt_square(a);
    F::axiom_sqrt_square(b);

    // By totality: either sqrt(a) ≤ sqrt(b) or sqrt(b) ≤ sqrt(a).
    F::axiom_le_total(a.sqrt(), b.sqrt());

    if a.sqrt().le(b.sqrt()) {
        // Done
    } else {
        // sqrt(b) ≤ sqrt(a) → sqrt(b)² ≤ sqrt(a)² [square_le_square]
        lemma_square_le_square::<F>(b.sqrt(), a.sqrt());
        // sqrt(b)² ≡ b and sqrt(a)² ≡ a, so b ≤ a
        F::axiom_le_congruence(
            b.sqrt().mul(b.sqrt()), b,
            a.sqrt().mul(a.sqrt()), a,
        );
        // a ≤ b and b ≤ a → a ≡ b
        F::axiom_le_antisymmetric(a, b);
        // a ≡ b → sqrt(a)² ≡ b → sqrt(a) is nonneg sq root of b → sqrt(a) ≡ sqrt(b)
        F::axiom_eqv_transitive(a.sqrt().mul(a.sqrt()), a, b);
        lemma_sqrt_unique::<F>(a.sqrt(), b);
        // sqrt(a) ≡ sqrt(b) → sqrt(a) ≤ sqrt(b)
        F::axiom_eqv_symmetric(a.sqrt(), b.sqrt());
        F::axiom_eqv_reflexive(a.sqrt());
        F::axiom_le_reflexive(a.sqrt());
        F::axiom_le_congruence(a.sqrt(), a.sqrt(), a.sqrt(), b.sqrt());
    }
}

/// sqrt(a) * sqrt(b) ≡ sqrt(a*b) for a, b ≥ 0.
pub proof fn lemma_sqrt_mul<F: Sqrt>(a: F, b: F)
    requires
        F::zero().le(a),
        F::zero().le(b),
    ensures
        a.sqrt().mul(b.sqrt()).eqv(a.mul(b).sqrt()),
{
    F::axiom_sqrt_nonneg(a);
    F::axiom_sqrt_nonneg(b);
    let p = a.sqrt();
    let q = b.sqrt();

    // sqrt(a)*sqrt(b) ≥ 0
    lemma_nonneg_mul_nonneg::<F>(p, q);

    // Need: (p*q)*(p*q) ≡ a*b
    // (p*q)*(p*q) → p*(q*(p*q)) [assoc]
    F::axiom_mul_associative(p, q, p.mul(q));
    // q*(p*q) → (q*p)*q [assoc reversed]
    F::axiom_mul_associative(q, p, q);
    F::axiom_eqv_symmetric(q.mul(p).mul(q), q.mul(p.mul(q)));
    // q*p ≡ p*q [comm]
    F::axiom_mul_commutative(q, p);
    // (q*p)*q ≡ (p*q)*q
    F::axiom_mul_congruence_left(q.mul(p), p.mul(q), q);
    F::axiom_eqv_transitive(q.mul(p.mul(q)), q.mul(p).mul(q), p.mul(q).mul(q));
    // (p*q)*q → p*(q*q) [assoc]
    F::axiom_mul_associative(p, q, q);
    // q*(p*q) ≡ (p*q)*q ≡ p*(q*q)
    F::axiom_eqv_transitive(q.mul(p.mul(q)), p.mul(q).mul(q), p.mul(q.mul(q)));
    // p*(q*(p*q)) ≡ p*(p*(q*q))
    lemma_mul_congruence_right::<F>(p, q.mul(p.mul(q)), p.mul(q.mul(q)));
    // p*(p*(q*q)) → (p*p)*(q*q) [assoc reversed]
    F::axiom_mul_associative(p, p, q.mul(q));
    F::axiom_eqv_symmetric(p.mul(p).mul(q.mul(q)), p.mul(p.mul(q.mul(q))));
    F::axiom_eqv_transitive(
        p.mul(q.mul(p.mul(q))),
        p.mul(p.mul(q.mul(q))),
        p.mul(p).mul(q.mul(q)),
    );
    // (p*q)*(p*q) ≡ p*(q*(p*q)) ≡ (p*p)*(q*q)
    F::axiom_eqv_transitive(
        p.mul(q).mul(p.mul(q)),
        p.mul(q.mul(p.mul(q))),
        p.mul(p).mul(q.mul(q)),
    );
    // p*p ≡ a and q*q ≡ b
    F::axiom_sqrt_square(a);
    F::axiom_sqrt_square(b);
    lemma_mul_congruence::<F>(p.mul(p), a, q.mul(q), b);
    // (p*q)*(p*q) ≡ (p*p)*(q*q) ≡ a*b
    F::axiom_eqv_transitive(
        p.mul(q).mul(p.mul(q)),
        p.mul(p).mul(q.mul(q)),
        a.mul(b),
    );

    // a*b ≥ 0
    lemma_nonneg_mul_nonneg::<F>(a, b);

    // p*q is a nonneg square root of a*b, so p*q ≡ sqrt(a*b)
    lemma_sqrt_unique::<F>(p.mul(q), a.mul(b));
}

/// For any a: sqrt(a*a) ≡ abs(a).
/// (Unlike sqrt_of_square, this works for negative a too.)
pub proof fn lemma_sqrt_abs<F: Sqrt>(a: F)
    ensures
        a.mul(a).sqrt().eqv(inequalities::abs::<F>(a)),
{
    lemma_square_nonneg::<F>(a);
    // abs(a) ≥ 0 and abs(a)*abs(a) ≡ a*a
    inequalities::lemma_abs_nonneg::<F>(a);
    inequalities::lemma_abs_mul_self::<F>(a);
    F::axiom_eqv_symmetric(inequalities::abs::<F>(a).mul(inequalities::abs::<F>(a)), a.mul(a));

    // abs(a) is a nonneg square root of a*a
    lemma_sqrt_unique::<F>(inequalities::abs::<F>(a), a.mul(a));
    F::axiom_eqv_symmetric(inequalities::abs::<F>(a), a.mul(a).sqrt());
}

} // verus!
