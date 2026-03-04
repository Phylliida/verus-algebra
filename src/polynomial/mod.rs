use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::field::Field;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::field_lemmas::*;

verus! {

// ============================================================
//  Spec functions
// ============================================================

/// Horner evaluation of a polynomial represented by its coefficient sequence.
/// coeffs[0] + x * (coeffs[1] + x * (... + x * coeffs[n]))
/// Computes c₀ + c₁x + c₂x² + ... + cₙxⁿ in n muls and n adds.
pub open spec fn horner<R: Ring>(coeffs: Seq<R>, x: R) -> R
    decreases coeffs.len(),
{
    if coeffs.len() == 0 {
        R::zero()
    } else {
        coeffs[0].add(x.mul(horner::<R>(coeffs.subrange(1, coeffs.len() as int), x)))
    }
}

/// Direct (naive) polynomial evaluation: sum of coeffs[i] * x^i.
pub open spec fn eval_direct<R: Ring>(coeffs: Seq<R>, x: R, i: nat) -> R
    decreases coeffs.len() - i,
{
    if i >= coeffs.len() {
        R::zero()
    } else {
        coeffs[i as int].mul(pow_spec::<R>(x, i)).add(
            eval_direct::<R>(coeffs, x, i + 1)
        )
    }
}

/// Power: x^n (used locally to avoid circular dependency with power module).
pub open spec fn pow_spec<R: Ring>(base: R, exp: nat) -> R
    decreases exp,
{
    if exp == 0 { R::one() }
    else { base.mul(pow_spec::<R>(base, (exp - 1) as nat)) }
}

// ============================================================
//  Basic Horner lemmas
// ============================================================

/// horner([], x) ≡ 0.
pub proof fn lemma_horner_empty<R: Ring>(x: R)
    ensures
        horner::<R>(Seq::empty(), x).eqv(R::zero()),
{
    R::axiom_eqv_reflexive(R::zero());
}

/// horner([c], x) ≡ c.
pub proof fn lemma_horner_single<R: Ring>(c: R, x: R)
    ensures
        horner::<R>(seq![c], x).eqv(c),
{
    let s: Seq<R> = seq![c];
    let rest = s.subrange(1, s.len() as int);
    assert(rest =~= Seq::<R>::empty());
    assert(rest.len() == 0);
    assert(horner::<R>(rest, x) == R::zero());

    // horner([c], x) = c + x * horner([], x) = c + x * 0
    // x * 0 ≡ 0
    R::axiom_mul_zero_right(x);
    // c + x*0 ≡ c + 0
    lemma_add_congruence_right::<R>(c, x.mul(R::zero()), R::zero());
    // c + 0 ≡ c
    R::axiom_add_zero_right(c);
    // Chain: c + x*0 ≡ c + 0 ≡ c
    R::axiom_eqv_transitive(
        c.add(x.mul(R::zero())),
        c.add(R::zero()),
        c,
    );
}

/// horner([c₀, c₁], x) ≡ c₀ + c₁ * x.
pub proof fn lemma_horner_linear<R: Ring>(c0: R, c1: R, x: R)
    ensures
        horner::<R>(seq![c0, c1], x).eqv(c0.add(c1.mul(x))),
{
    let s: Seq<R> = seq![c0, c1];
    assert(s.subrange(1, 2) =~= seq![c1]);

    // horner([c0,c1], x) = c0 + x * horner([c1], x)
    // horner([c1], x) ≡ c1
    lemma_horner_single::<R>(c1, x);

    // x * horner([c1], x) ≡ x * c1
    lemma_mul_congruence_right::<R>(x, horner::<R>(seq![c1], x), c1);

    // c0 + x*horner ≡ c0 + x*c1
    lemma_add_congruence_right::<R>(
        c0,
        x.mul(horner::<R>(seq![c1], x)),
        x.mul(c1),
    );

    // x*c1 ≡ c1*x
    R::axiom_mul_commutative(x, c1);

    // c0 + x*c1 ≡ c0 + c1*x
    lemma_add_congruence_right::<R>(c0, x.mul(c1), c1.mul(x));

    // Chain: horner ≡ c0 + x*c1 ≡ c0 + c1*x
    R::axiom_eqv_transitive(
        c0.add(x.mul(horner::<R>(seq![c1], x))),
        c0.add(x.mul(c1)),
        c0.add(c1.mul(x)),
    );
}

/// horner([c₀, c₁, c₂], x) ≡ c₀ + c₁*x + c₂*x².
pub proof fn lemma_horner_quadratic<R: Ring>(c0: R, c1: R, c2: R, x: R)
    ensures
        horner::<R>(seq![c0, c1, c2], x).eqv(
            c0.add(c1.mul(x).add(c2.mul(x.mul(x))))),
{
    let s: Seq<R> = seq![c0, c1, c2];
    assert(s.subrange(1, 3) =~= seq![c1, c2]);

    // horner([c0,c1,c2], x) = c0 + x * horner([c1,c2], x)
    // horner([c1,c2], x) ≡ c1 + c2*x
    lemma_horner_linear::<R>(c1, c2, x);

    // x * horner([c1,c2], x) ≡ x * (c1 + c2*x)
    lemma_mul_congruence_right::<R>(
        x, horner::<R>(seq![c1, c2], x), c1.add(c2.mul(x)),
    );

    // x * (c1 + c2*x) ≡ x*c1 + x*(c2*x)  [left dist]
    R::axiom_mul_distributes_left(x, c1, c2.mul(x));

    // Chain: x*horner ≡ x*(c1+c2*x) ≡ x*c1 + x*(c2*x)
    R::axiom_eqv_transitive(
        x.mul(horner::<R>(seq![c1, c2], x)),
        x.mul(c1.add(c2.mul(x))),
        x.mul(c1).add(x.mul(c2.mul(x))),
    );

    // x*c1 ≡ c1*x
    R::axiom_mul_commutative(x, c1);

    // x*(c2*x) ≡ (x*c2)*x ≡ (c2*x)*x ≡ c2*(x*x)
    R::axiom_mul_associative(x, c2, x);
    R::axiom_eqv_symmetric(x.mul(c2).mul(x), x.mul(c2.mul(x)));
    R::axiom_mul_commutative(x, c2);
    R::axiom_mul_congruence_left(x.mul(c2), c2.mul(x), x);
    R::axiom_eqv_transitive(
        x.mul(c2.mul(x)),
        x.mul(c2).mul(x),
        c2.mul(x).mul(x),
    );
    R::axiom_mul_associative(c2, x, x);
    R::axiom_eqv_transitive(
        x.mul(c2.mul(x)),
        c2.mul(x).mul(x),
        c2.mul(x.mul(x)),
    );

    // x*c1 + x*(c2*x) ≡ c1*x + c2*(x*x)
    lemma_add_congruence::<R>(
        x.mul(c1), c1.mul(x),
        x.mul(c2.mul(x)), c2.mul(x.mul(x)),
    );

    // Chain: x*horner ≡ x*c1 + x*(c2*x) ≡ c1*x + c2*x²
    R::axiom_eqv_transitive(
        x.mul(horner::<R>(seq![c1, c2], x)),
        x.mul(c1).add(x.mul(c2.mul(x))),
        c1.mul(x).add(c2.mul(x.mul(x))),
    );

    // Outer: c0 + x*horner ≡ c0 + (c1*x + c2*x²)
    lemma_add_congruence_right::<R>(
        c0,
        x.mul(horner::<R>(seq![c1, c2], x)),
        c1.mul(x).add(c2.mul(x.mul(x))),
    );
}

/// Evaluating at zero: horner(coeffs, 0) ≡ coeffs[0] when non-empty.
pub proof fn lemma_horner_at_zero<R: Ring>(coeffs: Seq<R>)
    requires
        coeffs.len() > 0,
    ensures
        horner::<R>(coeffs, R::zero()).eqv(coeffs[0]),
{
    let rest = coeffs.subrange(1, coeffs.len() as int);
    // horner(coeffs, 0) = coeffs[0] + 0 * horner(rest, 0)
    // 0 * anything ≡ 0
    lemma_mul_zero_left::<R>(horner::<R>(rest, R::zero()));
    // coeffs[0] + 0*horner ≡ coeffs[0] + 0
    lemma_add_congruence_right::<R>(
        coeffs[0],
        R::zero().mul(horner::<R>(rest, R::zero())),
        R::zero(),
    );
    // coeffs[0] + 0 ≡ coeffs[0]
    R::axiom_add_zero_right(coeffs[0]);
    // Chain
    R::axiom_eqv_transitive(
        coeffs[0].add(R::zero().mul(horner::<R>(rest, R::zero()))),
        coeffs[0].add(R::zero()),
        coeffs[0],
    );
}

/// Horner respects equivalence of x:
/// if x1 ≡ x2, then horner(coeffs, x1) ≡ horner(coeffs, x2).
pub proof fn lemma_horner_congruence_x<R: Ring>(coeffs: Seq<R>, x1: R, x2: R)
    requires
        x1.eqv(x2),
    ensures
        horner::<R>(coeffs, x1).eqv(horner::<R>(coeffs, x2)),
    decreases coeffs.len(),
{
    if coeffs.len() == 0 {
        R::axiom_eqv_reflexive(R::zero());
    } else {
        let rest = coeffs.subrange(1, coeffs.len() as int);
        // IH: horner(rest, x1) ≡ horner(rest, x2)
        lemma_horner_congruence_x::<R>(rest, x1, x2);
        // x1 ≡ x2 and horner(rest,x1) ≡ horner(rest,x2)
        // → x1*horner(rest,x1) ≡ x2*horner(rest,x2)
        lemma_mul_congruence::<R>(x1, x2, horner::<R>(rest, x1), horner::<R>(rest, x2));
        // coeffs[0] + x1*horner ≡ coeffs[0] + x2*horner
        R::axiom_eqv_reflexive(coeffs[0]);
        lemma_add_congruence::<R>(
            coeffs[0], coeffs[0],
            x1.mul(horner::<R>(rest, x1)),
            x2.mul(horner::<R>(rest, x2)),
        );
    }
}

/// Scaling: horner(k*coeffs, x) ≡ k * horner(coeffs, x),
/// where k*coeffs means each coefficient is multiplied by k.
///
/// Stated pointwise: if each d[i] ≡ k*c[i], then horner(d, x) ≡ k*horner(c, x).
pub proof fn lemma_horner_scale<R: Ring>(
    coeffs: Seq<R>, scaled: Seq<R>, k: R, x: R,
)
    requires
        coeffs.len() == scaled.len(),
        forall|i: int| 0 <= i < coeffs.len() ==> scaled[i].eqv(k.mul(#[trigger] coeffs[i])),
    ensures
        horner::<R>(scaled, x).eqv(k.mul(horner::<R>(coeffs, x))),
    decreases coeffs.len(),
{
    if coeffs.len() == 0 {
        // k * 0 ≡ 0
        R::axiom_mul_zero_right(k);
        R::axiom_eqv_symmetric(k.mul(R::zero()), R::zero());
    } else {
        let rest_c = coeffs.subrange(1, coeffs.len() as int);
        let rest_s = scaled.subrange(1, scaled.len() as int);

        // IH: horner(rest_s, x) ≡ k * horner(rest_c, x)
        assert forall|i: int| 0 <= i < rest_c.len()
            implies rest_s[i].eqv(k.mul(#[trigger] rest_c[i]))
        by {
            assert(rest_s[i] == scaled[i + 1]);
            assert(rest_c[i] == coeffs[i + 1]);
        }
        lemma_horner_scale::<R>(rest_c, rest_s, k, x);

        // x * horner(rest_s, x) ≡ x * (k * horner(rest_c, x))
        lemma_mul_congruence_right::<R>(
            x, horner::<R>(rest_s, x), k.mul(horner::<R>(rest_c, x)),
        );

        // x * (k * h) ≡ (x*k) * h ≡ (k*x) * h ≡ k * (x*h)  [assoc + comm]
        R::axiom_mul_associative(x, k, horner::<R>(rest_c, x));
        R::axiom_eqv_symmetric(
            x.mul(k).mul(horner::<R>(rest_c, x)),
            x.mul(k.mul(horner::<R>(rest_c, x))),
        );
        R::axiom_mul_commutative(x, k);
        R::axiom_mul_congruence_left(x.mul(k), k.mul(x), horner::<R>(rest_c, x));
        R::axiom_eqv_transitive(
            x.mul(k.mul(horner::<R>(rest_c, x))),
            x.mul(k).mul(horner::<R>(rest_c, x)),
            k.mul(x).mul(horner::<R>(rest_c, x)),
        );
        R::axiom_mul_associative(k, x, horner::<R>(rest_c, x));
        R::axiom_eqv_transitive(
            x.mul(k.mul(horner::<R>(rest_c, x))),
            k.mul(x).mul(horner::<R>(rest_c, x)),
            k.mul(x.mul(horner::<R>(rest_c, x))),
        );

        // Chain: x*horner(rest_s,x) ≡ k*(x*horner(rest_c,x))
        R::axiom_eqv_transitive(
            x.mul(horner::<R>(rest_s, x)),
            x.mul(k.mul(horner::<R>(rest_c, x))),
            k.mul(x.mul(horner::<R>(rest_c, x))),
        );

        // scaled[0] ≡ k * coeffs[0]  [hypothesis]
        // scaled[0] + x*horner_s ≡ k*coeffs[0] + k*(x*horner_c) ≡ k*(coeffs[0] + x*horner_c)
        lemma_add_congruence::<R>(
            scaled[0], k.mul(coeffs[0]),
            x.mul(horner::<R>(rest_s, x)),
            k.mul(x.mul(horner::<R>(rest_c, x))),
        );

        // k*coeffs[0] + k*(x*horner_c) ≡ k*(coeffs[0] + x*horner_c)  [distributes reversed]
        R::axiom_mul_distributes_left(k, coeffs[0], x.mul(horner::<R>(rest_c, x)));
        R::axiom_eqv_symmetric(
            k.mul(coeffs[0].add(x.mul(horner::<R>(rest_c, x)))),
            k.mul(coeffs[0]).add(k.mul(x.mul(horner::<R>(rest_c, x)))),
        );

        // Chain
        R::axiom_eqv_transitive(
            scaled[0].add(x.mul(horner::<R>(rest_s, x))),
            k.mul(coeffs[0]).add(k.mul(x.mul(horner::<R>(rest_c, x)))),
            k.mul(coeffs[0].add(x.mul(horner::<R>(rest_c, x)))),
        );
    }
}

} // verus!
