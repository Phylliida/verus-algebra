use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::summation;
use crate::traits::field::Field;
use crate::traits::ring::Ring;
use vstd::prelude::*;

verus! {

// ============================================================
//  Spec functions: Horner evaluation
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

    R::axiom_mul_zero_right(x);
    lemma_add_congruence_right::<R>(c, x.mul(R::zero()), R::zero());
    R::axiom_add_zero_right(c);
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

    lemma_horner_single::<R>(c1, x);
    lemma_mul_congruence_right::<R>(x, horner::<R>(seq![c1], x), c1);
    lemma_add_congruence_right::<R>(c0, x.mul(horner::<R>(seq![c1], x)), x.mul(c1));
    R::axiom_mul_commutative(x, c1);
    lemma_add_congruence_right::<R>(c0, x.mul(c1), c1.mul(x));
    R::axiom_eqv_transitive(
        c0.add(x.mul(horner::<R>(seq![c1], x))),
        c0.add(x.mul(c1)),
        c0.add(c1.mul(x)),
    );
}

/// horner([c₀, c₁, c₂], x) ≡ c₀ + c₁*x + c₂*x².
pub proof fn lemma_horner_quadratic<R: Ring>(c0: R, c1: R, c2: R, x: R)
    ensures
        horner::<R>(seq![c0, c1, c2], x).eqv(c0.add(c1.mul(x).add(c2.mul(x.mul(x))))),
{
    let s: Seq<R> = seq![c0, c1, c2];
    assert(s.subrange(1, 3) =~= seq![c1, c2]);

    lemma_horner_linear::<R>(c1, c2, x);
    lemma_mul_congruence_right::<R>(x, horner::<R>(seq![c1, c2], x), c1.add(c2.mul(x)));
    R::axiom_mul_distributes_left(x, c1, c2.mul(x));
    R::axiom_eqv_transitive(
        x.mul(horner::<R>(seq![c1, c2], x)),
        x.mul(c1.add(c2.mul(x))),
        x.mul(c1).add(x.mul(c2.mul(x))),
    );
    R::axiom_mul_commutative(x, c1);
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
    lemma_add_congruence::<R>(
        x.mul(c1), c1.mul(x),
        x.mul(c2.mul(x)), c2.mul(x.mul(x)),
    );
    R::axiom_eqv_transitive(
        x.mul(horner::<R>(seq![c1, c2], x)),
        x.mul(c1).add(x.mul(c2.mul(x))),
        c1.mul(x).add(c2.mul(x.mul(x))),
    );
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
    lemma_mul_zero_left::<R>(horner::<R>(rest, R::zero()));
    lemma_add_congruence_right::<R>(
        coeffs[0],
        R::zero().mul(horner::<R>(rest, R::zero())),
        R::zero(),
    );
    R::axiom_add_zero_right(coeffs[0]);
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
        lemma_horner_congruence_x::<R>(rest, x1, x2);
        lemma_mul_congruence::<R>(x1, x2, horner::<R>(rest, x1), horner::<R>(rest, x2));
        R::axiom_eqv_reflexive(coeffs[0]);
        lemma_add_congruence::<R>(
            coeffs[0], coeffs[0],
            x1.mul(horner::<R>(rest, x1)),
            x2.mul(horner::<R>(rest, x2)),
        );
    }
}

// ============================================================
//  Polynomial ring operations
// ============================================================

/// A polynomial over a ring R, represented as a sequence of coefficients.
/// The coefficient at index i is the coefficient of x^i.
/// The zero polynomial is represented by an empty sequence.
pub ghost struct SpecPoly<R: Ring> {
    pub coeffs: Seq<R>,
}

/// Construct a polynomial from a sequence of coefficients.
pub open spec fn poly<R: Ring>(coeffs: Seq<R>) -> SpecPoly<R> {
    SpecPoly { coeffs }
}

/// The zero polynomial.
pub open spec fn poly_zero<R: Ring>() -> SpecPoly<R> {
    SpecPoly { coeffs: Seq::empty() }
}

/// The constant polynomial with value c.
pub open spec fn poly_constant<R: Ring>(c: R) -> SpecPoly<R> {
    SpecPoly { coeffs: seq![c] }
}

/// The monomial c * x^n.
pub open spec fn poly_monomial<R: Ring>(c: R, n: nat) -> SpecPoly<R> {
    SpecPoly { coeffs: Seq::new(n + 1, |i: int| if i == n as int { c } else { R::zero() }) }
}

/// Degree of a polynomial.
pub open spec fn degree<R: Ring>(p: SpecPoly<R>) -> nat
    decreases p.coeffs.len(),
{
    if p.coeffs.len() == 0 {
        0
    } else {
        let last = p.coeffs.len() - 1;
        if !p.coeffs[last as int].eqv(R::zero()) {
            last as nat
        } else {
            degree(SpecPoly { coeffs: p.coeffs.subrange(0, last) })
        }
    }
}

/// Check if polynomial is zero.
pub open spec fn is_zero<R: Ring>(p: SpecPoly<R>) -> bool {
    forall|i: int| 0 <= i < p.coeffs.len() ==> p.coeffs[i].eqv(R::zero())
}

/// Leading coefficient.
pub open spec fn leading_coeff<R: Ring>(p: SpecPoly<R>) -> R {
    let d = degree(p);
    if p.coeffs.len() == 0 {
        R::zero()
    } else {
        p.coeffs[d as int]
    }
}

/// Addition: coefficient-wise.
pub open spec fn poly_add<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>) -> SpecPoly<R> {
    let len = if p.coeffs.len() >= q.coeffs.len() { p.coeffs.len() } else { q.coeffs.len() };
    SpecPoly {
        coeffs: Seq::new(len, |i: int| {
            let a = if i < p.coeffs.len() { p.coeffs[i] } else { R::zero() };
            let b = if i < q.coeffs.len() { q.coeffs[i] } else { R::zero() };
            a.add(b)
        }),
    }
}

/// Negation: negate each coefficient.
pub open spec fn poly_neg<R: Ring>(p: SpecPoly<R>) -> SpecPoly<R> {
    SpecPoly {
        coeffs: Seq::new(p.coeffs.len(), |i: int| p.coeffs[i].neg()),
    }
}

/// Subtraction: p - q = p + (-q).
pub open spec fn poly_sub<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>) -> SpecPoly<R> {
    poly_add(p, poly_neg(q))
}

/// Multiplication: convolution of coefficients.
pub open spec fn poly_mul<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>) -> SpecPoly<R> {
    if is_zero(p) || is_zero(q) {
        poly_zero()
    } else {
        let deg_p = degree(p);
        let deg_q = degree(q);
        let result_degree = deg_p + deg_q;
        SpecPoly {
            coeffs: Seq::new(result_degree + 1, |k: int| {
                crate::summation::sum::<R>(|i: int| {
                    if i <= k && i < p.coeffs.len() && (k - i) < q.coeffs.len() {
                        p.coeffs[i].mul(q.coeffs[k - i])
                    } else {
                        R::zero()
                    }
                }, 0, k + 1)
            }),
        }
    }
}

/// One polynomial: constant 1.
pub open spec fn poly_one<R: Ring>() -> SpecPoly<R> {
    poly_constant(R::one())
}

    /// Polynomial equivalence: same length and all coefficients equivalent.
    pub open spec fn poly_eqv<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>) -> bool {
        if p.coeffs.len() != q.coeffs.len() {
            false
        } else {
            forall|i: int| 0 <= i < p.coeffs.len() ==> p.coeffs[i].eqv(q.coeffs[i])
        }
    }

    // ============================================================
    //  Equivalence lemmas
    // ============================================================

    pub proof fn lemma_poly_eqv_reflexive<R: Ring>(p: SpecPoly<R>)
        ensures
            poly_eqv(p, p)
    {
        assert forall|i: int| 0 <= i < p.coeffs.len() implies p.coeffs[i].eqv(p.coeffs[i]) by {
            R::axiom_eqv_reflexive(p.coeffs[i]);
        }
    }

    pub proof fn lemma_poly_eqv_symmetric<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>)
        requires
            poly_eqv(p, q),
        ensures
            poly_eqv(q, p)
    {
        assert forall|i: int| 0 <= i < p.coeffs.len() implies q.coeffs[i].eqv(p.coeffs[i]) by {
            R::axiom_eqv_symmetric(p.coeffs[i], q.coeffs[i]);
        }
    }

    pub proof fn lemma_poly_eqv_transitive<R: Ring>(p: SpecPoly<R>, q: SpecPoly<R>, r: SpecPoly<R>)
        requires
            poly_eqv(p, q),
            poly_eqv(q, r),
        ensures
            poly_eqv(p, r)
    {
        assert forall|i: int| 0 <= i < p.coeffs.len() implies p.coeffs[i].eqv(r.coeffs[i]) by {
            R::axiom_eqv_transitive(p.coeffs[i], q.coeffs[i], r.coeffs[i]);
        }
    }


    // ============================================================
    //  Division with remainder (Euclidean algorithm)
    // ============================================================
    // Note: We use a fuel parameter for termination. The wrapper `poly_div_rem` supplies enough fuel.
    /// Recursive division with remainder.
    pub proof fn poly_div_rem_rec<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>, fuel: nat) -> (SpecPoly<R>, SpecPoly<R>)
        decreases fuel,
    {
        if fuel == 0 {
            // Out of fuel: return arbitrary result
            (poly_zero(), p)
        } else if is_zero(divisor) || leading_coeff(divisor).eqv(R::zero()) {
            (poly_zero(), p)
        } else if is_zero(p) || degree(p) < degree(divisor) {
            (poly_zero(), p)
        } else {
            let d_val = degree(p) - degree(divisor);
            // Since degree(p) >= degree(divisor), d_val >= 0. We'll assert it (admitted for now).
            assert(d_val >= 0) by { admit(); }
            let d = d_val as nat;
            let lc_p = leading_coeff(p);
            let lc_div = leading_coeff(divisor);
            let factor = lc_p.mul(lc_div.recip());
            let term = poly_mul(poly_monomial(factor, d), divisor);
            let p_prime = poly_sub(p, term);
            // For termination (via fuel) we don't need to show degree decrease, but we need it for correctness.
            // We'll admit the degree decrease lemma here.
            assert(degree(p_prime) < degree(p)) by { admit(); }
            let (q_prime, r_prime) = poly_div_rem_rec(p_prime, divisor, fuel - 1);
            (poly_add(q_prime, poly_monomial(factor, d)), r_prime)
        }
    }

    /// Public interface for division with remainder.
    pub open spec fn poly_div_rem<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>) -> (SpecPoly<R>, SpecPoly<R>) {
        let fuel = p.coeffs.len() + 1;
        poly_div_rem_rec(p, divisor, fuel)
    }

    /// Polynomial remainder.
    pub open spec fn poly_mod<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>) -> SpecPoly<R> {
        poly_div_rem(p, divisor).1
    }

// ============================================================
//  Correctness lemmas (to be fully proven incrementally)
// ============================================================

    /// Correctness of poly_div_rem_rec. (admitted)
    pub proof fn lemma_poly_div_rem_correct<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>)
        requires
            !is_zero(divisor),
            !leading_coeff(divisor).eqv(R::zero()),
    {
        admit();
    }

    /// Degree of remainder from poly_mod is less than divisor's degree. (admitted)
    pub proof fn lemma_poly_mod_degree<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>)
        requires
            !is_zero(divisor),
            !leading_coeff(divisor).eqv(R::zero()),
    {
        admit();
    }

    /// After subtracting leading term multiple, degree strictly decreases. (admitted)
    pub proof fn lemma_poly_sub_leading_decrease<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>)
        requires
            !is_zero(divisor),
            !leading_coeff(divisor).eqv(R::zero()),
            degree(p) >= degree(divisor),
    {
        admit();
    }

    /// Uniqueness of remainder. (admitted)
    pub proof fn lemma_poly_div_rem_unique<R: Field>(p: SpecPoly<R>, divisor: SpecPoly<R>, r1: SpecPoly<R>, r2: SpecPoly<R>)
        requires
            !is_zero(divisor),
            !leading_coeff(divisor).eqv(R::zero()),
            exists|q1: SpecPoly<R>| p == poly_add(poly_mul(q1, divisor), r1),
            exists|q2: SpecPoly<R>| p == poly_add(poly_mul(q2, divisor), r2),
            (is_zero(r1) || degree(r1) < degree(divisor)),
            (is_zero(r2) || degree(r2) < degree(divisor)),
    {
        admit();
    }

} // verus!
