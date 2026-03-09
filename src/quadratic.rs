use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::{Field, OrderedField};
use crate::sqrt::Sqrt;
use crate::embedding::from_int;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::field_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;

verus! {

// ============================================================
//  Specs
// ============================================================

/// Discriminant of ax² + bx + c: disc(a,b,c) = b² - 4ac.
pub open spec fn discriminant<T: Ring>(a: T, b: T, c: T) -> T {
    b.mul(b).sub(from_int::<T>(4).mul(a.mul(c)))
}

/// The "plus" root: (-b + sqrt(disc)) / (2a).
pub open spec fn quadratic_root_plus<T: Sqrt>(a: T, b: T, c: T) -> T {
    b.neg().add(discriminant(a, b, c).sqrt()).div(from_int::<T>(2).mul(a))
}

/// The "minus" root: (-b - sqrt(disc)) / (2a).
pub open spec fn quadratic_root_minus<T: Sqrt>(a: T, b: T, c: T) -> T {
    b.neg().sub(discriminant(a, b, c).sqrt()).div(from_int::<T>(2).mul(a))
}

/// Evaluate the quadratic polynomial: a*t² + b*t + c.
pub open spec fn quadratic_eval<T: Ring>(a: T, b: T, c: T, t: T) -> T {
    a.mul(t.mul(t)).add(b.mul(t)).add(c)
}

// ============================================================
//  Small helpers
// ============================================================

/// neg(0) ≡ 0.
pub proof fn lemma_neg_zero<T: Ring>()
    ensures T::zero().neg().eqv(T::zero()),
{
    // 0 + 0 ≡ 0 → 0 ≡ -0
    lemma_add_zero_left::<T>(T::zero());
    lemma_neg_unique::<T>(T::zero(), T::zero());
    T::axiom_eqv_symmetric(T::zero(), T::zero().neg());
}

/// 2a ≢ 0 when a ≢ 0.
pub proof fn lemma_two_a_nonzero<T: OrderedField>(a: T)
    requires !a.eqv(T::zero()),
    ensures !from_int::<T>(2).mul(a).eqv(T::zero()),
{
    crate::embedding::lemma_from_int_nonzero::<T>(2);
    if from_int::<T>(2).mul(a).eqv(T::zero()) {
        T::axiom_mul_zero_right(from_int::<T>(2));
        T::axiom_eqv_symmetric(from_int::<T>(2).mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(from_int::<T>(2).mul(a), T::zero(), from_int::<T>(2).mul(T::zero()));
        lemma_mul_cancel_left::<T>(a, T::zero(), from_int::<T>(2));
    }
}

/// 4a ≢ 0 when a ≢ 0.
proof fn lemma_four_a_nonzero<T: OrderedField>(a: T)
    requires !a.eqv(T::zero()),
    ensures !from_int::<T>(4).mul(a).eqv(T::zero()),
{
    crate::embedding::lemma_from_int_nonzero::<T>(4);
    if from_int::<T>(4).mul(a).eqv(T::zero()) {
        T::axiom_mul_zero_right(from_int::<T>(4));
        T::axiom_eqv_symmetric(from_int::<T>(4).mul(T::zero()), T::zero());
        T::axiom_eqv_transitive(from_int::<T>(4).mul(a), T::zero(), from_int::<T>(4).mul(T::zero()));
        lemma_mul_cancel_left::<T>(a, T::zero(), from_int::<T>(4));
    }
}

/// Division congruence.
pub proof fn lemma_div_congruence<T: Field>(a1: T, a2: T, b1: T, b2: T)
    requires a1.eqv(a2), b1.eqv(b2), !b1.eqv(T::zero()),
    ensures a1.div(b1).eqv(a2.div(b2)),
{
    // a/b ≡ a*recip(b)
    T::axiom_div_is_mul_recip(a1, b1);  // a1/b1 ≡ a1*recip(b1)
    T::axiom_div_is_mul_recip(a2, b2);  // a2/b2 ≡ a2*recip(b2)
    T::axiom_recip_congruence(b1, b2);  // recip(b1) ≡ recip(b2)
    lemma_mul_congruence::<T>(a1, a2, b1.recip(), b2.recip()); // a1*r(b1) ≡ a2*r(b2)
    // a1/b1 ≡ a1*r(b1) ≡ a2*r(b2)
    T::axiom_eqv_transitive(a1.div(b1), a1.mul(b1.recip()), a2.mul(b2.recip()));
    // a2/b2 ≡ a2*r(b2), symmetric: a2*r(b2) ≡ ... no, we need a2*r(b2) ≡ a2/b2
    T::axiom_eqv_symmetric(a2.div(b2), a2.mul(b2.recip()));
    T::axiom_eqv_transitive(a1.div(b1), a2.mul(b2.recip()), a2.div(b2));
}

/// Left additive cancellation.
pub proof fn lemma_add_cancel_left<T: Ring>(a: T, b: T, c: T)
    requires a.add(b).eqv(a.add(c)),
    ensures b.eqv(c),
{
    // Add -a on left of both sides
    T::axiom_eqv_reflexive(a.neg());
    lemma_add_congruence::<T>(a.neg(), a.neg(), a.add(b), a.add(c));
    // -a + (a + b) ≡ (-a + a) + b by assoc reversed
    T::axiom_add_associative(a.neg(), a, b);
    // -a + a ≡ 0
    lemma_add_inverse_left::<T>(a);
    // (-a+a) + b ≡ 0 + b ≡ b
    T::axiom_eqv_reflexive(b);
    lemma_add_congruence::<T>(a.neg().add(a), T::zero(), b, b);
    lemma_add_zero_left::<T>(b);
    T::axiom_eqv_transitive(a.neg().add(a).add(b), T::zero().add(b), b);
    // -a+(a+b) ≡ (-a+a)+b [sym of assoc]
    T::axiom_eqv_symmetric(a.neg().add(a).add(b), a.neg().add(a.add(b)));
    // b ≡ (-a+a)+b [sym] ≡ -a+(a+b) [sym assoc]
    T::axiom_eqv_symmetric(a.neg().add(a).add(b), b);
    T::axiom_eqv_transitive(b, a.neg().add(a).add(b), a.neg().add(a.add(b)));

    // Same for c
    T::axiom_add_associative(a.neg(), a, c);
    T::axiom_eqv_reflexive(c);
    lemma_add_congruence::<T>(a.neg().add(a), T::zero(), c, c);
    lemma_add_zero_left::<T>(c);
    T::axiom_eqv_transitive(a.neg().add(a).add(c), T::zero().add(c), c);

    // b ≡ -a+(a+b) ≡ -a+(a+c) [congruence]
    T::axiom_eqv_transitive(b, a.neg().add(a.add(b)), a.neg().add(a.add(c)));
    // -a+(a+c) ≡ (-a+a)+c [sym of assoc]
    T::axiom_eqv_symmetric(a.neg().add(a).add(c), a.neg().add(a.add(c)));
    T::axiom_eqv_transitive(b, a.neg().add(a.add(c)), a.neg().add(a).add(c));
    T::axiom_eqv_transitive(b, a.neg().add(a).add(c), c);
}

/// (-b + x) + b ≡ x.
proof fn lemma_cancel_neg_b<T: Ring>(b: T, x: T)
    ensures b.neg().add(x).add(b).eqv(x),
{
    // (-b+x)+b ≡ -b+(x+b) by assoc
    T::axiom_add_associative(b.neg(), x, b);
    // x+b ≡ b+x by comm
    T::axiom_add_commutative(x, b);
    lemma_add_congruence_right::<T>(b.neg(), x.add(b), b.add(x));
    // -b+(b+x) ≡ (-b+b)+x by assoc reversed
    T::axiom_add_associative(b.neg(), b, x);
    T::axiom_eqv_symmetric(b.neg().add(b).add(x), b.neg().add(b.add(x)));
    // -b+b ≡ 0
    lemma_add_inverse_left::<T>(b);
    T::axiom_eqv_reflexive(x);
    lemma_add_congruence::<T>(b.neg().add(b), T::zero(), x, x);
    // 0+x ≡ x
    lemma_add_zero_left::<T>(x);
    T::axiom_eqv_transitive(b.neg().add(b).add(x), T::zero().add(x), x);
    // chain: (-b+x)+b ≡ -b+(x+b) ≡ -b+(b+x) ≡ (-b+b)+x ≡ x
    T::axiom_eqv_transitive(b.neg().add(x.add(b)), b.neg().add(b.add(x)), b.neg().add(b).add(x));
    T::axiom_eqv_transitive(b.neg().add(x.add(b)), b.neg().add(b).add(x), x);
    T::axiom_eqv_transitive(b.neg().add(x).add(b), b.neg().add(x.add(b)), x);
}

/// (p*q)*(p*q) ≡ (p*p)*(q*q).
proof fn lemma_square_product<T: Ring>(p: T, q: T)
    ensures p.mul(q).mul(p.mul(q)).eqv(p.mul(p).mul(q.mul(q))),
{
    let pq = p.mul(q);
    // pq*pq ≡ p*(q*pq) by assoc
    T::axiom_mul_associative(p, q, pq);
    // q*pq = q*(p*q) ≡ (q*p)*q by assoc reversed
    T::axiom_mul_associative(q, p, q);
    T::axiom_eqv_symmetric(q.mul(p).mul(q), q.mul(p.mul(q)));
    // q*p ≡ p*q by comm
    T::axiom_mul_commutative(q, p);
    T::axiom_mul_congruence_left(q.mul(p), pq, q);
    // (q*p)*q ≡ pq*q
    T::axiom_eqv_transitive(q.mul(pq), q.mul(p).mul(q), pq.mul(q));
    // pq*q ≡ p*(q*q) by assoc
    T::axiom_mul_associative(p, q, q);
    T::axiom_eqv_transitive(q.mul(pq), pq.mul(q), p.mul(q.mul(q)));
    // p*(q*pq) ≡ p*(p*(q*q))
    lemma_mul_congruence_right::<T>(p, q.mul(pq), p.mul(q.mul(q)));
    // p*(p*(q*q)) ≡ (p*p)*(q*q) by assoc reversed
    T::axiom_mul_associative(p, p, q.mul(q));
    T::axiom_eqv_symmetric(p.mul(p).mul(q.mul(q)), p.mul(p.mul(q.mul(q))));
    T::axiom_eqv_transitive(p.mul(q.mul(pq)), p.mul(p.mul(q.mul(q))), p.mul(p).mul(q.mul(q)));
    // chain: pq*pq ≡ p*(q*pq) ≡ (p*p)*(q*q)
    T::axiom_eqv_transitive(pq.mul(pq), p.mul(q.mul(pq)), p.mul(p).mul(q.mul(q)));
}

/// (2a)*(2a) ≡ 4*(a*a).
proof fn lemma_two_sq_is_four<T: Ring>(a: T)
    ensures from_int::<T>(2).mul(a).mul(from_int::<T>(2).mul(a)).eqv(from_int::<T>(4).mul(a.mul(a))),
{
    lemma_square_product::<T>(from_int::<T>(2), a);
    crate::embedding::lemma_from_int_mul::<T>(2, 2);
    T::axiom_eqv_symmetric(from_int::<T>(4), from_int::<T>(2).mul(from_int::<T>(2)));
    T::axiom_mul_congruence_left(from_int::<T>(2).mul(from_int::<T>(2)), from_int::<T>(4), a.mul(a));
    T::axiom_eqv_transitive(
        from_int::<T>(2).mul(a).mul(from_int::<T>(2).mul(a)),
        from_int::<T>(2).mul(from_int::<T>(2)).mul(a.mul(a)),
        from_int::<T>(4).mul(a.mul(a)),
    );
}

/// 1+1 ≡ from_int(2).
proof fn lemma_one_plus_one_is_two<T: Ring>()
    ensures T::one().add(T::one()).eqv(from_int::<T>(2)),
{
    // from_int(1+1) ≡ from_int(1) + from_int(1)
    crate::embedding::lemma_from_int_add::<T>(1, 1);
    // from_int(1) ≡ 1
    crate::embedding::lemma_from_int_one::<T>();
    // 1 ≡ from_int(1) [symmetric]
    T::axiom_eqv_symmetric(from_int::<T>(1), T::one());
    T::axiom_eqv_reflexive(T::one());
    // from_int(1) ≡ 1 and from_int(1) ≡ 1, so from_int(1)+from_int(1) ≡ 1+1
    lemma_add_congruence::<T>(from_int::<T>(1), T::one(), from_int::<T>(1), T::one());
    // fi(2) ≡ fi(1)+fi(1) ≡ 1+1
    T::axiom_eqv_transitive(from_int::<T>(2), from_int::<T>(1).add(from_int::<T>(1)), T::one().add(T::one()));
    // 1+1 ≡ fi(2) [symmetric]
    T::axiom_eqv_symmetric(from_int::<T>(2), T::one().add(T::one()));
}

/// (x + y) - y ≡ x.
proof fn lemma_add_sub_cancel<T: Ring>(x: T, y: T)
    ensures x.add(y).sub(y).eqv(x),
{
    // (x+y) - y = (x+y) + (-y) by sub_is_add_neg
    T::axiom_sub_is_add_neg(x.add(y), y);
    // (x+y)+(-y) ≡ x+(y+(-y)) by assoc
    T::axiom_add_associative(x, y, y.neg());
    // y+(-y) ≡ 0
    T::axiom_add_inverse_right(y);
    // x+(y+(-y)) ≡ x+0
    T::axiom_eqv_reflexive(x);
    lemma_add_congruence::<T>(x, x, y.add(y.neg()), T::zero());
    // x+0 ≡ 0+x ≡ x
    T::axiom_add_commutative(x, T::zero());
    lemma_add_zero_left::<T>(x);
    T::axiom_eqv_transitive(x.add(T::zero()), T::zero().add(x), x);
    // chain: x+(y+(-y)) ≡ x+0 ≡ x
    T::axiom_eqv_transitive(x.add(y.add(y.neg())), x.add(T::zero()), x);
    // chain: (x+y)+(-y) ≡ x+(y+(-y)) ≡ x
    T::axiom_eqv_symmetric(x.add(y.add(y.neg())), x.add(y).add(y.neg()));
    T::axiom_eqv_transitive(x.add(y).add(y.neg()), x.add(y.add(y.neg())), x);
    // chain: (x+y)-y ≡ (x+y)+(-y) ≡ x
    T::axiom_eqv_transitive(x.add(y).sub(y), x.add(y).add(y.neg()), x);
}

/// (a + b) - a ≡ b (swap version).
proof fn lemma_add_sub_cancel_left<T: Ring>(a: T, b: T)
    ensures a.add(b).sub(a).eqv(b),
{
    // a+b ≡ b+a by comm
    T::axiom_add_commutative(a, b);
    // (a+b) - a ... need congruence: (a+b).sub(a) ≡ (b+a).sub(a)
    T::axiom_eqv_reflexive(a);
    lemma_sub_congruence::<T>(a.add(b), b.add(a), a, a);
    // (b+a) - a ≡ b by add_sub_cancel
    lemma_add_sub_cancel::<T>(b, a);
    T::axiom_eqv_transitive(a.add(b).sub(a), b.add(a).sub(a), b);
}

/// 2*(2a*b) ≡ 4*(a*b). Used to connect square_expand's (1+1) coefficient.
proof fn lemma_two_times_two_a_b<T: Ring>(a: T, b: T)
    ensures
        from_int::<T>(2).mul(from_int::<T>(2).mul(a).mul(b)).eqv(from_int::<T>(4).mul(a.mul(b))),
{
    let two = from_int::<T>(2);
    let four = from_int::<T>(4);
    let two_a = two.mul(a);
    // 2*(2a*b) ≡ (2*2a)*b by assoc
    T::axiom_mul_associative(two, two_a, b);
    T::axiom_eqv_symmetric(two.mul(two_a).mul(b), two.mul(two_a.mul(b)));
    // 2*2a = 2*(2*a) ≡ (2*2)*a by assoc
    T::axiom_mul_associative(two, two, a);
    T::axiom_eqv_symmetric(two.mul(two).mul(a), two.mul(two.mul(a)));
    // 2*2 ≡ 4
    crate::embedding::lemma_from_int_mul::<T>(2, 2);
    T::axiom_eqv_symmetric(four, two.mul(two));
    T::axiom_mul_congruence_left(two.mul(two), four, a);
    // 2*(2*a) ≡ (2*2)*a ≡ 4*a
    T::axiom_eqv_transitive(two.mul(two_a), two.mul(two).mul(a), four.mul(a));
    // (2*2a)*b ≡ (4*a)*b
    T::axiom_mul_congruence_left(two.mul(two_a), four.mul(a), b);
    // (4*a)*b ≡ 4*(a*b) by assoc
    T::axiom_mul_associative(four, a, b);
    T::axiom_eqv_transitive(two.mul(two_a).mul(b), four.mul(a).mul(b), four.mul(a.mul(b)));
    // chain: 2*(2a*b) ≡ (2*2a)*b ≡ 4*(a*b)
    T::axiom_eqv_transitive(two.mul(two_a.mul(b)), two.mul(two_a).mul(b), four.mul(a.mul(b)));
}

// ============================================================
//  Factoring helper: 4a*(at² + bt + c) ≡ 4a²t² + 4abt + 4ac
// ============================================================

/// Shows that 4a * eval(a,b,c,t) ≡ u² + (1+1)*u*b + 4ac
/// where u = 2a*t, using square_expand.
proof fn lemma_factor_via_u<T: Sqrt>(a: T, b: T, c: T, t: T, u: T)
    requires
        !a.eqv(T::zero()),
        u.eqv(from_int::<T>(2).mul(a).mul(t)),
    ensures
        from_int::<T>(4).mul(a).mul(quadratic_eval(a, b, c, t)).eqv(
            u.mul(u).add(T::one().add(T::one()).mul(u.mul(b))).add(from_int::<T>(4).mul(a.mul(c)))
        ),
{
    let two = from_int::<T>(2);
    let four = from_int::<T>(4);
    let two_a = two.mul(a);
    let four_a = four.mul(a);
    let one_one = T::one().add(T::one());
    let eval_val = quadratic_eval(a, b, c, t);
    let four_ac = four.mul(a.mul(c));

    // u ≡ 2a*t, so u*u ≡ (2a*t)*(2a*t) ≡ (2a)²*(t*t) ≡ 4*(a*a)*(t*t)
    lemma_mul_congruence::<T>(u, two_a.mul(t), u, two_a.mul(t));
    lemma_square_product::<T>(two_a, t);
    T::axiom_eqv_transitive(u.mul(u), two_a.mul(t).mul(two_a.mul(t)), two_a.mul(two_a).mul(t.mul(t)));
    lemma_two_sq_is_four::<T>(a);
    T::axiom_mul_congruence_left(two_a.mul(two_a), four.mul(a.mul(a)), t.mul(t));
    T::axiom_eqv_transitive(u.mul(u), two_a.mul(two_a).mul(t.mul(t)), four.mul(a.mul(a)).mul(t.mul(t)));
    // u*u ≡ 4*(a*a)*(t*t)

    // u*b ≡ (2a*t)*b ≡ (2a)*(t*b) ≡ (2a)*(b*t) ≡ (2a*b)*t
    T::axiom_eqv_reflexive(b);
    lemma_mul_congruence::<T>(u, two_a.mul(t), b, b);
    T::axiom_mul_associative(two_a, t, b);
    T::axiom_mul_commutative(t, b);
    lemma_mul_congruence_right::<T>(two_a, t.mul(b), b.mul(t));
    T::axiom_mul_associative(two_a, b, t);
    T::axiom_eqv_symmetric(two_a.mul(b).mul(t), two_a.mul(b.mul(t)));
    T::axiom_eqv_transitive(two_a.mul(t.mul(b)), two_a.mul(b.mul(t)), two_a.mul(b).mul(t));
    T::axiom_eqv_transitive(two_a.mul(t).mul(b), two_a.mul(t.mul(b)), two_a.mul(b).mul(t));
    T::axiom_eqv_transitive(u.mul(b), two_a.mul(t).mul(b), two_a.mul(b).mul(t));
    // u*b ≡ (2a*b)*t

    // (1+1)*(u*b) ≡ (1+1)*((2a*b)*t) ≡ ((1+1)*(2a*b))*t
    lemma_mul_congruence_right::<T>(one_one, u.mul(b), two_a.mul(b).mul(t));
    T::axiom_mul_associative(one_one, two_a.mul(b), t);
    T::axiom_eqv_symmetric(one_one.mul(two_a.mul(b)).mul(t), one_one.mul(two_a.mul(b).mul(t)));
    T::axiom_eqv_transitive(one_one.mul(u.mul(b)), one_one.mul(two_a.mul(b).mul(t)), one_one.mul(two_a.mul(b)).mul(t));
    // (1+1) ≡ 2
    lemma_one_plus_one_is_two::<T>();
    // (1+1)*(2a*b) ≡ 2*(2a*b)
    T::axiom_mul_congruence_left(one_one, two, two_a.mul(b));
    // 2*(2a*b) ≡ 4*(a*b)
    lemma_two_times_two_a_b::<T>(a, b);
    T::axiom_eqv_transitive(one_one.mul(two_a.mul(b)), two.mul(two_a.mul(b)), four.mul(a.mul(b)));
    // So (1+1)*(u*b) ≡ (4*(a*b))*t
    T::axiom_mul_congruence_left(one_one.mul(two_a.mul(b)), four.mul(a.mul(b)), t);
    T::axiom_eqv_transitive(
        one_one.mul(u.mul(b)),
        one_one.mul(two_a.mul(b)).mul(t),
        four.mul(a.mul(b)).mul(t),
    );
    // (1+1)*ub ≡ 4*(a*b)*t

    // Combine first two terms:
    // u*u + (1+1)*ub ≡ 4*(a²)*(t²) + 4*(ab)*t
    lemma_add_congruence::<T>(
        u.mul(u), four.mul(a.mul(a)).mul(t.mul(t)),
        one_one.mul(u.mul(b)), four.mul(a.mul(b)).mul(t),
    );

    // Now show the target sum ≡ 4a * eval_val using distributivity
    // 4*(a²)*(t²) = (4*a)*(a*(t²)) by assoc
    T::axiom_mul_associative(four, a, a);
    T::axiom_eqv_symmetric(four_a.mul(a), four.mul(a.mul(a)));
    T::axiom_mul_congruence_left(four.mul(a.mul(a)), four_a.mul(a), t.mul(t));
    T::axiom_mul_associative(four_a, a, t.mul(t));
    T::axiom_eqv_transitive(four.mul(a.mul(a)).mul(t.mul(t)), four_a.mul(a).mul(t.mul(t)), four_a.mul(a.mul(t.mul(t))));

    // 4*(ab)*t = (4*a)*(b*t) by assoc
    T::axiom_mul_associative(four, a, b);
    T::axiom_eqv_symmetric(four_a.mul(b), four.mul(a.mul(b)));
    T::axiom_mul_congruence_left(four.mul(a.mul(b)), four_a.mul(b), t);
    T::axiom_mul_associative(four_a, b, t);
    T::axiom_eqv_transitive(four.mul(a.mul(b)).mul(t), four_a.mul(b).mul(t), four_a.mul(b.mul(t)));

    // 4a*(at²) + 4a*(bt) ≡ 4a*(at²+bt) by distributivity
    lemma_add_congruence::<T>(
        four.mul(a.mul(a)).mul(t.mul(t)), four_a.mul(a.mul(t.mul(t))),
        four.mul(a.mul(b)).mul(t), four_a.mul(b.mul(t)),
    );
    T::axiom_mul_distributes_left(four_a, a.mul(t.mul(t)), b.mul(t));
    T::axiom_eqv_symmetric(four_a.mul(a.mul(t.mul(t))).add(four_a.mul(b.mul(t))), four_a.mul(a.mul(t.mul(t)).add(b.mul(t))));
    T::axiom_eqv_transitive(
        four.mul(a.mul(a)).mul(t.mul(t)).add(four.mul(a.mul(b)).mul(t)),
        four_a.mul(a.mul(t.mul(t))).add(four_a.mul(b.mul(t))),
        four_a.mul(a.mul(t.mul(t)).add(b.mul(t))),
    );

    // + 4ac: (4a*(at²+bt)) + 4ac ≡ 4a*(at²+bt+c)
    // 4ac = 4*(a*c) ≡ (4*a)*c by assoc
    T::axiom_mul_associative(four, a, c);
    T::axiom_eqv_symmetric(four_a.mul(c), four_ac);

    // Need: (u²+(1+1)*ub) + four_ac ≡ (4a*(at²+bt)) + four_ac ≡ (4a*(at²+bt)) + 4a*c
    let first_two = u.mul(u).add(one_one.mul(u.mul(b)));
    let first_two_expanded = four.mul(a.mul(a)).mul(t.mul(t)).add(four.mul(a.mul(b)).mul(t));
    let att_bt = a.mul(t.mul(t)).add(b.mul(t));

    // first_two + four_ac ≡ first_two_expanded + four_ac
    T::axiom_eqv_reflexive(four_ac);
    lemma_add_congruence::<T>(first_two, first_two_expanded, four_ac, four_ac);

    // first_two_expanded + four_ac ≡ 4a*(att_bt) + 4a*c
    lemma_add_congruence::<T>(first_two_expanded, four_a.mul(att_bt), four_ac, four_a.mul(c));
    T::axiom_eqv_transitive(
        first_two.add(four_ac),
        first_two_expanded.add(four_ac),
        four_a.mul(att_bt).add(four_a.mul(c)),
    );

    // 4a*(att_bt) + 4a*c ≡ 4a*(att_bt + c) by distributivity
    T::axiom_mul_distributes_left(four_a, att_bt, c);
    T::axiom_eqv_symmetric(four_a.mul(att_bt).add(four_a.mul(c)), four_a.mul(att_bt.add(c)));
    T::axiom_eqv_transitive(
        first_two.add(four_ac),
        four_a.mul(att_bt).add(four_a.mul(c)),
        four_a.mul(att_bt.add(c)),
    );
    // att_bt.add(c) = eval_val definitionally
    // So first_two + four_ac ≡ 4a * eval_val
    // We want the symmetric: 4a * eval_val ≡ first_two + four_ac
    T::axiom_eqv_symmetric(first_two.add(four_ac), four_a.mul(eval_val));
}

// ============================================================
//  Main theorem: root+ satisfies equation
// ============================================================

/// The plus root satisfies a*t² + b*t + c ≡ 0.
pub proof fn lemma_quadratic_root_plus_satisfies<T: Sqrt>(a: T, b: T, c: T)
    requires
        !a.eqv(T::zero()),
        T::zero().le(discriminant(a, b, c)),
    ensures
        quadratic_eval(a, b, c, quadratic_root_plus(a, b, c)).eqv(T::zero()),
{
    let disc = discriminant(a, b, c);
    let sqrt_d = disc.sqrt();
    let two = from_int::<T>(2);
    let four = from_int::<T>(4);
    let two_a = two.mul(a);
    let four_a = four.mul(a);
    let t = quadratic_root_plus(a, b, c);
    let neg_b = b.neg();
    let one_one = T::one().add(T::one());
    let four_ac = four.mul(a.mul(c));

    // u = 2a*t ≡ -b + sqrt_d
    lemma_two_a_nonzero::<T>(a);
    // t*two_a ≡ -b+sqrt_d
    lemma_div_mul_cancel::<T>(neg_b.add(sqrt_d), two_a);
    // two_a*t ≡ t*two_a by comm
    T::axiom_mul_commutative(two_a, t);
    let u = two_a.mul(t);
    // u = two_a*t ≡ t*two_a ≡ -b+sqrt_d
    T::axiom_eqv_transitive(u, t.mul(two_a), neg_b.add(sqrt_d));

    // u + b ≡ sqrt_d
    T::axiom_eqv_reflexive(b);
    lemma_add_congruence::<T>(u, neg_b.add(sqrt_d), b, b);
    lemma_cancel_neg_b::<T>(b, sqrt_d);
    T::axiom_eqv_transitive(u.add(b), neg_b.add(sqrt_d).add(b), sqrt_d);

    // (u+b)² ≡ sqrt_d² ≡ disc
    lemma_mul_congruence::<T>(u.add(b), sqrt_d, u.add(b), sqrt_d);
    T::axiom_sqrt_square(disc);
    T::axiom_eqv_transitive(u.add(b).mul(u.add(b)), sqrt_d.mul(sqrt_d), disc);

    // Expand (u+b)² = u² + (1+1)*ub + b²
    lemma_square_expand::<T>(u, b);
    let expanded = u.mul(u).add(one_one.mul(u.mul(b))).add(b.mul(b));
    // expanded ≡ (u+b)² ≡ disc
    T::axiom_eqv_symmetric(u.add(b).mul(u.add(b)), expanded);
    T::axiom_eqv_transitive(expanded, u.add(b).mul(u.add(b)), disc);

    // Cancel b²: expanded - b² ≡ disc - b²
    let u_sq_plus = u.mul(u).add(one_one.mul(u.mul(b)));
    T::axiom_eqv_reflexive(b.mul(b));
    lemma_sub_congruence::<T>(expanded, disc, b.mul(b), b.mul(b));

    // expanded = u_sq_plus + b², so expanded.sub(b²) = (u_sq_plus + b²).sub(b²) ≡ u_sq_plus
    lemma_add_sub_cancel::<T>(u_sq_plus, b.mul(b));
    // expanded.sub(b²) is already the same expression as (u_sq_plus + b²).sub(b²)

    // disc - b² ≡ -4ac
    // disc = b² - 4ac, so disc - b² = (b² - 4ac) - b²
    // = (b² + (-4ac)) - b² by sub_is_add_neg
    // By add_sub_cancel_left on (b², -4ac): (b² + (-4ac)) - b² ≡ -4ac
    T::axiom_sub_is_add_neg(b.mul(b), four_ac);
    // disc = b².sub(four_ac) ≡ b².add(four_ac.neg())
    // disc - b² = disc.sub(b²)
    // disc ≡ b².add(four_ac.neg()), so disc.sub(b²) ≡ (b².add(four_ac.neg())).sub(b²)
    T::axiom_eqv_reflexive(b.mul(b));
    lemma_sub_congruence::<T>(disc, b.mul(b).add(four_ac.neg()), b.mul(b), b.mul(b));
    lemma_add_sub_cancel_left::<T>(b.mul(b), four_ac.neg());
    T::axiom_eqv_transitive(disc.sub(b.mul(b)), b.mul(b).add(four_ac.neg()).sub(b.mul(b)), four_ac.neg());

    // u_sq_plus ≡ expanded - b² ≡ disc - b² ≡ -4ac
    T::axiom_eqv_transitive(expanded.sub(b.mul(b)), disc.sub(b.mul(b)), four_ac.neg());
    T::axiom_eqv_symmetric(expanded.sub(b.mul(b)), u_sq_plus);
    T::axiom_eqv_transitive(u_sq_plus, expanded.sub(b.mul(b)), four_ac.neg());

    // u_sq_plus + 4ac ≡ -4ac + 4ac ≡ 0
    T::axiom_eqv_reflexive(four_ac);
    lemma_add_congruence::<T>(u_sq_plus, four_ac.neg(), four_ac, four_ac);
    lemma_add_inverse_left::<T>(four_ac);
    T::axiom_eqv_transitive(u_sq_plus.add(four_ac), four_ac.neg().add(four_ac), T::zero());

    // 4a * eval ≡ u_sq_plus + 4ac (from factoring lemma)
    T::axiom_eqv_reflexive(two_a.mul(t));
    lemma_factor_via_u::<T>(a, b, c, t, u);
    // 4a*eval ≡ u_sq_plus + 4ac ≡ 0
    let eval_val = quadratic_eval(a, b, c, t);
    T::axiom_eqv_transitive(four_a.mul(eval_val), u_sq_plus.add(four_ac), T::zero());

    // Cancel 4a
    lemma_four_a_nonzero::<T>(a);
    T::axiom_mul_zero_right(four_a);
    T::axiom_eqv_symmetric(four_a.mul(T::zero()), T::zero());
    T::axiom_eqv_transitive(four_a.mul(eval_val), T::zero(), four_a.mul(T::zero()));
    lemma_mul_cancel_left::<T>(eval_val, T::zero(), four_a);
}

/// The minus root satisfies a*t² + b*t + c ≡ 0.
pub proof fn lemma_quadratic_root_minus_satisfies<T: Sqrt>(a: T, b: T, c: T)
    requires
        !a.eqv(T::zero()),
        T::zero().le(discriminant(a, b, c)),
    ensures
        quadratic_eval(a, b, c, quadratic_root_minus(a, b, c)).eqv(T::zero()),
{
    let disc = discriminant(a, b, c);
    let sqrt_d = disc.sqrt();
    let two = from_int::<T>(2);
    let four = from_int::<T>(4);
    let two_a = two.mul(a);
    let four_a = four.mul(a);
    let t = quadratic_root_minus(a, b, c);
    let neg_b = b.neg();
    let one_one = T::one().add(T::one());
    let four_ac = four.mul(a.mul(c));

    // u = 2a*t ≡ -b - sqrt_d
    lemma_two_a_nonzero::<T>(a);
    // t*two_a ≡ -b-sqrt_d
    lemma_div_mul_cancel::<T>(neg_b.sub(sqrt_d), two_a);
    // two_a*t ≡ t*two_a by comm
    T::axiom_mul_commutative(two_a, t);
    let u = two_a.mul(t);
    T::axiom_eqv_transitive(u, t.mul(two_a), neg_b.sub(sqrt_d));

    // u + b ≡ -sqrt_d
    T::axiom_eqv_reflexive(b);
    lemma_add_congruence::<T>(u, neg_b.sub(sqrt_d), b, b);
    // (-b - sqrt_d) + b = (-b + (-sqrt_d)) + b ≡ -sqrt_d
    T::axiom_sub_is_add_neg(neg_b, sqrt_d);
    lemma_add_congruence::<T>(neg_b.sub(sqrt_d), neg_b.add(sqrt_d.neg()), b, b);
    T::axiom_eqv_transitive(u.add(b), neg_b.sub(sqrt_d).add(b), neg_b.add(sqrt_d.neg()).add(b));
    lemma_cancel_neg_b::<T>(b, sqrt_d.neg());
    T::axiom_eqv_transitive(u.add(b), neg_b.add(sqrt_d.neg()).add(b), sqrt_d.neg());

    // (u+b)² ≡ (-sqrt_d)² ≡ sqrt_d² ≡ disc
    lemma_mul_congruence::<T>(u.add(b), sqrt_d.neg(), u.add(b), sqrt_d.neg());
    lemma_neg_mul_neg::<T>(sqrt_d, sqrt_d);
    T::axiom_eqv_transitive(u.add(b).mul(u.add(b)), sqrt_d.neg().mul(sqrt_d.neg()), sqrt_d.mul(sqrt_d));
    T::axiom_sqrt_square(disc);
    T::axiom_eqv_transitive(u.add(b).mul(u.add(b)), sqrt_d.mul(sqrt_d), disc);

    // From here it's identical to plus case
    lemma_square_expand::<T>(u, b);
    let expanded = u.mul(u).add(one_one.mul(u.mul(b))).add(b.mul(b));
    T::axiom_eqv_symmetric(u.add(b).mul(u.add(b)), expanded);
    T::axiom_eqv_transitive(expanded, u.add(b).mul(u.add(b)), disc);

    let u_sq_plus = u.mul(u).add(one_one.mul(u.mul(b)));
    T::axiom_eqv_reflexive(b.mul(b));
    lemma_sub_congruence::<T>(expanded, disc, b.mul(b), b.mul(b));
    lemma_add_sub_cancel::<T>(u_sq_plus, b.mul(b));

    T::axiom_sub_is_add_neg(b.mul(b), four_ac);
    T::axiom_eqv_reflexive(b.mul(b));
    lemma_sub_congruence::<T>(disc, b.mul(b).add(four_ac.neg()), b.mul(b), b.mul(b));
    lemma_add_sub_cancel_left::<T>(b.mul(b), four_ac.neg());
    T::axiom_eqv_transitive(disc.sub(b.mul(b)), b.mul(b).add(four_ac.neg()).sub(b.mul(b)), four_ac.neg());
    T::axiom_eqv_transitive(expanded.sub(b.mul(b)), disc.sub(b.mul(b)), four_ac.neg());
    T::axiom_eqv_symmetric(expanded.sub(b.mul(b)), u_sq_plus);
    T::axiom_eqv_transitive(u_sq_plus, expanded.sub(b.mul(b)), four_ac.neg());

    T::axiom_eqv_reflexive(four_ac);
    lemma_add_congruence::<T>(u_sq_plus, four_ac.neg(), four_ac, four_ac);
    lemma_add_inverse_left::<T>(four_ac);
    T::axiom_eqv_transitive(u_sq_plus.add(four_ac), four_ac.neg().add(four_ac), T::zero());

    T::axiom_eqv_reflexive(two_a.mul(t));
    lemma_factor_via_u::<T>(a, b, c, t, u);
    let eval_val = quadratic_eval(a, b, c, t);
    T::axiom_eqv_transitive(four_a.mul(eval_val), u_sq_plus.add(four_ac), T::zero());

    lemma_four_a_nonzero::<T>(a);
    T::axiom_mul_zero_right(four_a);
    T::axiom_eqv_symmetric(four_a.mul(T::zero()), T::zero());
    T::axiom_eqv_transitive(four_a.mul(eval_val), T::zero(), four_a.mul(T::zero()));
    lemma_mul_cancel_left::<T>(eval_val, T::zero(), four_a);
}

// ============================================================
//  Double root
// ============================================================

/// When disc ≡ 0, both roots are equal.
pub proof fn lemma_double_root<T: Sqrt>(a: T, b: T, c: T)
    requires
        !a.eqv(T::zero()),
        discriminant(a, b, c).eqv(T::zero()),
    ensures
        quadratic_root_plus(a, b, c).eqv(quadratic_root_minus(a, b, c)),
{
    let disc = discriminant(a, b, c);
    let two_a = from_int::<T>(2).mul(a);
    let neg_b = b.neg();
    lemma_two_a_nonzero::<T>(a);

    // 0 ≤ disc (from disc ≡ 0)
    T::axiom_le_reflexive(T::zero());
    T::axiom_eqv_symmetric(disc, T::zero());
    T::axiom_eqv_reflexive(T::zero());
    T::axiom_le_congruence(T::zero(), T::zero(), T::zero(), disc);

    // sqrt(disc) ≡ 0
    let sqrt_d = disc.sqrt();
    T::axiom_sqrt_nonneg(disc);
    T::axiom_sqrt_square(disc);
    T::axiom_eqv_transitive(sqrt_d.mul(sqrt_d), disc, T::zero());
    // sqrt_d ≥ 0 and sqrt_d² ≡ 0 → sqrt_d ≡ 0
    if !sqrt_d.eqv(T::zero()) {
        // !sqrt_d.eqv(0) → !0.eqv(sqrt_d) (contrapositive of symmetric)
        if T::zero().eqv(sqrt_d) {
            T::axiom_eqv_symmetric(T::zero(), sqrt_d);
        }
        // 0 ≤ sqrt_d && !0.eqv(sqrt_d) → 0 < sqrt_d
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), sqrt_d);
        // sqrt_d > 0 → sqrt_d*sqrt_d > 0
        lemma_mul_pos_pos::<T>(sqrt_d, sqrt_d);
        // 0 < sqrt_d*sqrt_d means 0.le(sqrt_d*sqrt_d) && !0.eqv(sqrt_d*sqrt_d)
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), sqrt_d.mul(sqrt_d));
        // But sqrt_d*sqrt_d ≡ 0, so 0.eqv(sqrt_d*sqrt_d) — contradiction
        T::axiom_eqv_symmetric(sqrt_d.mul(sqrt_d), T::zero());
    }

    // -b + sqrt_d ≡ -b + 0 ≡ -b
    T::axiom_eqv_reflexive(neg_b);
    lemma_add_congruence::<T>(neg_b, neg_b, sqrt_d, T::zero());
    T::axiom_add_commutative(neg_b, T::zero());
    lemma_add_zero_left::<T>(neg_b);
    T::axiom_eqv_transitive(neg_b.add(T::zero()), T::zero().add(neg_b), neg_b);
    T::axiom_eqv_transitive(neg_b.add(sqrt_d), neg_b.add(T::zero()), neg_b);

    // -b - sqrt_d ≡ -b - 0 ≡ -b + (-0) ≡ -b + 0 ≡ -b
    T::axiom_sub_is_add_neg(neg_b, sqrt_d);
    T::axiom_neg_congruence(sqrt_d, T::zero());
    lemma_neg_zero::<T>();
    T::axiom_eqv_transitive(sqrt_d.neg(), T::zero().neg(), T::zero());
    lemma_add_congruence::<T>(neg_b, neg_b, sqrt_d.neg(), T::zero());
    T::axiom_eqv_transitive(neg_b.add(sqrt_d.neg()), neg_b.add(T::zero()), neg_b);
    T::axiom_eqv_transitive(neg_b.sub(sqrt_d), neg_b.add(sqrt_d.neg()), neg_b);

    // Both numerators ≡ -b, so roots ≡ -b/(2a)
    T::axiom_eqv_reflexive(two_a);
    lemma_div_congruence::<T>(neg_b.add(sqrt_d), neg_b, two_a, two_a);
    lemma_div_congruence::<T>(neg_b.sub(sqrt_d), neg_b, two_a, two_a);
    T::axiom_eqv_symmetric(quadratic_root_minus(a, b, c), neg_b.div(two_a));
    T::axiom_eqv_transitive(quadratic_root_plus(a, b, c), neg_b.div(two_a), quadratic_root_minus(a, b, c));
}

// ============================================================
//  Distinct roots
// ============================================================

/// When disc > 0, the two roots are distinct.
pub proof fn lemma_distinct_roots<T: Sqrt>(a: T, b: T, c: T)
    requires
        !a.eqv(T::zero()),
        T::zero().lt(discriminant(a, b, c)),
    ensures
        !quadratic_root_plus(a, b, c).eqv(quadratic_root_minus(a, b, c)),
{
    let disc = discriminant(a, b, c);
    let two_a = from_int::<T>(2).mul(a);
    let neg_b = b.neg();
    let sqrt_d = disc.sqrt();

    lemma_two_a_nonzero::<T>(a);

    if quadratic_root_plus(a, b, c).eqv(quadratic_root_minus(a, b, c)) {
        // 2a * root+ ≡ 2a * root-
        lemma_mul_congruence_right::<T>(two_a, quadratic_root_plus(a, b, c), quadratic_root_minus(a, b, c));
        T::axiom_lt_iff_le_and_not_eqv(T::zero(), disc);
        lemma_div_mul_cancel::<T>(neg_b.add(sqrt_d), two_a);
        lemma_div_mul_cancel::<T>(neg_b.sub(sqrt_d), two_a);

        // div_mul_cancel gives root+*two_a ≡ neg_b+sqrt_d, need two_a*root+ via comm
        let root_p = quadratic_root_plus(a, b, c);
        let root_m = quadratic_root_minus(a, b, c);
        T::axiom_mul_commutative(two_a, root_p);
        T::axiom_eqv_transitive(two_a.mul(root_p), root_p.mul(two_a), neg_b.add(sqrt_d));
        T::axiom_mul_commutative(two_a, root_m);
        T::axiom_eqv_transitive(two_a.mul(root_m), root_m.mul(two_a), neg_b.sub(sqrt_d));

        // -b + sqrt_d ≡ 2a*root+ ≡ 2a*root- ≡ -b - sqrt_d
        T::axiom_eqv_symmetric(two_a.mul(root_p), neg_b.add(sqrt_d));
        T::axiom_eqv_transitive(neg_b.add(sqrt_d), two_a.mul(root_p), two_a.mul(root_m));
        T::axiom_eqv_transitive(neg_b.add(sqrt_d), two_a.mul(root_m), neg_b.sub(sqrt_d));

        // -b + sqrt_d ≡ -b + (-sqrt_d) [sub is add neg]
        T::axiom_sub_is_add_neg(neg_b, sqrt_d);
        T::axiom_eqv_transitive(neg_b.add(sqrt_d), neg_b.sub(sqrt_d), neg_b.add(sqrt_d.neg()));

        // Cancel -b: sqrt_d ≡ -sqrt_d
        lemma_add_cancel_left::<T>(neg_b, sqrt_d, sqrt_d.neg());

        // sqrt_d + sqrt_d ≡ -sqrt_d + sqrt_d ≡ 0
        T::axiom_eqv_reflexive(sqrt_d);
        lemma_add_congruence::<T>(sqrt_d, sqrt_d.neg(), sqrt_d, sqrt_d);
        lemma_add_inverse_left::<T>(sqrt_d);
        T::axiom_eqv_transitive(sqrt_d.add(sqrt_d), sqrt_d.neg().add(sqrt_d), T::zero());

        // sqrt_d ≥ 0
        T::axiom_sqrt_nonneg(disc);

        // From sqrt_d ≡ -sqrt_d and 0 ≤ sqrt_d: 0 ≤ -sqrt_d
        T::axiom_eqv_reflexive(T::zero());
        T::axiom_le_congruence(T::zero(), T::zero(), sqrt_d, sqrt_d.neg());
        // 0 ≤ -sqrt_d → add sqrt_d: sqrt_d ≤ 0
        T::axiom_le_add_monotone(T::zero(), sqrt_d.neg(), sqrt_d);
        lemma_add_zero_left::<T>(sqrt_d);
        // -sqrt_d + sqrt_d ≡ 0
        T::axiom_le_congruence(T::zero().add(sqrt_d), sqrt_d, sqrt_d.neg().add(sqrt_d), T::zero());

        // 0 ≤ sqrt_d ≤ 0 → sqrt_d ≡ 0
        T::axiom_le_antisymmetric(sqrt_d, T::zero());

        // disc ≡ sqrt_d² ≡ 0
        lemma_mul_congruence::<T>(sqrt_d, T::zero(), sqrt_d, T::zero());
        lemma_mul_zero_left::<T>(T::zero());
        T::axiom_eqv_transitive(sqrt_d.mul(sqrt_d), T::zero().mul(T::zero()), T::zero());
        T::axiom_sqrt_square(disc);
        T::axiom_eqv_symmetric(sqrt_d.mul(sqrt_d), disc);
        T::axiom_eqv_transitive(disc, sqrt_d.mul(sqrt_d), T::zero());

        // disc ≡ 0 contradicts 0 < disc
        T::axiom_eqv_symmetric(disc, T::zero());
    }
}

} // verus!
