use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;

verus! {

// ============================================================
//  Spec functions
// ============================================================

/// 2D determinant: det2(a, b, c, d) = a*d - b*c.
/// Represents the determinant of the matrix [[a, b], [c, d]].
/// Also serves as the 2D cross product (signed area of parallelogram).
pub open spec fn det2<R: Ring>(a: R, b: R, c: R, d: R) -> R {
    a.mul(d).sub(b.mul(c))
}

/// 3D determinant via cofactor expansion along the first row.
/// det3 of the matrix [[a11,a12,a13],[a21,a22,a23],[a31,a32,a33]].
pub open spec fn det3<R: Ring>(
    a11: R, a12: R, a13: R,
    a21: R, a22: R, a23: R,
    a31: R, a32: R, a33: R,
) -> R {
    a11.mul(det2(a22, a23, a32, a33))
        .sub(a12.mul(det2(a21, a23, a31, a33)))
        .add(a13.mul(det2(a21, a22, a31, a32)))
}

// ============================================================
//  Helper: (p+q) - (r+s) ≡ (p-r) + (q-s)
// ============================================================

/// (p+q) - (r+s) ≡ (p-r) + (q-s).
/// Useful for distributing subtraction over component-wise pairs.
pub proof fn lemma_sub_pairs<A: Ring>(p: A, q: A, r: A, s: A)
    ensures
        p.add(q).sub(r.add(s)).eqv(p.sub(r).add(q.sub(s))),
{
    // Step 1: (p+q) - (r+s) ≡ (p+q) + (-(r+s))
    A::axiom_sub_is_add_neg(p.add(q), r.add(s));

    // Step 2: -(r+s) ≡ (-r) + (-s)
    lemma_neg_add::<A>(r, s);

    // Step 3: (p+q) + (-(r+s)) ≡ (p+q) + ((-r)+(-s))
    lemma_add_congruence_right::<A>(p.add(q), r.add(s).neg(), r.neg().add(s.neg()));

    // Chain steps 1-3: (p+q)-(r+s) ≡ (p+q)+((-r)+(-s))
    A::axiom_eqv_transitive(
        p.add(q).sub(r.add(s)),
        p.add(q).add(r.add(s).neg()),
        p.add(q).add(r.neg().add(s.neg())),
    );

    // Step 4: (p+q) + ((-r)+(-s)) ≡ (p+(-r)) + (q+(-s))  [rearrange_2x2]
    lemma_add_rearrange_2x2::<A>(p, q, r.neg(), s.neg());

    // Chain: (p+q)-(r+s) ≡ (p+(-r))+(q+(-s))
    A::axiom_eqv_transitive(
        p.add(q).sub(r.add(s)),
        p.add(q).add(r.neg().add(s.neg())),
        p.add(r.neg()).add(q.add(s.neg())),
    );

    // Step 5: p+(-r) ≡ p-r and q+(-s) ≡ q-s
    A::axiom_sub_is_add_neg(p, r);
    A::axiom_eqv_symmetric(p.sub(r), p.add(r.neg()));
    A::axiom_sub_is_add_neg(q, s);
    A::axiom_eqv_symmetric(q.sub(s), q.add(s.neg()));

    // (p+(-r))+(q+(-s)) ≡ (p-r)+(q-s)
    lemma_add_congruence::<A>(
        p.add(r.neg()), p.sub(r),
        q.add(s.neg()), q.sub(s),
    );

    // Final chain
    A::axiom_eqv_transitive(
        p.add(q).sub(r.add(s)),
        p.add(r.neg()).add(q.add(s.neg())),
        p.sub(r).add(q.sub(s)),
    );
}

// ============================================================
//  2D determinant lemmas
// ============================================================

/// Antisymmetry: swapping the two rows negates the determinant.
/// det2(a, b, c, d) ≡ -det2(c, d, a, b).
pub proof fn lemma_det2_antisymmetric<R: Ring>(a: R, b: R, c: R, d: R)
    ensures
        det2(a, b, c, d).eqv(det2(c, d, a, b).neg()),
{
    // det2(a,b,c,d) = a*d - b*c
    // det2(c,d,a,b) = c*b - d*a
    // Need: a*d - b*c ≡ -(c*b - d*a)

    // a*d ≡ d*a and b*c ≡ c*b
    R::axiom_mul_commutative(a, d);
    R::axiom_mul_commutative(b, c);

    // a*d - b*c ≡ d*a - c*b
    lemma_sub_congruence::<R>(a.mul(d), d.mul(a), b.mul(c), c.mul(b));

    // d*a - c*b ≡ -(c*b - d*a)  [sub_antisymmetric]
    lemma_sub_antisymmetric::<R>(d.mul(a), c.mul(b));

    // Chain: a*d - b*c ≡ d*a - c*b ≡ -(c*b - d*a)
    R::axiom_eqv_transitive(
        a.mul(d).sub(b.mul(c)),
        d.mul(a).sub(c.mul(b)),
        c.mul(b).sub(d.mul(a)).neg(),
    );
}

/// Equal rows vanish: det2(a, b, a, b) ≡ 0.
pub proof fn lemma_det2_equal_rows<R: Ring>(a: R, b: R)
    ensures
        det2(a, b, a, b).eqv(R::zero()),
{
    // det2(a,b,a,b) = a*b - b*a
    // a*b ≡ b*a [comm]
    R::axiom_mul_commutative(a, b);
    R::axiom_eqv_reflexive(b.mul(a));

    // a*b - b*a ≡ b*a - b*a
    lemma_sub_congruence::<R>(a.mul(b), b.mul(a), b.mul(a), b.mul(a));

    // b*a - b*a ≡ 0
    lemma_sub_self::<R>(b.mul(a));

    // Chain
    R::axiom_eqv_transitive(
        a.mul(b).sub(b.mul(a)),
        b.mul(a).sub(b.mul(a)),
        R::zero(),
    );
}

/// Transpose invariance: det2(a, b, c, d) ≡ det2(a, c, b, d).
/// The determinant of a matrix equals the determinant of its transpose.
pub proof fn lemma_det2_transpose<R: Ring>(a: R, b: R, c: R, d: R)
    ensures
        det2(a, b, c, d).eqv(det2(a, c, b, d)),
{
    // det2(a,b,c,d) = a*d - b*c
    // det2(a,c,b,d) = a*d - c*b
    // b*c ≡ c*b [comm]
    R::axiom_mul_commutative(b, c);
    R::axiom_eqv_reflexive(a.mul(d));

    // a*d - b*c ≡ a*d - c*b
    lemma_sub_congruence::<R>(a.mul(d), a.mul(d), b.mul(c), c.mul(b));
}

/// A row of zeros gives zero: det2(0, 0, c, d) ≡ 0.
pub proof fn lemma_det2_zero_row<R: Ring>(c: R, d: R)
    ensures
        det2(R::zero(), R::zero(), c, d).eqv(R::zero()),
{
    // det2(0,0,c,d) = 0*d - 0*c
    // 0*d ≡ 0 and 0*c ≡ 0
    lemma_mul_zero_left::<R>(d);
    lemma_mul_zero_left::<R>(c);

    // 0*d - 0*c ≡ 0 - 0
    lemma_sub_congruence::<R>(R::zero().mul(d), R::zero(), R::zero().mul(c), R::zero());

    // 0 - 0 ≡ 0
    lemma_sub_self::<R>(R::zero());

    // Chain
    R::axiom_eqv_transitive(
        R::zero().mul(d).sub(R::zero().mul(c)),
        R::zero().sub(R::zero()),
        R::zero(),
    );
}

/// Scaling first row: det2(k*a, k*b, c, d) ≡ k * det2(a, b, c, d).
pub proof fn lemma_det2_scale_row<R: Ring>(k: R, a: R, b: R, c: R, d: R)
    ensures
        det2(k.mul(a), k.mul(b), c, d).eqv(k.mul(det2(a, b, c, d))),
{
    // LHS = (k*a)*d - (k*b)*c
    // (k*a)*d ≡ k*(a*d) [assoc]
    R::axiom_mul_associative(k, a, d);
    // (k*b)*c ≡ k*(b*c) [assoc]
    R::axiom_mul_associative(k, b, c);

    // LHS ≡ k*(a*d) - k*(b*c)
    lemma_sub_congruence::<R>(
        k.mul(a).mul(d), k.mul(a.mul(d)),
        k.mul(b).mul(c), k.mul(b.mul(c)),
    );

    // k*(a*d) - k*(b*c) ≡ k*(a*d - b*c)  [distributes_over_sub reversed]
    lemma_mul_distributes_over_sub::<R>(k, a.mul(d), b.mul(c));
    R::axiom_eqv_symmetric(
        k.mul(a.mul(d).sub(b.mul(c))),
        k.mul(a.mul(d)).sub(k.mul(b.mul(c))),
    );

    // Chain: LHS ≡ k*(a*d) - k*(b*c) ≡ k*(a*d - b*c)
    R::axiom_eqv_transitive(
        k.mul(a).mul(d).sub(k.mul(b).mul(c)),
        k.mul(a.mul(d)).sub(k.mul(b.mul(c))),
        k.mul(a.mul(d).sub(b.mul(c))),
    );
}

/// Linearity in first row (addition):
/// det2(a1+a2, b1+b2, c, d) ≡ det2(a1, b1, c, d) + det2(a2, b2, c, d).
pub proof fn lemma_det2_add_rows<R: Ring>(a1: R, a2: R, b1: R, b2: R, c: R, d: R)
    ensures
        det2(a1.add(a2), b1.add(b2), c, d).eqv(
            det2(a1, b1, c, d).add(det2(a2, b2, c, d))
        ),
{
    // LHS = (a1+a2)*d - (b1+b2)*c
    // (a1+a2)*d ≡ a1*d + a2*d
    lemma_mul_distributes_right::<R>(a1, a2, d);
    // (b1+b2)*c ≡ b1*c + b2*c
    lemma_mul_distributes_right::<R>(b1, b2, c);

    // LHS ≡ (a1*d + a2*d) - (b1*c + b2*c)
    lemma_sub_congruence::<R>(
        a1.add(a2).mul(d), a1.mul(d).add(a2.mul(d)),
        b1.add(b2).mul(c), b1.mul(c).add(b2.mul(c)),
    );

    // (a1*d + a2*d) - (b1*c + b2*c) ≡ (a1*d - b1*c) + (a2*d - b2*c)
    lemma_sub_pairs::<R>(a1.mul(d), a2.mul(d), b1.mul(c), b2.mul(c));

    // Chain
    R::axiom_eqv_transitive(
        a1.add(a2).mul(d).sub(b1.add(b2).mul(c)),
        a1.mul(d).add(a2.mul(d)).sub(b1.mul(c).add(b2.mul(c))),
        a1.mul(d).sub(b1.mul(c)).add(a2.mul(d).sub(b2.mul(c))),
    );
}

/// Congruence: det2 respects equivalence in all arguments.
pub proof fn lemma_det2_congruence<R: Ring>(
    a1: R, a2: R, b1: R, b2: R, c1: R, c2: R, d1: R, d2: R,
)
    requires
        a1.eqv(a2),
        b1.eqv(b2),
        c1.eqv(c2),
        d1.eqv(d2),
    ensures
        det2(a1, b1, c1, d1).eqv(det2(a2, b2, c2, d2)),
{
    // a1*d1 ≡ a2*d2
    lemma_mul_congruence::<R>(a1, a2, d1, d2);
    // b1*c1 ≡ b2*c2
    lemma_mul_congruence::<R>(b1, b2, c1, c2);
    // a1*d1 - b1*c1 ≡ a2*d2 - b2*c2
    lemma_sub_congruence::<R>(a1.mul(d1), a2.mul(d2), b1.mul(c1), b2.mul(c2));
}

/// Scaling second row: det2(a, b, k*c, k*d) ≡ k * det2(a, b, c, d).
pub proof fn lemma_det2_scale_col<R: Ring>(a: R, b: R, k: R, c: R, d: R)
    ensures
        det2(a, b, k.mul(c), k.mul(d)).eqv(k.mul(det2(a, b, c, d))),
{
    // det2(a,b,k*c,k*d) = a*(k*d) - b*(k*c)
    // a*(k*d) ≡ (a*k)*d ≡ (k*a)*d ≡ k*(a*d)
    R::axiom_mul_associative(a, k, d);
    R::axiom_eqv_symmetric(a.mul(k).mul(d), a.mul(k.mul(d)));
    R::axiom_mul_commutative(a, k);
    R::axiom_mul_congruence_left(a.mul(k), k.mul(a), d);
    R::axiom_eqv_transitive(a.mul(k.mul(d)), a.mul(k).mul(d), k.mul(a).mul(d));
    R::axiom_mul_associative(k, a, d);
    R::axiom_eqv_transitive(a.mul(k.mul(d)), k.mul(a).mul(d), k.mul(a.mul(d)));

    // b*(k*c) ≡ k*(b*c) [same pattern]
    R::axiom_mul_associative(b, k, c);
    R::axiom_eqv_symmetric(b.mul(k).mul(c), b.mul(k.mul(c)));
    R::axiom_mul_commutative(b, k);
    R::axiom_mul_congruence_left(b.mul(k), k.mul(b), c);
    R::axiom_eqv_transitive(b.mul(k.mul(c)), b.mul(k).mul(c), k.mul(b).mul(c));
    R::axiom_mul_associative(k, b, c);
    R::axiom_eqv_transitive(b.mul(k.mul(c)), k.mul(b).mul(c), k.mul(b.mul(c)));

    // a*(k*d) - b*(k*c) ≡ k*(a*d) - k*(b*c)
    lemma_sub_congruence::<R>(
        a.mul(k.mul(d)), k.mul(a.mul(d)),
        b.mul(k.mul(c)), k.mul(b.mul(c)),
    );

    // k*(a*d) - k*(b*c) ≡ k*(a*d - b*c)
    lemma_mul_distributes_over_sub::<R>(k, a.mul(d), b.mul(c));
    R::axiom_eqv_symmetric(
        k.mul(a.mul(d).sub(b.mul(c))),
        k.mul(a.mul(d)).sub(k.mul(b.mul(c))),
    );

    // Chain
    R::axiom_eqv_transitive(
        a.mul(k.mul(d)).sub(b.mul(k.mul(c))),
        k.mul(a.mul(d)).sub(k.mul(b.mul(c))),
        k.mul(a.mul(d).sub(b.mul(c))),
    );
}

} // verus!
