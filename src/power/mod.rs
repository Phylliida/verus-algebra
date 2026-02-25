use vstd::prelude::*;
use crate::traits::ring::Ring;
use crate::traits::ordered_ring::OrderedRing;
use crate::traits::field::OrderedField;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;
use crate::lemmas::ordered_field_lemmas::*;

verus! {

/// Power function: base^exp.
pub open spec fn pow<R: Ring>(base: R, exp: nat) -> R
    decreases exp,
{
    if exp == 0 { R::one() }
    else { base.mul(pow::<R>(base, (exp - 1) as nat)) }
}

/// pow(a, 0) ≡ 1.
pub proof fn lemma_pow_zero<R: Ring>(a: R)
    ensures
        pow::<R>(a, 0).eqv(R::one()),
{
    R::axiom_eqv_reflexive(R::one());
}

/// pow(a, 1) ≡ a.
pub proof fn lemma_pow_one<R: Ring>(a: R)
    ensures
        pow::<R>(a, 1).eqv(a),
{
    // pow(a, 1) ≡ a * pow(a, 0) [by succ, which is structural]
    // pow(a, 0) ≡ 1
    lemma_pow_zero::<R>(a);
    // a * pow(a, 0) ≡ a * 1
    lemma_mul_congruence_right::<R>(a, pow::<R>(a, 0), R::one());
    // a * 1 ≡ a
    R::axiom_mul_one_right(a);
    // Chain: pow(a,1) = a*pow(a,0) ≡ a*1 ≡ a
    R::axiom_eqv_transitive(a.mul(pow::<R>(a, 0)), a.mul(R::one()), a);
}

/// pow(a, 2) ≡ a * a.
pub proof fn lemma_pow_two<R: Ring>(a: R)
    ensures
        pow::<R>(a, 2).eqv(a.mul(a)),
{
    // pow(a, 2) = a * pow(a, 1)
    // pow(a, 1) ≡ a
    lemma_pow_one::<R>(a);
    // a * pow(a, 1) ≡ a * a
    lemma_mul_congruence_right::<R>(a, pow::<R>(a, 1), a);
}

/// pow(a, n+1) ≡ a * pow(a, n).
pub proof fn lemma_pow_succ<R: Ring>(a: R, n: nat)
    ensures
        pow::<R>(a, n + 1).eqv(a.mul(pow::<R>(a, n))),
{
    R::axiom_eqv_reflexive(a.mul(pow::<R>(a, n)));
}

/// pow(1, n) ≡ 1.
pub proof fn lemma_one_pow<R: Ring>(n: nat)
    ensures
        pow::<R>(R::one(), n).eqv(R::one()),
    decreases n,
{
    if n == 0 {
        R::axiom_eqv_reflexive(R::one());
    } else {
        // pow(1, n) = 1 * pow(1, n-1)
        lemma_one_pow::<R>((n - 1) as nat);
        // pow(1, n-1) ≡ 1, so 1 * pow(1, n-1) ≡ 1 * 1
        lemma_mul_congruence_right::<R>(R::one(), pow::<R>(R::one(), (n - 1) as nat), R::one());
        // 1 * 1 ≡ 1
        R::axiom_mul_one_right(R::one());
        R::axiom_eqv_transitive(
            R::one().mul(pow::<R>(R::one(), (n - 1) as nat)),
            R::one().mul(R::one()),
            R::one(),
        );
    }
}

/// n > 0 implies pow(0, n) ≡ 0.
pub proof fn lemma_zero_pow<R: Ring>(n: nat)
    requires
        n > 0,
    ensures
        pow::<R>(R::zero(), n).eqv(R::zero()),
    decreases n,
{
    // pow(0, n) = 0 * pow(0, n-1), 0 * x ≡ 0
    lemma_mul_zero_left::<R>(pow::<R>(R::zero(), (n - 1) as nat));
}

/// pow(a, m + n) ≡ pow(a, m) * pow(a, n).
pub proof fn lemma_pow_add<R: Ring>(a: R, m: nat, n: nat)
    ensures
        pow::<R>(a, m + n).eqv(pow::<R>(a, m).mul(pow::<R>(a, n))),
    decreases m,
{
    if m == 0 {
        // pow(a, n) and 1 * pow(a, n) ≡ pow(a, n)
        lemma_mul_one_left::<R>(pow::<R>(a, n));
        R::axiom_eqv_symmetric(R::one().mul(pow::<R>(a, n)), pow::<R>(a, n));
    } else {
        // pow(a, m+n) = a * pow(a, (m-1)+n)
        // IH: pow(a, (m-1)+n) ≡ pow(a, m-1) * pow(a, n)
        lemma_pow_add::<R>(a, (m - 1) as nat, n);
        // a * pow(a, (m-1)+n) ≡ a * (pow(a, m-1) * pow(a, n))
        lemma_mul_congruence_right::<R>(
            a,
            pow::<R>(a, ((m - 1) as nat) + n),
            pow::<R>(a, (m - 1) as nat).mul(pow::<R>(a, n)),
        );
        // a * (pow(a, m-1) * pow(a, n)) ≡ (a * pow(a, m-1)) * pow(a, n) [assoc, reversed]
        R::axiom_mul_associative(a, pow::<R>(a, (m - 1) as nat), pow::<R>(a, n));
        R::axiom_eqv_symmetric(
            a.mul(pow::<R>(a, (m - 1) as nat).mul(pow::<R>(a, n))),
            a.mul(pow::<R>(a, (m - 1) as nat)).mul(pow::<R>(a, n)),
        );
        // Chain
        R::axiom_eqv_transitive(
            a.mul(pow::<R>(a, ((m - 1) as nat) + n)),
            a.mul(pow::<R>(a, (m - 1) as nat).mul(pow::<R>(a, n))),
            a.mul(pow::<R>(a, (m - 1) as nat)).mul(pow::<R>(a, n)),
        );
    }
}

/// pow(a, m * n) ≡ pow(pow(a, m), n).
pub proof fn lemma_pow_mul<R: Ring>(a: R, m: nat, n: nat)
    ensures
        pow::<R>(a, m * n).eqv(pow::<R>(pow::<R>(a, m), n)),
    decreases n,
{
    if n == 0 {
        R::axiom_eqv_reflexive(R::one());
    } else {
        // IH: pow(a, m*(n-1)) ≡ pow(pow(a,m), n-1)
        lemma_pow_mul::<R>(a, m, (n - 1) as nat);
        // pow(a, m + m*(n-1)) ≡ pow(a,m) * pow(a, m*(n-1))
        lemma_pow_add::<R>(a, m, m * ((n - 1) as nat));
        let n1: nat = (n - 1) as nat;
        assert(m + m * n1 == m * n) by(nonlinear_arith)
            requires n == n1 + 1
        ;
        // pow(a,m) * pow(a, m*(n-1)) ≡ pow(a,m) * pow(pow(a,m), n-1)
        lemma_mul_congruence_right::<R>(
            pow::<R>(a, m),
            pow::<R>(a, m * ((n - 1) as nat)),
            pow::<R>(pow::<R>(a, m), (n - 1) as nat),
        );
        // Chain: pow(a, m*n) ≡ pow(a,m) * pow(a,m*(n-1)) ≡ pow(a,m) * pow(pow(a,m), n-1)
        R::axiom_eqv_transitive(
            pow::<R>(a, m * n),
            pow::<R>(a, m).mul(pow::<R>(a, m * ((n - 1) as nat))),
            pow::<R>(a, m).mul(pow::<R>(pow::<R>(a, m), (n - 1) as nat)),
        );
    }
}

/// 0 ≤ a implies 0 ≤ pow(a, n).
pub proof fn lemma_pow_nonneg<R: OrderedRing>(a: R, n: nat)
    requires
        R::zero().le(a),
    ensures
        R::zero().le(pow::<R>(a, n)),
    decreases n,
{
    if n == 0 {
        // pow(a, 0) = 1, 0 < 1 implies 0 ≤ 1
        lemma_zero_lt_one::<R>();
        R::axiom_lt_iff_le_and_not_eqv(R::zero(), R::one());
    } else {
        lemma_pow_nonneg::<R>(a, (n - 1) as nat);
        lemma_nonneg_mul_nonneg::<R>(a, pow::<R>(a, (n - 1) as nat));
    }
}

/// 0 ≤ a ≤ b implies pow(a, n) ≤ pow(b, n).
pub proof fn lemma_pow_monotone<R: OrderedRing>(a: R, b: R, n: nat)
    requires
        R::zero().le(a),
        a.le(b),
    ensures
        pow::<R>(a, n).le(pow::<R>(b, n)),
    decreases n,
{
    if n == 0 {
        R::axiom_le_reflexive(R::one());
    } else {
        // IH: pow(a, n-1) ≤ pow(b, n-1)
        lemma_pow_monotone::<R>(a, b, (n - 1) as nat);
        lemma_pow_nonneg::<R>(a, (n - 1) as nat);
        R::axiom_le_transitive(R::zero(), a, b);
        lemma_pow_nonneg::<R>(b, (n - 1) as nat);

        // Step 1: a * pow(a,n-1) ≤ a * pow(b,n-1)
        // axiom: pow(a,n-1) ≤ pow(b,n-1) and 0 ≤ a → pow(a,n-1)*a ≤ pow(b,n-1)*a
        R::axiom_le_mul_nonneg_monotone(
            pow::<R>(a, (n - 1) as nat),
            pow::<R>(b, (n - 1) as nat),
            a,
        );
        // Commute: pow(a,n-1)*a → a*pow(a,n-1) and pow(b,n-1)*a → a*pow(b,n-1)
        R::axiom_mul_commutative(pow::<R>(a, (n - 1) as nat), a);
        R::axiom_mul_commutative(pow::<R>(b, (n - 1) as nat), a);
        R::axiom_eqv_symmetric(a.mul(pow::<R>(a, (n - 1) as nat)), pow::<R>(a, (n - 1) as nat).mul(a));
        R::axiom_eqv_symmetric(a.mul(pow::<R>(b, (n - 1) as nat)), pow::<R>(b, (n - 1) as nat).mul(a));
        R::axiom_le_congruence(
            pow::<R>(a, (n - 1) as nat).mul(a),
            a.mul(pow::<R>(a, (n - 1) as nat)),
            pow::<R>(b, (n - 1) as nat).mul(a),
            a.mul(pow::<R>(b, (n - 1) as nat)),
        );

        // Step 2: a * pow(b,n-1) ≤ b * pow(b,n-1)
        // axiom: a ≤ b and 0 ≤ pow(b,n-1) → a*pow(b,n-1) ≤ b*pow(b,n-1)
        R::axiom_le_mul_nonneg_monotone(a, b, pow::<R>(b, (n - 1) as nat));

        // Transitivity: a*pow(a,n-1) ≤ a*pow(b,n-1) ≤ b*pow(b,n-1)
        R::axiom_le_transitive(
            a.mul(pow::<R>(a, (n - 1) as nat)),
            a.mul(pow::<R>(b, (n - 1) as nat)),
            b.mul(pow::<R>(b, (n - 1) as nat)),
        );
    }
}

/// a ≡ b implies pow(a, n) ≡ pow(b, n).
pub proof fn lemma_pow_eqv<R: Ring>(a: R, b: R, n: nat)
    requires
        a.eqv(b),
    ensures
        pow::<R>(a, n).eqv(pow::<R>(b, n)),
    decreases n,
{
    if n == 0 {
        R::axiom_eqv_reflexive(R::one());
    } else {
        // IH: pow(a, n-1) ≡ pow(b, n-1)
        lemma_pow_eqv::<R>(a, b, (n - 1) as nat);
        // a ≡ b and pow(a,n-1) ≡ pow(b,n-1)
        // a * pow(a,n-1) ≡ b * pow(b,n-1) [mul_congruence]
        lemma_mul_congruence::<R>(a, b, pow::<R>(a, (n - 1) as nat), pow::<R>(b, (n - 1) as nat));
    }
}

/// 0 < a implies 0 < pow(a, n) (for OrderedField).
pub proof fn lemma_pow_pos<F: OrderedField>(a: F, n: nat)
    requires
        F::zero().lt(a),
    ensures
        F::zero().lt(pow::<F>(a, n)),
    decreases n,
{
    if n == 0 {
        // pow(a, 0) = 1, 0 < 1
        lemma_zero_lt_one::<F>();
    } else {
        // IH: 0 < pow(a, n-1)
        lemma_pow_pos::<F>(a, (n - 1) as nat);
        // 0 < a and 0 < pow(a, n-1) → 0 < a * pow(a, n-1)
        lemma_mul_pos_pos::<F>(a, pow::<F>(a, (n - 1) as nat));
    }
}

/// pow(a*b, n) ≡ pow(a, n) * pow(b, n).
pub proof fn lemma_pow_mul_base<R: Ring>(a: R, b: R, n: nat)
    ensures
        pow::<R>(a.mul(b), n).eqv(pow::<R>(a, n).mul(pow::<R>(b, n))),
    decreases n,
{
    if n == 0 {
        // pow(a*b, 0) = 1, pow(a,0)*pow(b,0) = 1*1 ≡ 1
        R::axiom_mul_one_right(R::one());
        R::axiom_eqv_symmetric(R::one().mul(R::one()), R::one());
    } else {
        // pow(a*b, n) = (a*b) * pow(a*b, n-1)
        // IH: pow(a*b, n-1) ≡ pow(a,n-1)*pow(b,n-1)
        lemma_pow_mul_base::<R>(a, b, (n - 1) as nat);

        // (a*b)*pow(a*b,n-1) ≡ (a*b)*(pow(a,n-1)*pow(b,n-1))
        lemma_mul_congruence_right::<R>(
            a.mul(b),
            pow::<R>(a.mul(b), (n - 1) as nat),
            pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat)),
        );

        // (a*b)*(pow(a,n-1)*pow(b,n-1))
        // ≡ a*(b*(pow(a,n-1)*pow(b,n-1)))    [assoc]
        R::axiom_mul_associative(a, b, pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat)));
        R::axiom_eqv_transitive(
            a.mul(b).mul(pow::<R>(a.mul(b), (n - 1) as nat)),
            a.mul(b).mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat))),
            a.mul(b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat)))),
        );

        // b*(pow(a,n-1)*pow(b,n-1))
        // ≡ (b*pow(a,n-1))*pow(b,n-1)    [assoc reversed]
        R::axiom_mul_associative(b, pow::<R>(a, (n - 1) as nat), pow::<R>(b, (n - 1) as nat));
        R::axiom_eqv_symmetric(
            b.mul(pow::<R>(a, (n - 1) as nat)).mul(pow::<R>(b, (n - 1) as nat)),
            b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat))),
        );
        // b*pow(a,n-1) ≡ pow(a,n-1)*b     [comm]
        R::axiom_mul_commutative(b, pow::<R>(a, (n - 1) as nat));
        // (b*pow(a,n-1))*pow(b,n-1) ≡ (pow(a,n-1)*b)*pow(b,n-1)
        R::axiom_mul_congruence_left(
            b.mul(pow::<R>(a, (n - 1) as nat)),
            pow::<R>(a, (n - 1) as nat).mul(b),
            pow::<R>(b, (n - 1) as nat),
        );
        // (pow(a,n-1)*b)*pow(b,n-1) ≡ pow(a,n-1)*(b*pow(b,n-1))   [assoc]
        R::axiom_mul_associative(pow::<R>(a, (n - 1) as nat), b, pow::<R>(b, (n - 1) as nat));

        // Chain: b*(pow(a,n-1)*pow(b,n-1)) ≡ (b*pow(a,n-1))*pow(b,n-1)
        //        ≡ (pow(a,n-1)*b)*pow(b,n-1) ≡ pow(a,n-1)*(b*pow(b,n-1))
        R::axiom_eqv_transitive(
            b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat))),
            b.mul(pow::<R>(a, (n - 1) as nat)).mul(pow::<R>(b, (n - 1) as nat)),
            pow::<R>(a, (n - 1) as nat).mul(b).mul(pow::<R>(b, (n - 1) as nat)),
        );
        R::axiom_eqv_transitive(
            b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat))),
            pow::<R>(a, (n - 1) as nat).mul(b).mul(pow::<R>(b, (n - 1) as nat)),
            pow::<R>(a, (n - 1) as nat).mul(b.mul(pow::<R>(b, (n - 1) as nat))),
        );

        // a*(b*(pow(a,n-1)*pow(b,n-1))) ≡ a*(pow(a,n-1)*(b*pow(b,n-1)))
        lemma_mul_congruence_right::<R>(
            a,
            b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat))),
            pow::<R>(a, (n - 1) as nat).mul(b.mul(pow::<R>(b, (n - 1) as nat))),
        );
        R::axiom_eqv_transitive(
            a.mul(b).mul(pow::<R>(a.mul(b), (n - 1) as nat)),
            a.mul(b.mul(pow::<R>(a, (n - 1) as nat).mul(pow::<R>(b, (n - 1) as nat)))),
            a.mul(pow::<R>(a, (n - 1) as nat).mul(b.mul(pow::<R>(b, (n - 1) as nat)))),
        );

        // a*(pow(a,n-1)*(b*pow(b,n-1))) ≡ (a*pow(a,n-1))*(b*pow(b,n-1))   [assoc reversed]
        R::axiom_mul_associative(a, pow::<R>(a, (n - 1) as nat), b.mul(pow::<R>(b, (n - 1) as nat)));
        R::axiom_eqv_symmetric(
            a.mul(pow::<R>(a, (n - 1) as nat)).mul(b.mul(pow::<R>(b, (n - 1) as nat))),
            a.mul(pow::<R>(a, (n - 1) as nat).mul(b.mul(pow::<R>(b, (n - 1) as nat)))),
        );
        R::axiom_eqv_transitive(
            a.mul(b).mul(pow::<R>(a.mul(b), (n - 1) as nat)),
            a.mul(pow::<R>(a, (n - 1) as nat).mul(b.mul(pow::<R>(b, (n - 1) as nat)))),
            a.mul(pow::<R>(a, (n - 1) as nat)).mul(b.mul(pow::<R>(b, (n - 1) as nat))),
        );
        // pow(a,n) = a*pow(a,n-1) and pow(b,n) = b*pow(b,n-1) — these are definitional equalities
    }
}

/// pow((-1), 2*n) ≡ 1.
pub proof fn lemma_pow_neg_one_even<R: Ring>(n: nat)
    ensures
        pow::<R>(R::one().neg(), 2 * n).eqv(R::one()),
    decreases n,
{
    if n == 0 {
        R::axiom_eqv_reflexive(R::one());
    } else {
        // IH: pow(-1, 2*(n-1)) ≡ 1
        lemma_pow_neg_one_even::<R>((n - 1) as nat);
        let n1: nat = (n - 1) as nat;
        // 2*n = 2 + 2*n1
        assert(2 * n == 2 + 2 * n1) by(nonlinear_arith)
            requires n == n1 + 1
        ;
        // pow(-1, 2+2*n1) ≡ pow(-1,2) * pow(-1, 2*n1)  [pow_add]
        lemma_pow_add::<R>(R::one().neg(), 2, 2 * n1);
        // pow(-1, 2) ≡ (-1)*(-1)
        lemma_pow_two::<R>(R::one().neg());
        // (-1)*(-1) ≡ 1*1  [neg_mul_neg]
        lemma_neg_mul_neg::<R>(R::one(), R::one());
        // 1*1 ≡ 1
        R::axiom_mul_one_right(R::one());
        // pow(-1,2) ≡ (-1)*(-1) ≡ 1*1 ≡ 1
        R::axiom_eqv_transitive(
            pow::<R>(R::one().neg(), 2),
            R::one().neg().mul(R::one().neg()),
            R::one().mul(R::one()),
        );
        R::axiom_eqv_transitive(
            pow::<R>(R::one().neg(), 2),
            R::one().mul(R::one()),
            R::one(),
        );
        // pow(-1,2) * pow(-1, 2*n1) ≡ 1 * 1 ≡ 1
        lemma_mul_congruence::<R>(
            pow::<R>(R::one().neg(), 2), R::one(),
            pow::<R>(R::one().neg(), 2 * n1), R::one(),
        );
        R::axiom_eqv_transitive(
            pow::<R>(R::one().neg(), 2 * n),
            pow::<R>(R::one().neg(), 2).mul(pow::<R>(R::one().neg(), 2 * n1)),
            R::one().mul(R::one()),
        );
        R::axiom_eqv_transitive(
            pow::<R>(R::one().neg(), 2 * n),
            R::one().mul(R::one()),
            R::one(),
        );
    }
}

} // verus!
