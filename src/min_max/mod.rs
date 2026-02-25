use vstd::prelude::*;
use crate::traits::ordered_ring::OrderedRing;
use crate::lemmas::additive_group_lemmas::*;
use crate::lemmas::ring_lemmas::*;
use crate::lemmas::ordered_ring_lemmas::*;

verus! {

/// Minimum of two elements.
pub open spec fn min<R: OrderedRing>(a: R, b: R) -> R {
    if a.le(b) { a } else { b }
}

/// Maximum of two elements.
pub open spec fn max<R: OrderedRing>(a: R, b: R) -> R {
    if a.le(b) { b } else { a }
}

/// min(a, b) ≤ a.
pub proof fn lemma_min_le_left<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(a),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, need a ≤ a
        R::axiom_le_reflexive(a);
    } else {
        // min = b, and b ≤ a from totality
    }
}

/// min(a, b) ≤ b.
pub proof fn lemma_min_le_right<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(b),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, a ≤ b given
    } else {
        // min = b, need b ≤ b
        R::axiom_le_reflexive(b);
    }
}

/// a ≤ max(a, b).
pub proof fn lemma_max_ge_left<R: OrderedRing>(a: R, b: R)
    ensures
        a.le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // max = b, a ≤ b given
    } else {
        // max = a, need a ≤ a
        R::axiom_le_reflexive(a);
    }
}

/// b ≤ max(a, b).
pub proof fn lemma_max_ge_right<R: OrderedRing>(a: R, b: R)
    ensures
        b.le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // max = b, need b ≤ b
        R::axiom_le_reflexive(b);
    } else {
        // max = a, and b ≤ a from totality
    }
}

/// min(a, b) ≡ min(b, a).
pub proof fn lemma_min_commutative<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).eqv(min::<R>(b, a)),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, a);

    if a.le(b) && b.le(a) {
        // min(a,b) = a, min(b,a) = b, and a ≡ b by antisymmetry
        R::axiom_le_antisymmetric(a, b);
    } else if a.le(b) && !b.le(a) {
        // min(a,b) = a, min(b,a) = a (since ¬(b≤a), b is not min)
        R::axiom_eqv_reflexive(a);
    } else if !a.le(b) && b.le(a) {
        // min(a,b) = b, min(b,a) = b
        R::axiom_eqv_reflexive(b);
    } else {
        // Impossible by totality, but if both fail:
        R::axiom_eqv_reflexive(a);
    }
}

/// max(a, b) ≡ max(b, a).
pub proof fn lemma_max_commutative<R: OrderedRing>(a: R, b: R)
    ensures
        max::<R>(a, b).eqv(max::<R>(b, a)),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, a);

    if a.le(b) && b.le(a) {
        // max(a,b) = b, max(b,a) = a, and a ≡ b
        R::axiom_le_antisymmetric(a, b);
        R::axiom_eqv_symmetric(a, b);
    } else if a.le(b) && !b.le(a) {
        // max(a,b) = b, max(b,a) = b
        R::axiom_eqv_reflexive(b);
    } else if !a.le(b) && b.le(a) {
        // max(a,b) = a, max(b,a) = a
        R::axiom_eqv_reflexive(a);
    } else {
        R::axiom_eqv_reflexive(a);
    }
}

/// min(a, b) ≤ max(a, b).
pub proof fn lemma_min_le_max<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).le(max::<R>(a, b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, max = b, a ≤ b given
    } else {
        // min = b, max = a, b ≤ a from totality
    }
}

/// min(a, b) + max(a, b) ≡ a + b.
pub proof fn lemma_min_max_sum<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).add(max::<R>(a, b)).eqv(a.add(b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a, max = b, a + b ≡ a + b
        R::axiom_eqv_reflexive(a.add(b));
    } else {
        // min = b, max = a, b + a ≡ a + b
        R::axiom_add_commutative(b, a);
        R::axiom_eqv_symmetric(a.add(b), b.add(a));
    }
}

/// min(a, a) ≡ a.
pub proof fn lemma_min_self<R: OrderedRing>(a: R)
    ensures
        min::<R>(a, a).eqv(a),
{
    R::axiom_le_reflexive(a);
    R::axiom_eqv_reflexive(a);
}

/// max(a, a) ≡ a.
pub proof fn lemma_max_self<R: OrderedRing>(a: R)
    ensures
        max::<R>(a, a).eqv(a),
{
    R::axiom_le_reflexive(a);
    R::axiom_eqv_reflexive(a);
}

/// min(min(a,b),c) ≡ min(a,min(b,c)).
pub proof fn lemma_min_associative<R: OrderedRing>(a: R, b: R, c: R)
    ensures
        min::<R>(min::<R>(a, b), c).eqv(min::<R>(a, min::<R>(b, c))),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, c);
    R::axiom_le_total(a, c);

    if a.le(b) && b.le(c) {
        // min(a,b)=a, min(b,c)=b, min(a,c)=a
        // LHS = min(a,c) = a (since a≤c by transitivity)
        R::axiom_le_transitive(a, b, c);
        // RHS = min(a,b) = a
        R::axiom_eqv_reflexive(a);
    } else if a.le(b) && !b.le(c) {
        // min(a,b)=a, min(b,c)=c
        // LHS = min(a,c)
        // Need to show min(a,c) ≡ min(a,c) — trivially
        R::axiom_le_total(a, c);
        if a.le(c) {
            // LHS=a, RHS=min(a,c)=a
            R::axiom_eqv_reflexive(a);
        } else {
            // c < b and c < a: LHS=c, RHS=min(a,c)=c
            R::axiom_eqv_reflexive(c);
        }
    } else if !a.le(b) && b.le(c) {
        // min(a,b)=b, min(b,c)=b
        // LHS = min(b,c) = b (since b≤c)
        // RHS = min(a,b) = b (since ¬(a≤b) means b < a)
        R::axiom_eqv_reflexive(b);
    } else {
        // ¬(a≤b) and ¬(b≤c): b < a and c < b
        // min(a,b)=b, min(b,c)=c
        // LHS = min(b,c) = c (since ¬(b≤c))
        // RHS = min(a,c)
        // c < b < a, so c < a, so ¬(a≤c) [from totality]
        R::axiom_le_total(a, c);
        if a.le(c) {
            // a≤c and c<b<a contradicts. c<b (from totality), b<a (from totality)
            // c≤a from a.le(c), so we need to handle
            // Actually b.le(a) since ¬(a.le(b)), and c.le(b) since ¬(b.le(c))
            // c ≤ b ≤ a, and a ≤ c, so a ≡ c
            R::axiom_le_transitive(c, b, a);
            R::axiom_le_antisymmetric(a, c);
            // RHS = min(a,c) = a ≡ c
            R::axiom_eqv_symmetric(a, c);
        } else {
            // RHS = min(a,c) = c
            R::axiom_eqv_reflexive(c);
        }
    }
}

/// max(max(a,b),c) ≡ max(a,max(b,c)).
pub proof fn lemma_max_associative<R: OrderedRing>(a: R, b: R, c: R)
    ensures
        max::<R>(max::<R>(a, b), c).eqv(max::<R>(a, max::<R>(b, c))),
{
    R::axiom_le_total(a, b);
    R::axiom_le_total(b, c);
    R::axiom_le_total(a, c);

    if a.le(b) && b.le(c) {
        // max(a,b)=b, max(b,c)=c
        // LHS = max(b,c) = c
        // RHS = max(a,c) = c (since a≤c by transitivity)
        R::axiom_le_transitive(a, b, c);
        R::axiom_eqv_reflexive(c);
    } else if a.le(b) && !b.le(c) {
        // max(a,b)=b, max(b,c)=b
        // LHS = max(b,c) = b (since ¬(b≤c))
        // RHS = max(a,b) = b
        R::axiom_eqv_reflexive(b);
    } else if !a.le(b) && b.le(c) {
        // max(a,b)=a, max(b,c)=c
        // LHS = max(a,c)
        R::axiom_le_total(a, c);
        if a.le(c) {
            // LHS=c, RHS=max(a,c)=c
            R::axiom_eqv_reflexive(c);
        } else {
            // LHS=a, RHS=max(a,c)=a
            R::axiom_eqv_reflexive(a);
        }
    } else {
        // ¬(a≤b) and ¬(b≤c): b < a and c < b
        // max(a,b)=a, max(b,c)=b
        // LHS = max(a,c): since c<b<a, c<a, so max(a,c)=a
        // RHS = max(a,b) = a
        R::axiom_le_total(a, c);
        if a.le(c) {
            R::axiom_le_transitive(c, b, a);
            R::axiom_le_antisymmetric(a, c);
            R::axiom_eqv_symmetric(a, c);
        } else {
            R::axiom_eqv_reflexive(a);
        }
    }
}

/// min(a,b) ≤ c if and only if a ≤ c or b ≤ c.
pub proof fn lemma_min_le_iff<R: OrderedRing>(a: R, b: R, c: R)
    ensures
        min::<R>(a, b).le(c) == (a.le(c) || b.le(c)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min = a
        if a.le(c) {
            // a ≤ c, LHS ✓, RHS ✓ (a ≤ c)
        }
        // If RHS: a ≤ c ⟹ min=a ≤ c. b ≤ c ⟹ a ≤ b ≤ c, so a ≤ c.
        if b.le(c) {
            R::axiom_le_transitive(a, b, c);
        }
    } else {
        // min = b, and b ≤ a
        if b.le(c) {
            // b ≤ c, LHS ✓, RHS ✓ (b ≤ c)
        }
        if a.le(c) {
            // b ≤ a ≤ c
            R::axiom_le_transitive(b, a, c);
        }
    }
}

/// c ≤ max(a,b) if and only if c ≤ a or c ≤ b.
pub proof fn lemma_max_le_iff<R: OrderedRing>(a: R, b: R, c: R)
    ensures
        c.le(max::<R>(a, b)) == (c.le(a) || c.le(b)),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // max = b
        if c.le(b) {
            // c ≤ b, LHS ✓, RHS ✓ (c ≤ b)
        }
        if c.le(a) {
            R::axiom_le_transitive(c, a, b);
        }
    } else {
        // max = a, and a > b so b ≤ a
        if c.le(a) {
            // c ≤ a, LHS ✓, RHS ✓ (c ≤ a)
        }
        if c.le(b) {
            // b ≤ a, so c ≤ b ≤ a
            R::axiom_le_transitive(c, b, a);
        }
    }
}

/// min(a,b).neg() ≡ max(a.neg(), b.neg()).
pub proof fn lemma_min_neg<R: OrderedRing>(a: R, b: R)
    ensures
        min::<R>(a, b).neg().eqv(max::<R>(a.neg(), b.neg())),
{
    R::axiom_le_total(a, b);
    if a.le(b) {
        // min(a,b) = a, so LHS = -a
        // Need: -a = max(-a, -b)
        // a ≤ b → -b ≤ -a, so max(-a,-b) = -a (since -a ≥ -b)
        lemma_le_neg_flip::<R>(a, b);
        // -b ≤ -a, so for max(-a,-b): need ¬(-a ≤ -b) or -a ≤ -b
        R::axiom_le_total(a.neg(), b.neg());
        if a.neg().le(b.neg()) {
            // max(-a,-b) = -b, and -b ≤ -a and -a ≤ -b, so -a ≡ -b
            R::axiom_le_antisymmetric(a.neg(), b.neg());
            R::axiom_eqv_symmetric(a.neg(), b.neg());
        } else {
            // max(-a,-b) = -a
            R::axiom_eqv_reflexive(a.neg());
        }
    } else {
        // min(a,b) = b, so LHS = -b
        // ¬(a ≤ b), so b ≤ a (totality). -a ≤ -b.
        lemma_le_neg_flip::<R>(b, a);
        // -a ≤ -b, so max(-a,-b) = -b
        R::axiom_le_total(a.neg(), b.neg());
        if a.neg().le(b.neg()) {
            // max = -b
            R::axiom_eqv_reflexive(b.neg());
        } else {
            // ¬(-a ≤ -b), max = -a, but -a ≤ -b, contradiction handled:
            // Actually if ¬(-a ≤ -b), that means -b < -a, but we proved -a ≤ -b
            // So -a ≡ -b
            R::axiom_le_antisymmetric(a.neg(), b.neg());
        }
    }
}

} // verus!
