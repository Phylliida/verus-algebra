# verus-algebra — Implementation TODO

Formally verified algebraic trait hierarchy and lemma library in Rust + Verus.

This crate is the **abstract algebra foundation** for the entire verus-cad
stack. It defines traits (Ring, Field, OrderedRing, ...) and proves generic
lemmas that any concrete type can instantiate.

## Crate layering

```
verus-algebra              ← this crate (traits + lemmas)
  └→ verus-linalg          (Vec2, Vec3, Vec4, Mat3)
  └→ verus-geometry        (predicates: orientation, intersection)
  └→ verus-bigint          (implements Ring)
  └→ verus-rational        (implements OrderedField)
  └→ verus-interval-arithmetic (uses Ring/OrderedRing lemmas)
```

Every crate in the project depends on verus-algebra.

## What we have now

187 verified items, 0 errors, 0 assumes/admits.

### Trait hierarchy

```
Equivalence
  ├→ PartialOrder
  ├→ AdditiveCommutativeMonoid
  │    └→ AdditiveGroup
  │         └→ Ring
  │              ├→ OrderedRing  (Ring + PartialOrder + totality)
  │              └→ Field        (Ring + reciprocal)
  │                   └→ OrderedField  (OrderedRing + Field)
  └→ (used by all above)
```

### Lemma modules

| Module | Lemma count | Coverage |
|---|---|---|
| `additive_commutative_monoid_lemmas` | ~3 | zero-left, congruence |
| `partial_order_lemmas` | ~3 | congruence, eqv implies le |
| `additive_group_lemmas` | ~26 | inverses, cancellation, sub properties, neg, telescoping |
| `ring_lemmas` | ~15 | distributivity, negation*mul, square identities |
| `ordered_ring_lemmas` | ~35 | trichotomy, monotonicity, sign rules, square nonneg |
| `field_lemmas` | ~10 | reciprocal, cancellation, division distributes |
| `ordered_field_lemmas` | ~15 | sign of products, reciprocal ordering, div inequalities |

### Utility modules

| Module | Contents |
|---|---|
| `number_theory` | `divides` predicate + 7 lemmas (reflexive, transitive, add, mul, neg) |
| `min_max` | `min`, `max` specs + 25 lemmas (bounds, commutative, associative, sum, neg, add/mul compat, absorption) |
| `power` | `pow` spec + 17 lemmas (exponent rules, monotonicity, base rules, congruence) |
| `convex` | `two`, `midpoint`, `convex` specs + 12 lemmas (bounds, self, commutative, complement) |
| `inequalities` | `abs`, `signum` + 26 lemmas (triangle ineq, reverse triangle, AM-GM, Cauchy-Schwarz, sum-of-squares) |

---

## Phase 1 — Integral domain & zero-divisor properties

An integral domain is a commutative ring where `a * b ≡ 0` implies
`a ≡ 0 ∨ b ≡ 0`. This is important for cancellation in polynomials
and for ruling out degenerate cases in geometry.

- [ ] Define `IntegralDomain` trait extending `Ring`
      - Axiom: `a * b ≡ 0 → a ≡ 0 ∨ b ≡ 0` (no zero divisors)
- [ ] Lemma: every Field is an IntegralDomain
- [ ] Lemma: every OrderedRing is an IntegralDomain
      (proof: if a > 0 and b > 0 then a*b > 0 by nonneg_mul; similar for other sign combos)
- [ ] Lemma: cancellation law `a * b ≡ a * c ∧ a ≢ 0 → b ≡ c`
      (already have this for Field via division; IntegralDomain gives it without division)

---

## Phase 2 — GCD and Euclidean domains

Needed for: rational number normalization, polynomial GCD, exact arithmetic.

### 2.1 GCD predicate

```
spec fn is_gcd<R: IntegralDomain>(g: R, a: R, b: R) -> bool {
    divides(g, a) && divides(g, b)
    && forall|d: R| divides(d, a) && divides(d, b) ==> divides(d, g)
}
```

- [ ] Define `is_gcd` spec
- [ ] Lemma: GCD is unique up to unit (associate) equivalence
- [ ] Lemma: `is_gcd(a, a, 0)` — GCD with zero
- [ ] Lemma: `is_gcd(1, a, b)` when a, b are coprime
- [ ] Lemma: `is_gcd(g, a, b) → is_gcd(g, b, a)` — symmetry

### 2.2 Euclidean domain trait

```
trait EuclideanDomain: IntegralDomain {
    spec fn euclidean_norm(self) -> nat;
    spec fn euclidean_div(self, other: Self) -> Self;
    spec fn euclidean_rem(self, other: Self) -> Self;
    // axioms about norm decreasing, division + remainder identity
}
```

- [ ] Define `EuclideanDomain` trait
- [ ] Axiom: `a ≡ euclidean_div(a, b) * b + euclidean_rem(a, b)`
- [ ] Axiom: `euclidean_norm(euclidean_rem(a, b)) < euclidean_norm(b)` (when b ≢ 0)
- [ ] Lemma: Euclidean algorithm terminates (follows from norm decrease)
- [ ] Lemma: Euclidean algorithm computes GCD

### 2.3 Bezout's identity

- [ ] `spec fn bezout_coefficients<R: EuclideanDomain>(a, b) -> (R, R)`
- [ ] Lemma: `let (s, t) = bezout_coefficients(a, b); s*a + t*b ≡ gcd(a, b)`
- [ ] This is the extended Euclidean algorithm

---

## Phase 3 — Polynomial ring

Needed for: characteristic polynomials, algebraic curve representation,
resultants for intersection computation.

### 3.1 Polynomial type

```
pub struct Polynomial<T: Ring> {
    pub coeffs: Seq<T>,  // coeffs[i] is coefficient of x^i
}
```

- [ ] Define `Polynomial<T>` (ghost type for spec-level reasoning)
- [ ] `degree(p)` — highest index with nonzero coefficient
- [ ] `eval(p, x)` — evaluate polynomial at a point (Horner's method spec)
- [ ] `zero_poly()`, `one_poly()`, `monomial(c, n)` — constructors
- [ ] Implement `Equivalence`, `AdditiveGroup`, `Ring` for `Polynomial<T>`

### 3.2 Polynomial arithmetic lemmas

- [ ] Lemma: `degree(p + q) ≤ max(degree(p), degree(q))`
- [ ] Lemma: `degree(p * q) ≡ degree(p) + degree(q)` (when R is integral domain)
- [ ] Lemma: `eval(p + q, x) ≡ eval(p, x) + eval(q, x)`
- [ ] Lemma: `eval(p * q, x) ≡ eval(p, x) * eval(q, x)`
- [ ] Lemma: `eval(zero_poly, x) ≡ 0`

### 3.3 Polynomial division (when R is a Field)

- [ ] `poly_div(p, q)` — quotient
- [ ] `poly_rem(p, q)` — remainder
- [ ] Lemma: `p ≡ poly_div(p, q) * q + poly_rem(p, q)`
- [ ] Lemma: `degree(poly_rem(p, q)) < degree(q)`

### 3.4 Roots and factors

- [ ] `is_root(p, r)` — `eval(p, r) ≡ 0`
- [ ] Lemma: root implies linear factor `(x - r)` divides `p`
- [ ] Lemma: polynomial of degree n has at most n roots (over integral domain)
- [ ] `resultant(p, q)` — resultant of two polynomials (spec via Sylvester matrix det)
- [ ] Lemma: `resultant(p, q) ≡ 0` iff p and q share a common root

---

## Phase 4 — Module / vector space traits

Currently verus-linalg defines vector operations ad-hoc on Vec2/Vec3/Vec4.
A proper `Module` (or `VectorSpace`) trait would allow generic linear algebra.

### 4.1 Module trait

```
trait Module<R: Ring>: AdditiveGroup {
    spec fn scale(r: R, self) -> Self;
    // axioms: distributes over both additions, associative with ring mul, 1*v = v
}
```

- [ ] Define `Module` trait
- [ ] Axioms: `scale(r, a + b) ≡ scale(r, a) + scale(r, b)`
- [ ] Axioms: `scale(r + s, a) ≡ scale(r, a) + scale(s, a)`
- [ ] Axioms: `scale(r * s, a) ≡ scale(r, scale(s, a))`
- [ ] Axioms: `scale(1, a) ≡ a`
- [ ] Implement `Module<T>` for `Vec2<T>`, `Vec3<T>`, `Vec4<T>`

### 4.2 Inner product space trait

```
trait InnerProductSpace<R: OrderedField>: Module<R> {
    spec fn inner(self, other: Self) -> R;
    // axioms: symmetric, bilinear, positive-definite
}
```

- [ ] Define `InnerProductSpace` trait
- [ ] Axiom: `inner(a, b) ≡ inner(b, a)` (symmetry)
- [ ] Axiom: `inner(scale(r, a), b) ≡ r * inner(a, b)` (linearity)
- [ ] Axiom: `inner(a + b, c) ≡ inner(a, c) + inner(b, c)` (additivity)
- [ ] Axiom: `inner(a, a) ≥ 0` and `inner(a, a) ≡ 0 → a ≡ 0` (positive-definite)
- [ ] Implement for Vec2, Vec3, Vec4 (inner = dot)
- [ ] Lemma: Cauchy-Schwarz follows from axioms (already proven for concrete types,
      but having it at the trait level avoids re-proving per dimension)

### 4.3 Norm trait

```
trait NormedSpace<R: OrderedField>: InnerProductSpace<R> {
    spec fn norm_sq(self) -> R { inner(self, self) }
    // No square root needed — work with norm_sq everywhere
}
```

- [ ] Define `NormedSpace` (or just add `norm_sq` to `InnerProductSpace`)
- [ ] Lemma: `norm_sq(a) ≥ 0`
- [ ] Lemma: `norm_sq(scale(r, a)) ≡ r² * norm_sq(a)`
- [ ] Lemma: parallelogram law at trait level

---

## Phase 5 — Extended number theory

### 5.1 More divisibility lemmas

- [ ] Lemma: `divides(a, b) ∧ divides(a, c) → divides(a, b - c)`
- [ ] Lemma: `divides(a, b) → divides(a, scale(k, b))` (already have mul_right)
- [ ] Lemma: `divides(a, b) ∧ divides(b, a) → a and b are associates` (unit multiples)

### 5.2 Modular arithmetic

- [ ] `congruent_mod(a, b, m)` — `divides(m, a - b)`
- [ ] Lemma: congruence is an equivalence relation
- [ ] Lemma: congruence respects addition and multiplication
- [ ] Useful for: hash-based data structures, periodicity in patterns

### 5.3 Prime elements (in integral domains)

- [ ] `is_prime(p)` spec — p ≢ 0 and not a unit, and `divides(p, a*b) → divides(p, a) ∨ divides(p, b)`
- [ ] `is_irreducible(p)` spec — not a unit, and if p = a*b then a or b is a unit
- [ ] Lemma: in a PID, prime ↔ irreducible
- [ ] Probably not needed soon, but completes the algebra picture

---

## Phase 6 — Additional inequalities and analysis-adjacent lemmas

### 6.1 More classical inequalities

- [ ] Lemma: Cauchy-Schwarz for n terms (generalize from 2D)
- [ ] Lemma: Holder's inequality (generalization of Cauchy-Schwarz)
- [ ] Lemma: Minkowski inequality (triangle inequality for norms)
- [ ] Lemma: Power mean inequality

### 6.2 Absolute value extended

- [ ] Lemma: `abs(a / b) ≡ abs(a) / abs(b)` (for nonzero b, OrderedField)
- [ ] Lemma: `abs(pow(a, n)) ≡ pow(abs(a), n)`
- [ ] Lemma: `abs(a - b) ≡ 0 → a ≡ b`

### 6.3 Floor / ceiling (for ordered fields with integer subring)

This might be better as a separate trait or in a downstream crate.

- [ ] `floor(a)` — largest integer ≤ a
- [ ] `ceiling(a)` — smallest integer ≥ a
- [ ] Lemma: `floor(a) ≤ a < floor(a) + 1`
- [ ] Lemma: `ceiling(a) - 1 < a ≤ ceiling(a)`

---

## Phase 7 — Proof automation helpers

### 7.1 Tactic-like lemma combinators

Common proof patterns that come up repeatedly:

- [ ] `lemma_chain_eqv_3(a, b, c)` — a ≡ b ∧ b ≡ c → a ≡ c (just transitivity, but named for readability)
- [ ] `lemma_chain_eqv_4(a, b, c, d)` — 4-step transitivity
- [ ] `lemma_chain_le_eqv(a, b, c)` — a ≤ b ∧ b ≡ c → a ≤ c
- [ ] `lemma_chain_eqv_le(a, b, c)` — a ≡ b ∧ b ≤ c → a ≤ c
- [ ] These reduce boilerplate in downstream proofs

### 7.2 Witness constructors for existential lemmas

- [ ] Helper functions that produce the witness for `divides` from known divisibility
- [ ] Helper functions for `is_gcd` witness construction

---

## Proof strategy notes

### What's solid

The core hierarchy (Equivalence through OrderedField) and its lemma suite
are mature — 187 verified items with comprehensive coverage of the algebraic
properties that downstream crates actually use. The min_max, power, convex,
and inequalities modules are practical and well-proven.

### What's missing that downstream crates need

1. **IntegralDomain** — verus-bigint and verus-rational would benefit from
   cancellation laws without requiring Field.
2. **Module/VectorSpace** — verus-linalg currently re-proves the same scale
   lemmas for Vec2, Vec3, Vec4 separately. A trait would deduplicate.
3. **GCD** — verus-rational's normalization relies on GCD. Currently GCD is
   proven in verus-bigint directly. Lifting the spec to verus-algebra would
   let us state normalization properties generically.

### Difficulty estimates

| Item | Difficulty | Notes |
|---|---|---|
| IntegralDomain trait | Easy | One new axiom + a few lemmas |
| GCD predicate | Easy | Spec only, no algorithm |
| Euclidean domain | Medium | Need norm decrease axiom + termination |
| Bezout's identity | Medium | Extended Euclidean algorithm correctness |
| Polynomial type | Medium | Degree tracking is fiddly |
| Polynomial arithmetic | Medium-Hard | Convolution for mul, degree bounds |
| Polynomial division | Hard | Long division correctness |
| Resultant | Hard | Sylvester matrix determinant |
| Module trait | Easy | Just axioms + existing impl adaptation |
| InnerProductSpace | Easy-Medium | Axioms + Cauchy-Schwarz lift |
| Extended inequalities | Medium | Each is an independent proof |

---

## Trust surface

| Trusted | Why |
|---|---|
| `vstd` | Verus standard library |
| Trait axioms | Assumed sound — match standard math definitions |

The axioms (e.g., ring axioms, field axioms) are the TCB. They're standard
textbook definitions — if they're wrong, the math is wrong. Everything else
is proven from these axioms.

---

## Milestones

| Milestone | Phases | What it enables |
|---|---|---|
| **M1: IntegralDomain** | 1 | Cancellation without division, zero-divisor freedom |
| **M2: GCD + Euclidean** | 2 | Generic normalization, rational simplification |
| **M3: Polynomials** | 3 | Algebraic curves, resultants for intersection |
| **M4: Module/VectorSpace** | 4 | Generic linear algebra, deduplicate verus-linalg |
| **M5: Extended number theory** | 5 | Modular arithmetic, primes |
| **M6: Proof helpers** | 7 | Reduce boilerplate across all downstream crates |

**M1 is quick and immediately useful.** M2 matters once rational normalization
is formalized generically. M3 is a bigger project but essential for algebraic
geometry in the BREP kernel. M4 improves the architecture but doesn't unblock
anything critical.
