# verus-algebra TODO

## Current state

26 verified lemmas, 0 errors, 0 `assume()` calls.

### Traits defined
- **Equivalence** — `eqv` + reflexive/symmetric/transitive (3 axioms)
- **AdditiveGroup** — `zero`/`add`/`neg`/`sub` + group axioms + congruence (7 axioms)
- **Ring** — `one`/`mul` + commutativity/associativity/distributivity + congruence (6 axioms)
- **OrderedRing** — `le`/`lt` + total order + monotonicity + congruence (8 axioms)
- **Field** — `recip`/`div` + inverse + congruence (3 axioms)
- **OrderedField** — marker trait (OrderedRing + Field)

### Derived lemmas proven
- **AdditiveGroup (8):** `add_zero_left`, `add_inverse_left`, `add_congruence_right`, `add_congruence`, `add_right_cancel`, `add_left_cancel`, `neg_involution`, `neg_zero`
- **Ring (9):** `mul_one_left`, `mul_zero_left`, `mul_distributes_right`, `mul_congruence_right`, `mul_congruence`, `mul_neg_one`, `mul_neg_right`, `mul_neg_left`, `neg_mul_neg`
- **OrderedRing (7):** `lt_irreflexive`, `lt_asymmetric`, `lt_transitive`, `le_add_compatible`, `lt_add_compatible`, `nonneg_mul_nonneg`, `square_nonneg`
- **Field (2):** `mul_recip_left`, `div_self`

---

## Missing derived lemmas

### AdditiveGroup lemmas

From VerusCAD `scalar.rs` and `verus-rational`:

- [ ] `lemma_sub_antisymmetric(a, b)` — `a - b ≡ -(b - a)`
- [ ] `lemma_neg_add(a, b)` — `-(a + b) ≡ (-a) + (-b)`
- [ ] `lemma_sub_congruence(a1, a2, b1, b2)` — full subtraction congruence
- [ ] `lemma_add_then_sub_cancel(a, b)` — `(a + b) - b ≡ a`
- [ ] `lemma_sub_then_add_cancel(a, b)` — `(a - b) + b ≡ a`
- [ ] `lemma_sub_eqv_zero_iff_eqv(a, b)` — `a - b ≡ 0 ⟺ a ≡ b`
- [ ] `lemma_sub_neg_both(a, b)` — `(-a) - (-b) ≡ b - a`
- [ ] `lemma_sub_add_distributes(a, b, c, d)` — `(a - b) + (c - d) ≡ (a + c) - (b + d)`
- [ ] `lemma_add_rearrange_2x2(a, b, c, d)` — `(a + b) + (c + d) ≡ (a + c) + (b + d)`
- [ ] `lemma_sub_self(a)` — `a - a ≡ 0`

### Ring lemmas

- [ ] `lemma_mul_distributes_over_sub(a, b, c)` — `a * (b - c) ≡ a*b - a*c`
- [ ] `lemma_sub_mul_right(a, b, k)` — `(a - b) * k ≡ a*k - b*k`
- [ ] `lemma_mul_zero_implies_factor_zero(a, b)` — `a * b ≡ 0 ⟹ a ≡ 0 ∨ b ≡ 0` (for integral domains)
- [ ] `lemma_one_ne_zero()` — `¬(1 ≡ 0)` (may need as an axiom if not derivable)

### OrderedRing lemmas

From `verus-rational/src/rational/ordering.rs`:

- [ ] `lemma_le_iff_lt_or_eqv(a, b)` — `a ≤ b ⟺ a < b ∨ a ≡ b` (derive from `axiom_lt_iff_le_and_not_eqv`)
- [ ] `lemma_lt_le_transitive(a, b, c)` — `a < b ∧ b ≤ c ⟹ a < c`
- [ ] `lemma_le_lt_transitive(a, b, c)` — `a ≤ b ∧ b < c ⟹ a < c`
- [ ] `lemma_le_neg_flip(a, b)` — `a ≤ b ⟺ -b ≤ -a`
- [ ] `lemma_lt_neg_flip(a, b)` — `a < b ⟺ -b < -a`
- [ ] `lemma_neg_nonneg_iff(a)` — `0 ≤ a ⟺ -a ≤ 0`
- [ ] `lemma_neg_nonpos_iff(a)` — `a ≤ 0 ⟺ 0 ≤ -a`
- [ ] `lemma_le_sub_monotone(a, b, c)` — `a ≤ b ⟹ a - c ≤ b - c`
- [ ] `lemma_lt_sub_monotone(a, b, c)` — `a < b ⟹ a - c < b - c`
- [ ] `lemma_le_mul_nonneg_both(a, b, c, d)` — `0 ≤ a ≤ c ∧ 0 ≤ b ≤ d ⟹ a*b ≤ c*d`
- [ ] `lemma_mul_pos_pos(a, b)` — `0 < a ∧ 0 < b ⟹ 0 < a*b`
- [ ] `lemma_mul_neg_neg(a, b)` — `a < 0 ∧ b < 0 ⟹ 0 < a*b`
- [ ] `lemma_mul_pos_neg(a, b)` — `0 < a ∧ b < 0 ⟹ a*b < 0`
- [ ] `lemma_trichotomy(a, b)` — exactly one of: `a < b`, `a ≡ b`, `b < a`
- [ ] `lemma_le_congruence_left(a1, a2, b)` — single-argument congruence shortcuts
- [ ] `lemma_le_congruence_right(a, b1, b2)` — single-argument congruence shortcuts

### Field lemmas

From `verus-rational/src/rational/division.rs`:

- [ ] `lemma_div_one(a)` — `a / 1 ≡ a` (needs `1 ≢ 0` axiom or lemma)
- [ ] `lemma_recip_involution(a)` — `recip(recip(a)) ≡ a`
- [ ] `lemma_mul_cancel_left(a, b, c)` — `a ≢ 0 ∧ a*b ≡ a*c ⟹ b ≡ c`
- [ ] `lemma_mul_cancel_right(a, b, c)` — `c ≢ 0 ∧ a*c ≡ b*c ⟹ a ≡ b`
- [ ] `lemma_div_mul_cancel(a, b)` — `b ≢ 0 ⟹ (a / b) * b ≡ a`
- [ ] `lemma_mul_div_cancel(a, b)` — `b ≢ 0 ⟹ (a * b) / b ≡ a`
- [ ] `lemma_div_distributes_over_add(a, b, c)` — `(a + b) / c ≡ a/c + b/c`
- [ ] `lemma_recip_mul(a, b)` — `recip(a * b) ≡ recip(a) * recip(b)`
- [ ] `lemma_div_div(a, b, c)` — `(a / b) / c ≡ a / (b * c)`
- [ ] `lemma_recip_neg(a)` — `recip(-a) ≡ -recip(a)`

### OrderedField lemmas

From `verus-rational/src/rational/ordering.rs` and `division.rs`:

- [ ] `lemma_recip_pos(a)` — `0 < a ⟹ 0 < recip(a)`
- [ ] `lemma_recip_neg(a)` — `a < 0 ⟹ recip(a) < 0`
- [ ] `lemma_recip_reverses_le_pos(a, b)` — `0 < a ≤ b ⟹ recip(b) ≤ recip(a)`
- [ ] `lemma_recip_reverses_lt_pos(a, b)` — `0 < a < b ⟹ recip(b) < recip(a)`
- [ ] `lemma_recip_reverses_le_neg(a, b)` — `a ≤ b < 0 ⟹ recip(b) ≤ recip(a)`
- [ ] `lemma_div_pos(a, b)` — `0 < a ∧ 0 < b ⟹ 0 < a / b`
- [ ] `lemma_le_div_monotone(a, b, c)` — `a ≤ b ∧ 0 < c ⟹ a/c ≤ b/c`

---

## Trait design questions

- [ ] **`one_ne_zero` axiom?** Many field/ring lemmas need `¬(1 ≡ 0)`. Should this be an axiom on Ring or Field? (Without it, we can't prove `lemma_div_one`, `lemma_recip_involution`, etc.)
- [ ] **Integral domain trait?** `lemma_mul_zero_implies_factor_zero` holds for integral domains but not all rings. Could add `IntegralDomain: Ring` with this as an axiom.
- [ ] **`abs` / `signum` functions?** Several useful lemmas (triangle inequality, sign rules) require an absolute value or signum function. Could add `spec fn abs(self) -> Self` + axioms to OrderedRing, or keep it as a derived definition in a separate module.
- [ ] **Power / exponentiation?** `verus-rational` has power lemmas (`pow_zero`, `pow_one`, `pow_succ`, `pow_mul`, `pow_add`, `pow_monotone`). These could go in a `power.rs` module with a recursive `spec fn pow(self, n: nat) -> Self` definition + generic lemmas.

---

## Stub modules to populate

### `src/number_theory/mod.rs`

Potential content (generic over Ring or IntegralDomain):

- [ ] Divisibility predicate: `spec fn divides(a, b) -> bool` (exists k such that a*k ≡ b)
- [ ] GCD properties (if we add a GCD function to a trait or define it abstractly)
- [ ] Bezout's identity
- [ ] Division algorithm lemmas

### `src/inequalities/mod.rs`

Potential content (generic over OrderedRing / OrderedField):

- [ ] Inequality chain helpers (multi-step transitivity)
- [ ] Absolute value lemmas (if `abs` is added)
- [ ] Triangle inequality
- [ ] AM-GM inequality (for OrderedField)
- [ ] Sum-of-squares lemmas (2D, 3D, 4D — currently in `verus-rational/applications.rs`)
- [ ] Cauchy-Schwarz (currently in `verus-rational/applications.rs`)
- [ ] Convexity / midpoint lemmas

---

## Implementation tasks

### Phase 1: Complete the core lemma library
- [ ] Prove all AdditiveGroup lemmas listed above
- [ ] Prove all Ring lemmas listed above
- [ ] Prove all OrderedRing lemmas listed above
- [ ] Prove all Field lemmas listed above (may need `one_ne_zero` axiom first)
- [ ] Prove OrderedField lemmas (reciprocal reversal, etc.)
- [ ] Decide on `one_ne_zero` — add it as an axiom and re-prove field lemmas

### Phase 2: Make verus-rational and verus-bigint implement the traits
- [ ] Implement `Equivalence` for `Rational`
- [ ] Implement `AdditiveGroup` for `Rational`
- [ ] Implement `Ring` for `Rational`
- [ ] Implement `OrderedRing` for `Rational`
- [ ] Implement `Field` for `Rational`
- [ ] Implement `OrderedField` for `Rational`
- [ ] Implement `Equivalence` + `AdditiveGroup` + `Ring` + `OrderedRing` for bigint
- [ ] Verify that generic lemmas apply to both types

### Phase 3: Populate number_theory and inequalities
- [ ] Define divisibility, add basic lemmas
- [ ] Add absolute value (derived or trait-level)
- [ ] Port sum-of-squares and triangle inequality from verus-rational
- [ ] Add power/exponentiation module

### Phase 4: Use in verus-linalg
- [ ] verus-linalg depends on verus-algebra traits for generic vector operations
- [ ] Generic vector addition, scalar multiplication, dot product over any Ring/Field
