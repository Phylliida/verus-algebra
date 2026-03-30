///  Runtime arithmetic trait hierarchy for verified exec-level computation.
///
///  These traits bridge spec-level algebraic structures (Ring, Field, OrderedField)
///  to exec-level runtime types with verified postconditions.
///
///    RuntimeRingOps<V: Ring>              — add, sub, neg, mul, eq, copy, zero, one
///    RuntimeFieldOps<V: Field>            — extends ring with recip, div
///    RuntimeOrderedFieldOps<V: OrderedField> — extends field with le, lt
///
///  Method names match the spec-level trait names (add, sub, mul, etc.) for clean
///  call sites. In concrete impl blocks, use fully-qualified syntax to delegate:
///    `fn add(&self, rhs: &Self) -> (out: Self) { ConcreteType::add(self, rhs) }`
///
///  Example implementations:
///    RuntimeRational      → RuntimeOrderedFieldOps<Rational>
///    RuntimeQExt          → RuntimeOrderedFieldOps<SpecQuadExt>
///    RuntimeFixedPoint    → RuntimeRingOps<Rational>
use vstd::prelude::*;
use super::equivalence::Equivalence;
use super::ring::Ring;
use super::field::Field;
use super::field::OrderedField;

verus! {

//  ═══════════════════════════════════════════════════════════════════
//   Level 1: RuntimeRingOps<V: Ring>
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level ring operations: add, sub, neg, mul, equivalence, copy, construction.
///
///  "Like" construction methods (zero_like, one_like) take &self
///  to allow copying internal context (e.g., radicand values, format info).
pub trait RuntimeRingOps<V: Ring>: Sized {
    ///  Map this runtime element to its spec-level counterpart.
    spec fn model(&self) -> V;

    ///  Well-formedness: runtime fields match the ghost model.
    spec fn wf_spec(&self) -> bool;

    //  ─── Ring operations ─────────────────────────────────────────

    fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.model() == self.model().add(rhs.model());

    fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.model() == self.model().sub(rhs.model());

    fn neg(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model() == self.model().neg();

    fn mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.model() == self.model().mul(rhs.model());

    //  ─── Equivalence ─────────────────────────────────────────────

    fn eq(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.model().eqv(rhs.model());

    //  ─── Copy and construction ───────────────────────────────────

    fn copy(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model() == self.model();

    fn zero_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model() == V::zero();

    fn one_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.model() == V::one();
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 2: RuntimeFieldOps<V: Field> (adds recip, div)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level field operations: extends ring with reciprocal and division.
pub trait RuntimeFieldOps<V: Field>: RuntimeRingOps<V> {
    fn recip(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !self.model().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.model() == self.model().recip();

    fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs.model().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.model() == self.model().div(rhs.model());
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 3: RuntimeOrderedFieldOps<V: OrderedField> (adds le, lt)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level ordered field operations: extends field with ordering.
pub trait RuntimeOrderedFieldOps<V: OrderedField>: RuntimeFieldOps<V> {
    fn le(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.model().le(rhs.model());

    fn lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.model().lt(rhs.model());
}

} //  verus!
