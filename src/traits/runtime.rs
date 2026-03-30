///  Runtime arithmetic trait hierarchy for verified exec-level computation.
///
///  These traits bridge spec-level algebraic structures (Ring, Field, OrderedField)
///  to exec-level runtime types with verified postconditions.
///
///    RuntimeRingOps<V: Ring>              — add, sub, neg, mul, eq, copy, zero, one
///    RuntimeFieldOps<V: Field>            — extends ring with recip, div
///    RuntimeOrderedFieldOps<V: OrderedField> — extends field with le, lt
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
///  "Like" construction methods (rf_zero_like, rf_one_like) take &self
///  to allow copying internal context (e.g., radicand values, format info).
pub trait RuntimeRingOps<V: Ring>: Sized {
    ///  Map this runtime element to its spec-level counterpart.
    spec fn rf_view(&self) -> V;

    ///  Well-formedness: runtime fields match the ghost model.
    spec fn wf_spec(&self) -> bool;

    //  ─── Ring operations ─────────────────────────────────────────

    fn rf_add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().add(rhs.rf_view());

    fn rf_sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().sub(rhs.rf_view());

    fn rf_neg(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().neg();

    fn rf_mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view().mul(rhs.rf_view());

    //  ─── Equivalence ─────────────────────────────────────────────

    fn rf_eq(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().eqv(rhs.rf_view());

    //  ─── Copy and construction ───────────────────────────────────

    fn rf_copy(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == self.rf_view();

    fn rf_zero_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == V::zero();

    fn rf_one_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out.rf_view() == V::one();
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 2: RuntimeFieldOps<V: Field> (adds recip, div)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level field operations: extends ring with reciprocal and division.
pub trait RuntimeFieldOps<V: Field>: RuntimeRingOps<V> {
    fn rf_recip(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !self.rf_view().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.rf_view() == self.rf_view().recip();

    fn rf_div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs.rf_view().eqv(V::zero()),
        ensures
            out.wf_spec(),
            out.rf_view() == self.rf_view().div(rhs.rf_view());
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 3: RuntimeOrderedFieldOps<V: OrderedField> (adds le, lt)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level ordered field operations: extends field with ordering.
pub trait RuntimeOrderedFieldOps<V: OrderedField>: RuntimeFieldOps<V> {
    fn rf_le(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().le(rhs.rf_view());

    fn rf_lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self.rf_view().lt(rhs.rf_view());
}

} //  verus!
