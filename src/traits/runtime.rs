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
use vstd::view::View;
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
pub trait RuntimeRingOps<V: Ring>: Sized + View<V = V> {

    ///  Well-formedness: runtime fields match the ghost model.
    spec fn wf_spec(&self) -> bool;

    //  ─── Ring operations ─────────────────────────────────────────

    fn add(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out@ == self@.add(rhs@);

    fn sub(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out@ == self@.sub(rhs@);

    fn neg(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out@ == self@.neg();

    fn mul(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out.wf_spec(), out@ == self@.mul(rhs@);

    //  ─── Equivalence ─────────────────────────────────────────────

    fn eq(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self@.eqv(rhs@);

    //  ─── Copy and construction ───────────────────────────────────

    fn copy(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out@ == self@;

    fn zero_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out@ == V::zero();

    fn one_like(&self) -> (out: Self)
        requires self.wf_spec()
        ensures out.wf_spec(), out@ == V::one();
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 2: RuntimeFieldOps<V: Field> (adds recip, div)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level field operations: extends ring with reciprocal and division.
pub trait RuntimeFieldOps<V: Field>: RuntimeRingOps<V> {
    fn recip(&self) -> (out: Self)
        requires
            self.wf_spec(),
            !self@.eqv(V::zero()),
        ensures
            out.wf_spec(),
            out@ == self@.recip();

    fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs@.eqv(V::zero()),
        ensures
            out.wf_spec(),
            out@ == self@.div(rhs@);
}

//  ═══════════════════════════════════════════════════════════════════
//   Level 3: RuntimeOrderedFieldOps<V: OrderedField> (adds le, lt)
//  ═══════════════════════════════════════════════════════════════════

///  Exec-level ordered field operations: extends field with ordering.
pub trait RuntimeOrderedFieldOps<V: OrderedField>: RuntimeFieldOps<V> {
    fn le(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self@.le(rhs@);

    fn lt(&self, rhs: &Self) -> (out: bool)
        requires self.wf_spec(), rhs.wf_spec()
        ensures out == self@.lt(rhs@);

    fn min(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out@ == crate::min_max::min::<V>(self@, rhs@),
    {
        if self.le(rhs) { self.copy() } else { rhs.copy() }
    }

    fn max(&self, rhs: &Self) -> (out: Self)
        requires self.wf_spec(), rhs.wf_spec(),
        ensures out.wf_spec(), out@ == crate::min_max::max::<V>(self@, rhs@),
    {
        if self.le(rhs) { rhs.copy() } else { self.copy() }
    }

    fn clamp(&self, lo: &Self, hi: &Self) -> (out: Self)
        requires self.wf_spec(), lo.wf_spec(), hi.wf_spec(),
        ensures out.wf_spec(),
            out@ == crate::min_max::max::<V>(lo@, crate::min_max::min::<V>(self@, hi@)),
    {
        let mid = if self.le(hi) { self.copy() } else { hi.copy() };
        if lo.le(&mid) { mid } else { lo.copy() }
    }
}

} //  verus!
