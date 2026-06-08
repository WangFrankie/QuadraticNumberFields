/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Ideal.Span

/-!
# Ideal Span Lemmas

Material destined for mathlib.
-/

namespace Ideal

/-- A span is contained in a principal span iff each generator is divisible by
the principal generator. -/
-- Repository use: support theorem for `span_le_span_singleton_of_forall_dvd`.
theorem span_le_span_singleton_iff_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α} :
    span S ≤ span {a} ↔ ∀ x ∈ S, a ∣ x := by
  rw [span_le]
  exact forall_congr' fun x => forall_congr' fun _ => mem_span_singleton

/-- If `a` divides every element of `S`, then `Ideal.span S ≤ Ideal.span {a}`. -/
-- Repository use: `Examples/SqrtNeg5/Ideals.lean` uses this for explicit
-- ideal-factorization containments.
theorem span_le_span_singleton_of_forall_dvd
    {α : Type*} [CommSemiring α] {a : α} {S : Set α}
    (h : ∀ x ∈ S, a ∣ x) :
    span S ≤ span {a} :=
  span_le_span_singleton_iff_forall_dvd.2 h

end Ideal
