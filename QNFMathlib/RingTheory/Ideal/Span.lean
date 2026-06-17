/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Ideal.Operations
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

/-- If `x * a` and `x * b` both lie in `K`, then `(x) * (a, b) ≤ K`. -/
theorem span_singleton_mul_span_pair_le {R : Type*} [CommRing R]
    {x a b : R} {K : Ideal R} (ha : x * a ∈ K) (hb : x * b ∈ K) :
    span ({x} : Set R) * span ({a, b} : Set R) ≤ K := by
  rw [span_singleton_mul_le_iff]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
  | zero => simp
  | add y z _ _ hy hz => simpa [mul_add] using K.add_mem hy hz
  | smul r y _ hy =>
      simpa [mul_assoc, mul_comm, mul_left_comm] using K.mul_mem_left r hy

end Ideal
