/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.Reduction
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

/-!
# Enumeration of Reduced Binary Quadratic Forms

This file defines a computable search space for primitive reduced positive
definite forms of a negative discriminant.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

instance decidableHasDiscriminant (Q : BinaryQuadraticForm) (D : ℤ) :
    Decidable (Q.HasDiscriminant D) := by
  unfold HasDiscriminant
  infer_instance

instance decidableIsPositiveDefinite (Q : BinaryQuadraticForm) :
    Decidable Q.IsPositiveDefinite := by
  unfold IsPositiveDefinite
  infer_instance

instance decidableIsReduced (Q : BinaryQuadraticForm) :
    Decidable Q.IsReduced := by
  unfold IsReduced
  infer_instance

instance decidableIsPrimitive (Q : BinaryQuadraticForm) :
    Decidable Q.IsPrimitive := by
  unfold IsPrimitive
  infer_instance

/-- A simple computable search bound for reduced forms. -/
def searchBound (D : ℤ) : ℕ :=
  Nat.sqrt D.natAbs + 1

/-- A reduced positive definite form has its `a` coefficient within the
enumeration search bound. -/
theorem a_natAbs_le_searchBound (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    Q.a.natAbs ≤ searchBound Q.disc := by
  have hbound := three_mul_a_natAbs_sq_le_disc_natAbs Q hpos hred
  have hsq : Q.a.natAbs ^ 2 ≤ Q.disc.natAbs := by
    nlinarith
  exact (Nat.le_sqrt'.mpr hsq).trans (Nat.le_succ _)

/-- Positive `a` candidates up to the search bound. -/
def aCandidates (D : ℤ) : List ℕ :=
  (List.range (searchBound D + 1)).filter fun a => 0 < a

/-- Integer `b` candidates in `[-a, a]`, generated computably from naturals. -/
def bCandidates (a : ℕ) : List ℤ :=
  (List.range (2 * a + 1)).map fun k : ℕ => (k : ℤ) - (a : ℤ)

/-- Candidate triples before the reduced/primitive filters. -/
def candidateForms (D : ℤ) : List BinaryQuadraticForm :=
  (aCandidates D).flatMap fun a : ℕ =>
    (bCandidates a).map fun b : ℤ =>
      BinaryQuadraticForm.mk (a : ℤ) b ((b ^ 2 - D) / (4 * (a : ℤ)))

/-- Primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedFormsList (D : ℤ) : List BinaryQuadraticForm :=
  (candidateForms D).filter fun Q =>
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive

/-- Finset view of primitive reduced positive definite forms of discriminant `D`. -/
def enumPrimitiveReducedForms (D : ℤ) : Finset BinaryQuadraticForm :=
  (enumPrimitiveReducedFormsList D).toFinset

/-- Membership in the finset view is membership in the underlying list modulo
`List.toFinset`. -/
theorem mem_enumPrimitiveReducedForms_iff (D : ℤ) (Q : BinaryQuadraticForm) :
    Q ∈ enumPrimitiveReducedForms D ↔
      Q ∈ (enumPrimitiveReducedFormsList D).toFinset := Iff.rfl

/-- Every list-enumerated form satisfies the filter predicates. -/
theorem of_mem_enumPrimitiveReducedFormsList {D : ℤ} {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedFormsList D) :
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
  have hfilter : Q ∈ candidateForms D ∧
      Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
    simpa [enumPrimitiveReducedFormsList] using hQ
  exact hfilter.2

/-- Every finset-enumerated form satisfies the filter predicates. -/
theorem of_mem_enumPrimitiveReducedForms {D : ℤ} {Q : BinaryQuadraticForm}
    (hQ : Q ∈ enumPrimitiveReducedForms D) :
    Q.HasDiscriminant D ∧ Q.IsPositiveDefinite ∧ Q.IsReduced ∧ Q.IsPrimitive := by
  apply of_mem_enumPrimitiveReducedFormsList
  simpa [enumPrimitiveReducedForms] using hQ

example : bCandidates 1 = [-1, 0, 1] := by
  decide

-- Smoke checks used during development:
-- `#guard (enumPrimitiveReducedFormsList (-20)).length == 2`
-- `#guard (enumPrimitiveReducedFormsList (-163)).length == 1`

end BinaryQuadraticForm
end QuadraticNumberFields
