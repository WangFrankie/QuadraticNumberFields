/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Class
import BinaryQuadraticForms.Core.ReducedUniqueness

/-!
# Reduced Representatives of Form Classes

This file connects the primitive positive definite form-class carrier to the
Gauss reduction existence and uniqueness theorems.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Restricted Gauss reduction interface -/

/-- Every primitive positive definite form has a properly equivalent reduced
representative inside the same restricted carrier. -/
theorem exists_isReduced_primitivePositiveDefiniteForm_properEquivalent
    {D : ℤ} (Q : PrimitivePositiveDefiniteForm D) :
    ∃ R : PrimitivePositiveDefiniteForm D, R.1.IsReduced ∧
      PrimitivePositiveDefiniteForm.ProperEquivalent Q R := by
  obtain ⟨R, hRred, hQR⟩ := exists_isReduced_properEquivalent Q.1 Q.2.2.2
  rcases hQR with ⟨g, rfl⟩
  refine ⟨⟨transform Q.1 g, ?_⟩, hRred, ⟨g, rfl⟩⟩
  constructor
  · exact (disc_transform Q.1 g).trans Q.2.1
  · constructor
    · exact isPrimitive_transform Q.1 Q.2.2.1 g
    · exact isPositiveDefinite_transform Q.1 Q.2.2.2 g

/-- Boundary-normalized reduced representatives are unique within the
restricted primitive positive definite carrier. -/
theorem eq_of_isReduced_primitivePositiveDefiniteForm_of_properEquivalent
    {D : ℤ} {Q R : PrimitivePositiveDefiniteForm D}
    (hQred : Q.1.IsReduced) (hRred : R.1.IsReduced)
    (h : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) : Q = R := by
  apply Subtype.ext
  exact eq_of_isReduced_of_properEquivalent Q.2.2.2 hQred hRred h

/-- Every form class has a reduced primitive positive definite representative. -/
theorem exists_isReduced_mk_eq_formClass {D : ℤ} (C : FormClass D) :
    ∃ R : PrimitivePositiveDefiniteForm D, R.1.IsReduced ∧
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) R = C := by
  induction C using Quotient.inductionOn with
  | h Q =>
      obtain ⟨R, hRred, hQR⟩ :=
        exists_isReduced_primitivePositiveDefiniteForm_properEquivalent Q
      exact ⟨R, hRred, (Quotient.sound hQR).symm⟩

/-- Reduced representatives of the same form class are equal. -/
theorem eq_of_isReduced_of_mk_eq_mk {D : ℤ} {Q R : PrimitivePositiveDefiniteForm D}
    (hQred : Q.1.IsReduced) (hRred : R.1.IsReduced)
    (hclass : Quotient.mk (primitivePositiveDefiniteFormSetoid D) Q =
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) R) :
    Q = R :=
  eq_of_isReduced_primitivePositiveDefiniteForm_of_properEquivalent hQred hRred
    (Quotient.exact hclass)

end BinaryQuadraticForm
end QuadraticNumberFields
