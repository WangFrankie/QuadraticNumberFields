/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Bridge
import QuadraticNumberFields.Forms.GaussComposition

/-!
# Gauss Composition on Primitive Positive Definite Forms

This file lifts the direct concordant Gauss composition formula from raw
integer triples to the restricted primitive positive definite carrier used by
the Cox 7.7 form-class bridge.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

namespace PrimitivePositiveDefiniteForm

/-- Direct Gauss composition of concordant primitive positive definite forms.

This is still representative-level composition: the caller supplies concordant
representatives.  The later quotient-level multiplication must prove that any
two classes admit concordant representatives and that the output class is
independent of those choices. -/
def composeConcordant {D : ℤ} (Q R : PrimitivePositiveDefiniteForm D)
    (h : Q.1.IsConcordant R.1) : PrimitivePositiveDefiniteForm D where
  val := BinaryQuadraticForm.composeConcordant Q.1 R.1
  property := by
    refine ⟨?_, ?_, ?_⟩
    · exact hasDiscriminant_composeConcordant_of_isConcordant Q.2.1 h
        (ne_of_gt Q.2.2.2.1) (ne_of_gt R.2.2.2.1)
    · exact isPrimitive_composeConcordant_of_isConcordant h Q.2.2.1 R.2.2.1
        (ne_of_gt Q.2.2.2.1) (ne_of_gt R.2.2.2.1)
    · exact isPositiveDefinite_composeConcordant_of_isConcordant h Q.2.2.2 R.2.2.2

@[simp] theorem composeConcordant_val {D : ℤ} (Q R : PrimitivePositiveDefiniteForm D)
    (h : Q.1.IsConcordant R.1) :
    (composeConcordant Q R h).1 = BinaryQuadraticForm.composeConcordant Q.1 R.1 :=
  rfl

/-- Concordant composition is symmetric on primitive positive definite
representatives. -/
theorem composeConcordant_comm {D : ℤ} (Q R : PrimitivePositiveDefiniteForm D)
    (h : Q.1.IsConcordant R.1) :
    composeConcordant Q R h = composeConcordant R Q h.symm := by
  apply Subtype.ext
  exact BinaryQuadraticForm.composeConcordant_comm_of_isConcordant h

end PrimitivePositiveDefiniteForm

end BinaryQuadraticForm
end QuadraticNumberFields
