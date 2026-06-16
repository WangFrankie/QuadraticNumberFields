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

/-- The representative-level unit attached to a primitive positive definite
form, lifted to the restricted carrier of the same discriminant. -/
def concordantUnitRepresentative {D : ℤ} (Q : PrimitivePositiveDefiniteForm D) :
    PrimitivePositiveDefiniteForm D where
  val := BinaryQuadraticForm.concordantUnitRepresentative Q.1
  property := by
    refine ⟨?_, ?_, ?_⟩
    · exact (BinaryQuadraticForm.concordantUnitRepresentative_isConcordant Q.1).1.trans Q.2.1
    · unfold BinaryQuadraticForm.IsPrimitive
      simp [BinaryQuadraticForm.concordantUnitRepresentative, Int.gcd]
    · constructor
      · norm_num [BinaryQuadraticForm.concordantUnitRepresentative]
      · rw [(BinaryQuadraticForm.concordantUnitRepresentative_isConcordant Q.1).1]
        exact Q.2.2.2.2

/-- The attached unit representative is concordant to the original primitive
positive definite form. -/
theorem concordantUnitRepresentative_isConcordant {D : ℤ}
    (Q : PrimitivePositiveDefiniteForm D) :
    (concordantUnitRepresentative Q).1.IsConcordant Q.1 :=
  BinaryQuadraticForm.concordantUnitRepresentative_isConcordant Q.1

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

/-- The attached unit representative is a left identity for direct concordant
composition on the restricted carrier. -/
theorem composeConcordant_concordantUnitRepresentative {D : ℤ}
    (Q : PrimitivePositiveDefiniteForm D) :
    composeConcordant (concordantUnitRepresentative Q) Q
      (concordantUnitRepresentative_isConcordant Q) = Q := by
  apply Subtype.ext
  exact BinaryQuadraticForm.composeConcordant_concordantUnitRepresentative Q.1
    (ne_of_gt Q.2.2.2.1)

/-- The attached unit representative is a right identity for direct concordant
composition on the restricted carrier. -/
theorem composeConcordant_concordantUnitRepresentative_right {D : ℤ}
    (Q : PrimitivePositiveDefiniteForm D) :
    composeConcordant Q (concordantUnitRepresentative Q)
      (concordantUnitRepresentative_isConcordant Q).symm = Q := by
  apply Subtype.ext
  exact BinaryQuadraticForm.composeConcordant_concordantUnitRepresentative_right Q.1
    (ne_of_gt Q.2.2.2.1)

/-- Any two primitive positive definite forms of the same discriminant admit
properly equivalent concordant representatives. -/
theorem exists_concordant_representatives {D : ℤ}
    (Q R : PrimitivePositiveDefiniteForm D) :
    ∃ Q' R' : PrimitivePositiveDefiniteForm D,
      ProperEquivalent Q Q' ∧ ProperEquivalent R R' ∧ Q'.1.IsConcordant R'.1 := by
  obtain ⟨Q', R', ⟨g, hg⟩, ⟨h, hh⟩, hcon⟩ :=
    BinaryQuadraticForm.exists_concordant_of_sameDiscriminant
      Q.2.2.1 R.2.2.1 Q.2.2.2 R.2.2.2 (Q.2.1.trans R.2.1.symm)
  refine ⟨⟨Q', ?_⟩, ⟨R', ?_⟩, ⟨g, hg⟩, ⟨h, hh⟩, hcon⟩
  · constructor
    · rw [← hg]
      exact (disc_transform Q.1 g).trans Q.2.1
    · constructor
      · rw [← hg]
        exact isPrimitive_transform Q.1 Q.2.2.1 g
      · rw [← hg]
        exact isPositiveDefinite_transform Q.1 Q.2.2.2 g
  · constructor
    · rw [← hh]
      exact (disc_transform R.1 h).trans R.2.1
    · constructor
      · rw [← hh]
        exact isPrimitive_transform R.1 R.2.2.1 h
      · rw [← hh]
        exact isPositiveDefinite_transform R.1 R.2.2.2 h

end PrimitivePositiveDefiniteForm

namespace FormClass

/-- The form class produced by directly composing chosen concordant primitive
positive definite representatives.

This is not yet a multiplication on `FormClass D`: it still depends on chosen
representatives and a concordance proof.  The later well-definedness theorem
will remove those choices. -/
def composeConcordantOfRepresentatives {D : ℤ}
    (Q R : PrimitivePositiveDefiniteForm D) (h : Q.1.IsConcordant R.1) :
    FormClass D :=
  Quotient.mk (primitivePositiveDefiniteFormSetoid D)
    (PrimitivePositiveDefiniteForm.composeConcordant Q R h)

/-- Chosen-representative concordant composition is symmetric after passing to
form classes. -/
theorem composeConcordantOfRepresentatives_comm {D : ℤ}
    (Q R : PrimitivePositiveDefiniteForm D) (h : Q.1.IsConcordant R.1) :
    composeConcordantOfRepresentatives Q R h =
      composeConcordantOfRepresentatives R Q h.symm := by
  unfold composeConcordantOfRepresentatives
  rw [PrimitivePositiveDefiniteForm.composeConcordant_comm]

/-- Any two form classes admit concordant representatives. -/
theorem exists_concordant_representatives {D : ℤ} (C E : FormClass D) :
    ∃ Q R : PrimitivePositiveDefiniteForm D,
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) Q = C ∧
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) R = E ∧ Q.1.IsConcordant R.1 := by
  induction C using Quotient.inductionOn with
  | h Q =>
      induction E using Quotient.inductionOn with
      | h R =>
          obtain ⟨Q', R', hQ, hR, hcon⟩ :=
            PrimitivePositiveDefiniteForm.exists_concordant_representatives Q R
          exact ⟨Q', R', (Quotient.sound hQ).symm, (Quotient.sound hR).symm, hcon⟩

end FormClass

end BinaryQuadraticForm
end QuadraticNumberFields
