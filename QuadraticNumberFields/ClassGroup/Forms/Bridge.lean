/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.ClassNumber
import QuadraticNumberFields.ClassGroup.Forms.Reduction
import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# Cox 7.7 Bridge from Forms to Ideal Classes

This WIP module records the intended imaginary-side Cox 7.7 bridge. It is
imported only by `Sketch.lean` until the full Gauss reduction and ideal-class
proofs close.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## WIP Gauss reduction interface -/

/-- WIP Gauss reduction existence statement for positive definite forms. -/
theorem exists_isReduced_properEquivalent (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) : ∃ R, R.IsReduced ∧ ProperEquivalent Q R := by
  sorry

/-- WIP uniqueness statement for boundary-normalized reduced representatives. -/
theorem eq_of_isReduced_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQpos : Q.IsPositiveDefinite) (hQred : Q.IsReduced) (hRred : R.IsReduced)
    (h : ProperEquivalent Q R) : Q = R := by
  sorry

/-! ## WIP Cox 7.7 class-group bridge -/

/-- Primitive positive definite forms of discriminant `D`. This is the
imaginary-side carrier used by Cox 7.7; negative definite forms of the same
negative discriminant are not part of this class-number bridge. -/
def PrimitivePositiveDefiniteForm (D : ℤ) : Type :=
  { Q : BinaryQuadraticForm //
    Q.HasDiscriminant D ∧ Q.IsPrimitive ∧ Q.IsPositiveDefinite }

namespace PrimitivePositiveDefiniteForm

/-- Proper equivalence restricted to primitive positive definite forms. -/
def ProperEquivalent {D : ℤ}
    (Q R : PrimitivePositiveDefiniteForm D) : Prop :=
  BinaryQuadraticForm.ProperEquivalent Q.1 R.1

end PrimitivePositiveDefiniteForm

/-- Setoid on primitive positive definite forms given by proper equivalence. -/
instance primitivePositiveDefiniteFormSetoid (D : ℤ) :
    Setoid (PrimitivePositiveDefiniteForm D) where
  r := PrimitivePositiveDefiniteForm.ProperEquivalent
  iseqv := ⟨
    fun Q => BinaryQuadraticForm.ProperEquivalent.refl Q.1,
    fun h => BinaryQuadraticForm.ProperEquivalent.symm h,
    fun hQR hRS => BinaryQuadraticForm.ProperEquivalent.trans hQR hRS⟩

/-- Proper equivalence classes of primitive positive definite binary quadratic
forms of discriminant `D`. -/
def FormClass (D : ℤ) : Type :=
  Quotient (primitivePositiveDefiniteFormSetoid D)

/-- The field discriminant attached to a squarefree `Qsqrtd d` parameter. -/
def fieldDiscriminant (d : ℤ) : ℤ :=
  if d % 4 = 1 then d else 4 * d

/-- WIP map from form classes to ideal classes in the `d % 4 ≠ 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  intro Q
  classical
  sorry

/-- WIP map from form classes to ideal classes in the `d % 4 = 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  intro Q
  classical
  sorry

/-- WIP Cox 7.7 bijection for imaginary quadratic fields. -/
noncomputable def formClassEquivClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  sorry

end BinaryQuadraticForm
end QuadraticNumberFields
