/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.ClassNumber
import QuadraticNumberFields.ClassGroup.Forms.UpperHalfPlane
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
  obtain ⟨g, hgfd⟩ := ModularGroup.exists_smul_mem_fd (tauOfForm Q hQ)
  let P := transform Q g⁻¹
  have hPpos : P.IsPositiveDefinite := isPositiveDefinite_transform Q hQ g⁻¹
  have hτP : tauOfForm P hPpos = g • tauOfForm Q hQ := by
    simpa [P] using tauOfForm_transform Q hQ g⁻¹ hPpos
  have hPfd : tauOfForm P hPpos ∈ ModularGroup.fd := by
    simpa [hτP] using hgfd
  obtain ⟨n, hnred⟩ := exists_isReduced_transform_of_mem_fd P hPpos hPfd
  refine ⟨transform P n, hnred, ?_⟩
  refine ⟨g⁻¹ * n, ?_⟩
  simpa [P] using (transform_mul Q g⁻¹ n).symm

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
