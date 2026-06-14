/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.InverseCox

/-!
# Cox 7.7 Equivalence Assembly

This file is the assembly layer for the imaginary Cox 7.7 correspondence.  The
forward map from form classes to ideal classes lives in `Forms.Bridge`; the
inverse-direction map from ideal classes to form classes lives in
`Forms.InverseCox`, which imports `Forms.Bridge`.  Therefore the final
equivalence belongs here rather than in `Forms.Bridge`.
-/

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxEquivalence

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- Assemble the Cox 7.7 equivalence once the forward and inverse maps have
been proved to be inverse to each other. -/
noncomputable def formClassEquivClassGroupOfInverseLaws (hdneg : d < 0)
    (hleft : ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C)
    (hright : ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K where
  toFun := formClassToClassGroup d
  invFun := classGroupToFormClass hdneg
  left_inv := hleft
  right_inv := hright

/-- It is enough to prove the left inverse law on form representatives. -/
theorem formClassToClassGroup_leftInverse_of_representatives (hdneg : d < 0)
    (hrep : ∀ Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d),
      classGroupToFormClass hdneg
        (formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)) =
          Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C := by
  intro C
  induction C using Quotient.inductionOn with
  | h Q => exact hrep Q

/-- It is enough to prove the right inverse law on nonzero integral ideal
representatives. -/
theorem formClassToClassGroup_rightInverse_of_ideal_representatives (hdneg : d < 0)
    (hrep : ∀ I : (Ideal 𝓞K)⁰,
      formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) = ClassGroup.mk0 I) :
    ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C := by
  intro C
  obtain ⟨I, hmk, hform⟩ := exists_mk0_eq_formClassOfNonzeroIdeal hdneg C
  rw [← hform, hrep I, hmk]

/-- Assemble the Cox 7.7 equivalence from representative-level compatibility
of the two maps. -/
noncomputable def formClassEquivClassGroupOfRepresentativeLaws (hdneg : d < 0)
    (hform : ∀ Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d),
      classGroupToFormClass hdneg
        (formClassToClassGroup d (Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)) =
          Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)
    (hideal : ∀ I : (Ideal 𝓞K)⁰,
      formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) = ClassGroup.mk0 I) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K :=
  formClassEquivClassGroupOfInverseLaws hdneg
    (formClassToClassGroup_leftInverse_of_representatives hdneg hform)
    (formClassToClassGroup_rightInverse_of_ideal_representatives hdneg hideal)

end CoxEquivalence
end BinaryQuadraticForm
end QuadraticNumberFields
