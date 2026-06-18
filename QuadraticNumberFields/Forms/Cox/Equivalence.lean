/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Cox.LeftInverse
import QuadraticNumberFields.Forms.Cox.LeftInverseEqOne
import QuadraticNumberFields.Forms.Cox.RightInverse

/-!
# Cox 7.7 Equivalence Assembly

This file is the assembly layer for the imaginary Cox 7.7 correspondence.  The
forward map from form classes to ideal classes lives in `Forms.Cox.Bridge`; the
inverse-direction map from ideal classes to form classes lives in
`Forms.Cox.Inverse`.  The branch round-trip laws live in `Forms.Cox.LeftInverse`,
`Forms.Cox.LeftInverseEqOne`, and `Forms.Cox.RightInverse`; this file only holds
the representative-reduction interface and the final assembly.

## Main result

`formClassEquivClassGroup`, the Cox 7.7 equivalence between primitive positive
definite form classes of the field discriminant and ideal classes of the
imaginary quadratic order.
-/

open scoped NumberField nonZeroDivisors
open Module

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
  exact Quotient.inductionOn C hrep

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

/-- In the `d % 4 ≠ 1` branch, applying the forward map to the inverse form of
an ideal computes to the Cox ideal class of the attached norm form. -/
theorem formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰) :
    formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) =
      let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
      idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg hI b) := by
  unfold formClassOfNonzeroIdeal
  exact formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4 _

/-- In the `d % 4 = 1` branch, applying the forward map to the inverse form of
an ideal computes to the Cox ideal class of the attached norm form. -/
theorem formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰) :
    formClassToClassGroup d (formClassOfNonzeroIdeal hdneg I) =
      let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
      let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
      idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg hI b) := by
  unfold formClassOfNonzeroIdeal
  exact formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4 _

/-- It is enough to prove the left inverse law separately for the two explicit
Cox ideal class constructors. -/
theorem formClassToClassGroup_leftInverse_of_branch_representatives (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)),
      classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_ne_one d hd4 Q) =
        Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q)
    (heq : ∀ (hd4 : d % 4 = 1) (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)),
      classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_eq_one d hd4 Q) =
        Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C := by
  apply formClassToClassGroup_leftInverse_of_representatives hdneg
  intro Q
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_mk_eq_of_mod_four_eq_one d hd4]
    exact heq hd4 Q
  · rw [formClassToClassGroup_mk_eq_of_mod_four_ne_one d hd4]
    exact hne hd4 Q

/-- It is enough to prove the right inverse law separately for the two explicit
Cox ideal class constructors attached to norm forms of ideal bases. -/
theorem formClassToClassGroup_rightInverse_of_branch_ideal_representatives (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_ne_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I)
    (heq : ∀ (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_eq_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I) :
    ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C := by
  apply formClassToClassGroup_rightInverse_of_ideal_representatives hdneg
  intro I
  by_cases hd4 : d % 4 = 1
  · rw [formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_eq_one hdneg hd4]
    exact heq hd4 I
  · rw [formClassToClassGroup_formClassOfNonzeroIdeal_eq_of_mod_four_ne_one hdneg hd4]
    exact hne hd4 I

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

section CoxAssembly

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- The Cox map followed by the inverse ideal-to-form map is the identity on
form classes. -/
theorem formClassToClassGroup_leftInverse (hdneg : d < 0) :
    ∀ C : FormClass (fieldDiscriminant d),
      classGroupToFormClass hdneg (formClassToClassGroup d C) = C :=
  formClassToClassGroup_leftInverse_of_branch_representatives hdneg
    (classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_ne_one hdneg)
    (classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_eq_one hdneg)

/-- Assemble the Cox 7.7 equivalence from the two remaining right-inverse
branch laws.  The left inverse branch laws are already proved in this file. -/
noncomputable def formClassEquivClassGroupOfRightBranchLaws (hdneg : d < 0)
    (hne : ∀ (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_ne_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I)
    (heq : ∀ (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰),
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       idealClassOfForm_of_mod_four_eq_one d hd4
         (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K :=
  formClassEquivClassGroupOfInverseLaws hdneg
    (formClassToClassGroup_leftInverse hdneg)
    (formClassToClassGroup_rightInverse_of_branch_ideal_representatives hdneg hne heq)

/-- The inverse ideal-to-form map followed by the Cox map is the identity on
ideal classes. -/
theorem formClassToClassGroup_rightInverse (hdneg : d < 0) :
    ∀ C : ClassGroup 𝓞K,
      formClassToClassGroup d (classGroupToFormClass hdneg C) = C :=
  formClassToClassGroup_rightInverse_of_branch_ideal_representatives hdneg
    (idealClassOfNormForm_eq_mk0_of_mod_four_ne_one hdneg)
    (idealClassOfNormForm_eq_mk0_of_mod_four_eq_one hdneg)

/-- Cox 7.7 equivalence between primitive positive definite form classes of the
field discriminant and ideal classes of the imaginary quadratic order. -/
noncomputable def formClassEquivClassGroup (hdneg : d < 0) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup 𝓞K :=
  formClassEquivClassGroupOfInverseLaws hdneg
    (formClassToClassGroup_leftInverse hdneg)
    (formClassToClassGroup_rightInverse hdneg)


end CoxAssembly

end BinaryQuadraticForm
end QuadraticNumberFields
