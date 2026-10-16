/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Basic
import FormClassGroup.Cox.Equivalence
import BinaryQuadraticForms.Core.Enumeration

/-!
# Class Numbers via Reduced Binary Quadratic Forms

This file connects `NumberField.classNumber (Qsqrtd (d : ℚ))` to reduced
primitive positive definite binary quadratic forms via Cox's equivalence.

## Main definitions

* `classGroupRepresentativesQsqrtd`: class-group representatives obtained from
  reduced primitive positive definite forms.

## Main statements

* `classGroupRepresentativesQsqrtd_eq_univ`: the reduced-form representatives
  cover the full class group for imaginary squarefree `d`.
* `classNumber_qsqrtd_eq_reducedForms_card`: the class number of an imaginary
  quadratic field is the cardinality of the reduced-form enumeration.
-/

open scoped NumberField

open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

/-- Close concrete imaginary quadratic class-number goals by transporting to
reduced forms and evaluating the native reduced-form enumerator. -/
syntax "compute_class_number_qsqrtd" : tactic

/- The name is generated from the user-facing `compute_class_number_qsqrtd` syntax. -/
attribute [nolint defsWithUnderscore] tacticCompute_class_number_qsqrtd

namespace QuadraticNumberFields

/-! ## Class-group representatives from reduced forms -/

/-- Representatives of the class group of `ℚ(√d)` obtained by enumerating
reduced primitive positive definite forms of the field discriminant and applying
the Cox 7.7 equivalence. -/
noncomputable def classGroupRepresentativesQsqrtd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    Finset (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) := by
  classical
  exact (BinaryQuadraticForm.reducedFormClasses (BinaryQuadraticForm.fieldDiscriminant d)).image
    (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg)

/-- The class-group representatives obtained from the reduced-form enumeration
cover the full class group. -/
theorem classGroupRepresentativesQsqrtd_eq_univ
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    classGroupRepresentativesQsqrtd d hdneg = Finset.univ := by
  classical
  rw [classGroupRepresentativesQsqrtd,
    BinaryQuadraticForm.reducedFormClasses_eq_univ]
  exact Finset.image_univ_equiv
    (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg)

/-- For imaginary squarefree `d`, the class number of `ℚ(√d)` is the number of
primitive reduced positive definite forms of the field discriminant. -/
theorem classNumber_qsqrtd_eq_reducedForms_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) =
      (BinaryQuadraticForm.enumPrimitiveReducedForms
        (BinaryQuadraticForm.fieldDiscriminant d)).card := by
  classical
  calc
    NumberField.classNumber (Qsqrtd (d : ℚ)) =
        (Finset.univ : Finset (ClassGroup (𝓞 (Qsqrtd (d : ℚ))))).card := by
      simp [NumberField.classNumber]
    _ = (classGroupRepresentativesQsqrtd d hdneg).card := by
      rw [classGroupRepresentativesQsqrtd_eq_univ]
    _ = (BinaryQuadraticForm.reducedFormClasses
          (BinaryQuadraticForm.fieldDiscriminant d)).card := by
      rw [classGroupRepresentativesQsqrtd]
      exact Finset.card_image_of_injective _
        (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg).injective
    _ = (BinaryQuadraticForm.enumPrimitiveReducedForms
          (BinaryQuadraticForm.fieldDiscriminant d)).card :=
      BinaryQuadraticForm.reducedFormClasses_card _

macro_rules
  | `(tactic| compute_class_number_qsqrtd) =>
      `(tactic|
        (try (change NumberField.classNumber (Qsqrtd (_ : ℚ)) = _);
         rw [classNumber_qsqrtd_eq_reducedForms_card _ (by norm_num)];
         rw [BinaryQuadraticForm.enumPrimitiveReducedForms_card_eq_length];
         norm_num [BinaryQuadraticForm.fieldDiscriminant];
         reduce_forms_count))

end QuadraticNumberFields
