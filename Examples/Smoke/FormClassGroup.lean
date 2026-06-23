/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import FormClassGroup.ClassGroup.ClassNumber
import FormClassGroup.ClassGroup.Law

/-!
# Form Class Group Smoke Examples

Small examples for the form-class-group transport and reduced-form class-number
interfaces.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

example (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    haveI := formClassCommGroup hdneg
    formClassEquivClassGroup hdneg (1 : FormClass (fieldDiscriminant d)) =
      (1 : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) := by
  simp [Equiv.one_def]

example (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (x y : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    formClassEquivClassGroup hdneg (x * y) =
    formClassEquivClassGroup hdneg x * formClassEquivClassGroup hdneg y := by
  simp [Equiv.mul_def]

section ReducedRepresentatives

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)

example (C : FormClass (fieldDiscriminant d)) :
    (reducedRepresentative C).1.IsReduced :=
  reducedRepresentative_isReduced C

example (C E : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
      (reducedProductRepresentative hdneg C E) = C * E :=
  reducedProductRepresentative_mk_eq_mul hdneg C E

example (C E : FormClass (fieldDiscriminant d))
    {Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)}
    (hQred : Q.1.IsReduced)
    (hQ : haveI := formClassCommGroup hdneg
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q = C * E) :
    Q = reducedProductRepresentative hdneg C E :=
  eq_reducedProductRepresentative_of_isReduced_mk_eq_mul hdneg hQred hQ

end ReducedRepresentatives

end BinaryQuadraticForm

example : NumberField.classNumber (Qsqrtd ((-1 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-2 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-3 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-7 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-11 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-19 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-43 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-67 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

example : NumberField.classNumber (Qsqrtd ((-163 : ℤ) : ℚ)) = 1 := by
  compute_class_number_qsqrtd

end QuadraticNumberFields
