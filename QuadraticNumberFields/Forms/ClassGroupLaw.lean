/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Enumeration
import QuadraticNumberFields.Forms.Structure

/-!
# Class-group law on form classes

This file packages the class-group law on `FormClass (fieldDiscriminant d)`
transported across the Cox equivalence, together with reduced representatives
for products.  The product representative is the target that explicit Gauss
composition should eventually compute.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section ReducedRepresentatives

variable {D : ℤ}

/-- The finite representative type of reduced primitive positive definite
forms of discriminant `D`, backed by the enumerator. -/
abbrev ReducedFormRep (D : ℤ) : Type :=
  { Q : BinaryQuadraticForm // Q ∈ enumPrimitiveReducedForms D }

/-- Interpret an enumerated reduced form as its proper-equivalence class. -/
def ReducedFormRep.formClass (Q : ReducedFormRep D) : FormClass D :=
  Quotient.mk (primitivePositiveDefiniteFormSetoid D)
    (primitivePositiveDefiniteFormOfMemEnum Q.2)

/-- The reduced representative of a form class, chosen using Gauss reduction. -/
noncomputable def reducedRepresentative (C : FormClass D) : PrimitivePositiveDefiniteForm D :=
  Classical.choose (exists_isReduced_mk_eq_formClass C)

/-- The chosen representative of a form class is reduced. -/
theorem reducedRepresentative_isReduced (C : FormClass D) :
    (reducedRepresentative C).1.IsReduced :=
  (Classical.choose_spec (exists_isReduced_mk_eq_formClass C)).1

/-- The chosen reduced representative represents the original form class. -/
theorem reducedRepresentative_mk_eq (C : FormClass D) :
    Quotient.mk (primitivePositiveDefiniteFormSetoid D) (reducedRepresentative C) = C :=
  (Classical.choose_spec (exists_isReduced_mk_eq_formClass C)).2

/-- The chosen reduced representative belongs to the finite reduced-form
enumeration. -/
theorem reducedRepresentative_mem_enum (C : FormClass D) :
    (reducedRepresentative C).1 ∈ enumPrimitiveReducedForms D :=
  mem_enumPrimitiveReducedForms_of_reduced
    (reducedRepresentative C).2.1
    (reducedRepresentative C).2.2.2
    (reducedRepresentative_isReduced C)
    (reducedRepresentative C).2.2.1

/-- The chosen reduced representative as an element of the finite enumerated
representative type. -/
noncomputable def reducedRepresentativeRep (C : FormClass D) : ReducedFormRep D :=
  ⟨(reducedRepresentative C).1, reducedRepresentative_mem_enum C⟩

/-- The chosen reduced representative represents the original form class. -/
theorem reducedRepresentativeRep_formClass (C : FormClass D) :
    (reducedRepresentativeRep C).formClass = C := by
  simpa [ReducedFormRep.formClass, reducedRepresentativeRep,
    primitivePositiveDefiniteFormOfMemEnum] using reducedRepresentative_mk_eq C

/-- Any reduced representative of a form class is the chosen reduced
representative of that class. -/
theorem eq_reducedRepresentative_of_isReduced_mk_eq
    {C : FormClass D} {Q : PrimitivePositiveDefiniteForm D}
    (hQred : Q.1.IsReduced)
    (hQ : Quotient.mk (primitivePositiveDefiniteFormSetoid D) Q = C) :
    Q = reducedRepresentative C :=
  eq_of_isReduced_of_mk_eq_mk hQred (reducedRepresentative_isReduced C)
    (hQ.trans (reducedRepresentative_mk_eq C).symm)

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)

/-- The reduced representative of the product of two form classes, using the
class-group law transported across the Cox equivalence.

This is the specification target for explicit Gauss composition: a future
computable composition algorithm should reduce its output to this
representative. -/
noncomputable def reducedProductRepresentative
    (C E : FormClass (fieldDiscriminant d)) :
    PrimitivePositiveDefiniteForm (fieldDiscriminant d) := by
  letI := formClassCommGroup hdneg
  exact reducedRepresentative (C * E)

/-- The reduced product representative represents the product class. -/
theorem reducedProductRepresentative_mk_eq_mul
    (C E : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
      (reducedProductRepresentative hdneg C E) = C * E :=
  by
    letI := formClassCommGroup hdneg
    exact reducedRepresentative_mk_eq (C * E)

/-- The reduced product representative is reduced. -/
theorem reducedProductRepresentative_isReduced
    (C E : FormClass (fieldDiscriminant d)) :
    (reducedProductRepresentative hdneg C E).1.IsReduced := by
  letI := formClassCommGroup hdneg
  exact reducedRepresentative_isReduced (C * E)

/-- Multiplication on finite reduced-form representatives, using the
Cox-transported class-group law and reducing back to the finite enumeration.

Explicit Gauss composition should eventually compute the same representative. -/
noncomputable def reducedFormRepMul
    (Q R : ReducedFormRep (fieldDiscriminant d)) :
    ReducedFormRep (fieldDiscriminant d) := by
  letI := formClassCommGroup hdneg
  exact reducedRepresentativeRep (Q.formClass * R.formClass)

/-- The finite representative multiplication represents class multiplication. -/
theorem reducedFormRepMul_formClass
    (Q R : ReducedFormRep (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    (reducedFormRepMul hdneg Q R).formClass = Q.formClass * R.formClass := by
  letI := formClassCommGroup hdneg
  exact reducedRepresentativeRep_formClass (Q.formClass * R.formClass)

/-- Any reduced form representing the product class is the chosen reduced
product representative. -/
theorem eq_reducedProductRepresentative_of_isReduced_mk_eq_mul
    {C E : FormClass (fieldDiscriminant d)}
    {Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)}
    (hQred : Q.1.IsReduced)
    (hQ : haveI := formClassCommGroup hdneg
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q = C * E) :
    Q = reducedProductRepresentative hdneg C E := by
  letI := formClassCommGroup hdneg
  exact eq_reducedRepresentative_of_isReduced_mk_eq hQred hQ

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
end QuadraticNumberFields
