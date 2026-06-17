/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Enumeration
import QuadraticNumberFields.Forms.ClassGroup.Structure

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

/-- The discriminant of a reduced representative is the indexing
discriminant. -/
theorem ReducedFormRep.disc_eq (Q : ReducedFormRep D) : Q.1.disc = D :=
  (of_mem_enumPrimitiveReducedForms Q.2).1

/-- A reduced representative is positive definite. -/
theorem ReducedFormRep.isPositiveDefinite (Q : ReducedFormRep D) :
    Q.1.IsPositiveDefinite :=
  (of_mem_enumPrimitiveReducedForms Q.2).2.1

/-- A reduced representative is reduced. -/
theorem ReducedFormRep.isReduced (Q : ReducedFormRep D) : Q.1.IsReduced :=
  (of_mem_enumPrimitiveReducedForms Q.2).2.2.1

/-- A reduced representative is primitive. -/
theorem ReducedFormRep.isPrimitive (Q : ReducedFormRep D) : Q.1.IsPrimitive :=
  (of_mem_enumPrimitiveReducedForms Q.2).2.2.2

/-- The finite representative type has the same cardinality as the reduced-form
enumeration backing it. -/
theorem reducedFormRep_card (D : ℤ) :
    Fintype.card (ReducedFormRep D) = (enumPrimitiveReducedForms D).card := by
  classical
  change Fintype.card {Q : BinaryQuadraticForm // Q ∈ enumPrimitiveReducedForms D} = _
  exact Fintype.card_coe (enumPrimitiveReducedForms D)

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

/-- Passing from a reduced representative to its class and choosing the reduced
representative returns the original enumerated representative. -/
theorem reducedRepresentativeRep_formClass_leftInverse (Q : ReducedFormRep D) :
    reducedRepresentativeRep Q.formClass = Q := by
  apply Subtype.ext
  have hQred : (primitivePositiveDefiniteFormOfMemEnum Q.2).1.IsReduced :=
    Q.isReduced
  have hQ :
      Quotient.mk (primitivePositiveDefiniteFormSetoid D)
        (primitivePositiveDefiniteFormOfMemEnum Q.2) = Q.formClass := rfl
  have h :=
    eq_of_isReduced_of_mk_eq_mk hQred (reducedRepresentative_isReduced Q.formClass)
      (hQ.trans (reducedRepresentative_mk_eq Q.formClass).symm)
  simpa [reducedRepresentativeRep, primitivePositiveDefiniteFormOfMemEnum] using
    congrArg Subtype.val h.symm

/-- Reduced representatives are equivalent to form classes. -/
noncomputable def reducedFormRepEquivFormClass (D : ℤ) :
    ReducedFormRep D ≃ FormClass D where
  toFun := ReducedFormRep.formClass
  invFun := reducedRepresentativeRep
  left_inv := reducedRepresentativeRep_formClass_leftInverse
  right_inv := reducedRepresentativeRep_formClass

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

/-- Finite reduced-form representatives are equivalent to the ideal class group. -/
noncomputable def reducedFormRepEquivClassGroup (hdneg : d < 0) :
    ReducedFormRep (fieldDiscriminant d) ≃ ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  (reducedFormRepEquivFormClass (fieldDiscriminant d)).trans
    (formClassEquivClassGroup hdneg)

/-- Transported `CommGroup` structure on finite reduced-form representatives.
This is a `def` (not an instance), matching `formClassCommGroup`. -/
@[reducible]
noncomputable def reducedFormRepCommGroup (hdneg : d < 0) :
    CommGroup (ReducedFormRep (fieldDiscriminant d)) :=
  Equiv.commGroup (reducedFormRepEquivClassGroup hdneg)

/-- Multiplication on reduced representatives agrees with ideal class-group
multiplication under the Cox equivalence. -/
theorem reducedFormRepEquivClassGroup_mul
    (Q R : ReducedFormRep (fieldDiscriminant d)) :
    reducedFormRepEquivClassGroup hdneg (reducedFormRepMul hdneg Q R) =
      reducedFormRepEquivClassGroup hdneg Q * reducedFormRepEquivClassGroup hdneg R := by
  letI := formClassCommGroup hdneg
  change formClassEquivClassGroup hdneg (ReducedFormRep.formClass (reducedFormRepMul hdneg Q R)) =
    formClassEquivClassGroup hdneg Q.formClass * formClassEquivClassGroup hdneg R.formClass
  rw [reducedFormRepMul_formClass, formClassEquivClassGroup_mul]

/-- The transported group multiplication on finite reduced-form representatives
is the reduced representative product. -/
theorem reducedFormRep_mul_eq_reducedFormRepMul
    (Q R : ReducedFormRep (fieldDiscriminant d)) :
    haveI := reducedFormRepCommGroup hdneg
    Q * R = reducedFormRepMul hdneg Q R := by
  letI := reducedFormRepCommGroup hdneg
  apply (reducedFormRepEquivClassGroup hdneg).injective
  calc
    reducedFormRepEquivClassGroup hdneg (Q * R)
        = reducedFormRepEquivClassGroup hdneg Q *
          reducedFormRepEquivClassGroup hdneg R := by
          simp [Equiv.mul_def]
    _ = reducedFormRepEquivClassGroup hdneg (reducedFormRepMul hdneg Q R) :=
          (reducedFormRepEquivClassGroup_mul hdneg Q R).symm

/-- Class-number-one shortcut on finite reduced-form representatives: if the
enumerated representative type has cardinality one, every representative is the
identity in the transported group. -/
theorem reducedFormRep_eq_one_of_card_eq_one
    (hcard : Fintype.card (ReducedFormRep (fieldDiscriminant d)) = 1)
    (Q : ReducedFormRep (fieldDiscriminant d)) :
    haveI := reducedFormRepCommGroup hdneg
    Q = 1 := by
  letI := reducedFormRepCommGroup hdneg
  rcases Fintype.card_eq_one_iff.mp hcard with ⟨Q0, hQ0⟩
  exact (hQ0 Q).trans (hQ0 1).symm

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
