/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

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

example (C : FormClass (fieldDiscriminant d)) :
    (reducedRepresentative C).1.IsReduced :=
  reducedRepresentative_isReduced C

example (C E : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
      (reducedProductRepresentative hdneg C E) = C * E :=
  reducedProductRepresentative_mk_eq_mul hdneg C E

end ReducedRepresentatives

end BinaryQuadraticForm
end QuadraticNumberFields
