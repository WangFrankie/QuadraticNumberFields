/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.CoxEquivalence

/-!
# Form class group structure via Cox 7.7 transport

This file transports the ideal class-group law from `ClassGroup` to
`FormClass (fieldDiscriminant d)` across the Cox 7.7 equivalence, yielding
a `CommGroup` structure and a multiplicative equivalence property.

The group structure is a `def` (not an `instance`) to avoid uncontrolled
typeclass inference on the `Quotient` type.

## Main declarations

* `formClassCommGroup` : transported `CommGroup` structure on form classes
* `formClassEquivClassGroup_mul` : the Cox equivalence preserves multiplication

## TODO

The Cox ideal-class bridge for direct concordant Gauss composition is staged in
`Forms.CoxComposition`.  The remaining Gauss-composition work is quotient-level
well-definedness and replacing the transported multiplication with the explicit
quotient-level operation.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section GroupStructure

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Transported `CommGroup` structure on `FormClass (fieldDiscriminant d)` via
the Cox 7.7 equivalence.  This is a `def` (not an `instance`) to avoid
uncontrolled typeclass inference on the `Quotient` type.

TODO: after quotient-level Gauss composition is well-defined, replace this
transported multiplication by the explicit operation proved equivalent to it. -/
@[reducible]
noncomputable def formClassCommGroup (hdneg : d < 0) :
    CommGroup (FormClass (fieldDiscriminant d)) :=
  Equiv.commGroup (formClassEquivClassGroup hdneg)

/-- The Cox 7.7 equivalence preserves multiplication when `FormClass` carries
the transported group structure.

TODO: use the representative-level Cox composition bridge to identify the final
quotient-level explicit Gauss composition with this transported multiplication. -/
theorem formClassEquivClassGroup_mul (hdneg : d < 0) (x y : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    formClassEquivClassGroup hdneg (x * y) =
    formClassEquivClassGroup hdneg x * formClassEquivClassGroup hdneg y := by
  simp [Equiv.mul_def]

end GroupStructure

/-! ## Sanity checks -/

section SanityChecks

/-- Identity maps to identity via the Cox equivalence (with transported structure). -/
example (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    haveI := formClassCommGroup hdneg
    formClassEquivClassGroup hdneg (1 : FormClass (fieldDiscriminant d)) =
      (1 : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) := by
  simp [Equiv.one_def]

/-- Multiplication commutes with the Cox equivalence (with transported structure). -/
example (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0)
    (x y : FormClass (fieldDiscriminant d)) :
    haveI := formClassCommGroup hdneg
    formClassEquivClassGroup hdneg (x * y) =
    formClassEquivClassGroup hdneg x * formClassEquivClassGroup hdneg y := by
  simp [Equiv.mul_def]

end SanityChecks

end BinaryQuadraticForm
end QuadraticNumberFields
