/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Cox.Equivalence

/-!
# Form class group structure via Cox 7.7 transport

This file transports the ideal class-group law from `ClassGroup` to
`FormClass (fieldDiscriminant d)` across the Cox 7.7 equivalence, yielding
a `CommGroup` structure and a multiplicative equivalence property.

The group structure is exposed as a canonical instance when negativity is
available as `[Fact (d < 0)]`; `formClassCommGroup hdneg` is the explicit
proof-parametrized helper used by older Cox statements that still take
`hdneg : d < 0` directly.

## Main declarations

* `formClassCommGroup` : transported `CommGroup` structure on form classes
* `instFormClassCommGroup` : canonical transported `CommGroup` instance
* `formClassEquivClassGroup_mul` : the Cox equivalence preserves multiplication

## TODO

* The computable Gauss composition pipeline is in `Forms.Computable.Composition`
  (`composeForm`, CRT-adjusted), `Forms.Computable.Reduction` (`reduceForm`,
  well-founded recursion), and `Forms.Computable.ClassGroup` (`gaussMul`,
  `composeAndReduce`).  The consistency theorem
  `gaussMul_eq_reducedFormRepMul` identifies this executable multiplication
  with the transported class-group law on reduced representatives.

* Concrete class-group isomorphism types for `-5`, `-23`, `-21` live in
  `Forms.Computable.Structure` (standard type descriptions plus cyclic / Klein
  four-group identification tools).

* The Cox ideal-class bridge for direct concordant Gauss composition is proved in
  `Forms.ClassGroup.CoxComposition`
  (`FormClass.composeConcordantOfRepresentatives_eq_of_mk_eq`).
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section GroupStructure

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Transported `CommGroup` structure on `FormClass (fieldDiscriminant d)` via
the Cox 7.7 equivalence.

The executable representative-level multiplication is `gaussMul`; see
`Forms.Computable.ClassGroup.gaussMul_eq_reducedFormRepMul` for the theorem
identifying it with the transported operation. -/
@[reducible]
noncomputable def formClassCommGroup (hdneg : d < 0) :
    CommGroup (FormClass (fieldDiscriminant d)) :=
  Equiv.commGroup (formClassEquivClassGroup hdneg)

/-- Canonical transported `CommGroup` instance on form classes of negative
fundamental discriminant fields. -/
noncomputable instance instFormClassCommGroup {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]
    [Fact (d < 0)] : CommGroup (FormClass (fieldDiscriminant d)) :=
  formClassCommGroup (Fact.out)

/-- The Cox 7.7 equivalence preserves multiplication when `FormClass` carries
the transported group structure.

At the reduced-representative level, `Forms.Computable.ClassGroup` identifies
the explicit Gauss composition and reduction pipeline with this transported
multiplication. -/
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
