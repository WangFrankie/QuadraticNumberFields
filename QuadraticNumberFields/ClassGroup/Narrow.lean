/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.NumberField.NarrowClassGroup
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

/-!
# Narrow Class Groups of Quadratic Fields

This file specializes `NarrowClassGroup` to the standard quadratic fields
`Qsqrtd d`.
-/

open scoped NumberField nonZeroDivisors

namespace QuadraticNumberFields

/-- Scoped notation for the narrow ideal class group of `𝓞(ℚ(√d))`. -/
scoped[QuadraticNumberFields.ClassGroup]
  notation "Cl⁺(" d ")" => NarrowClassGroup
    (NumberField.RingOfIntegers
      (Qsqrtd ((d : ℤ) : ℚ)))

namespace Qsqrtd

open _root_.Qsqrtd

open scoped QuadraticNumberFields.ClassGroup

section NarrowClassGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞 (Qsqrtd (d : ℚ))

-- Number-field APIs elaborate `Qsqrtd` through `DivisionRing.toRatAlgebra`,
-- so this section supplies the matching quadratic-field structure.
--? NEED DECIDE
local instance instQsqrtdRatAlgebraIsQuadraticExtension :
    Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) :=
  { finrank_eq_two' := finrank_ratAlgebra_eq_two ((d : ℤ) : ℚ) }

local instance instQsqrtdRatAlgebraQuadraticField : QuadraticField (Qsqrtd (d : ℚ)) :=
  { isQuadratic := inferInstance }

/-- The narrow class number of `ℚ(√d)`. -/
noncomputable def narrowClassNumber : ℕ :=
  NumberField.narrowClassNumber (Qsqrtd (d : ℚ))

/-- Forget the positivity condition and map the narrow class group to the ordinary
ideal class group. -/
noncomputable abbrev narrowToClassGroup :
    Cl⁺(d) →* Cl(d) :=
  NarrowClassGroup.toClassGroup OK

/-- If every unit of the fraction field is totally positive, the narrow and
ordinary class groups are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_forall_isTotallyPositive OK hpos

/-- If every unit of the fraction field is totally positive, then
`narrowToClassGroup` is bijective. -/
theorem narrowToClassGroup_bijective_of_forall_isTotallyPositive
    (hpos : ∀ x : (FractionRing OK)ˣ,
      NarrowClassGroup.IsTotallyPositive (x : FractionRing OK)) :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_forall_isTotallyPositive OK hpos

namespace Imaginary

/-- If `d < 0`, the fraction field of `𝓞(ℚ(√d))` has no real embeddings. -/
theorem isEmpty_fractionRing_realEmbeddings (hd : d < 0) :
    IsEmpty (FractionRing OK →+* ℝ) := by
  haveI := isTotallyComplex d hd
  exact NumberField.isEmpty_fractionRing_realEmbeddings_of_isTotallyComplex (Qsqrtd (d : ℚ))

/-- For imaginary quadratic fields, the narrow and ordinary principal fractional
ideal subgroups coincide. -/
theorem narrowPrincipalIdeals_eq_principalIdeals (hd : d < 0) :
    NarrowClassGroup.narrowPrincipalIdeals OK (FractionRing OK) =
      (toPrincipalIdeal OK (FractionRing OK)).range := by
  haveI := isTotallyComplex d hd
  exact
    NumberField.narrowPrincipalIdeals_eq_principalIdeals_of_isTotallyComplex
      (Qsqrtd (d : ℚ))

/-- For imaginary quadratic fields, the narrow class group is isomorphic to the
ordinary ideal class group. -/
noncomputable def narrowMulEquivClassGroup (hd : d < 0) :
    Cl⁺(d) ≃* Cl(d) := by
  haveI := isTotallyComplex d hd
  exact NumberField.narrowMulEquivClassGroupOfIsTotallyComplex (Qsqrtd (d : ℚ))

/-- Nonempty form of `narrowMulEquivClassGroup`. -/
theorem nonempty_narrowMulEquivClassGroup (hd : d < 0) :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  ⟨narrowMulEquivClassGroup d hd⟩

/-- For imaginary quadratic fields, `narrowToClassGroup` is bijective. -/
theorem narrowToClassGroup_bijective (hd : d < 0) :
    Function.Bijective (narrowToClassGroup d) := by
  haveI := isTotallyComplex d hd
  exact NumberField.narrowToClassGroup_bijective_of_isTotallyComplex (Qsqrtd (d : ℚ))

end Imaginary

/-- If the fraction field has no real embeddings, the narrow and ordinary class
groups are isomorphic. -/
theorem nonempty_narrowMulEquivClassGroup_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Nonempty (Cl⁺(d) ≃* Cl(d)) :=
  NarrowClassGroup.nonempty_mulEquivClassGroup_of_isEmpty OK

/-- If the fraction field has no real embeddings, then `narrowToClassGroup` is
bijective. -/
theorem narrowToClassGroup_bijective_of_isEmpty
    [IsEmpty (FractionRing OK →+* ℝ)] :
    Function.Bijective (narrowToClassGroup d) :=
  NarrowClassGroup.toClassGroup_bijective_of_isEmpty OK

end NarrowClassGroup

end Qsqrtd

end QuadraticNumberFields
