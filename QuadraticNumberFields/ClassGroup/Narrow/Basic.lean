/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.NumberField.NarrowClassGroup
import QuadraticNumberFields.ClassGroup.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Units.Fundamental

/-!
# Narrow Class Groups of Quadratic Fields

This file specializes the basic `NarrowClassGroup` API to the standard
quadratic fields `Qsqrtd d`.

## TODO

For Keune Ch6 Ex. 11, add the real quadratic narrow-class-number dichotomy.

* Choose a fundamental unit `ε` for `𝓞(ℚ(√d))`.
* Prove the two cases for `narrowToClassGroup`, depending on whether `ε` is
  totally positive.
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

/-- The narrow class number of `ℚ(√d)`. -/
noncomputable def narrowClassNumber : ℕ :=
  NumberField.narrowClassNumber (Qsqrtd (d : ℚ))

/-- View a unit of the ring of integers inside the fraction field. -/
noncomputable abbrev unitToFractionRing :
    OKˣ →* (FractionRing OK)ˣ :=
  _root_.Units.map (algebraMap OK (FractionRing OK)).toMonoidHom

/-- Forget the positivity condition and map the narrow class group to the ordinary
ideal class group. -/
noncomputable abbrev narrowToClassGroup :
    Cl⁺(d) →* Cl(d) :=
  NarrowClassGroup.toClassGroup OK

/-! ### Keune, Chapter 6, Exercise 11 -/

/-- Keune Ch6 Ex. 11: the narrow class number is twice the ordinary class
number when the normalized fundamental unit is totally positive. -/
theorem narrowClassNumber_eq_two_mul_classNumber_of_isTotallyPositive_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    narrowClassNumber d = 2 * NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  sorry

/-- Keune Ch6 Ex. 11: the narrow class number equals the ordinary class number
when the normalized fundamental unit is not totally positive. -/
theorem narrowClassNumber_eq_classNumber_of_not_isTotallyPositive_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK))
    (hε_tp : ¬ NarrowClassGroup.IsTotallyPositive
      ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    narrowClassNumber d = NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  sorry

/-- Keune Ch6 Ex. 11, with the two class-number cases bundled together. -/
theorem narrowClassNumber_eq_cases_fundamentalUnit
    (hd : 0 < d) (ε : OKˣ)
    (hε : Units.IsFundamentalUnit ε)
    (hε_pos : ∃ σ : FractionRing OK →+* ℝ,
      0 < σ ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK)) :
    (NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) →
      narrowClassNumber d = 2 * NumberField.classNumber (Qsqrtd (d : ℚ))) ∧
    (¬ NarrowClassGroup.IsTotallyPositive
        ((unitToFractionRing d ε : (FractionRing OK)ˣ) : FractionRing OK) →
      narrowClassNumber d = NumberField.classNumber (Qsqrtd (d : ℚ))) := by
  constructor
  · exact narrowClassNumber_eq_two_mul_classNumber_of_isTotallyPositive_fundamentalUnit
      d hd ε hε hε_pos
  · exact narrowClassNumber_eq_classNumber_of_not_isTotallyPositive_fundamentalUnit
      d hd ε hε hε_pos

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
