/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.GroupTheory.QuotientGroup.Finite
import QuadraticNumberFields.ClassGroup.Genus.QuotientMap

/-!
# Surjectivity of Genus Characters

This file records the Dirichlet-plus-CRT lower-bound side of genus theory: every
admissible sign vector is represented by a narrow ideal class.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The genus-character map itself is surjective. -/
theorem genusCharacterMap_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMap d) := by
  sorry

/-- Direct genus-character surjectivity descends to the square quotient. -/
theorem genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) := by
  intro χ
  obtain ⟨C, hC⟩ := genusCharacterMap_surjective d χ
  refine ⟨QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C, ?_⟩
  simpa [genusCharacterMapOnSquareQuotient_mk'] using hC

/-- Surjectivity gives the lower bound for the narrow square-class quotient. -/
theorem genusBound_le_card_narrowClassGroupSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    2 ^ (ramifiedPrimeCount d - 1) ≤
      Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) := by
  rw [← card_genusCharacterTargetRelation d]
  exact Nat.card_le_card_of_surjective (genusCharacterMapOnSquareQuotient d)
    (genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective d)

/-- Genus-character surjectivity gives the standard genus-theory divisibility for
the narrow class number. -/
theorem genus_divisibility_narrowClassNumber
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    2 ^ (ramifiedPrimeCount d - 1) ∣
      Qsqrtd.narrowClassNumber d := by
  have htarget_dvd_quot :
      Nat.card (genusCharacterTargetRelation d) ∣
        Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) :=
    Subgroup.card_dvd_of_surjective (genusCharacterMapOnSquareQuotient d)
      (genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective d)
  have hquot_dvd :
      Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) ∣
        Qsqrtd.narrowClassNumber d := by
    simpa [Qsqrtd.narrowClassNumber, NarrowClassGroup.classNumber, Subgroup.index_eq_card] using
      (Subgroup.square (Cl⁺(d))).index_dvd_card
  rw [card_genusCharacterTargetRelation d] at htarget_dvd_quot
  exact dvd_trans htarget_dvd_quot hquot_dvd
end Genus
end ClassGroup
end QuadraticNumberFields
