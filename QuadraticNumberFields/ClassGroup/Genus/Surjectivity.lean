/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.ExactSequence
import QuadraticNumberFields.ClassGroup.Genus.SquareClass

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
  intro χ
  obtain ⟨Q, hQ⟩ := genusCharacterMapOnSquareQuotient_surjective d χ
  obtain ⟨C, rfl⟩ := QuotientGroup.mk'_surjective (narrowSquareSubgroup d) Q
  exact ⟨C, by simpa [genusCharacterMapOnSquareQuotient_mk'] using hQ⟩

/-- Surjectivity gives the lower bound for the narrow square-class quotient. -/
theorem genusBound_le_card_narrowSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    2 ^ (ramifiedPrimeCount d - 1) ≤ Nat.card (narrowSquareQuotient d) := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
