/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.QuotientEquiv

/-!
# Genus Formula

This file states the genus formula for the new narrow-class-group genus-theory
layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The genus formula for quadratic fields, stated on the narrow class group. -/
theorem genusFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) :=
  card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one d

/-- The genus formula is equivalent to the principal-genus kernel statement for the
genus-character map. -/
theorem genusFormula_iff_genusCharacterMap_ker_eq_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) ↔
      (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  constructor
  · intro _
    apply (genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d).mp
    exact (MonoidHom.ker_eq_bot_iff (genusCharacterMapOnSquareQuotient d)).mpr
      (genusQuotientEquiv d).injective
  · intro _
    exact genusFormula d

/-- The narrow two-torsion has cardinality equal to the number of genera. -/
theorem card_narrowClassGroupTwoTorsion_eq_numberOfGenera
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = numberOfGenera d :=
  (card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion d).symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
