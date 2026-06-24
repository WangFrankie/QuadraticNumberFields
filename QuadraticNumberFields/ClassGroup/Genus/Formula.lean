/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.QuotientEquiv

/-!
# Genus Formula

This file states the genus formula for the new narrow-class-group genus-theory
layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The genus formula for the narrow class group: the quotient of the narrow class
group by its subgroup of squares has cardinality `2 ^ (t - 1)`, where `t` is the
number of ramified rational primes. -/
def genusFormula (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : Prop :=
  Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) = 2 ^ (ramifiedPrimeCount d - 1)

/-- The genus formula is equivalent to the principal-genus kernel statement for the
genus-character map. -/
theorem genusFormula_iff_genusCharacterMap_ker_eq_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    genusFormula d ↔ (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  constructor
  · intro _
    apply (genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d).mp
    exact (MonoidHom.ker_eq_bot_iff (genusCharacterMapOnSquareQuotient d)).mpr
      (genusQuotientEquiv d).injective
  · intro _
    rw [genusFormula]
    exact card_narrowClassGroupSquareQuotient_eq_genusBound d

/-- The genus formula for quadratic fields, stated on the narrow class group. -/
theorem genusFormula_holds
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    genusFormula d := by
  rw [genusFormula]
  exact card_narrowClassGroupSquareQuotient_eq_genusBound d

end Genus
end ClassGroup
end QuadraticNumberFields
