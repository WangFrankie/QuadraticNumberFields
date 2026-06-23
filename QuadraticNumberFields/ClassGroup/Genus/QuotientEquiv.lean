/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.AmbiguousIdeals
import QuadraticNumberFields.ClassGroup.Genus.Surjectivity

/-!
# The Genus Quotient Equivalence

This file states the final genus-theory isomorphism between the narrow
square-class quotient and the product-one sign-vector target.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The final genus quotient isomorphism:
`Cl⁺(d) / Cl⁺(d)^2` is the product-one group of signed prime-discriminant
characters. -/
noncomputable def genusQuotientEquiv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) ≃* genusCharacterTargetRelation d := by
  sorry

/-- The genus quotient equivalence agrees with the genus-character map on
representatives. -/
theorem genusQuotientEquiv_apply_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    genusQuotientEquiv d (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      genusCharacterMap d C := by
  sorry

/-- Cardinality equality induced by the genus quotient equivalence. -/
theorem card_narrowSquareQuotient_eq_genusCharacterTargetRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) = Nat.card (genusCharacterTargetRelation d) :=
  Nat.card_congr (genusQuotientEquiv d).toEquiv

/-- Cardinality form of the genus quotient equivalence. -/
theorem card_narrowSquareQuotient_eq_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) = 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowSquareQuotient_eq_genusCharacterTargetRelation,
    card_genusCharacterTargetRelation]

end Genus
end ClassGroup
end QuadraticNumberFields
