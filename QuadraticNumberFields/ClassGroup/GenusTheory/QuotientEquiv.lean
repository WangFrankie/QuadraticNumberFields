/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals
import QuadraticNumberFields.ClassGroup.GenusTheory.ExactSequence
import QuadraticNumberFields.ClassGroup.GenusTheory.NumberOfGenera

/-!
# The Genus Quotient Equivalence

This file states the final genus-theory isomorphism between the narrow
square-class quotient and the product-one sign-vector target.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- Cardinality form of the genus quotient. -/
theorem card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) = 2 ^ (ramifiedPrimeCount d - 1) :=
  le_antisymm (card_narrowClassGroupSquareQuotient_le_two_pow_sub_one d)
    (two_pow_sub_one_le_card_narrowClassGroupSquareQuotient d)

/-- The genus-theory square-class quotient is finite. -/
instance instFiniteNarrowClassGroupSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Finite (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) :=
  Nat.finite_of_card_ne_zero <| by
    rw [card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one]
    exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)

/-- Cardinality equality between the square-class quotient and the genus-character target. -/
theorem card_narrowClassGroupSquareQuotient_eq_genusCharacterTargetRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) =
      Nat.card (genusCharacterTargetRelation d) := by
  rw [card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one,
    card_genusCharacterTargetRelation]

/-- The final genus quotient isomorphism:
`Cl⁺(d) / Cl⁺(d)^2` is the product-one group of signed prime-discriminant
characters. -/
noncomputable def genusQuotientEquiv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) ≃* genusCharacterTargetRelation d := by
  refine MulEquiv.ofBijective (genusCharacterMapOnSquareQuotient d) ?_
  exact Function.Surjective.bijective_of_nat_card_le
    (genusCharacterMapOnSquareQuotient_surjective d)
    (le_of_eq (card_narrowClassGroupSquareQuotient_eq_genusCharacterTargetRelation d))

/-- The genus quotient equivalence agrees with the genus-character map on
representatives. -/
theorem genusQuotientEquiv_apply_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    genusQuotientEquiv d (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      genusCharacterMap d C :=
  genusCharacterMapOnSquareQuotient_mk' d C

end GenusTheory
end ClassGroup
end QuadraticNumberFields
