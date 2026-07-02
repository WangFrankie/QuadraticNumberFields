/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.Bound
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

/-- The descended genus-character map has kernel of cardinality one. -/
theorem genusCharacterMapOnSquareQuotient_ker_card_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (genusCharacterMapOnSquareQuotient d).ker = 1 := by
  have hcard := genusCharacterMapOnSquareQuotient_card_eq_ker_mul_target d
  rw [card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one,
    card_genusCharacterTargetRelation] at hcard
  have hpos : 0 < 2 ^ (ramifiedPrimeCount d - 1) :=
    pow_pos (by norm_num : 0 < (2 : ℕ)) _
  exact Nat.eq_of_mul_eq_mul_right hpos (by simpa using hcard.symm)

/-- The descended genus-character map has trivial kernel. -/
theorem genusCharacterMapOnSquareQuotient_ker_eq_bot
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (genusCharacterMapOnSquareQuotient d).ker = ⊥ :=
  Subgroup.card_eq_one.mp (genusCharacterMapOnSquareQuotient_ker_card_eq_one d)

/-- Cardinality equality between the square-class quotient and the genus-character target. -/
theorem card_narrowClassGroupSquareQuotient_eq_genusCharacterTargetRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) =
      Nat.card (genusCharacterTargetRelation d) := by
  rw [genusCharacterMapOnSquareQuotient_card_eq_ker_mul_target,
    genusCharacterMapOnSquareQuotient_ker_card_eq_one, one_mul]

/-- The final genus quotient isomorphism:
`Cl⁺(d) / Cl⁺(d)^2` is the product-one group of signed prime-discriminant
characters. -/
noncomputable def genusQuotientEquiv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) ≃* genusCharacterTargetRelation d := by
  refine MulEquiv.ofBijective (genusCharacterMapOnSquareQuotient d) ?_
  exact ⟨(MonoidHom.ker_eq_bot_iff (genusCharacterMapOnSquareQuotient d)).mp
      (genusCharacterMapOnSquareQuotient_ker_eq_bot d),
    (genusCharacterMapOnSquareQuotient_shortExact d).2.2⟩

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
