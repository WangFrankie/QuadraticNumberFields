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

/-- Cardinality form of the genus quotient, obtained by squeezing the square-class quotient
between the surjectivity lower bound and the ambiguous-ideal upper bound. -/
theorem card_narrowSquareQuotient_eq_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) = 2 ^ (ramifiedPrimeCount d - 1) :=
  le_antisymm (card_narrowSquareQuotient_le_genusBound d)
    (genusBound_le_card_narrowSquareQuotient d)

/-- Cardinality equality between the square-class quotient and the genus-character target. -/
theorem card_narrowSquareQuotient_eq_genusCharacterTargetRelation
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) = Nat.card (genusCharacterTargetRelation d) := by
  rw [card_narrowSquareQuotient_eq_genusBound, card_genusCharacterTargetRelation]

/-- The final genus quotient isomorphism:
`Cl⁺(d) / Cl⁺(d)^2` is the product-one group of signed prime-discriminant
characters. -/
noncomputable def genusQuotientEquiv
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) ≃* genusCharacterTargetRelation d := by
  refine MulEquiv.ofBijective (genusCharacterMapOnSquareQuotient d) ?_
  constructor
  · classical
    have hcard := card_narrowSquareQuotient_eq_genusCharacterTargetRelation d
    have hquot_card_ne_zero : Nat.card (narrowSquareQuotient d) ≠ 0 := by
      rw [card_narrowSquareQuotient_eq_genusBound]
      exact pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)
    haveI : Finite (narrowSquareQuotient d) :=
      Nat.finite_of_card_ne_zero hquot_card_ne_zero
    letI : Fintype (narrowSquareQuotient d) := Fintype.ofFinite _
    letI : Fintype (genusCharacterTargetRelation d) := Fintype.ofFinite _
    have hcard' : Fintype.card (narrowSquareQuotient d) =
        Fintype.card (genusCharacterTargetRelation d) := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    exact ((Fintype.bijective_iff_surjective_and_card (genusCharacterMapOnSquareQuotient d)).2
      ⟨genusCharacterMapOnSquareQuotient_surjective d, hcard'⟩).1
  · exact genusCharacterMapOnSquareQuotient_surjective d

/-- The genus quotient equivalence agrees with the genus-character map on
representatives. -/
theorem genusQuotientEquiv_apply_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    genusQuotientEquiv d (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      genusCharacterMap d C := by
  rw [genusQuotientEquiv]
  exact genusCharacterMapOnSquareQuotient_mk' d C

end Genus
end ClassGroup
end QuadraticNumberFields
