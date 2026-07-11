/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.UpperBound
import QuadraticNumberFields.ClassGroup.GenusTheory.LowerBound
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Exact Genus Cardinalities

This file combines the independent genus-character lower bound and
ramified-parity upper bound to determine the cardinalities of the narrow
square-class quotient and narrow two-torsion subgroup.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The narrow two-torsion subgroup has the exact genus-theory cardinality. -/
theorem card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one :
    Nat.card (NarrowClassGroup.twoTorsion OK) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  apply le_antisymm (Ambiguous.card_narrowClassGroupTwoTorsion_le_two_pow_sub_one d)
  calc
    2 ^ (ramifiedPrimeCount d - 1) ≤
        Nat.card (squareQuotient (Cl⁺(d))) :=
      two_pow_sub_one_le_card_narrowSquareClassGroup d
    _ = Nat.card (NarrowClassGroup.twoTorsion OK) := by
      simpa using
        (card_squareQuotient_eq_card_twoTorsion (G := Cl⁺(d)))

/-- The narrow square-class quotient has the exact genus-theory cardinality. -/
theorem card_narrowSquareClassGroup_eq_two_pow_sub_one :
    Nat.card (squareQuotient (Cl⁺(d))) = 2 ^ (ramifiedPrimeCount d - 1) := by
  calc
    Nat.card (squareQuotient (Cl⁺(d))) =
        Nat.card (NarrowClassGroup.twoTorsion OK) := by
      simpa using
        (card_squareQuotient_eq_card_twoTorsion (G := Cl⁺(d)))
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
      card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one d

end GenusTheory
end ClassGroup
end QuadraticNumberFields
