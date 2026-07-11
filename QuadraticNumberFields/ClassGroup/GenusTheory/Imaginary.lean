/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.MainTheorem
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Genus Cardinalities for Imaginary Quadratic Class Groups

For `d < 0` the narrow and ordinary ideal class groups of `ℚ(√d)` coincide,
so the exact narrow genus cardinalities transfer to the ordinary class group.
The result is stated uniformly using `ramifiedPrimeCount d`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- For an imaginary quadratic field, the two-torsion subgroup of the ordinary
class group has the exact genus-theory cardinality. -/
theorem card_classGroupTwoTorsion_eq_two_pow_sub_one_of_neg (hd : d < 0) :
    Nat.card (ClassGroup.twoTorsion OK) = 2 ^ (ramifiedPrimeCount d - 1) :=
  calc
    Nat.card (ClassGroup.twoTorsion OK) =
        Nat.card (NarrowClassGroup.twoTorsion OK) :=
      (Subgroup.card_twoTorsion_congr
        (Qsqrtd.Imaginary.narrowMulEquivClassGroup d hd)).symm
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
      card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one d

/-- For an imaginary quadratic field, the square-class quotient of the ordinary
class group has the exact genus-theory cardinality. -/
theorem card_squareClassGroup_eq_two_pow_sub_one_of_neg (hd : d < 0) :
    Nat.card (squareQuotient (Cl(d))) = 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_squareQuotient_eq_card_twoTorsion]
  exact card_classGroupTwoTorsion_eq_two_pow_sub_one_of_neg d hd

end GenusTheory
end ClassGroup
end QuadraticNumberFields
