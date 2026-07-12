/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Genus Theory for Imaginary Quadratic Class Groups

For `d < 0`, the narrow and ordinary ideal class groups of `ℚ(√d)` coincide.
The narrow genus theorem therefore gives the rank and cardinality formulas for
the ordinary class group in terms of `ramifiedPrimeCount d`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The 2-rank of an imaginary quadratic class group is `t - 1`. -/
theorem twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_neg (hd : d < 0) :
    ClassGroup.twoRank OK = ramifiedPrimeCount d - 1 := by
  calc
    ClassGroup.twoRank OK = NarrowClassGroup.twoRank OK := by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      simpa [ClassGroup.twoRank, NarrowClassGroup.twoRank, CommGroup.twoRank] using
        (squareQuotientLinearEquiv
          (Qsqrtd.Imaginary.narrowMulEquivClassGroup d hd)).finrank_eq.symm
    _ = ramifiedPrimeCount d - 1 :=
      twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one d

/-- For an imaginary quadratic field, the square-class quotient of the ordinary
class group has the exact genus-theory cardinality. -/
theorem card_squareClassGroup_eq_two_pow_sub_one_of_neg (hd : d < 0) :
    Nat.card (squareQuotient (Cl(d))) = 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_squareQuotient_eq_two_pow_twoRank]
  exact congrArg (2 ^ ·) (twoRank_classGroup_eq_ramifiedPrimeCount_sub_one_of_neg d hd)

/-- For an imaginary quadratic field, the two-torsion subgroup of the ordinary
class group has the exact genus-theory cardinality. -/
theorem card_classGroupTwoTorsion_eq_two_pow_sub_one_of_neg (hd : d < 0) :
    Nat.card (ClassGroup.twoTorsion OK) = 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [← card_squareQuotient_eq_card_twoTorsion]
  exact card_squareClassGroup_eq_two_pow_sub_one_of_neg d hd

end GenusTheory
end ClassGroup
end QuadraticNumberFields
