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
The abstract exponent `t - 1` is then made explicit through the mod-`4`
computation of the ramified-prime count: `t = ω(|d|)` when `d % 4 ∈ {1, 2}`
and `t = ω(|d|) + 1` when `d % 4 = 3`, where `ω` counts distinct prime
factors.  The classical mod-`8` subdivision of the even case only selects the
prime discriminant at `2` and does not change the count.
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

/-- Corrected genus formula for `d < 0` with `d ≡ 1 (mod 4)`: the ordinary
class group has `2 ^ (ω(|d|) - 1)` square classes. -/
theorem card_squareClassGroup_of_neg_of_mod_four_eq_one
    (hd : d < 0) (hd4 : d % 4 = 1) :
    Nat.card (squareQuotient (Cl(d))) =
      2 ^ (d.natAbs.primeFactors.card - 1) := by
  rw [card_squareClassGroup_eq_two_pow_sub_one_of_neg d hd,
    ramifiedPrimeCount_of_mod_four_eq_one d hd4]

/-- Corrected genus formula for `d < 0` with `d ≡ 2 (mod 4)`: the ordinary
class group has `2 ^ (ω(|d|) - 1)` square classes. -/
theorem card_squareClassGroup_of_neg_of_mod_four_eq_two
    (hd : d < 0) (hd4 : d % 4 = 2) :
    Nat.card (squareQuotient (Cl(d))) =
      2 ^ (d.natAbs.primeFactors.card - 1) := by
  rw [card_squareClassGroup_eq_two_pow_sub_one_of_neg d hd,
    ramifiedPrimeCount_of_mod_four_eq_two d hd4]

/-- Corrected genus formula for `d < 0` with `d ≡ 3 (mod 4)`: the wild prime
`2` raises the count to `2 ^ ω(|d|)` square classes. -/
theorem card_squareClassGroup_of_neg_of_mod_four_eq_three
    (hd : d < 0) (hd4 : d % 4 = 3) :
    Nat.card (squareQuotient (Cl(d))) = 2 ^ d.natAbs.primeFactors.card := by
  rw [card_squareClassGroup_eq_two_pow_sub_one_of_neg d hd,
    ramifiedPrimeCount_of_mod_four_eq_three d hd4, Nat.add_sub_cancel]

end GenusTheory
end ClassGroup
end QuadraticNumberFields
