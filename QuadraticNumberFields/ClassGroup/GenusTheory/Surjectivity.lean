/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Formula

/-!
# Genus-Character Surjectivity

This file contains the weak odd-discriminant genus-theory boundary needed by the
class-number-one sieve. It separates the route proving the product genus-character
map is surjective from the stronger principal-genus theorem.

The main missing mathematical input is the Cox/Gauss surjectivity step translated
to ideal classes: choose primes in arithmetic progressions with prescribed
Legendre symbols, use the splitting criterion in `ℚ(√d)`, and take a prime ideal
above the resulting split rational prime.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

/-- **Odd genus-character surjectivity.** In the odd fundamental-discriminant
branch, every sign vector satisfying the single product relation is realized by
the odd genus-character product of an ideal class.

This is the weak Cox/Gauss genus-theory input needed for divisibility. The
intended proof uses CRT to prescribe Legendre symbols, Dirichlet's theorem on
primes in arithmetic progressions, the splitting criterion for `ℚ(√d)`, and the
norm calculation for a prime ideal over a split rational prime. -/
theorem oddGenusCharacterProductToRelationSubgroup_surjective_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) (hrel : oddGenusProductRelation d hd_neg) :
    Function.Surjective
      (oddGenusCharacterProductToRelationSubgroup d hd_neg hrel) := by
  sorry

/-- **Weak odd genus-theory divisibility.** For an imaginary quadratic field with
odd fundamental discriminant (`d % 4 = 1`), the genus-theory factor
`2 ^ (t - 1)` divides the class number.

This is weaker than the full principal-genus cardinality formula
`genusFormula_of_mod_four_eq_one`: it only uses surjectivity of the genus-character
product onto the relation subgroup, not the identification of its kernel with
the square-class subgroup. -/
theorem genus_divisibility_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd_neg : d < 0)
    (hd4 : d % 4 = 1) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  let hrel := oddGenusProductRelation_of_mod_four_eq_one d hd_neg hd4
  exact genus_divisibility_of_oddGenusCharacterProduct_surjective_of_discr_odd
    d hd_neg hodd hrel
    (oddGenusCharacterProductToRelationSubgroup_surjective_of_mod_four_eq_one
      d hd_neg hd4 hrel)

end ClassGroup
end QuadraticNumberFields
