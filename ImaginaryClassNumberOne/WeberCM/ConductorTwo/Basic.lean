/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QNFMathlib.Data.Int.Squarefree
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import FormClassGroup.ClassGroup.ClassNumber
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Basic Conductor-Two Weber/CM Setup

This file contains the shared conductor-`2` interface statements used by the
Weber/CM assembly: the class-number-three Prop, discriminant bridges, and the
specialized order class-number formula interface.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Class-number-three statement for the conductor-`2` discriminant `-4p`.

This is the conductor-`2` class-number-three statement used by the Weber/CM
route, stated as the primitive reduced-form cardinality at discriminant `-4p`.
The current proof route establishes it through reduced forms, while the
quadratic-order/Picard interpretation remains the Cox boundary. -/
def ConductorTwoClassNumberThree (p : ℕ) : Prop :=
  (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3

/-- In the inert-prime branch `p ≡ 3 (mod 8)`, the conductor-`2` order
discriminant is `2 ^ 2` times the field discriminant, namely `-4p`. -/
theorem conductor_two_order_discriminant_eq_neg_four_mul
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℤ) ^ 2 * BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) =
      -(4 * (p : ℤ)) := by
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8]
  ring

/-- In the inert branch `p % 8 = 3`, the forms-side field discriminant at `-p`
agrees with the number-field discriminant of `ℚ(√-p)`. -/
theorem fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) =
      NumberField.discr (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := by
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8,
    RingOfIntegers.discr_of_mod_four_eq_one (-(p : ℤ))
      (Int.neg_natCast_emod_four_eq_one_of_nat_mod_eight_eq_three hp8)]

/-- The concrete order `Zsqrtd (-p)` has standard-basis discriminant `-4p`.

For `p ≡ 3 (mod 8)`, the maximal order in `ℚ(√-p)` is half-integral, so this
is the expected conductor-`2` quadratic order.  The statement deliberately
records only the basis discriminant; the Picard/order class-number formula is
kept as the separate Cox boundary below. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul (p : ℕ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      -(4 * (p : ℤ)) := by
  rw [RingOfIntegers.discr_zsqrtd_basis]
  ring

/-- The concrete conductor-`2` order model `Zsqrtd (-p)` has discriminant
`2 ^ 2` times the field discriminant in the inert branch. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant
    (p : ℕ) (hp8 : p % 8 = 3) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      (2 : ℤ) ^ 2 * BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) := by
  rw [conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul,
    conductor_two_order_discriminant_eq_neg_four_mul p hp8]

/-- The concrete conductor-`2` order model `Zsqrtd (-p)` has discriminant
`2 ^ 2` times the number-field discriminant in the inert branch. -/
theorem conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_numberField_discr
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) :
    Algebra.discr ℤ (QuadraticAlgebra.basis (-(p : ℤ)) 0 :
      Module.Basis (Fin 2) ℤ (Zsqrtd (-(p : ℤ)))) =
      (2 : ℤ) ^ 2 * NumberField.discr (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)) := by
  rw [conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant p hp8,
    fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three p hp8]

/-- The conductor-`2` local factor in Cox's order class-number formula is `3`
for the inert-prime branch `p ≡ 3 (mod 8)`. -/
theorem conductor_two_order_class_number_formula_factor_eq_three
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3 := by
  rw [kroneckerTwo_neg_natCast_eq_neg_one_of_nat_mod_eight_eq_three hp8]
  norm_num

/-- Cox order class-number formula for the conductor-`2` order in the
non-exceptional inert branch.

This is exactly the missing order/Picard class-number formula input: primitive
reduced forms of discriminant `-4p` count the conductor-`2` order class number,
and Cox's formula relates it to the maximal-order class number with the inert
local factor at `2`.  The hypothesis `p ≠ 3` records that the unit index in Cox
Theorem 7.24 is `1`; the exceptional `p = 3` order has extra units.

The BHS conductor-`2` assembly does not use an unconditional proof of this Prop.
That full Cox 7.24 / Corollary 7.28 route is future quadratic-order/Picard-group
infrastructure.  The current assembly keeps only sorry-free finite-table
instances of this Prop and the conditional fiber-residue upper-bound route. -/
def ConductorTwoOrderClassNumberFormula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (_hp8 : p % 8 = 3) (_hp_ne_three : p ≠ 3) : Prop :=
  ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
    (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
      ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2))

end Heegner
end QuadraticNumberFields
