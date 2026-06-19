/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import FormClassGroup.ClassGroup.ClassNumber
import ImaginaryClassNumberOne.WeberData.Core
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbol

/-!
# Forms Provider for the Weber Data Interface

This file contains the reduced-forms route for supplying the conductor-`2`
ring-class-number input used by the Baker-Heegner-Stark Weber/CM interface.

The core Weber data interface remains independent of this file.  Import this
module only when the proof route explicitly goes through primitive reduced
binary quadratic forms.

## Main definitions

* `ConductorTwoFormClassNumberThreeData`: Forms-side class-number-three input for
  primitive reduced forms of discriminant `-4p` in the `p ≠ 3` inert branch.
* `conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet`: the
  finite-table reduced-form computation for the non-exceptional inert Heegner
  primes.
* `conductor_two_reduced_forms_card_order_class_number_formula`: the explicit
  Cox/order class-number formula boundary for the conductor-`2` route.
* `hasRingClassNumberThreeAtConductorTwo_of_forms`: the bridge from the Forms
  provider to the core ring-class-number interface.
* `formsInertPrimeWeberDataProvider`: the reduced-forms route packaged as the
  core inert-prime provider interface.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Forms-side class-number-three data for the conductor-`2` discriminant `-4p`.

This is the Cox/reduced-forms route into the conductor-`2` ring-class-number
input. It deliberately records only the computable primitive reduced form count,
leaving the still-missing Cox order class-number formula as the named bridge. -/
structure ConductorTwoFormClassNumberThreeData (p : ℕ) where
  /-- The discriminant whose primitive positive definite form classes are counted. -/
  discriminant : ℤ
  /-- The conductor-`2` discriminant is `-4p`. -/
  discriminant_eq_neg_four_mul : discriminant = -(4 * (p : ℤ))
  /-- The Forms-side class number, counted by primitive reduced forms. -/
  reducedFormClassNumber : ℕ
  /-- The Forms-side class number is the cardinality of the reduced-form enumeration. -/
  reducedFormClassNumber_eq_card :
    reducedFormClassNumber =
      (BinaryQuadraticForm.enumPrimitiveReducedForms discriminant).card
  /-- Cox's conductor-`2` class-number jump gives Forms-side class number `3`. -/
  reducedFormClassNumber_eq_three : reducedFormClassNumber = 3

/-- There is Forms-side class-number-three data for the conductor-`2`
discriminant `-4p`. -/
def HasConductorTwoFormClassNumberThreeData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoFormClassNumberThreeData p)

/-- In the inert-prime branch `p ≡ 3 (mod 8)`, the conductor-`2` order
discriminant is `2 ^ 2` times the field discriminant, namely `-4p`. -/
theorem conductor_two_order_discriminant_eq_neg_four_mul
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℤ) ^ 2 * BinaryQuadraticForm.fieldDiscriminant (-(p : ℤ)) =
      -(4 * (p : ℤ)) := by
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8]
  ring

/-- The conductor-`2` local factor in Cox's order class-number formula is `3`
for the inert-prime branch `p ≡ 3 (mod 8)`. -/
theorem conductor_two_order_class_number_formula_factor_eq_three
    (p : ℕ) (hp8 : p % 8 = 3) :
    (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3 := by
  rw [kroneckerTwo_neg_natCast_eq_neg_one_of_nat_mod_eight_eq_three hp8]
  norm_num

/-- A concrete reduced-form cardinality computation supplies the Forms-side
conductor-`2` class-number-three data. -/
theorem hasConductorTwoFormClassNumberThreeData_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    HasConductorTwoFormClassNumberThreeData p := by
  exact ⟨{
    discriminant := -(4 * (p : ℤ))
    discriminant_eq_neg_four_mul := rfl
    reducedFormClassNumber :=
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card
    reducedFormClassNumber_eq_card := rfl
    reducedFormClassNumber_eq_three := hcard }⟩

/-- The Forms-side conductor-`2` data is equivalent to the reduced-form
cardinality statement at discriminant `-4p`. -/
theorem hasConductorTwoFormClassNumberThreeData_iff_reducedForms_card
    (p : ℕ) :
    HasConductorTwoFormClassNumberThreeData p ↔
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  constructor
  · rintro ⟨hforms⟩
    rw [← hforms.discriminant_eq_neg_four_mul]
    rw [← hforms.reducedFormClassNumber_eq_card]
    exact hforms.reducedFormClassNumber_eq_three
  · exact hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p

/-- Forms-side class-number-three data supplies the conductor-`2`
ring-class-number input used by the Weber/CM layer. -/
theorem hasRingClassNumberThreeAtConductorTwo_of_forms
    {p : ℕ} (hforms : HasConductorTwoFormClassNumberThreeData p) :
    HasRingClassNumberThreeAtConductorTwo p := by
  rcases hforms with ⟨hforms⟩
  exact ⟨{
    conductor := 2
    conductor_eq_two := rfl
    discriminant := hforms.discriminant
    discriminant_eq := hforms.discriminant_eq_neg_four_mul
    orderClassNumber := hforms.reducedFormClassNumber
    orderClassNumber_eq_three := hforms.reducedFormClassNumber_eq_three }⟩

/-- A reduced-form cardinality computation at discriminant `-4p` supplies the
core conductor-`2` ring-class-number input. -/
theorem hasRingClassNumberThreeAtConductorTwo_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p hcard)

/-- For the non-exceptional inert Heegner primes, the conductor-`2`
discriminant `-4p` has exactly three primitive reduced positive definite forms.

This is the finite-table reduced-form computation behind the conductor-`2`
ring/order/forms bridge. It intentionally avoids the `p = 3` unit-exception
case, where the order class-number formula has a different unit index. -/
theorem conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  rw [BinaryQuadraticForm.enumPrimitiveReducedForms_card_eq_length]
  norm_num [heegnerPrimeSet] at hp_mem
  rcases hp_mem with hp | hp | hp | hp | hp | hp
  · omega
  · have hp' : p = 11 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg44_length
  · have hp' : p = 19 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg76_length
  · have hp' : p = 43 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg172_length
  · have hp' : p = 67 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg268_length
  · have hp' : p = 163 := by exact_mod_cast hp
    subst p
    exact BinaryQuadraticForm.enumPrimitiveReducedFormsList_neg652_length

/-- The finite inert-Heegner-prime reduced-form computation supplies
Forms-side conductor-`2` class-number-three data. -/
theorem conductor_two_form_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    HasConductorTwoFormClassNumberThreeData p :=
  hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
      p hp_mem hp_ne_three)

/-- The finite inert-Heegner-prime reduced-form computation supplies the core
conductor-`2` ring-class-number-three input. -/
theorem conductor_two_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three_of_mem_heegnerPrimeSet
      p hp_mem hp_ne_three)

/-- On the finite non-exceptional inert Heegner-prime table, the conductor-`2`
reduced-form count agrees with the specialized order class-number formula. -/
theorem conductor_two_reduced_forms_card_order_class_number_formula_of_mem_heegnerPrimeSet
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
      (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
        ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)) := by
  have hcard :=
    conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet p hp_mem hp_ne_three
  have hclass : classNumberQsqrtd (-(p : ℤ)) = 1 := by
    unfold classNumberQsqrtd
    apply classNumber_eq_one_of_mem_heegnerSet
    norm_num [heegnerSet, heegnerPrimeSet] at hp_mem ⊢
    omega
  have hfactor := conductor_two_order_class_number_formula_factor_eq_three p hp8
  rw [hcard, hclass, hfactor]
  norm_num

/-- **Cox/order class-number formula, conductor `2`, reduced-form version.** In
the inert prime family `d = -p`, the primitive reduced forms of discriminant
`-4p` are counted by the maximal-order class number times the conductor-`2`
local factor.

This is the remaining mathematical input for the conductor-`2` ring/order/forms
bridge.  It should ultimately be replaced by Cox's order class-number formula
or an equivalent Picard-group computation for the quadratic order of conductor
`2`. -/
theorem conductor_two_reduced_forms_card_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3) :
    ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
      (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
        ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)) := by
  -- Cox 7.24 / Corollary 7.28, or an equivalent quadratic-order Picard-group
  -- computation, belongs here. The discriminant and local Kronecker factor
  -- specializations are already closed above.
  sorry

/-- In the inert prime family `d = -p`, class number one for `ℚ(√-p)` gives
three primitive reduced positive definite forms of conductor-`2` discriminant
`-4p`, away from the unit-exception case `p = 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  have hfactor := conductor_two_order_class_number_formula_factor_eq_three p hp8
  have hformula :=
    conductor_two_reduced_forms_card_order_class_number_formula p hp hp8 hp_ne_three
  have hcard_rat :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        3 := by
    rw [hformula, hclass, hfactor]
    norm_num
  exact_mod_cast hcard_rat

/-- **Cox forms class-number input.** In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three data for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasConductorTwoFormClassNumberThreeData p := by
  exact hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one
      p hp hp8 hp_ne_three hclass)

/-- The reduced-forms provider supplies the core conductor-`2` ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasRingClassNumberThreeAtConductorTwo p := by
  exact hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- **Deep Weber/CM input from ring-class-number three, via the Forms provider.**
The conductor-`2` ring-class-number-three datum supplies the refined Weber data:
a concrete Heegner equation solution, the associated gamma value, and its
finite-table association with `p`, in the non-exceptional inert branch `p ≠ 3`. -/
theorem conductor_two_weber_data_of_ring_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3) (horder : HasRingClassNumberThreeAtConductorTwo p) :
    HasConductorTwoClassNumberThreeWeberData p := by
  sorry

/-- The Forms provider turns conductor-`2` ring-class-number-three data into
Stark-Heegner algebraic data. -/
theorem exists_weber_data_of_conductor_two_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3)
    (horder : HasRingClassNumberThreeAtConductorTwo p) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_weber_data
    (conductor_two_weber_data_of_ring_class_number_three_of_forms p hp hp8 hp_ne_three horder)

/-- The reduced-forms route supplies Weber/CM algebraic data from class number
one in the non-exceptional inert branch. -/
theorem exists_weber_data_of_classNumber_one_inert_prime_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) := by
  exact exists_weber_data_of_conductor_two_class_number_three_of_forms p hp hp8 hp_ne_three
    (conductor_two_class_number_three_of_forms p hp hp8 hp_ne_three hclass)

/-- The reduced-forms route packaged as the core provider interface. -/
def formsInertPrimeWeberDataProvider : InertPrimeWeberDataProvider where
  exists_weber_data p _ _ hp hp8 hp_ne_three hclass :=
    exists_weber_data_of_classNumber_one_inert_prime_of_forms p hp hp8 hp_ne_three hclass

end Heegner
end QuadraticNumberFields
