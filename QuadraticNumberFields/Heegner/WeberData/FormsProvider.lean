/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Forms.ClassGroup.ClassNumber
import QuadraticNumberFields.Heegner.WeberData.Core

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

/-- **Cox forms class-number input.** In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three data for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    HasConductorTwoFormClassNumberThreeData p := by
  -- Alternative routes for this bridge:
  -- * prove Cox's order class-number formula via Picard groups of quadratic orders;
  -- * build the conductor-`2` Picard group directly and avoid reduced-form enumeration;
  -- * follow Stark's no-Weber variant, replacing this downstream input entirely.
  sorry

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
