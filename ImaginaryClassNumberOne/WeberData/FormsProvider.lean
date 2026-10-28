/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import BinaryQuadraticForms.Core.ConductorTwo
import FormClassGroup.ClassGroup.ClassNumber
import ImaginaryClassNumberOne.StarkHeegner

/-!
# Forms Provider for the Weber Data Interface

This file contains the reduced-forms route through the conductor-`2` step of
the Baker-Heegner-Stark Weber/CM interface.

The core Weber data interface remains independent of this file.  Import this
module only when the proof route explicitly goes through primitive reduced
binary quadratic forms.

The elementary half of the route is proved here: class number one for `ℚ(√-p)`
gives exactly three primitive reduced forms of discriminant `-4p`.  The deep
half, Heegner's Weber-function argument on the order of conductor `2`, is the
explicit hypothesis `ConductorTwoWeberInput`.

## Main definitions

* `ConductorTwoFormClassNumberThreeData`: Forms-side class-number-three input for
  primitive reduced forms of discriminant `-4p` in the `p ≠ 3` inert branch.
* `conductor_two_form_class_number_three`: class number one gives that input.
* `ConductorTwoWeberInput`: the deep Weber/CM step from that input to
  Stark-Heegner algebraic data.
* `formsInertPrimeWeberDataProvider`: the reduced-forms route packaged as the
  core inert-prime provider interface, given `ConductorTwoWeberInput`.
* `classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberInput`: the
  Baker-Heegner-Stark theorem from `ConductorTwoWeberInput`.
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

attribute [nolint simpNF] ConductorTwoFormClassNumberThreeData.mk.injEq

/-- There is Forms-side class-number-three data for the conductor-`2`
discriminant `-4p`. -/
def HasConductorTwoFormClassNumberThreeData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoFormClassNumberThreeData p)

/-- A concrete reduced-form cardinality computation gives the Forms-side
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

/-- Forms-side class-number-three data gives the conductor-`2`
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

/-- Cox forms class-number input. In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three data for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    HasConductorTwoFormClassNumberThreeData p := by
  have hneg : (-(p : ℤ)) < 0 := by
    have := hp.pos
    omega
  have hcard : (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1 := by
    have h := classNumber_qsqrtd_eq_reducedForms_card (-(p : ℤ)) hneg
    rw [hclass, BinaryQuadraticForm.fieldDiscriminant_of_mod_four_eq_one (by omega)] at h
    exact h.symm
  exact hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (BinaryQuadraticForm.card_enumPrimitiveReducedForms_neg_four_mul_eq_three hp8 hp_ne_three
      hcard)

/-- The reduced-forms provider gives the core conductor-`2` ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    HasRingClassNumberThreeAtConductorTwo p := by
  exact hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- The deep Weber/CM step of Heegner's proof in its conductor-`2` form: in the
non-exceptional inert branch, three primitive reduced forms of discriminant
`-4p` give the Stark-Heegner algebraic data.

This is Heegner's Weber-function argument on the order of conductor `2`
(Cox, Theorem 12.34).  It is recorded as an explicit input and is not proved
here.  Its premise is the Forms-side datum, which pins down the reduced-form
count; the core ring-class-number datum alone does not. -/
structure ConductorTwoWeberInput where
  /-- Three reduced forms of discriminant `-4p` give Stark-Heegner data. -/
  exists_weber_data_of_forms :
    ∀ p : ℕ, Nat.Prime p → p % 8 = 3 → p ≠ 3 →
      HasConductorTwoFormClassNumberThreeData p → Nonempty (StarkHeegnerAlgebraicData p)

/-- The reduced-forms route gives Weber/CM algebraic data from class number
one in the non-exceptional inert branch, given the conductor-`2` Weber input. -/
theorem exists_weber_data_of_classNumber_one_inert_prime_of_forms
    (hweber : ConductorTwoWeberInput)
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicData p) :=
  hweber.exists_weber_data_of_forms p hp hp8 hp_ne_three
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- The reduced-forms route packaged as the core provider interface. -/
theorem formsInertPrimeWeberDataProvider (hweber : ConductorTwoWeberInput) :
    InertPrimeWeberDataProvider :=
  ⟨fun p _ _ hp hp8 hp_ne_three hclass =>
    exists_weber_data_of_classNumber_one_inert_prime_of_forms hweber p hp hp8 hp_ne_three hclass⟩

/-- **Baker-Heegner-Stark from the conductor-`2` Weber input.** Once Heegner's
Weber-function step at conductor `2` is supplied, a negative squarefree `d`
gives class number one exactly for the nine Heegner numbers. -/
theorem classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberInput
    (hweber : ConductorTwoWeberInput)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet :=
  classNumber_eq_one_iff_mem_heegnerSet (formsInertPrimeWeberDataProvider hweber) d hd

end Heegner
end QuadraticNumberFields
