/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import BinaryQuadraticForms.Core.ConductorTwo
import FormClassGroup.ClassGroup.ClassNumber
import ImaginaryClassNumberOne.StarkHeegner

/-!
# Reduced Forms and Weber's Hypothesis at Conductor Two

This file relates class number one to primitive reduced binary quadratic
forms of conductor `2`, and states the remaining Weber existence hypothesis.

The elementary half of the route is proved here: class number one for `ℚ(√-p)`
gives exactly three primitive reduced forms of discriminant `-4p`.  The deep
half, Heegner's Weber-function argument on the order of conductor `2`, is the
explicit hypothesis `ConductorTwoWeberHypothesis`.

## Main definitions

* `ConductorTwoFormClassNumberThree`: the reduced-form class number of
  discriminant `-4p` equals `3` in the `p ≠ 3` inert case.
* `conductor_two_form_class_number_three`: the conductor-`2` class-number relation.
* `ConductorTwoWeberHypothesis`: three reduced forms of discriminant `-4p`
  imply the existence of an associated Heegner integral point.
* `inertPrimeWeberHypothesis_of_conductorTwoWeberHypothesis`: deduce Weber's
  class-number-one hypothesis from its conductor-`2` form.
* `classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberHypothesis`: the
  Baker-Heegner-Stark theorem from `ConductorTwoWeberHypothesis`.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- The reduced-form class number of the conductor-`2` discriminant `-4p` equals `3`.

The count is defined by primitive reduced forms; its identification with the
class number of the quadratic order is a separate mathematical statement. -/
structure ConductorTwoFormClassNumberThree (p : ℕ) where
  /-- The discriminant whose primitive positive definite form classes are counted. -/
  discriminant : ℤ
  /-- The conductor-`2` discriminant is `-4p`. -/
  discriminant_eq_neg_four_mul : discriminant = -(4 * (p : ℤ))
  /-- The class number counted by primitive reduced forms. -/
  reducedFormClassNumber : ℕ
  /-- The class number is the cardinality of the reduced-form enumeration. -/
  reducedFormClassNumber_eq_card :
    reducedFormClassNumber =
      (BinaryQuadraticForm.enumPrimitiveReducedForms discriminant).card
  /-- The reduced-form class number equals `3`. -/
  reducedFormClassNumber_eq_three : reducedFormClassNumber = 3

attribute [nolint simpNF] ConductorTwoFormClassNumberThree.mk.injEq

/-- The conductor-`2` discriminant `-4p` has reduced-form class number `3`. -/
def HasConductorTwoFormClassNumberThree (p : ℕ) : Prop :=
  Nonempty (ConductorTwoFormClassNumberThree p)

/-- A reduced-form count proves the conductor-`2` class-number relation. -/
theorem hasConductorTwoFormClassNumberThree_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    HasConductorTwoFormClassNumberThree p := by
  exact ⟨{
    discriminant := -(4 * (p : ℤ))
    discriminant_eq_neg_four_mul := rfl
    reducedFormClassNumber :=
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card
    reducedFormClassNumber_eq_card := rfl
    reducedFormClassNumber_eq_three := hcard }⟩

/-- The reduced-form count determines the conductor-`2` numerical parameters. -/
theorem hasConductorTwoClassNumberParameters_of_forms
    {p : ℕ} (hforms : HasConductorTwoFormClassNumberThree p) :
    HasConductorTwoClassNumberParameters p := by
  rcases hforms with ⟨hforms⟩
  exact ⟨{
    conductor := 2
    conductor_eq_two := rfl
    discriminant := hforms.discriminant
    discriminant_eq := hforms.discriminant_eq_neg_four_mul
    orderClassNumber := hforms.reducedFormClassNumber
    orderClassNumber_eq_three := hforms.reducedFormClassNumber_eq_three }⟩

/-- Cox's class-number relation. In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives class number `3` for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    HasConductorTwoFormClassNumberThree p := by
  have hneg : (-(p : ℤ)) < 0 := by
    have := hp.pos
    omega
  have hcard : (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1 := by
    have h := classNumber_qsqrtd_eq_reducedForms_card (-(p : ℤ)) hneg
    rw [hclass, BinaryQuadraticForm.fieldDiscriminant_of_mod_four_eq_one (by omega)] at h
    exact h.symm
  exact hasConductorTwoFormClassNumberThree_of_reducedForms_card p
    (BinaryQuadraticForm.card_enumPrimitiveReducedForms_neg_four_mul_eq_three hp8 hp_ne_three
      hcard)

/-- Class number one determines the conductor-`2` numerical parameters in the
non-exceptional inert prime case. -/
theorem conductor_two_class_number_parameters_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    HasConductorTwoClassNumberParameters p := by
  exact hasConductorTwoClassNumberParameters_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- The deep Weber/CM step of Heegner's proof in its conductor-`2` form: in the
non-exceptional inert branch, three primitive reduced forms of discriminant
`-4p` imply the existence of an associated Heegner integral point.

This is Heegner's Weber-function argument on the order of conductor `2`
(Cox, Theorem 12.34). It is an explicit hypothesis, not a theorem proved here.
Its premise specifies the actual reduced-form count; the numerical order
parameters alone do not determine that count. -/
def ConductorTwoWeberHypothesis : Prop :=
  ∀ p : ℕ, Nat.Prime p → p % 8 = 3 → p ≠ 3 →
    HasConductorTwoFormClassNumberThree p → Nonempty (HeegnerIntegralPoint p)

/-- Class number one gives a Heegner integral point under the conductor-`2`
Weber hypothesis. -/
theorem nonempty_heegnerIntegralPoint_of_classNumber_eq_one_of_forms
    (hweber : ConductorTwoWeberHypothesis)
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1) :
    Nonempty (HeegnerIntegralPoint p) :=
  hweber p hp hp8 hp_ne_three
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- The conductor-`2` Weber hypothesis implies the class-number-one version. -/
theorem inertPrimeWeberHypothesis_of_conductorTwoWeberHypothesis
    (hweber : ConductorTwoWeberHypothesis) :
    InertPrimeWeberHypothesis :=
  fun p _ _ hp hp8 hp_ne_three hclass =>
    nonempty_heegnerIntegralPoint_of_classNumber_eq_one_of_forms hweber p hp hp8 hp_ne_three hclass

/-- **Baker-Heegner-Stark under the conductor-`2` Weber hypothesis.** Assuming
Heegner's Weber existence statement, a negative squarefree `d`
gives class number one exactly for the nine Heegner numbers. -/
theorem classNumber_eq_one_iff_mem_heegnerSet_of_conductorTwoWeberHypothesis
    (hweber : ConductorTwoWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet :=
  classNumber_eq_one_iff_mem_heegnerSet
    (inertPrimeWeberHypothesis_of_conductorTwoWeberHypothesis hweber) d hd

end Heegner
end QuadraticNumberFields
