/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Diophantine
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Residue

/-!
# Reduced-Form Counts for the Conductor-Two Route

This file contains the finite reduced-form computations, lower bounds, and
exact-cardinality consequences used by the conductor-`2` Weber/CM assembly.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- A concrete reduced-form cardinality computation supplies the Forms-side
conductor-`2` class-number-three statement. -/
theorem conductorTwoFormClassNumberThree_of_reducedForms_card
    (p : ℕ)
    (hcard :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3) :
    ConductorTwoFormClassNumberThree p :=
  hcard

/-- The Forms-side conductor-`2` statement is equivalent to the reduced-form
cardinality statement at discriminant `-4p`. -/
theorem conductorTwoFormClassNumberThree_iff_reducedForms_card
    (p : ℕ) :
    ConductorTwoFormClassNumberThree p ↔
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  rfl

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

/-- In the non-exceptional inert prime branch, the conductor-`2` discriminant
`-4p` has at least three primitive reduced positive definite forms.

For `p = 11` this uses the finite table. For larger `p`, the three forms are
`(1, 0, p)` and `(4, ±2, (p + 1) / 4)`, with the quotient represented by the
integer `2 * (p / 8) + 1`. -/
theorem three_le_conductor_two_reduced_forms_card
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3) :
    3 ≤ (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card := by
  by_cases hp11 : p = 11
  · subst p
    have hcard :=
      conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet 11
        (by norm_num [heegnerPrimeSet]) (by norm_num)
    omega
  · obtain ⟨m, hm, hm_ge, hm_odd⟩ :
        ∃ m : ℤ, 4 * m = (p : ℤ) + 1 ∧ 4 ≤ m ∧ m % 2 = 1 := by
      refine ⟨2 * (p / 8 : ℤ) + 1, ?_, ?_, ?_⟩
      · omega
      · have hp_div_ge : 2 ≤ p / 8 := by omega
        omega
      · omega
    exact
      BinaryQuadraticForm.three_le_card_enumPrimitiveReducedForms_neg_four_mul
        p m hp hm hm_ge hm_odd

/-- In the inert branch, class number one for `ℚ(√-p)` is equivalent on the
Forms side to the field-discriminant reduced-form count at `-p`. -/
theorem field_reduced_forms_card_eq_classNumberQsqrtd
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card =
      classNumberQsqrtd (-(p : ℤ)) := by
  have hp_pos_int : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hdneg : -(p : ℤ) < 0 := neg_neg_iff_pos.mpr hp_pos_int
  have hclass_forms := classNumberQsqrtd_eq_reducedForms_card (-(p : ℤ)) hdneg
  rw [BinaryQuadraticForm.fieldDiscriminant_neg_natCast_of_nat_mod_eight_eq_three hp8]
    at hclass_forms
  exact hclass_forms.symm

/-- In the inert branch, class number one for `ℚ(√-p)` gives a singleton
reduced-form enumeration at field discriminant `-p`. -/
theorem field_reduced_forms_card_eq_one_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1 := by
  rw [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8, hclass]

/-- The remaining upper bound `h(-4p) ≤ 3`, combined with the three explicit
conductor-`2` reduced forms, gives the exact conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  le_antisymm hupper (three_le_conductor_two_reduced_forms_card p hp hp8 hp_ne_three)

/-- Class number one for the maximal order, plus the remaining conductor-`2`
upper bound, gives the exact conductor-`2` reduced-form count. The class-number
hypothesis is first transported to the field-discriminant reduced-form count,
so this theorem is ready for either a coordinate upper-bound proof or a future
quadratic-order/Picard proof. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  have _hfield :=
    field_reduced_forms_card_eq_one_of_classNumber_one p hp hp8 hclass
  exact conductor_two_reduced_forms_card_eq_three_of_card_le_three p hp hp8 hp_ne_three hupper

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
on finite form-class cardinalities. -/
theorem conductor_two_formClass_card_le_three_mul_field_formClass_card_of_class_cover
    (p : ℕ) (hcover : ConductorTwoFormClassCoverData p) :
    Fintype.card (BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) ≤
      3 * Fintype.card (BinaryQuadraticForm.FormClass (-(p : ℤ))) := by
  classical
  let S : Finset (BinaryQuadraticForm.FormClass (-(4 * (p : ℤ)))) := Finset.univ
  let T : Finset (BinaryQuadraticForm.FormClass (-(p : ℤ))) := Finset.univ
  have hbound : S.card ≤ 3 * T.card := by
    have hmaps : ∀ Q ∈ S, hcover.toFieldClass Q ∈ T := by
      simp [T]
    have hfiber : ∀ R ∈ T, (S.filter fun Q => hcover.toFieldClass Q = R).card ≤ 3 := by
      intro R _hR
      have hcard :
          Nat.card
              { Q : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))) //
                hcover.toFieldClass Q = R } =
            (S.filter fun Q => hcover.toFieldClass Q = R).card := by
        apply Nat.subtype_card
        intro Q
        simp [S]
      rw [← hcard]
      exact hcover.fiber_card_le_three R
    exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber
  simpa [S, T] using hbound

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_class_cover
    (p : ℕ) (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  have hbound :=
    conductor_two_formClass_card_le_three_mul_field_formClass_card_of_class_cover
      p hcover
  simpa [BinaryQuadraticForm.formClass_card_eq_enumPrimitiveReducedForms_card] using hbound

/-- Quotient-level conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_class_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Class number one plus quotient-level conductor-`2` cover data gives the exact
conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_class_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoFormClassCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (by
      have hupper :=
        conductor_two_reduced_forms_card_le_three_mul_classNumber_of_class_cover
          p hp hp8 hcover
      rw [hclass] at hupper
      omega)

end Heegner
end QuadraticNumberFields
