/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import FormClassGroup.ClassGroup.ClassNumber
import FormClassGroup.ClassGroup.Law
import ImaginaryClassNumberOne.WeberData.Core
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import QuadraticNumberFields.RingOfIntegers.Discriminant
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
* `conductor_two_zsqrtd_basis_discriminant_eq_neg_four_mul`: the concrete
  `Zsqrtd (-p)` conductor-`2` order has basis discriminant `-4p`.
* `conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_fieldDiscriminant`:
  the same discriminant equals `2 ^ 2` times the field discriminant.
* `fieldDiscriminant_eq_numberField_discr_neg_natCast_of_nat_mod_eight_eq_three`:
  the forms-side and number-field discriminants agree for `d = -p`.
* `conductor_two_zsqrtd_basis_discriminant_eq_conductor_square_mul_numberField_discr`:
  the same bridge stated using `NumberField.discr`.
* `conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet`: the
  finite-table reduced-form computation for the non-exceptional inert Heegner
  primes.
* `three_le_conductor_two_reduced_forms_card`: the explicit lower bound coming
  from three conductor-`2` reduced forms.
* `ConductorTwoReducedFormCoverData`: the remaining forms-side upper-bound
  interface, expressed as a finite-fiber cover of conductor-`2` reduced forms by
  field-discriminant reduced forms.
* `ConductorTwoReducedFormRepCoverData`: the same upper-bound interface stated
  on finite reduced-form representative types.
* `conductor_two_reduced_forms_card_le_three_mul_classNumber_of_cover`: the
  finite-fiber cover bridge from conductor-`2` reduced forms to the maximal-order
  class number.
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

/-- Forms-side cover data for the conductor-`2` upper-bound step.

This is the explicit remaining finite-fiber interface behind the upper bound
`h(-4p) ≤ 3 * h(-p)`: every conductor-`2` reduced form maps to a field
discriminant reduced form, and each field reduced form has at most three
conductor-`2` reduced-form preimages.  Constructing this map can be done either
by a direct form-theoretic conductor-lowering argument or by the corresponding
quadratic-order/Picard-group map. -/
structure ConductorTwoReducedFormCoverData (p : ℕ) where
  /-- The conductor-lowering map on raw reduced-form representatives. -/
  toFieldForm : BinaryQuadraticForm → BinaryQuadraticForm
  /-- The map sends conductor-`2` reduced forms of discriminant `-4p` to field
  reduced forms of discriminant `-p`. -/
  maps_mem : ∀ {Q : BinaryQuadraticForm},
    Q ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ))) →
      toFieldForm Q ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))
  /-- Every field-discriminant reduced form has at most three conductor-`2`
  reduced-form preimages. -/
  fiber_card_le_three : ∀ {R : BinaryQuadraticForm},
    R ∈ BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ)) →
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).filter
        fun Q => toFieldForm Q = R).card ≤ 3

/-- There is conductor-`2` reduced-form cover data for `p`. -/
def HasConductorTwoReducedFormCoverData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoReducedFormCoverData p)

/-- Typed finite-cover data for the conductor-`2` upper-bound step.

This is the same mathematical interface as `ConductorTwoReducedFormCoverData`,
but stated directly on finite reduced-form representative types.  A future
conductor-lowering construction can target this form without separately
carrying membership proofs for raw forms. -/
structure ConductorTwoReducedFormRepCoverData (p : ℕ) where
  /-- The conductor-lowering map on finite conductor-`2` reduced representatives. -/
  toFieldRep :
    BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ))) →
      BinaryQuadraticForm.ReducedFormRep (-(p : ℤ))
  /-- Every field-discriminant reduced representative has at most three
  conductor-`2` reduced-representative preimages. -/
  fiber_card_le_three :
    ∀ R : BinaryQuadraticForm.ReducedFormRep (-(p : ℤ)),
      Fintype.card
        { Q : BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ))) // toFieldRep Q = R } ≤ 3

/-- There is typed conductor-`2` reduced-representative cover data for `p`. -/
def HasConductorTwoReducedFormRepCoverData (p : ℕ) : Prop :=
  Nonempty (ConductorTwoReducedFormRepCoverData p)

/-- A conductor-`2` finite-fiber cover gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
    (p : ℕ) (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  let S := BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))
  let T := BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))
  have hmaps : ∀ Q ∈ S, hcover.toFieldForm Q ∈ T := by
    intro Q hQ
    exact hcover.maps_mem (by simpa [S] using hQ)
  have hfiber : ∀ R ∈ T, (S.filter fun Q => hcover.toFieldForm Q = R).card ≤ 3 := by
    intro R hR
    exact hcover.fiber_card_le_three (by simpa [T] using hR)
  exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber

/-- A conductor-`2` finite-fiber cover gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Typed conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * #forms(-p)` on reduced-form enumerations. -/
theorem conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_rep_cover
    (p : ℕ) (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card := by
  classical
  let S := BinaryQuadraticForm.ReducedFormRep (-(4 * (p : ℤ)))
  let T := BinaryQuadraticForm.ReducedFormRep (-(p : ℤ))
  have hrep := by
    have hmaps : ∀ Q ∈ (Finset.univ : Finset S), hcover.toFieldRep Q ∈
        (Finset.univ : Finset T) := by
      simp
    have hfiber :
        ∀ R ∈ (Finset.univ : Finset T),
          ((Finset.univ : Finset S).filter fun Q => hcover.toFieldRep Q = R).card ≤ 3 := by
      intro R _hR
      simpa [Fintype.card_subtype] using hcover.fiber_card_le_three R
    exact Finset.card_le_mul_card_image_of_maps_to hmaps 3 hfiber
  simpa [S, T, BinaryQuadraticForm.reducedFormRep_card] using hrep

/-- Typed conductor-`2` finite-fiber cover data gives the upper bound
`#forms(-4p) ≤ 3 * h(-p)` after transporting the field reduced-form count to
`classNumberQsqrtd`. -/
theorem conductor_two_reduced_forms_card_le_three_mul_classNumber_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤
      3 * classNumberQsqrtd (-(p : ℤ)) := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_rep_cover
      p hcover
  rwa [field_reduced_forms_card_eq_classNumberQsqrtd p hp hp8] at hbound

/-- Class number one plus typed conductor-`2` cover data gives the exact
conductor-`2` reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (by
      have hupper :=
        conductor_two_reduced_forms_card_le_three_mul_classNumber_of_rep_cover
          p hp hp8 hcover
      rw [hclass] at hupper
      omega)

/-- Class number one plus typed conductor-`2` cover data supplies Forms-side
class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    HasConductorTwoFormClassNumberThreeData p :=
  hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_rep_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- Class number one plus typed conductor-`2` cover data supplies the core
ring-class-number input. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_rep_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormRepCoverData p) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_rep_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- If the field reduced-form enumeration is a singleton and the conductor-`2`
cover has fibers of size at most three, then the conductor-`2` reduced-form
enumeration has size at most three. -/
theorem conductor_two_reduced_forms_card_le_three_of_field_card_eq_one_of_cover
    (p : ℕ)
    (hfield : (BinaryQuadraticForm.enumPrimitiveReducedForms (-(p : ℤ))).card = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3 := by
  have hbound :=
    conductor_two_reduced_forms_card_le_three_mul_field_reduced_forms_card_of_cover
      p hcover
  rw [hfield] at hbound
  omega

/-- Class number one plus conductor-`2` cover data gives the exact conductor-`2`
reduced-form count. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
    p hp hp8 hp_ne_three hclass
    (conductor_two_reduced_forms_card_le_three_of_field_card_eq_one_of_cover p
      (field_reduced_forms_card_eq_one_of_classNumber_one p hp hp8 hclass) hcover)

/-- Class number one plus conductor-`2` cover data supplies Forms-side
class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    HasConductorTwoFormClassNumberThreeData p :=
  hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_cover
      p hp hp8 hp_ne_three hclass hcover)

/-- Class number one plus conductor-`2` cover data supplies the core
ring-class-number input. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_cover
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hcover : ConductorTwoReducedFormCoverData p) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_cover
      p hp hp8 hp_ne_three hclass hcover)

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

/-- A conductor-`2` reduced-form upper bound supplies Forms-side
class-number-three data in the non-exceptional inert branch. -/
theorem conductor_two_form_class_number_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    HasConductorTwoFormClassNumberThreeData p :=
  hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_card_le_three p hp hp8 hp_ne_three hupper)

/-- Class number one plus a conductor-`2` reduced-form upper bound supplies
Forms-side conductor-`2` class-number-three data. -/
theorem conductor_two_form_class_number_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    HasConductorTwoFormClassNumberThreeData p :=
  hasConductorTwoFormClassNumberThreeData_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_card_le_three
      p hp hp8 hp_ne_three hclass hupper)

/-- A conductor-`2` reduced-form upper bound supplies the core ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_card_le_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three_of_card_le_three p hp hp8 hp_ne_three hupper)

/-- Class number one plus a conductor-`2` reduced-form upper bound supplies the
core ring-class-number input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_card_le_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hupper :
      (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card ≤ 3) :
    HasRingClassNumberThreeAtConductorTwo p :=
  hasRingClassNumberThreeAtConductorTwo_of_forms
    (conductor_two_form_class_number_three_of_classNumber_one_of_card_le_three
      p hp hp8 hp_ne_three hclass hupper)

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

/-- Once the conductor-`2` order class-number formula is available, class
number one for the maximal order and the inert local factor `3` give exactly
three conductor-`2` primitive reduced forms. -/
theorem conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hformula :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        (classNumberQsqrtd (-(p : ℤ)) : ℚ) *
          ((2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2)))
    (hfactor : (2 : ℚ) * (1 - (kroneckerTwo (-(p : ℤ)) : ℚ) / 2) = 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  have hcard_rat :
      ((BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card : ℚ) =
        3 := by
    rw [hformula, hclass, hfactor]
    norm_num
  exact_mod_cast hcard_rat

/-- In the inert prime family `d = -p`, class number one for `ℚ(√-p)` gives
three primitive reduced positive definite forms of conductor-`2` discriminant
`-4p`, away from the unit-exception case `p = 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula p
    (conductor_two_reduced_forms_card_order_class_number_formula p hp hp8 hp_ne_three)
    (conductor_two_order_class_number_formula_factor_eq_three p hp8) hclass

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
