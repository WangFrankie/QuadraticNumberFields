/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Forms
import ImaginaryClassNumberOne.WeberCM.Core

/-!
# Conductor-Two Assembly for the Weber/CM Interface

This file ties the conductor-`2` basic, residue, and reduced-form layers to the
core Baker-Heegner-Stark Weber/CM interface.

The core `Heegner.WeberCM.Core` interface remains independent of this file.
Import `Heegner.WeberCM.ConductorTwo.Assembly` only when the proof route
explicitly goes through primitive reduced binary quadratic forms.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- Forms-side class-number-three input supplies the conductor-`2`
ring-class-number input used by the Weber/CM layer. -/
theorem ringClassNumberConductorTwoEqualsThree_of_forms
    {p : ℕ} (hforms : ConductorTwoFormClassNumberThree p) :
    RingClassNumberConductorTwoEqualsThree p := by
  -- This is the remaining order/forms class-number bridge: it should identify
  -- the primitive reduced-form count for discriminant `-4p` with the ring
  -- class number of the conductor-`2` order.
  sorry

/-- The finite inert-Heegner-prime reduced-form computation supplies
Forms-side conductor-`2` class-number-three input. -/
theorem conductor_two_form_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
      p hp_mem hp_ne_three)

/-- The finite inert-Heegner-prime reduced-form computation supplies the core
conductor-`2` ring-class-number-three input. -/
theorem conductor_two_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
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

/-- On the finite non-exceptional inert Heegner-prime table, the specialized
order class-number formula holds. -/
theorem conductor_two_order_class_number_formula_of_mem_heegnerPrimeSet
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three :=
  conductor_two_reduced_forms_card_order_class_number_formula_of_mem_heegnerPrimeSet
    p hp8 hp_mem hp_ne_three

/-- Explicit conductor-`2` kernel certificates and maximal-order class number one give
exactly three conductor-`2` primitive reduced forms. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_kernel_certificate
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hkernel : ConductorTwoIdealClassKernelCertificate p hp8) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_class_cover
    p hp hp8 hp_ne_three hclass
    (conductor_two_form_class_cover_of_kernel_certificate p hp hp8 hkernel)

/-- In the class-number-one branch, explicit conductor-`2` kernel certificates supply
the Cox formula equality needed by the Forms route. -/
theorem conductor_two_order_class_number_formula_of_classNumber_one_of_kernel_certificate
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hkernel : ConductorTwoIdealClassKernelCertificate p hp8) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three := by
  unfold ConductorTwoOrderClassNumberFormula
  rw [conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass hkernel, hclass,
    conductor_two_order_class_number_formula_factor_eq_three p hp8]
  norm_num

/-- Injectivity of the explicit residue-unit map on every fiber gives exactly
three conductor-`2` primitive reduced forms in the class-number-one branch. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_fiberResidueUnit_injective
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hinj : ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_fiberResidueUnit_injective p hp8 hinj)

/-- In the class-number-one branch, injectivity of the explicit residue-unit map
on every fiber supplies the Cox formula equality needed by the Forms route. -/
theorem conductor_two_order_class_number_formula_of_classNumber_one_of_fiberResidueUnit_injective
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hinj : ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three :=
  conductor_two_order_class_number_formula_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_fiberResidueUnit_injective p hp8 hinj)

/-- The representative-level reconstruction criterion gives exactly three
conductor-`2` primitive reduced forms in the class-number-one branch. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_formClass_eq
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hform : ∀ Q R : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))),
      conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p Q) =
        conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p R) →
      Ideal.Quotient.mk
          (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
          ((((conductorTwoFormClassOddRepresentative p Q).1.a : ℤ) :
            𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) =
        Ideal.Quotient.mk
          (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
          ((((conductorTwoFormClassOddRepresentative p R).1.a : ℤ) :
            𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) →
      Q = R) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_formClass_eq p hp8 hform)

/-- In the class-number-one branch, the representative-level reconstruction
criterion supplies the Cox formula equality needed by the Forms route. -/
theorem conductor_two_order_class_number_formula_of_classNumber_one_of_formClass_eq
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hform : ∀ Q R : BinaryQuadraticForm.FormClass (-(4 * (p : ℤ))),
      conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p Q) =
        conductorTwoRingOfIntegersIdealClassOfForm p hp8
          (conductorTwoFormClassOddRepresentative p R) →
      Ideal.Quotient.mk
          (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
          ((((conductorTwoFormClassOddRepresentative p Q).1.a : ℤ) :
            𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) =
        Ideal.Quotient.mk
          (Ideal.span ({(2 : 𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))} : Set _))
          ((((conductorTwoFormClassOddRepresentative p R).1.a : ℤ) :
            𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))) →
      Q = R) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three :=
  conductor_two_order_class_number_formula_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_formClass_eq p hp8 hform)

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

/-- The order class-number formula and class number one give exactly three
conductor-`2` primitive reduced forms. -/
theorem conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula p
    hformula (conductor_two_order_class_number_formula_factor_eq_three p hp8) hclass

/-- The order class-number formula and class number one supply the Forms-side
class-number-three statement. -/
theorem conductorTwoFormClassNumberThree_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p :=
  conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
      p hp8 hp_ne_three hformula hclass)

/-- The order class-number formula and class number one supply the core
ring-class-number input. -/
theorem ringClassNumberConductorTwoEqualsThree_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    RingClassNumberConductorTwoEqualsThree p :=
  ringClassNumberConductorTwoEqualsThree_of_forms
    (conductorTwoFormClassNumberThree_of_order_class_number_formula
      p hp8 hp_ne_three hformula hclass)

/-- **Cox order class-number formula input, conductor `2`.** In the
non-exceptional inert prime branch, Cox's order class-number formula identifies
the conductor-`2` reduced-form count with the maximal-order class number times
the local factor at `2`.

This is now the remaining conductor-`2` mathematical input for the Forms
route.  It should be supplied by Cox 7.24 / Corollary 7.28, or by an
equivalent quadratic-order/Picard-group computation. -/
theorem conductor_two_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three := by
  -- Cox 7.24 / Corollary 7.28, or an equivalent quadratic-order Picard-group
  -- construction, belongs here. The local factor at `2` is already closed by
  -- `conductor_two_order_class_number_formula_factor_eq_three`.
  sorry

/-- In the inert prime family `d = -p`, class number one for `ℚ(√-p)` gives
three primitive reduced positive definite forms of conductor-`2` discriminant
`-4p`, away from the unit-exception case `p = 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  exact conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
    p hp8 hp_ne_three (conductor_two_order_class_number_formula p hp hp8 hp_ne_three)
    hclass

/-- Target-shaped conductor-`2` reduced-form class-number statement.

This version derives the squarefree parameter facts from the prime hypothesis,
so its assumptions match the Baker-Heegner-Stark inert branch:
`h(-p) = 1`, `p` prime, `p % 8 = 3`, and `p ≠ 3`. -/
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  haveI : Fact (Squarefree (-(p : ℤ))) :=
    ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
  haveI : Fact ((-(p : ℤ)) ≠ 1) :=
    ⟨Int.neg_natCast_ne_one p⟩
  exact conductor_two_reduced_forms_card_eq_three_of_classNumber_one
    p hp hp8 hp_ne_three hclass

/-- **Cox forms class-number input.** In the inert prime family `d = -p`, class
number one for `ℚ(√-p)` gives Forms-side class-number-three input for primitive
positive definite forms of conductor-`2` discriminant `-4p`, away from the
unit-exception case `p = 3`. -/
theorem conductor_two_form_class_number_three
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoFormClassNumberThree p := by
  exact conductorTwoFormClassNumberThree_of_order_class_number_formula
    p hp8 hp_ne_three (conductor_two_order_class_number_formula p hp hp8 hp_ne_three)
    hclass

/-- Target-shaped Forms-side conductor-`2` class-number statement.

This wrapper removes the auxiliary `Fact` parameters by deriving them from
`Nat.Prime p`.  The remaining mathematical input is still Cox 7.24 / Corollary
7.28, isolated by `conductor_two_order_class_number_formula`. -/
theorem conductor_two_form_class_number_three_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    ConductorTwoFormClassNumberThree p := by
  exact conductorTwoFormClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_prime
      p hp hp8 hp_ne_three hclass)

/-- The reduced-forms route supplies the core conductor-`2` ring-class-number
input in the non-exceptional inert branch. -/
theorem conductor_two_class_number_three_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    RingClassNumberConductorTwoEqualsThree p := by
  exact ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three p hp hp8 hp_ne_three hclass)

/-- Target-shaped core conductor-`2` ring-class-number statement supplied by the
Forms route. -/
theorem conductor_two_class_number_three_of_forms_of_prime
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1)) :
    RingClassNumberConductorTwoEqualsThree p := by
  exact ringClassNumberConductorTwoEqualsThree_of_forms
    (conductor_two_form_class_number_three_of_prime p hp hp8 hp_ne_three hclass)

/-- **Deep Weber/CM input from ring-class-number three, via the Forms route.**
The conductor-`2` ring-class-number-three input supplies the refined Weber certificate:
a concrete Heegner equation solution, the associated gamma value, and its
finite-table association with `p`, in the non-exceptional inert branch `p ≠ 3`. -/
theorem conductor_two_weber_certificate_of_ring_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3) (horder : RingClassNumberConductorTwoEqualsThree p) :
    Nonempty (ConductorTwoWeberCertificate p) := by
  sorry

/-- The Forms route turns conductor-`2` ring-class-number-three input into
Stark-Heegner algebraic certificates. -/
theorem exists_weber_certificate_of_conductor_two_class_number_three_of_forms
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3)
    (horder : RingClassNumberConductorTwoEqualsThree p) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact exists_weber_certificate_of_conductor_two_weber_certificate
    (conductor_two_weber_certificate_of_ring_class_number_three_of_forms
      p hp hp8 hp_ne_three horder)

/-- The reduced-forms route supplies Weber/CM algebraic certificates from class number
one in the non-exceptional inert branch. -/
theorem exists_weber_certificate_of_classNumber_one_inert_prime_of_forms
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact exists_weber_certificate_of_conductor_two_class_number_three_of_forms
    p hp hp8 hp_ne_three
    (conductor_two_class_number_three_of_forms p hp hp8 hp_ne_three hclass)

/-- The reduced-forms route packaged as the core Weber/CM input. -/
theorem hasInertPrimeWeberCM_of_forms : HasInertPrimeWeberCM := by
  intro p _ _ hp hp8 hp_ne_three hclass
  exact exists_weber_certificate_of_classNumber_one_inert_prime_of_forms
    p hp hp8 hp_ne_three hclass


end Heegner
end QuadraticNumberFields
