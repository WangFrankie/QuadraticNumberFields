/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Basic
import ImaginaryClassNumberOne.WeberCM.ConductorTwo.Forms
import ImaginaryClassNumberOne.WeberCM.Core

/-!
# Conductor-Two Assembly for the Weber/CM Interface

This file ties the conductor-`2` basic, residue, and reduced-form layers to the
core Baker-Heegner-Stark Weber/CM interface.

The core `Heegner.WeberCM.Core` interface remains independent of this file.
Import `Heegner.WeberCM.ConductorTwo.Assembly` only when the proof route
explicitly goes through primitive reduced binary quadratic forms.

The full unconditional Cox 7.24 / Corollary 7.28 order class-number formula is
future order/Picard infrastructure.  The BHS-facing route here uses the
fiber-residue upper bound, when supplied, plus the explicit reduced-form lower
bound from `Forms.lean`; finite Heegner-prime table instances of the Cox formula
remain as sorry-free comparison lemmas.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- The finite inert-Heegner-prime reduced-form computation supplies
conductor-`2` class-number-three input. -/
theorem conductor_two_class_number_three_of_mem_heegnerPrimeSet
    (p : ℕ) (hp_mem : (p : ℤ) ∈ heegnerPrimeSet) (hp_ne_three : p ≠ 3) :
    ConductorTwoClassNumberThree p :=
  conductorTwoClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_mem_heegnerPrimeSet
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
theorem conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hrec : ConductorTwoFormClassReconstruction p hp8) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 :=
  conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_formClassReconstruction p hp8 hrec)

/-- In the class-number-one branch, the representative-level reconstruction
criterion supplies the Cox formula equality needed by the Forms route. -/
theorem conductor_two_order_class_number_formula_of_classNumber_one_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hrec : ConductorTwoFormClassReconstruction p hp8) :
    ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three :=
  conductor_two_order_class_number_formula_of_classNumber_one_of_kernel_certificate
    p hp hp8 hp_ne_three hclass
    (conductor_two_ideal_class_kernel_certificate_of_formClassReconstruction p hp8 hrec)

/-- The named representative-level reconstruction criterion supplies the
conductor-`2` class-number-three statement in the class-number-one branch. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hrec : ConductorTwoFormClassReconstruction p hp8) :
    ConductorTwoClassNumberThree p := by
  exact conductorTwoClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_formClassReconstruction
      p hp hp8 hp_ne_three hclass hrec)

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

/-- The order class-number formula and class number one supply the conductor-`2`
class-number-three statement. -/
theorem conductorTwoClassNumberThree_of_order_class_number_formula
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hformula : ConductorTwoOrderClassNumberFormula p hp8 hp_ne_three)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1) :
    ConductorTwoClassNumberThree p :=
  conductorTwoClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_order_class_number_formula_prop
      p hp8 hp_ne_three hformula hclass)

/-- Target-shaped conductor-`2` reduced-form class-number statement.

This version derives the squarefree parameter facts from the prime hypothesis,
so its assumptions match the Baker-Heegner-Stark inert branch:
`h(-p) = 1`, `p` prime, `p % 8 = 3`, and `p ≠ 3`.  The remaining
fiber-residue injectivity hypothesis is the explicit conductor-`2` kernel input. -/
theorem conductor_two_reduced_forms_card_eq_three_of_prime_of_fiberResidueUnit_injective
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1))
    (hinj :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
        Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C))) :
    (BinaryQuadraticForm.enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  haveI : Fact (Squarefree (-(p : ℤ))) :=
    ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
  haveI : Fact ((-(p : ℤ)) ≠ 1) :=
    ⟨Int.neg_natCast_ne_one p⟩
  exact
    conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_fiberResidueUnit_injective
      p hp hp8 hp_ne_three hclass hinj

/-- **Conditional conductor-two class-number input.** In the inert prime family
`d = -p`, class number one for `ℚ(√-p)`, together with the explicit
fiber-residue injection, gives class-number-three input for primitive positive
definite forms of conductor-`2` discriminant `-4p`, away from the unit-exception
case `p = 3`. -/
theorem conductor_two_class_number_three_of_classNumber_one_of_fiberResidueUnit_injective
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hinj : ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    ConductorTwoClassNumberThree p := by
  exact conductorTwoClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_classNumber_one_of_fiberResidueUnit_injective
      p hp hp8 hp_ne_three hclass hinj)

/-- Target-shaped conductor-`2` class-number statement.

This wrapper removes the auxiliary `Fact` parameters by deriving them from
`Nat.Prime p`.  The remaining mathematical input is the explicit conductor-`2`
fiber-residue injection. -/
theorem conductor_two_class_number_three_of_prime_of_fiberResidueUnit_injective
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1))
    (hinj :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
        Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C))) :
    ConductorTwoClassNumberThree p := by
  exact conductorTwoClassNumberThree_of_reducedForms_card p
    (conductor_two_reduced_forms_card_eq_three_of_prime_of_fiberResidueUnit_injective
      p hp hp8 hp_ne_three hclass hinj)

/-- Target-shaped conductor-`2` class-number statement using the named
representative-level reconstruction criterion. -/
theorem conductor_two_class_number_three_of_prime_of_formClassReconstruction
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       classNumberQsqrtd (-(p : ℤ)) = 1))
    (hrec :
      (letI : Fact (Squarefree (-(p : ℤ))) := ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
       letI : Fact ((-(p : ℤ)) ≠ 1) := ⟨Int.neg_natCast_ne_one p⟩
       ConductorTwoFormClassReconstruction p hp8)) :
    ConductorTwoClassNumberThree p := by
  haveI : Fact (Squarefree (-(p : ℤ))) :=
    ⟨Int.squarefree_neg_natCast_of_nat_prime hp⟩
  haveI : Fact ((-(p : ℤ)) ≠ 1) :=
    ⟨Int.neg_natCast_ne_one p⟩
  exact conductor_two_class_number_three_of_classNumber_one_of_formClassReconstruction
    p hp hp8 hp_ne_three hclass hrec

/-- **Deep Weber/CM input from conductor-two class number three.**
The conductor-`2` class-number-three input supplies the refined Weber certificate:
a concrete Heegner equation solution, the associated gamma value, and its
finite-table association with `p`, in the non-exceptional inert branch `p ≠ 3`. -/
theorem conductor_two_weber_certificate_of_conductor_two_class_number_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3) (hclass_three : ConductorTwoClassNumberThree p) :
    Nonempty (ConductorTwoWeberCertificate p) := by
  sorry

/-- The Weber/CM boundary turns conductor-`2` class-number-three input into
Stark-Heegner algebraic certificates. -/
theorem exists_weber_certificate_of_conductor_two_class_number_three
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3)
    (hp_ne_three : p ≠ 3)
    (hclass_three : ConductorTwoClassNumberThree p) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact exists_weber_certificate_of_conductor_two_weber_certificate
    (conductor_two_weber_certificate_of_conductor_two_class_number_three
      p hp hp8 hp_ne_three hclass_three)

/-- The conditional reduced-forms route supplies Weber/CM algebraic certificates
from class number one in the non-exceptional inert branch, once the explicit
conductor-`2` fiber-residue injection is available. -/
theorem exists_weber_certificate_of_classNumber_one_inert_prime_of_fiberResidueUnit_injective
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hinj : ∀ C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact exists_weber_certificate_of_conductor_two_class_number_three
    p hp hp8 hp_ne_three
    (conductor_two_class_number_three_of_classNumber_one_of_fiberResidueUnit_injective
      p hp hp8 hp_ne_three hclass hinj)

/-- The named representative-level reconstruction criterion supplies Weber/CM
algebraic certificates from class number one in the non-exceptional inert branch. -/
theorem exists_weber_certificate_of_classNumber_one_inert_prime_of_formClassReconstruction
    (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
    (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hclass : classNumberQsqrtd (-(p : ℤ)) = 1)
    (hrec : ConductorTwoFormClassReconstruction p hp8) :
    Nonempty (StarkHeegnerAlgebraicCertificate p) := by
  exact exists_weber_certificate_of_conductor_two_class_number_three
    p hp hp8 hp_ne_three
    (conductor_two_class_number_three_of_classNumber_one_of_formClassReconstruction
      p hp hp8 hp_ne_three hclass hrec)

/-- The conditional reduced-forms route packaged as the core Weber/CM input.

The hypothesis is the named conductor-`2` kernel step still missing from the
current repository: injectivity of the explicit residue-unit map on every
ideal-class fiber. -/
theorem hasInertPrimeWeberCM_of_fiberResidueUnit_injective
    (hinj : ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
      (_hp : Nat.Prime p) (hp8 : p % 8 = 3) (_hp_ne_three : p ≠ 3)
      (C : ClassGroup (𝓞 (Qsqrtd ((-(p : ℤ) : ℤ) : ℚ)))),
      Function.Injective (conductorTwoIdealClassFiberResidueUnit p hp8 C)) :
    HasInertPrimeWeberCM := by
  intro p _ _ hp hp8 hp_ne_three hclass
  exact exists_weber_certificate_of_classNumber_one_inert_prime_of_fiberResidueUnit_injective
    p hp hp8 hp_ne_three hclass (hinj p hp hp8 hp_ne_three)

/-- The conditional reduced-forms route packaged with the named representative-level
reconstruction criterion as the missing conductor-`2` input. -/
theorem hasInertPrimeWeberCM_of_formClassReconstruction
    (hrec : ∀ (p : ℕ) [Fact (Squarefree (-(p : ℤ)))] [Fact ((-(p : ℤ)) ≠ 1)]
      (_hp : Nat.Prime p) (hp8 : p % 8 = 3) (_hp_ne_three : p ≠ 3),
      ConductorTwoFormClassReconstruction p hp8) :
    HasInertPrimeWeberCM := by
  intro p _ _ hp hp8 hp_ne_three hclass
  exact exists_weber_certificate_of_classNumber_one_inert_prime_of_formClassReconstruction
    p hp hp8 hp_ne_three hclass (hrec p hp hp8 hp_ne_three)

end Heegner
end QuadraticNumberFields
