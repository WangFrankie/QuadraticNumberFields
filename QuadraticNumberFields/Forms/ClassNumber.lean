/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.Forms.CoxEquivalence
import QuadraticNumberFields.Forms.Enumeration
import QuadraticNumberFields.Heegner.ClassNumberOne

/-!
# The Class Number of `ℚ(√d)` as a Function of `d`

This file defines `classNumberQsqrtd d`, the class number of the standard
quadratic field `Qsqrtd d` as a function of the integer parameter `d`, and
bridges the nine Heegner class-number-one theorems to this interface.

For now `classNumberQsqrtd` is a noncomputable thin alias of
`NumberField.classNumber`; after the planned binary-quadratic-form
enumeration it will acquire a computable equation on imaginary `d` with the
same signature.

## Main definitions

* `classNumberQsqrtd`: the class number of `ℚ(√d)` as a function of `d : ℤ`.
* `classGroupRepresentativesQsqrtd`: class-group representatives obtained from
  reduced primitive positive definite forms.

## Main statements

* `classGroupRepresentativesQsqrtd_eq_univ`: the reduced-form representatives
  cover the full class group for imaginary squarefree `d`.
* `classNumberQsqrtd_neg1` … `classNumberQsqrtd_neg163`: the nine Heegner
  fields have class number one.
* `classNumberQsqrtd_eq_one_of_mem_heegnerSet`: packaged form over
  `Heegner.heegnerSet`.
-/

open scoped NumberField

open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

/-- The class number of the quadratic field `ℚ(√d)`, as a function of the
squarefree integer parameter `d`. Thin alias of `NumberField.classNumber`. -/
noncomputable def classNumberQsqrtd (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℕ :=
  NumberField.classNumber (Qsqrtd (d : ℚ))

/-! ## Class-group representatives from reduced forms -/

/-- Representatives of the class group of `ℚ(√d)` obtained by enumerating
reduced primitive positive definite forms of the field discriminant and applying
the Cox 7.7 equivalence. -/
noncomputable def classGroupRepresentativesQsqrtd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    Finset (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) := by
  classical
  exact (BinaryQuadraticForm.reducedFormClasses (BinaryQuadraticForm.fieldDiscriminant d)).image
    (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg)

/-- The class-group representatives obtained from the reduced-form enumeration
cover the full class group. -/
theorem classGroupRepresentativesQsqrtd_eq_univ
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    classGroupRepresentativesQsqrtd d hdneg = Finset.univ := by
  classical
  rw [classGroupRepresentativesQsqrtd,
    BinaryQuadraticForm.reducedFormClasses_eq_univ]
  exact Finset.image_univ_equiv
    (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg)

/-- For imaginary squarefree `d`, the class number of `ℚ(√d)` is the number of
primitive reduced positive definite forms of the field discriminant. -/
theorem classNumberQsqrtd_eq_reducedForms_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    classNumberQsqrtd d =
      (BinaryQuadraticForm.enumPrimitiveReducedForms
        (BinaryQuadraticForm.fieldDiscriminant d)).card := by
  classical
  calc
    classNumberQsqrtd d =
        (Finset.univ : Finset (ClassGroup (𝓞 (Qsqrtd (d : ℚ))))).card := by
      simp [classNumberQsqrtd, NumberField.classNumber]
    _ = (classGroupRepresentativesQsqrtd d hdneg).card := by
      rw [classGroupRepresentativesQsqrtd_eq_univ]
    _ = (BinaryQuadraticForm.reducedFormClasses
          (BinaryQuadraticForm.fieldDiscriminant d)).card := by
      rw [classGroupRepresentativesQsqrtd]
      exact Finset.card_image_of_injective _
        (BinaryQuadraticForm.formClassEquivClassGroup (d := d) hdneg).injective
    _ = (BinaryQuadraticForm.enumPrimitiveReducedForms
          (BinaryQuadraticForm.fieldDiscriminant d)).card :=
      BinaryQuadraticForm.reducedFormClasses_card _

/-! ## Small-norm class-group closure lemmas -/

/-- The natural number `2` is irreducible, as a convenience for absolute-norm
arguments. -/
theorem irreducible_two_nat : Irreducible (2 : ℕ) :=
  (Nat.irreducible_iff_prime.mp Nat.prime_two).irreducible

/-- An ideal of absolute norm `2` is prime. -/
theorem Ideal.isPrime_of_absNorm_eq_two {R : Type*} [CommRing R] [Nontrivial R]
    [IsDedekindDomain R] [Module.Free ℤ R] {I : Ideal R} (hI : Ideal.absNorm I = 2) :
    I.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm
    (by rw [hI]; exact irreducible_two_nat)

/-- If every ideal class has a representative of absolute norm `< 3`, and all
norm-`2` ideals are principal, then every ideal class is trivial. -/
theorem classGroup_eq_one_of_exists_ideal_norm_lt_three
    {K : Type*} [Field K] [NumberField K]
    (hexists : ∀ C : ClassGroup (𝓞 K),
      ∃ I : nonZeroDivisors (Ideal (𝓞 K)),
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) < 3)
    (hprincipal_two : ∀ {I : Ideal (𝓞 K)}, Ideal.absNorm I = 2 → I.IsPrincipal)
    (C : ClassGroup (𝓞 K)) :
    C = 1 := by
  obtain ⟨I, hmk, hnorm⟩ := hexists C
  rw [← hmk, ClassGroup.mk0_eq_one_iff]
  have hIne : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hIne
  have hcase : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 ∨
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  rcases hcase with h1 | h2
  · rw [Ideal.absNorm_eq_one_iff] at h1
    rw [h1]
    exact ⟨1, Ideal.span_singleton_one.symm⟩
  · exact hprincipal_two h2

/-- If every ideal class has a representative of absolute norm `< 3`, and all
norm-`2` representatives have class `P`, then every ideal class is trivial or
equal to `P`. -/
theorem classGroup_eq_one_or_of_exists_ideal_norm_lt_three
    {K : Type*} [Field K] [NumberField K] (P : ClassGroup (𝓞 K))
    (hexists : ∀ C : ClassGroup (𝓞 K),
      ∃ I : nonZeroDivisors (Ideal (𝓞 K)),
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) < 3)
    (hclass_two : ∀ I : nonZeroDivisors (Ideal (𝓞 K)),
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 → ClassGroup.mk0 I = P)
    (C : ClassGroup (𝓞 K)) :
    C = 1 ∨ C = P := by
  obtain ⟨I, hmk, hnorm⟩ := hexists C
  rw [← hmk]
  have hIne : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hIne
  have hcase : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 ∨
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  rcases hcase with h1 | h2
  · left
    rw [ClassGroup.mk0_eq_one_iff]
    rw [Ideal.absNorm_eq_one_iff] at h1
    rw [h1]
    exact ⟨1, Ideal.span_singleton_one.symm⟩
  · right
    exact hclass_two I h2

/-- If every ideal class of a number field is trivial, then the class number is
one. -/
theorem NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    {K : Type*} [Field K] [NumberField K]
    (h : ∀ C : ClassGroup (𝓞 K), C = 1) :
    NumberField.classNumber K = 1 := by
  haveI : Unique (ClassGroup (𝓞 K)) := ⟨⟨1⟩, h⟩
  simpa only [NumberField.classNumber] using
    Fintype.card_unique (α := ClassGroup (𝓞 K))

/-! ## The nine Heegner fields have class number one -/

/-- `classNumberQsqrtd (-1) = 1`, bridged from `Heegner.classNumber_eq_one_neg1`. -/
theorem classNumberQsqrtd_neg1 : classNumberQsqrtd (-1) = 1 :=
  Heegner.classNumber_eq_one_neg1

/-- `classNumberQsqrtd (-2) = 1`, bridged from `Heegner.classNumber_eq_one_neg2`. -/
theorem classNumberQsqrtd_neg2 : classNumberQsqrtd (-2) = 1 :=
  Heegner.classNumber_eq_one_neg2

/-- `classNumberQsqrtd (-3) = 1`, bridged from `Heegner.classNumber_eq_one_neg3`. -/
theorem classNumberQsqrtd_neg3 : classNumberQsqrtd (-3) = 1 :=
  Heegner.classNumber_eq_one_neg3

/-- `classNumberQsqrtd (-7) = 1`, bridged from `Heegner.classNumber_eq_one_neg7`. -/
theorem classNumberQsqrtd_neg7 : classNumberQsqrtd (-7) = 1 :=
  Heegner.classNumber_eq_one_neg7

/-- `classNumberQsqrtd (-11) = 1`, bridged from `Heegner.classNumber_eq_one_neg11`. -/
theorem classNumberQsqrtd_neg11 : classNumberQsqrtd (-11) = 1 :=
  Heegner.classNumber_eq_one_neg11

/-- `classNumberQsqrtd (-19) = 1`, bridged from `Heegner.classNumber_eq_one_neg19`. -/
theorem classNumberQsqrtd_neg19 : classNumberQsqrtd (-19) = 1 :=
  Heegner.classNumber_eq_one_neg19

/-- `classNumberQsqrtd (-43) = 1`, bridged from `Heegner.classNumber_eq_one_neg43`. -/
theorem classNumberQsqrtd_neg43 : classNumberQsqrtd (-43) = 1 :=
  Heegner.classNumber_eq_one_neg43

/-- `classNumberQsqrtd (-67) = 1`, bridged from `Heegner.classNumber_eq_one_neg67`. -/
theorem classNumberQsqrtd_neg67 : classNumberQsqrtd (-67) = 1 :=
  Heegner.classNumber_eq_one_neg67

/-- `classNumberQsqrtd (-163) = 1`, bridged from `Heegner.classNumber_eq_one_neg163`. -/
theorem classNumberQsqrtd_neg163 : classNumberQsqrtd (-163) = 1 :=
  Heegner.classNumber_eq_one_neg163

/-- Packaged form: every Heegner number has `classNumberQsqrtd d = 1`. -/
theorem classNumberQsqrtd_eq_one_of_mem_heegnerSet
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d ∈ Heegner.heegnerSet) :
    classNumberQsqrtd d = 1 :=
  Heegner.classNumber_eq_one_of_mem_heegnerSet hd

end QuadraticNumberFields
