/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassNumber.SmallNorm
import Examples.SqrtNeg5.Ideals
import Examples.SqrtNeg5.Invariants
import QNFMathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.RingOfIntegers.Norm

/-!
# The Class Number of `ℚ(√-5)` Is Two

This file starts the hand computation of the class number of `ℚ(√-5)`.

The key ideal is the ramified prime `(2, 1 + √-5)` in the maximal order
`ℤ[√-5]`, transported along `Examples.SqrtNeg5.ringOfIntegersEquiv` to the
ring of integers. We transport its prime factorization `(2) = P²` and prove
that `P` is not principal; the following file section then uses the Minkowski
bound from `Examples.SqrtNeg5.Invariants` to show that every ideal class is
either trivial or represented by `P`.
-/

open scoped NumberField

open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields.Examples.SqrtNeg5

/-- The ring of integers of `ℚ(√-5)`. -/
abbrev O := 𝓞 (Qsqrtd ((-5 : ℤ) : ℚ))

/-- The project model `ℤ[√-5]`. -/
abbrev Z := Zsqrtd (-5 : ℤ)

local notation "sqrtd" => Zsqrtd.sqrtd

/-- The ideal `(2, 1 + √-5)` in the project model `ℤ[√-5]`. -/
noncomputable abbrev PZ : Ideal Z :=
  Ideal.span ({(2 : Z), 1 + sqrtd} : Set Z)

/-- The ramified prime `P = (2, 1 + √-5)` of `ℚ(√-5)`, transported to the ring
of integers along `ringOfIntegersEquiv`. -/
noncomputable def P : Ideal O :=
  Ideal.map (ringOfIntegersEquiv.symm : Z →+* O) PZ

/-- Transporting `PZ` by `ringOfIntegersEquiv.symm` agrees with comapping along
`ringOfIntegersEquiv`. -/
private theorem P_eq_comap : P = Ideal.comap (ringOfIntegersEquiv : O →+* Z) PZ := by
  rw [P, Ideal.map_comap_of_equiv ringOfIntegersEquiv.symm]
  rfl

/-- The transported ideal `P` is prime. -/
theorem isPrime_P : P.IsPrime := by
  haveI : PZ.IsPrime := SqrtNeg5.isPrime_span_two_one_plus_sqrtd
  rw [P_eq_comap]
  exact Ideal.comap_isPrime (ringOfIntegersEquiv : O →+* Z) PZ

/-- The principal ideal `(2)` factors as `P²` in the ring of integers. -/
theorem span_two_eq_P_sq :
    Ideal.span ({(2 : O)} : Set O) = P ^ 2 := by
  have hmap := congrArg (Ideal.map (ringOfIntegersEquiv.symm : Z →+* O))
    SqrtNeg5.factorization_of_two
  rw [Ideal.map_pow] at hmap
  have htwo : (ringOfIntegersEquiv.symm : Z →+* O) (2 : Z) = (2 : O) := map_ofNat _ 2
  rw [Ideal.map_span, Set.image_singleton, htwo] at hmap
  simpa [P, PZ, Ideal.map_span] using hmap

/-- The principal ideal `(2)` has absolute norm `4` in `𝓞(ℚ(√-5))`. -/
private theorem absNorm_span_two :
    Ideal.absNorm (Ideal.span ({(2 : O)} : Set O)) = 4 := by
  simpa [O] using QuadraticNumberFields.RingOfIntegers.absNorm_span_intCast (-5) 2

/-- The transported ramified prime `P` has absolute norm `2`. -/
theorem absNorm_P : Ideal.absNorm P = 2 := by
  have hnorm := congrArg Ideal.absNorm span_two_eq_P_sq
  have hsq : Ideal.absNorm P * Ideal.absNorm P = 4 := by
    rw [absNorm_span_two] at hnorm
    simpa [pow_two] using hnorm.symm
  nlinarith [sq_nonneg (Ideal.absNorm P : ℤ)]

/-- `P = (2, 1 + √-5)` is not principal: a generator would have norm `2`, but
`a² + 5b² = 2` has no integer solutions. -/
theorem not_isPrincipal_P : ¬ P.IsPrincipal := by
  rintro ⟨x, hx⟩
  have hxnorm_abs : (Algebra.norm ℤ x).natAbs = 2 := by
    have hspan : Ideal.absNorm (Ideal.span ({x} : Set O)) = 2 := by
      change Ideal.absNorm (O ∙ x) = 2
      rw [← hx, absNorm_P]
    rw [Ideal.absNorm_span_singleton] at hspan
    exact hspan
  let z : Z := ringOfIntegersEquiv x
  have hnorm_transport : Algebra.norm ℤ x = Zsqrtd.norm z := by
    simpa [z] using
      QuadraticNumberFields.RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one
        (-5) (by decide) x
  have hz_abs : (Zsqrtd.norm z).natAbs = 2 := by
    rw [← hnorm_transport]
    exact hxnorm_abs
  have hz_formula : Zsqrtd.norm z = z.re ^ 2 + 5 * z.im ^ 2 := by
    rw [Zsqrtd.norm_def]
    ring
  have hz_nonneg : 0 ≤ Zsqrtd.norm z := by
    rw [hz_formula]
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]
  have hz_norm : Zsqrtd.norm z = 2 := by
    omega
  have hsum : z.re ^ 2 + 5 * z.im ^ 2 = 2 := by
    nlinarith
  have him_sq_lt_one : z.im ^ 2 < 1 := by
    nlinarith [sq_nonneg z.re]
  have him_lt_one : z.im < 1 := by
    nlinarith [sq_nonneg (z.im - 1)]
  have him_gt_neg_one : -1 < z.im := by
    nlinarith [sq_nonneg (z.im + 1)]
  have him_zero : z.im = 0 := by
    omega
  have hre_sq : z.re ^ 2 = 2 := by
    nlinarith
  have hre_le : z.re ≤ 1 := by
    nlinarith [sq_nonneg (z.re - 2)]
  have hre_ge : -1 ≤ z.re := by
    nlinarith [sq_nonneg (z.re + 2)]
  interval_cases z.re <;> norm_num at hre_sq

/-- The ramified prime `P` is nonzero. -/
theorem P_ne_bot : P ≠ ⊥ := by
  rw [Ne, ← Ideal.absNorm_eq_zero_iff, absNorm_P]
  norm_num

/-- The ramified prime `P`, bundled as a non-zero ideal. -/
noncomputable def P0 : nonZeroDivisors (Ideal O) :=
  ⟨P, mem_nonZeroDivisors_iff_ne_zero.mpr P_ne_bot⟩

/-- The nontrivial ideal class `[P]` of `ℚ(√-5)`. -/
noncomputable def classP : ClassGroup O :=
  ClassGroup.mk0 P0

/-- The ideal class `[P]` is nontrivial. -/
theorem classP_ne_one : classP ≠ 1 := by
  intro h
  apply not_isPrincipal_P
  rw [classP, ClassGroup.mk0_eq_one_iff] at h
  exact h

/-- Every ideal of absolute norm `2` in `𝓞(ℚ(√-5))` is the ramified prime `P`. -/
theorem eq_P_of_absNorm_eq_two {I : Ideal O} (hI : Ideal.absNorm I = 2) : I = P := by
  have hIprime : I.IsPrime := Ideal.isPrime_of_absNorm_eq_two hI
  have hIbot : I ≠ ⊥ := by rw [Ne, ← Ideal.absNorm_eq_zero_iff, hI]; norm_num
  have hItop : I ≠ ⊤ := by intro h; rw [h, Ideal.absNorm_top] at hI; norm_num at hI
  have h2mem : (2 : O) ∈ I := by
    have hm := Ideal.absNorm_mem I
    rw [hI] at hm
    exact_mod_cast hm
  have hdvd2 : I ∣ Ideal.span ({(2 : O)} : Set O) := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact h2mem
  rw [span_two_eq_P_sq] at hdvd2
  have hIprimeElem : Prime I := (Ideal.prime_iff_isPrime hIbot).mpr hIprime
  have hdvdP : I ∣ P := hIprimeElem.dvd_of_dvd_pow hdvd2
  have hmax : P.IsMaximal := isPrime_P.isMaximal P_ne_bot
  exact (hmax.eq_of_le hItop (Ideal.le_of_dvd hdvdP)).symm

/-- Every norm-`2` ideal class is `[P]`. -/
theorem class_eq_classP_of_absNorm_eq_two
    (I : nonZeroDivisors (Ideal O)) (hI : Ideal.absNorm (I : Ideal O) = 2) :
    ClassGroup.mk0 I = classP := by
  change ClassGroup.mk0 I = ClassGroup.mk0 P0
  congr 1
  exact Subtype.ext (eq_P_of_absNorm_eq_two hI)

/-- Every ideal class of `ℚ(√-5)` is trivial or equal to `[P]`. -/
theorem classGroup_eq_one_or_classP (C : ClassGroup O) : C = 1 ∨ C = classP :=
  classGroup_eq_one_or_of_exists_ideal_norm_lt_three classP
    exists_ideal_in_class_of_norm_le class_eq_classP_of_absNorm_eq_two C

/-- **`ℚ(√-5)` has class number two** — the classic non-UFD example. -/
theorem classNumber_eq_two :
    NumberField.classNumber (Qsqrtd ((-5 : ℤ) : ℚ)) = 2 :=
  NumberField.classNumber_eq_two_of_forall_eq_one_or classP_ne_one classGroup_eq_one_or_classP

/-- `classNumberQsqrtd (-5) = 2`, the unified-interface form. -/
theorem classNumberQsqrtd_neg5 : classNumberQsqrtd (-5) = 2 :=
  classNumber_eq_two

end QuadraticNumberFields.Examples.SqrtNeg5
