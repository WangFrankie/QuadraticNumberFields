/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import QuadraticNumberFields.Forms.InverseCox
import QuadraticNumberFields.Forms.NormFormBasisChange
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic

/-!
# Cox 7.7 Right Inverse: ideal-class round-trip

Proves the right-inverse law
`formClassToClassGroup (classGroupToFormClass C) = C` at the level of ideal
representatives, for both the `d % 4 ≠ 1` and `d % 4 = 1` branches, via the
principal Cox ideal-generator relations.  The final equivalence is assembled
in `Forms.CoxEquivalence`.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxAssembly

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 ≠ 1`
branch for any chosen oriented basis.  This isolates the remaining Cox
arithmetic to constructing the two nonzero principal generators and the displayed
ideal equality. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  dsimp [idealClassOfForm_of_mod_four_ne_one]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨x, y, hx, hy, by
    simpa [nonzeroIdealOfForm_of_mod_four_ne_one] using hrel⟩

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 = 1`
branch for any chosen oriented basis.  This is the half-integral analogue of
`idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  dsimp [idealClassOfForm_of_mod_four_eq_one]
  rw [ClassGroup.mk0_eq_mk0_iff]
  exact ⟨x, y, hx, hy, by
    simpa [nonzeroIdealOfForm_of_mod_four_eq_one] using hrel⟩

/-- In the `d % 4 ≠ 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_ne_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  calc
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        idealClassOfForm_of_mod_four_ne_one d hd4 R :=
      idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4 _ _ hQR
    _ = ClassGroup.mk0 I := hR

/-- In the `d % 4 = 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_eq_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  calc
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        idealClassOfForm_of_mod_four_eq_one d hd4 R :=
      idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4 _ _ hQR
    _ = ClassGroup.mk0 I := hR

/-- In the `d % 4 ≠ 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hα : (b.basis 0 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 0).2
  have ha : e.symm (((Q.1.a : ℤ) : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨1, by simp⟩
  simpa [mul_comm] using Ideal.mul_mem_mul ha hα

/-- In the `d % 4 = 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hα : (b.basis 0 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 0).2
  have ha : e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) := by
    rw [Ideal.mem_span_singleton]
    exact ⟨1, by simp⟩
  simpa [mul_comm] using Ideal.mul_mem_mul ha hα

/-! ### Coordinate algebra for the Cox ideal-generator relation -/

/-- Rational real-coordinate identity behind the signed Cox relation
`α * ((-B) / 2 + √D) = -A * β` in the non-half-integral branch. -/
theorem cox_ideal_generator_relation_re {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = αi * βr - αr * βi) (hN0 : N ≠ 0) :
    αr * (-B / 2) + D * αi = -A * βr := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- Rational imaginary-coordinate identity behind the signed Cox relation
`α * ((-B) / 2 + √D) = -A * β` in the non-half-integral branch. -/
theorem cox_ideal_generator_relation_im {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = αi * βr - αr * βi) (hN0 : N ≠ 0) :
    αr + αi * (-B / 2) = -A * βi := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- Rational real-coordinate identity behind the signed Cox relation in the
half-integral branch. -/
theorem cox_ideal_generator_relation_eq_one_re {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = 2 * (αi * βr - αr * βi)) (hN0 : N ≠ 0) :
    αr * (-B / 2) + D * (αi / 2) = -A * βr := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- Rational imaginary-coordinate identity behind the signed Cox relation in the
half-integral branch. -/
theorem cox_ideal_generator_relation_eq_one_im {αr αi βr βi D N A B : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N)
    (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : N = 2 * (αi * βr - αr * βi)) (hN0 : N ≠ 0) :
    αr * (1 / 2) + αi * (-B / 2) = -A * βi := by
  apply mul_right_cancel₀ hN0
  rw [add_mul, neg_mul, hA, hB]
  field_simp [hN0]
  rw [hN]
  ring

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator of the norm form
satisfies the signed classical relation
`α · β_Q = -a_Q · β`, where `(α, β)` is the oriented ideal basis.  The sign is
forced by the orientation convention `N(I) = αᵢβᵣ - αᵣβᵢ`. -/
theorem basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg hI b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) =
      -(((Q.1.a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K)) := by
  intro hI Q e
  have hβQ :
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).re =
        (-(Q.1.b : ℚ)) / 2 ∧
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).im = 1 := by
    have hb_even : Even Q.1.b :=
      even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
    obtain ⟨k, hk⟩ := hb_even
    have hdiv : (-Q.1.b) / 2 = -k := by
      rw [hk]
      omega
    have hk_rat : (Q.1.b : ℚ) / 2 = k := by
      rw [hk]
      norm_num
    have h_embed (x : 𝓞K) : ((x : 𝓞K) : K) = Zsqrtd.toQsqrtdHom d (e x) := by
      simpa [e] using
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x).symm
    rw [h_embed]
    constructor
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
      linarith
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
  have ha : ((Q.1.a : ℤ) : ℚ) =
      (((b.basis 0 : 𝓞K) : K).re ^ 2 -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im ^ 2) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_a_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    rw [fieldNorm_int_eq] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using h
  have hb : ((Q.1.b : ℤ) : ℚ) =
      (2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
          ((b.basis 1 : 𝓞K) : K).im)) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_b_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using
      show ((normFormOfBasis hI b).b : ℚ) * (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
          2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
            (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
              ((b.basis 1 : 𝓞K) : K).im) by
        have h' : ((normFormOfBasis hI b).b : ℚ) *
            (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
            ((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
              Algebra.norm ℤ (b.basis 0 : 𝓞K) -
              Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℤ) : ℚ) := by
          simpa using h
        rw [h']
        push_cast
        rw [fieldNorm_int_eq, fieldNorm_int_eq, fieldNorm_int_eq]
        push_cast
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
        ring
  have hNdet : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
      ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
        ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im := by
    have hdet : b.detCoord = -(Ideal.absNorm (I : Ideal 𝓞K) : ℚ) :=
      OrientedBasis.detCoord_eq_neg_absNorm_of_mod_four_ne_one hI hd4 b
    unfold OrientedBasis.detCoord at hdet
    linarith
  have hN0 : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
    exact_mod_cast (absNorm_pos hI).ne'
  apply IsFractionRing.injective 𝓞K K
  ext <;>
    simp only [map_mul, map_neg, map_intCast, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, zero_mul, add_zero,
      mul_zero, hβQ.1, hβQ.2]
  · simpa [mul_one] using cox_ideal_generator_relation_re ha hb hNdet hN0
  · simpa [one_mul] using cox_ideal_generator_relation_im ha hb hNdet hN0

/-- In the `d % 4 = 1` branch, the second Cox ideal generator of the norm form
satisfies the signed classical relation
`α · β_Q = -a_Q · β`, where the Cox generator has `K`-coordinates
`(-b_Q / 2, 1 / 2)`. -/
theorem basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg hI b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      d hd4
    (b.basis 0 : 𝓞K) *
        e.symm ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))) =
      -(((Q.1.a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K)) := by
  intro hI Q e
  have hβQ :
      ((e.symm (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)) :
          𝓞K) : K).re = (-(Q.1.b : ℚ)) / 2 ∧
      ((e.symm (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)) :
          𝓞K) : K).im = (1 : ℚ) / 2 := by
    let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
    let x : 𝓞K := e.symm betaZ
    have hre := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x
    have him := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x
    dsimp [x, e] at hre him
    rw [RingEquiv.apply_symm_apply] at hre him
    have hodd : Odd Q.1.b :=
      odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
    obtain ⟨k, hk⟩ := hodd
    have hdiv : (-(Q.1.b + 1) / 2 : ℤ) = -(k + 1) := by
      rw [hk]
      omega
    have hdiv' : ((-1 + -Q.1.b) / 2 : ℤ) = -1 - k := by
      rw [hk]
      omega
    constructor
    · rw [← hre]
      calc
        ((betaZ.re : ℚ) + (betaZ.im : ℚ) / 2) = ((-1 - k : ℤ) : ℚ) + 1 / 2 := by
          simp [betaZ, hdiv']
        _ = -(Q.1.b : ℚ) / 2 := by
          rw [hk]
          norm_num
          ring
    · simpa [betaZ] using him.symm
  have ha : ((Q.1.a : ℤ) : ℚ) =
      (((b.basis 0 : 𝓞K) : K).re ^ 2 -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im ^ 2) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_a_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    rw [fieldNorm_int_eq] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using h
  have hb : ((Q.1.b : ℤ) : ℚ) =
      (2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
        (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
          ((b.basis 1 : 𝓞K) : K).im)) /
        (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) := by
    have h := congrArg (fun z : ℤ => (z : ℚ)) (normFormOfBasis_b_mul_absNorm hI b)
    dsimp [Q, primitivePositiveDefiniteNormFormOfBasis] at h
    have hN : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
      exact_mod_cast (absNorm_pos hI).ne'
    rw [eq_div_iff hN]
    simpa [Q, primitivePositiveDefiniteNormFormOfBasis] using
      show ((normFormOfBasis hI b).b : ℚ) * (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
          2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
            (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im *
              ((b.basis 1 : 𝓞K) : K).im) by
        have h' : ((normFormOfBasis hI b).b : ℚ) *
            (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
            ((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
              Algebra.norm ℤ (b.basis 0 : 𝓞K) -
              Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℤ) : ℚ) := by
          simpa using h
        rw [h']
        push_cast
        rw [fieldNorm_int_eq, fieldNorm_int_eq, fieldNorm_int_eq]
        push_cast
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
        ring
  have hNdet : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) =
      2 * (((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
        ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im) := by
    have hdet : b.detCoord = -(Ideal.absNorm (I : Ideal 𝓞K) : ℚ) / 2 :=
      OrientedBasis.detCoord_eq_neg_half_absNorm_of_mod_four_eq_one hI hd4 b
    unfold OrientedBasis.detCoord at hdet
    linarith
  have hN0 : (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) ≠ 0 := by
    exact_mod_cast (absNorm_pos hI).ne'
  apply IsFractionRing.injective 𝓞K K
  ext <;>
    simp only [map_mul, map_neg, map_intCast, QuadraticAlgebra.re_mul,
      QuadraticAlgebra.im_mul, QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg,
      QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast, zero_mul, add_zero,
      mul_zero, hβQ.1, hβQ.2]
  · simpa [mul_one, div_eq_mul_inv, mul_assoc] using
      cox_ideal_generator_relation_eq_one_re ha hb hNdet hN0
  · simpa [one_mul] using cox_ideal_generator_relation_eq_one_im ha hb hNdet hN0

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator also satisfies
the principal-relation inclusion `(b₀) · β_Q ∈ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  rw [basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
    hdneg hd4 I b]
  have hβ : (b.basis 1 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 1).2
  have ha : ((Q.1.a : ℤ) : 𝓞K) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) :=
    Ideal.subset_span (by simp)
  exact neg_mem (Ideal.mul_mem_mul ha hβ)

/-- In the `d % 4 = 1` branch, the second Cox ideal generator also satisfies
the principal-relation inclusion `(b₀) · β_Q ∈ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      d hd4
    (b.basis 0 : 𝓞K) *
        e.symm ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  rw [basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
    hdneg hd4 I b]
  have hβ : (b.basis 1 : 𝓞K) ∈ (I : Ideal 𝓞K) := (b.basis 1).2
  have ha : ((Q.1.a : ℤ) : 𝓞K) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) :=
    Ideal.subset_span (by simp)
  exact neg_mem (Ideal.mul_mem_mul ha hβ)

/-- In the `d % 4 ≠ 1` branch, the two Cox generator membership lemmas assemble
to the inclusion `(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q ≤
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let aZ : Zsqrtd d := ((Q.1.a : ℤ) : Zsqrtd d)
  let betaZ : Zsqrtd d := (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  let target : Ideal 𝓞K := Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) *
    (I : Ideal 𝓞K)
  have hscalar : (b.basis 0 : 𝓞K) * e.symm aZ ∈ target := by
    simpa [Q, e, aZ, target] using
      basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_ne_one hdneg hd4 I b
  have hbeta : (b.basis 0 : 𝓞K) * e.symm betaZ ∈ target := by
    simpa [Q, e, betaZ, target] using
      basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_ne_one hdneg hd4 I b
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hz' : e z ∈ Ideal.span ({aZ, betaZ} : Set (Zsqrtd d)) := by
    simpa [idealOfForm_of_mod_four_ne_one, e, aZ, betaZ] using hz
  rcases ((Ideal.mem_span_pair (x := aZ) (y := betaZ)).mp hz') with ⟨u, v, huv⟩
  have hz_eq : z = e.symm (u * aZ + v * betaZ) := by
    apply e.injective
    simp [huv]
  rw [hz_eq]
  have hsplit :
      (b.basis 0 : 𝓞K) * e.symm (u * aZ + v * betaZ) =
        e.symm u * ((b.basis 0 : 𝓞K) * e.symm aZ) +
          e.symm v * ((b.basis 0 : 𝓞K) * e.symm betaZ) := by
    simp
    ring
  rw [hsplit]
  exact target.add_mem (target.mul_mem_left (e.symm u) hscalar)
    (target.mul_mem_left (e.symm v) hbeta)

/-- In the `d % 4 = 1` branch, the two Cox generator membership lemmas assemble
to the inclusion `(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q ≤
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    d hd4
  let aZ : ZOnePlusSqrtdOverTwo (d / 4) := ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))
  let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
  let target : Ideal 𝓞K := Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) *
    (I : Ideal 𝓞K)
  have hscalar : (b.basis 0 : 𝓞K) * e.symm aZ ∈ target := by
    simpa [Q, e, aZ, target] using
      basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_eq_one hdneg hd4 I b
  have hbeta : (b.basis 0 : 𝓞K) * e.symm betaZ ∈ target := by
    simpa [Q, e, betaZ, target] using
      basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_eq_one hdneg hd4 I b
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  have hz' : e z ∈ Ideal.span ({aZ, betaZ} : Set (ZOnePlusSqrtdOverTwo (d / 4))) := by
    simpa [idealOfForm_of_mod_four_eq_one, e, aZ, betaZ] using hz
  rcases ((Ideal.mem_span_pair (x := aZ) (y := betaZ)).mp hz') with ⟨u, v, huv⟩
  have hz_eq : z = e.symm (u * aZ + v * betaZ) := by
    apply e.injective
    simp [huv]
  rw [hz_eq]
  have hsplit :
      (b.basis 0 : 𝓞K) * e.symm (u * aZ + v * betaZ) =
        e.symm u * ((b.basis 0 : 𝓞K) * e.symm aZ) +
          e.symm v * ((b.basis 0 : 𝓞K) * e.symm betaZ) := by
    simp
    ring
  rw [hsplit]
  exact target.add_mem (target.mul_mem_left (e.symm u) hscalar)
    (target.mul_mem_left (e.symm v) hbeta)

/-- In the `d % 4 ≠ 1` branch, the oriented basis decomposition of `I` gives
the reverse inclusion `(a_Q) · I ≤ (b₀) · J(Q_b)`. -/
theorem span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) ≤
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let aOK : 𝓞K := ((Q.1.a : ℤ) : 𝓞K)
  let aZ : Zsqrtd d := ((Q.1.a : ℤ) : Zsqrtd d)
  let betaZ : Zsqrtd d := (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  let target : Ideal 𝓞K := Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
    idealOfForm_of_mod_four_ne_one d hd4 Q
  have ha_mem_J : e.symm aZ ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := by
    change e (e.symm aZ) ∈ Ideal.span ({aZ, betaZ} : Set (Zsqrtd d))
    rw [RingEquiv.apply_symm_apply]
    exact Ideal.subset_span (by simp)
  have hbeta_mem_J : e.symm betaZ ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := by
    change e (e.symm betaZ) ∈ Ideal.span ({aZ, betaZ} : Set (Zsqrtd d))
    rw [RingEquiv.apply_symm_apply]
    exact Ideal.subset_span (by simp)
  have h_a_b0 : aOK * (b.basis 0 : 𝓞K) ∈ target := by
    have hb0 : (b.basis 0 : 𝓞K) ∈ Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) :=
      Ideal.subset_span (by simp)
    have h : (b.basis 0 : 𝓞K) * e.symm aZ ∈ target := Ideal.mul_mem_mul hb0 ha_mem_J
    simpa [target, aOK, aZ, mul_comm] using h
  have h_a_b1 : aOK * (b.basis 1 : 𝓞K) ∈ target := by
    have hb0 : (b.basis 0 : 𝓞K) ∈ Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) :=
      Ideal.subset_span (by simp)
    have hβ : (b.basis 0 : 𝓞K) * e.symm betaZ ∈ target :=
      Ideal.mul_mem_mul hb0 hbeta_mem_J
    have hrel :=
      basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
        hdneg hd4 I b
    dsimp only at hrel
    have hrel' : (b.basis 0 : 𝓞K) * e.symm betaZ =
        -(aOK * (b.basis 1 : 𝓞K)) := by
      simpa [Q, e, betaZ, aOK] using hrel
    have hneg : -(aOK * (b.basis 1 : 𝓞K)) ∈ target := by
      simpa [hrel'] using hβ
    simpa using neg_mem hneg
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  let zI : (I : Ideal 𝓞K) := ⟨z, hz⟩
  let m : ℤ := b.basis.repr zI 0
  let n : ℤ := b.basis.repr zI 1
  have hz_decomp : z = m • (b.basis 0 : 𝓞K) + n • (b.basis 1 : 𝓞K) := by
    have hsum := b.basis.sum_repr zI
    have hsub : ((∑ i : Fin 2, (b.basis.repr zI) i • b.basis i :
        (I : Ideal 𝓞K)) : 𝓞K) = z := by
      simp [zI, hsum]
    rw [Fin.sum_univ_two] at hsub
    simpa [m, n] using hsub.symm
  rw [hz_decomp, mul_add]
  apply target.add_mem
  · rw [zsmul_eq_mul']
    rw [show aOK * ((b.basis 0 : 𝓞K) * (m : 𝓞K)) =
        (m : 𝓞K) * (aOK * (b.basis 0 : 𝓞K)) by ring]
    exact target.mul_mem_left (m : 𝓞K) h_a_b0
  · rw [zsmul_eq_mul']
    rw [show aOK * ((b.basis 1 : 𝓞K) * (n : 𝓞K)) =
        (n : 𝓞K) * (aOK * (b.basis 1 : 𝓞K)) by ring]
    exact target.mul_mem_left (n : 𝓞K) h_a_b1

/-- In the `d % 4 = 1` branch, the oriented basis decomposition of `I` gives
the reverse inclusion `(a_Q) · I ≤ (b₀) · J(Q_b)`. -/
theorem span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) ≤
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    d hd4
  let aOK : 𝓞K := ((Q.1.a : ℤ) : 𝓞K)
  let aZ : ZOnePlusSqrtdOverTwo (d / 4) := ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))
  let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
  let target : Ideal 𝓞K := Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
    idealOfForm_of_mod_four_eq_one d hd4 Q
  have ha_mem_J : e.symm aZ ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
    change e (e.symm aZ) ∈ Ideal.span ({aZ, betaZ} : Set (ZOnePlusSqrtdOverTwo (d / 4)))
    rw [RingEquiv.apply_symm_apply]
    exact Ideal.subset_span (by simp)
  have hbeta_mem_J : e.symm betaZ ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
    change e (e.symm betaZ) ∈ Ideal.span ({aZ, betaZ} : Set (ZOnePlusSqrtdOverTwo (d / 4)))
    rw [RingEquiv.apply_symm_apply]
    exact Ideal.subset_span (by simp)
  have h_a_b0 : aOK * (b.basis 0 : 𝓞K) ∈ target := by
    have hb0 : (b.basis 0 : 𝓞K) ∈ Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) :=
      Ideal.subset_span (by simp)
    have h : (b.basis 0 : 𝓞K) * e.symm aZ ∈ target := Ideal.mul_mem_mul hb0 ha_mem_J
    simpa [target, aOK, aZ, mul_comm] using h
  have h_a_b1 : aOK * (b.basis 1 : 𝓞K) ∈ target := by
    have hb0 : (b.basis 0 : 𝓞K) ∈ Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) :=
      Ideal.subset_span (by simp)
    have hβ : (b.basis 0 : 𝓞K) * e.symm betaZ ∈ target :=
      Ideal.mul_mem_mul hb0 hbeta_mem_J
    have hrel :=
      basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
        hdneg hd4 I b
    dsimp only at hrel
    have hrel' : (b.basis 0 : 𝓞K) * e.symm betaZ =
        -(aOK * (b.basis 1 : 𝓞K)) := by
      simpa [Q, e, betaZ, aOK] using hrel
    have hneg : -(aOK * (b.basis 1 : 𝓞K)) ∈ target := by
      simpa [hrel'] using hβ
    simpa using neg_mem hneg
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  let zI : (I : Ideal 𝓞K) := ⟨z, hz⟩
  let m : ℤ := b.basis.repr zI 0
  let n : ℤ := b.basis.repr zI 1
  have hz_decomp : z = m • (b.basis 0 : 𝓞K) + n • (b.basis 1 : 𝓞K) := by
    have hsum := b.basis.sum_repr zI
    have hsub : ((∑ i : Fin 2, (b.basis.repr zI) i • b.basis i :
        (I : Ideal 𝓞K)) : 𝓞K) = z := by
      simp [zI, hsum]
    rw [Fin.sum_univ_two] at hsub
    simpa [m, n] using hsub.symm
  rw [hz_decomp, mul_add]
  apply target.add_mem
  · rw [zsmul_eq_mul']
    rw [show aOK * ((b.basis 0 : 𝓞K) * (m : 𝓞K)) =
        (m : 𝓞K) * (aOK * (b.basis 0 : 𝓞K)) by ring]
    exact target.mul_mem_left (m : 𝓞K) h_a_b0
  · rw [zsmul_eq_mul']
    rw [show aOK * ((b.basis 1 : 𝓞K) * (n : 𝓞K)) =
        (n : 𝓞K) * (aOK * (b.basis 1 : 𝓞K)) by ring]
    exact target.mul_mem_left (n : 𝓞K) h_a_b1

/-- In the `d % 4 ≠ 1` branch, the oriented basis first vector gives the
principal ideal relation `(b₀) · J(Q_b) = (a_Q) · I` for the norm form. -/
theorem basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q =
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  exact le_antisymm
    (basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_ne_one hdneg hd4 I b)
    (span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_ne_one hdneg hd4 I b)

/-- In the `d % 4 = 1` branch, the oriented basis first vector gives the
principal ideal relation `(b₀) · J(Q_b) = (a_Q) · I` for the norm form. -/
theorem basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q =
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  exact le_antisymm
    (basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_eq_one hdneg hd4 I b)
    (span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_eq_one hdneg hd4 I b)

/-- In the `d % 4 ≠ 1` branch, the right-inverse law follows from the classical
Cox relation `(α) · J(Q_b) = (a_Q) · I`, where `α` is the first vector of the
oriented ideal basis and `Q_b` is its norm form. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  have hb0_ne : (b.basis 0 : 𝓞K) ≠ 0 := fun h => b.basis.ne_zero 0 (Subtype.ext h)
  refine idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    hdneg hd4 I b hb0_ne ?_ hrel
  exact_mod_cast
    (primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).2.2.2.1.ne'

/-- In the `d % 4 ≠ 1` branch, the Cox ideal class of the norm form attached
to any oriented basis of `I` is the original ideal class. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I :=
  idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_first_vector_relation
    hdneg hd4 I b
    (basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_ne_one hdneg hd4 I b)

/-- Right-inverse branch law for the `d % 4 ≠ 1` Cox map, using the canonical
oriented basis chosen by `classGroupToFormClass`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_ne_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis hdneg hd4 I
    (orientedBasisOfNeZero (I : Ideal 𝓞K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))

/-- In the `d % 4 = 1` branch, the right-inverse law follows from the same
principal relation between the basis first vector, the Cox ideal of the norm
form, and the original ideal. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  have hb0_ne : (b.basis 0 : 𝓞K) ≠ 0 := fun h => b.basis.ne_zero 0 (Subtype.ext h)
  refine idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    hdneg hd4 I b hb0_ne ?_ hrel
  exact_mod_cast
    (primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).2.2.2.1.ne'

/-- In the `d % 4 = 1` branch, the Cox ideal class of the norm form attached to
any oriented basis of `I` is the original ideal class. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I :=
  idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_first_vector_relation
    hdneg hd4 I b
    (basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_eq_one hdneg hd4 I b)

/-- Right-inverse branch law for the `d % 4 = 1` Cox map, using the canonical
oriented basis chosen by `classGroupToFormClass`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_eq_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis hdneg hd4 I
    (orientedBasisOfNeZero (I : Ideal 𝓞K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 ≠ 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_ne_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 = 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_eq_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

end CoxAssembly

end BinaryQuadraticForm
end QuadraticNumberFields
