/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.ModularForms.HeckeTwoSymmetric
import QNFMathlib.NumberTheory.ModularForms.JInvariant

/-!
# Weber's Cubic and the Modular `j`-Invariant

Material destined for mathlib.

The three values `𝔣²⁴`, `-𝔣₁²⁴`, `-𝔣₂²⁴` are the roots of
`(X - 16)³ - j X`. The first two elementary symmetric functions come from the
`T₂`-translates of `Δ`, and the product comes from `𝔣 𝔣₁ 𝔣₂ = √2`.

This gives the three rational expressions
`j = (𝔣²⁴ - 16)³/𝔣²⁴ = (𝔣₁²⁴ + 16)³/𝔣₁²⁴ = (𝔣₂²⁴ + 16)³/𝔣₂²⁴`.
No choice of a cube root, or complex multiplication hypothesis, is involved.
-/

open Complex EisensteinSeries
open scoped ModularForm

namespace ModularForm

noncomputable section

/-- The second elementary symmetric function of `𝔣²⁴, -𝔣₁²⁴, -𝔣₂²⁴` is `768 - j`. -/
theorem weber_second_symmetric (τ : UpperHalfPlane) :
    weberF₁ τ ^ 24 * weberF₂ τ ^ 24 -
      weberF τ ^ 24 * (weberF₁ τ ^ 24 + weberF₂ τ ^ 24) = 768 - jInvariant τ := by
  have hη := eta_ne_zero τ.im_pos
  have h := heckeTwoSum₂_eq τ
  simp only [heckeTwoSum₂, discriminantC, discriminant] at h
  simp only [weberF, weberF₁, weberF₂, mul_pow, inv_pow, zeta48_pow_24, div_pow,
    ofReal_sqrt_two_pow_24, jInvariant, discriminant]
  field_simp
  simp only [mul_comm (τ : ℂ) 2]
  linear_combination h

/-- The product of `𝔣²⁴, -𝔣₁²⁴, -𝔣₂²⁴` is `4096`. -/
theorem weber_product_pow_24 {z : ℂ} (hz : 0 < z.im) :
    weberF z ^ 24 * weberF₁ z ^ 24 * weberF₂ z ^ 24 = 4096 := by
  rw [← mul_pow, ← mul_pow, weberF_mul_weberF₁_mul_weberF₂ hz, ofReal_sqrt_two_pow_24]

/-- The factorization of Weber's cubic, including multiplicities. -/
theorem weber_cubic_factorization (τ : UpperHalfPlane) (x : ℂ) :
    (x - weberF τ ^ 24) * (x + weberF₁ τ ^ 24) * (x + weberF₂ τ ^ 24) =
      (x - 16) ^ 3 - jInvariant τ * x := by
  have h₁ := weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24 τ.im_pos
  have h₂ := weber_second_symmetric τ
  have h₃ := weber_product_pow_24 τ.im_pos
  linear_combination -(x ^ 2) * h₁ + x * h₂ - h₃

theorem weberF_cubic (τ : UpperHalfPlane) :
    (weberF τ ^ 24 - 16) ^ 3 = jInvariant τ * weberF τ ^ 24 := by
  have h := weber_cubic_factorization τ (weberF τ ^ 24)
  simp only [sub_self, zero_mul] at h
  linear_combination -h

theorem weberF₁_cubic (τ : UpperHalfPlane) :
    (weberF₁ τ ^ 24 + 16) ^ 3 = jInvariant τ * weberF₁ τ ^ 24 := by
  have h := weber_cubic_factorization τ (-weberF₁ τ ^ 24)
  simp only [neg_add_cancel, mul_zero, zero_mul] at h
  linear_combination h

theorem weberF₂_cubic (τ : UpperHalfPlane) :
    (weberF₂ τ ^ 24 + 16) ^ 3 = jInvariant τ * weberF₂ τ ^ 24 := by
  have h := weber_cubic_factorization τ (-weberF₂ τ ^ 24)
  simp only [neg_add_cancel, mul_zero] at h
  linear_combination h

theorem jInvariant_eq_weberF (τ : UpperHalfPlane) :
    jInvariant τ = (weberF τ ^ 24 - 16) ^ 3 / weberF τ ^ 24 :=
  (eq_div_iff (pow_ne_zero _ (weberF_ne_zero τ.im_pos))).mpr (weberF_cubic τ).symm

theorem jInvariant_eq_weberF₁ (τ : UpperHalfPlane) :
    jInvariant τ = (weberF₁ τ ^ 24 + 16) ^ 3 / weberF₁ τ ^ 24 :=
  (eq_div_iff (pow_ne_zero _ (weberF₁_ne_zero τ.im_pos))).mpr (weberF₁_cubic τ).symm

theorem jInvariant_eq_weberF₂ (τ : UpperHalfPlane) :
    jInvariant τ = (weberF₂ τ ^ 24 + 16) ^ 3 / weberF₂ τ ^ 24 :=
  (eq_div_iff (pow_ne_zero _ (weberF₂_ne_zero τ.im_pos))).mpr (weberF₂_cubic τ).symm

/-- The second `j`-value on `X₀(2)`, in the parameter `𝔣₂(τ)²⁴`. -/
theorem jInvariant_two_mul_eq_weberF₂ (τ : UpperHalfPlane) :
    jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))) =
      (weberF₂ τ ^ 24 + 256) ^ 3 / (weberF₂ τ ^ 24) ^ 2 := by
  have hpos : 0 < (2 * (τ : ℂ)).im := by simpa using mul_pos two_pos τ.im_pos
  have hprod : weberF₁ (2 * (τ : ℂ)) ^ 24 * weberF₂ τ ^ 24 = 4096 := by
    rw [← mul_pow, weberF₁_two_mul_mul_weberF₂ τ.im_pos, ofReal_sqrt_two_pow_24]
  have hf := pow_ne_zero 24 (weberF₂_ne_zero τ.im_pos)
  have hquot := (eq_div_iff hf).mpr hprod
  rw [jInvariant_eq_weberF₁, UpperHalfPlane.ofComplex_apply_of_im_pos hpos, hquot]
  field_simp [weberF₂_ne_zero τ.im_pos]
  ring

end

end ModularForm
