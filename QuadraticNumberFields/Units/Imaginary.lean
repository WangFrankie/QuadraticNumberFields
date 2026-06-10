/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Units.Pell
import QuadraticNumberFields.ZOnePlusSqrtOverTwo.Basic

/-!
# Units of Imaginary Quadratic Orders

For `d < 0` the norm on `ℤ[√d]` is positive definite, so the unit groups of
the candidate rings of integers are finite. This file classifies them:

* `isUnit_zsqrtd_iff_of_lt_neg_one`: for `d < -1` the units of `ℤ[√d]` are
  `±1`.
* `isUnit_zsqrtd_neg_one_iff`: the Gaussian integers `ℤ[√-1]` have units
  `±1` and `±√-1`.
* `isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two`: for `k ≤ -2` (discriminant
  parameter `d = 1 + 4k ≤ -7`) the units of `ℤ[(1+√d)/2]` are `±1`.
* `isUnit_zOnePlusSqrtOverTwo_neg_one_iff`: the Eisenstein integers
  `ℤ[(1+√-3)/2]` have exactly six units.
-/

namespace QuadraticNumberFields
namespace Units

section Zsqrtd

variable {d : ℤ}

/-- For `d < 0` the norm on `ℤ[√d]` is nonnegative. -/
theorem zsqrtd_norm_nonneg (hd : d < 0) (z : Zsqrtd d) : 0 ≤ Zsqrtd.norm z := by
  rw [Zsqrtd.norm_def]
  nlinarith [mul_self_nonneg z.re, mul_self_nonneg z.im]

/-- For `d < -1` the only units of `ℤ[√d]` are `±1`. -/
theorem isUnit_zsqrtd_iff_of_lt_neg_one (hd : d < -1) (z : Zsqrtd d) :
    IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    rw [isUnit_mk_iff_isPellSolution] at hz
    unfold IsPellSolution at hz
    rcases hz with h | h
    · have hb : b = 0 := by nlinarith [sq_nonneg a, sq_nonneg b]
      subst hb
      have h1 : a * a = 1 := by rw [← pow_two]; linarith
      rcases mul_self_eq_one_iff.mp h1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
    · exact absurd h (by nlinarith [sq_nonneg a, sq_nonneg b])
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

/-- The units of the Gaussian integers `ℤ[√-1]` are `±1` and `±√-1`. -/
theorem isUnit_zsqrtd_neg_one_iff (z : Zsqrtd (-1)) :
    IsUnit z ↔ z = 1 ∨ z = -1 ∨ z = Zsqrtd.sqrtd ∨ z = -Zsqrtd.sqrtd := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    rw [isUnit_mk_iff_isPellSolution] at hz
    unfold IsPellSolution at hz
    have h : a ^ 2 + b ^ 2 = 1 := by
      rcases hz with h | h <;> nlinarith [sq_nonneg a, sq_nonneg b]
    have ha1 : a ≤ 1 := by nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
    have ha2 : -1 ≤ a := by nlinarith [sq_nonneg b, sq_nonneg (a + 1)]
    have hb1 : b ≤ 1 := by nlinarith [sq_nonneg a, sq_nonneg (b - 1)]
    have hb2 : -1 ≤ b := by nlinarith [sq_nonneg a, sq_nonneg (b + 1)]
    interval_cases a <;> interval_cases b <;>
      simp_all [QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · rintro (rfl | rfl | rfl | rfl) <;>
    · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
      simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end Zsqrtd

section ZOnePlusSqrtOverTwo

/-- For `k ≤ -2` (so `d = 1 + 4k ≤ -7`) the only units of `ℤ[(1+√(1+4k))/2]`
are `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two {k : ℤ} (hk : k ≤ -2)
    (z : ZOnePlusSqrtOverTwo k) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    have hnorm := Int.isUnit_iff.mp (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hz)
    have hval : QuadraticAlgebra.norm (⟨a, b⟩ : ZOnePlusSqrtOverTwo k) =
        a * a + 1 * a * b - k * b * b := QuadraticAlgebra.norm_def _
    rw [hval] at hnorm
    rcases hnorm with h | h
    · have hb : b = 0 := by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
      subst hb
      have h1 : a * a = 1 := by linarith
      rcases mul_self_eq_one_iff.mp h1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
    · exact absurd h (by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b])
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

/-- The Eisenstein integers `ℤ[(1+√-3)/2]` (parameter `k = -1`) have exactly
six units: `±1`, `±ω`, and `±(1 - ω)`, where `ω = (1+√-3)/2` is the
generator `⟨0, 1⟩`. -/
theorem isUnit_zOnePlusSqrtOverTwo_neg_one_iff (z : ZOnePlusSqrtOverTwo (-1)) :
    IsUnit z ↔
      z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨1, -1⟩ ∨ z = ⟨-1, 1⟩ := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    have hnorm := Int.isUnit_iff.mp (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hz)
    have hval : QuadraticAlgebra.norm (⟨a, b⟩ : ZOnePlusSqrtOverTwo (-1)) =
        a * a + 1 * a * b - (-1) * b * b := QuadraticAlgebra.norm_def _
    rw [hval] at hnorm
    have h : a * a + a * b + b * b = 1 := by
      rcases hnorm with h | h
      · linarith
      · exact absurd h (by nlinarith [sq_nonneg (2 * a + b), sq_nonneg b])
    have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a + b), sq_nonneg b]
    have ha2 : -1 ≤ a := by nlinarith [sq_nonneg (a + b), sq_nonneg b]
    have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (a + b), sq_nonneg a]
    have hb2 : -1 ≤ b := by nlinarith [sq_nonneg (a + b), sq_nonneg a]
    interval_cases a <;> interval_cases b <;>
      simp_all [QuadraticAlgebra.ext_iff, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · rw [QuadraticAlgebra.isUnit_iff_norm_isUnit]
      simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

end ZOnePlusSqrtOverTwo

end Units
end QuadraticNumberFields
