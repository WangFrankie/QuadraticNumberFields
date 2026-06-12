/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Units.Pell
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic

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

open QuadraticAlgebra

section Zsqrtd

variable {d : ℤ}

/-- For `d < 0` the norm on `ℤ[√d]` is nonnegative. -/
theorem zsqrtd_norm_nonneg (hd : d < 0) (z : Zsqrtd d) : 0 ≤ Zsqrtd.norm z := by
  exact norm_nonneg_of_discr_nonpos (a := d) (b := 0) (by nlinarith) z

/-- For `d < -1` the only units of `ℤ[√d]` are `±1`. -/
theorem isUnit_zsqrtd_iff_of_lt_neg_one (hd : d < -1) (z : Zsqrtd d) :
    IsUnit z ↔ z = 1 ∨ z = -1 := by
  exact isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (a := d) (b := 0)
    (by nlinarith) z

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
      simp_all [QuadraticAlgebra.ext_iff]
  · rintro (rfl | rfl | rfl | rfl) <;>
    · rw [isUnit_iff_norm_isUnit]
      simp [norm_def, re_one, im_one]

end Zsqrtd

section ZOnePlusSqrtdOverTwo

/-- For `k ≤ -2` (so `d = 1 + 4k ≤ -7`) the only units of `ℤ[(1+√(1+4k))/2]`
are `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two {k : ℤ} (hk : k ≤ -2)
    (z : ZOnePlusSqrtdOverTwo k) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  exact isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (a := k) (b := 1)
    (by nlinarith) z

/-- The Eisenstein integers `ℤ[(1+√-3)/2]` (parameter `k = -1`) have exactly
six units: `±1`, `±ω`, and `±(1 - ω)`, where `ω = (1+√-3)/2` is the
generator `⟨0, 1⟩`. -/
theorem isUnit_zOnePlusSqrtOverTwo_neg_one_iff (z : ZOnePlusSqrtdOverTwo (-1)) :
    IsUnit z ↔
      z = 1 ∨ z = -1 ∨ z = ⟨0, 1⟩ ∨ z = ⟨0, -1⟩ ∨ z = ⟨1, -1⟩ ∨ z = ⟨-1, 1⟩ := by
  constructor
  · intro hz
    obtain ⟨a, b⟩ := z
    rw [ZOnePlusSqrtdOverTwo.isUnit_mk_iff] at hz
    have h : a * a + a * b + b * b = 1 := by
      rcases hz with h | h
      · nlinarith
      · nlinarith [sq_nonneg (2 * a + b), sq_nonneg b]
    have ha1 : a ≤ 1 := by nlinarith [sq_nonneg (a + b), sq_nonneg b]
    have ha2 : -1 ≤ a := by nlinarith [sq_nonneg (a + b), sq_nonneg b]
    have hb1 : b ≤ 1 := by nlinarith [sq_nonneg (a + b), sq_nonneg a]
    have hb2 : -1 ≤ b := by nlinarith [sq_nonneg (a + b), sq_nonneg a]
    interval_cases a <;> interval_cases b <;>
      simp_all [QuadraticAlgebra.ext_iff]
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl) <;>
    · rw [ZOnePlusSqrtdOverTwo.isUnit_mk_iff]
      simp

end ZOnePlusSqrtdOverTwo

end Units
end QuadraticNumberFields
