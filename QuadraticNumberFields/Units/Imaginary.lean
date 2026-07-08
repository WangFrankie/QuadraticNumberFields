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
theorem zsqrtd_norm_nonneg (hd : d < 0) (z : Zsqrtd d) : 0 ≤ Zsqrtd.norm z :=
  norm_nonneg_of_discr_nonpos (a := d) (b := 0) (by nlinarith) z

/-- For `d < -1` the only units of `ℤ[√d]` are `±1`. -/
theorem isUnit_zsqrtd_iff_of_lt_neg_one (hd : d < -1) (z : Zsqrtd d) :
    IsUnit z ↔ z = 1 ∨ z = -1 :=
  isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (a := d) (b := 0)
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

private lemma sq_add_sq_eq_one_of_im_cube_eq_one {a b : ℤ}
    (h : b * (3 * a ^ 2 - b ^ 2) = 1) :
    a ^ 2 + b ^ 2 = 1 := by
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h with ⟨hb, hf⟩ | ⟨hb, hf⟩
  · subst b
    nlinarith [sq_nonneg a]
  · subst b
    nlinarith [sq_nonneg a]

private lemma sq_add_sq_eq_one_of_im_cube_eq_neg_one {a b : ℤ}
    (h : b * (3 * a ^ 2 - b ^ 2) = -1) :
    a ^ 2 + b ^ 2 = 1 := by
  have hneg : (-b) * (3 * a ^ 2 - b ^ 2) = 1 := by nlinarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hneg with ⟨hb, hf⟩ | ⟨hb, hf⟩ <;>
    nlinarith [sq_nonneg a]

private lemma sq_add_sq_eq_one_of_re_cube_eq_one {a b : ℤ}
    (h : a * (a ^ 2 - 3 * b ^ 2) = 1) :
    a ^ 2 + b ^ 2 = 1 := by
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h with ⟨ha, hf⟩ | ⟨ha, hf⟩
  · subst a
    nlinarith [sq_nonneg b]
  · subst a
    nlinarith [sq_nonneg b]

private lemma sq_add_sq_eq_one_of_re_cube_eq_neg_one {a b : ℤ}
    (h : a * (a ^ 2 - 3 * b ^ 2) = -1) :
    a ^ 2 + b ^ 2 = 1 := by
  have hneg : (-a) * (a ^ 2 - 3 * b ^ 2) = 1 := by nlinarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hneg with ⟨ha, hf⟩ | ⟨ha, hf⟩ <;>
    nlinarith [sq_nonneg b]

private lemma sq_add_two_mul_sq_eq_one_of_re_cube_neg_two_eq_one {a b : ℤ}
    (h : a * (a ^ 2 - 6 * b ^ 2) = 1) :
    a ^ 2 + 2 * b ^ 2 = 1 := by
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp h with ⟨ha, hf⟩ | ⟨ha, hf⟩
  · subst a
    nlinarith [sq_nonneg b]
  · subst a
    nlinarith [sq_nonneg b]

private lemma sq_add_two_mul_sq_eq_one_of_re_cube_neg_two_eq_neg_one {a b : ℤ}
    (h : a * (a ^ 2 - 6 * b ^ 2) = -1) :
    a ^ 2 + 2 * b ^ 2 = 1 := by
  have hneg : (-a) * (a ^ 2 - 6 * b ^ 2) = 1 := by nlinarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hneg with ⟨ha, hf⟩ | ⟨ha, hf⟩ <;>
    nlinarith [sq_nonneg b]

/-- If a cube in `Zsqrtd (-1)` is associated to an element with imaginary part
`1`, then the base of the cube has norm `1`. -/
-- Repository use: Cox's negative-square auxiliary equation factors
-- `n ^ 3 = z ^ 2 + 1` in the project-owned Gaussian order `Zsqrtd (-1)`.
theorem zsqrtd_neg_one_norm_eq_one_of_associated_cube_of_im_eq_one
    {w z : Zsqrtd (-1)} (h : Associated (w ^ 3) z) (hz : z.im = 1) :
    Zsqrtd.norm w = 1 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨a, b⟩ := w
  rcases (isUnit_zsqrtd_neg_one_iff (u : Zsqrtd (-1))).mp u.isUnit with
    hu1 | hum1 | hui | huni
  · rw [hu1] at hu
    have him : b * (3 * a ^ 2 - b ^ 2) = 1 := by
      have hraw := congrArg QuadraticAlgebra.im hu
      have hraw' : (a * a + -(b * b)) * b + (a * b + b * a) * a = 1 := by
        simpa [hz, Zsqrtd.sqrtd, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_sq_eq_one_of_im_cube_eq_one him
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm
  · rw [hum1] at hu
    have him : b * (3 * a ^ 2 - b ^ 2) = -1 := by
      have hraw := congrArg QuadraticAlgebra.im hu
      have hraw' : -((a * b + b * a) * a) + -((a * a + -(b * b)) * b) = 1 := by
        simpa [hz, Zsqrtd.sqrtd, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_sq_eq_one_of_im_cube_eq_neg_one him
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm
  · rw [hui] at hu
    have hre : a * (a ^ 2 - 3 * b ^ 2) = 1 := by
      have hraw := congrArg QuadraticAlgebra.im hu
      have hraw' : (a * a + -(b * b)) * a + (-(b * a) + -(a * b)) * b = 1 := by
        simpa [hz, Zsqrtd.sqrtd, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_sq_eq_one_of_re_cube_eq_one hre
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm
  · rw [huni] at hu
    have hre : a * (a ^ 2 - 3 * b ^ 2) = -1 := by
      have hraw := congrArg QuadraticAlgebra.im hu
      have hraw' :
          -((-(b * a) + -(a * b)) * b) + -((a * a + -(b * b)) * a) = 1 := by
        simpa [hz, Zsqrtd.sqrtd, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_sq_eq_one_of_re_cube_eq_neg_one hre
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm

/-- If a cube in `Zsqrtd (-2)` is associated to an element with real part `1`,
then the base of the cube has norm `1`. -/
-- Repository use: Cox's `ℤ[√-2]` auxiliary equation factors
-- `n ^ 3 = 2 * z ^ 2 + 1` in the project-owned order `Zsqrtd (-2)`.
theorem zsqrtd_neg_two_norm_eq_one_of_associated_cube_of_re_eq_one
    {w z : Zsqrtd (-2)} (h : Associated (w ^ 3) z) (hz : z.re = 1) :
    Zsqrtd.norm w = 1 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨a, b⟩ := w
  rcases (isUnit_zsqrtd_iff_of_lt_neg_one (by norm_num : (-2 : ℤ) < -1)
      (u : Zsqrtd (-2))).mp u.isUnit with hu1 | hum1
  · rw [hu1] at hu
    have hre : a * (a ^ 2 - 6 * b ^ 2) = 1 := by
      have hraw := congrArg QuadraticAlgebra.re hu
      have hraw' : (a * a + -(2 * b * b)) * a + -(2 * (a * b + b * a) * b) = 1 := by
        simpa [hz, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_two_mul_sq_eq_one_of_re_cube_neg_two_eq_one hre
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm
  · rw [hum1] at hu
    have hre : a * (a ^ 2 - 6 * b ^ 2) = -1 := by
      have hraw := congrArg QuadraticAlgebra.re hu
      have hraw' :
          2 * (a * b + b * a) * b + -((a * a + -(2 * b * b)) * a) = 1 := by
        simpa [hz, pow_succ] using hraw
      nlinarith
    have hnorm := sq_add_two_mul_sq_eq_one_of_re_cube_neg_two_eq_neg_one hre
    simpa [Zsqrtd.norm_mk, pow_two] using hnorm

end Zsqrtd

section ZOnePlusSqrtdOverTwo

/-- For `k ≤ -2` (so `d = 1 + 4k ≤ -7`) the only units of `ℤ[(1+√(1+4k))/2]`
are `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_of_le_neg_two {k : ℤ} (hk : k ≤ -2)
    (z : ZOnePlusSqrtdOverTwo k) : IsUnit z ↔ z = 1 ∨ z = -1 :=
  isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (a := k) (b := 1)
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
