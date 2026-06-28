/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Integer Parity Helpers

Material destined for mathlib.
-/

/-- Normalise the integer half of `-b` when `b` is even. -/
-- Repository use: Cox ideal formulas use this to recover the integer parameter
-- from the middle coefficient in the non-half-integral branch.
theorem Int.two_mul_neg_ediv_two_of_even {b : ℤ} (hb : Even b) : 2 * ((-b) / 2) = -b :=
  Int.two_mul_ediv_two_of_even hb.neg

/-- Normalise the integer half of `-(b + 1)` when `b` is odd. -/
-- Repository use: Cox ideal formulas use this to recover the integer parameter
-- from the middle coefficient in the half-integral branch.
theorem Int.two_mul_neg_succ_ediv_two_of_odd {b : ℤ} (hb : Odd b) :
    2 * (-(b + 1) / 2) = -(b + 1) := by
  exact Int.two_mul_ediv_two_of_even ((hb.add_odd odd_one : Even (b + 1))).neg

/-- An integer congruent modulo an even modulus to an even integer is even. -/
-- Repository use: `composeMiddleB` parity in computable Gauss composition.
theorem Int.even_of_modEq_even {B b a : ℤ} (hb : Even b) (hB : B ≡ b [ZMOD 2 * a]) :
    Even B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  refine ⟨m - a * k, ?_⟩
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

/-- An integer congruent modulo an even modulus to an odd integer is odd. -/
-- Repository use: `composeMiddleB` parity in computable Gauss composition.
theorem Int.odd_of_modEq_odd {B b a : ℤ} (hb : Odd b) (hB : B ≡ b [ZMOD 2 * a]) :
    Odd B := by
  rcases hb with ⟨m, hm⟩
  rcases Int.modEq_iff_dvd.mp hB with ⟨k, hk⟩
  refine ⟨m - a * k, ?_⟩
  have hB_eq : B = b - 2 * a * k := by linarith
  rw [hB_eq, hm]
  ring

/-- If twice an integer is a square, then the integer is twice a square. -/
-- Repository use: Heegner's Diophantine reduction uses this in the odd
-- `X` branch to pass from `2 * (X ^ 3 + 1)` being a square to
-- `X ^ 3 + 1` being twice a square.
theorem Int.exists_eq_two_mul_sq_of_two_mul_eq_sq {A z : ℤ}
    (h : 2 * A = z ^ 2) :
    ∃ w : ℤ, A = 2 * w ^ 2 := by
  have hz_even_sq : Even (z ^ 2) := by
    rw [← h]
    exact even_two_mul A
  have hz_even : Even z :=
    (Int.even_pow' (m := z) (n := 2) (by norm_num)).mp hz_even_sq
  rcases hz_even with ⟨w, hw⟩
  use w
  subst z
  nlinarith

/-- If twice an integer is the negative of a square, then the integer is
negative twice a square. -/
-- Repository use: Heegner's Diophantine reduction uses this in the odd
-- `X` branch to pass from `2 * (X ^ 3 + 1)` being a negative square to
-- `X ^ 3 + 1` being negative twice a square.
theorem Int.exists_eq_neg_two_mul_sq_of_two_mul_eq_neg_sq {A z : ℤ}
    (h : 2 * A = -z ^ 2) :
    ∃ w : ℤ, A = -2 * w ^ 2 := by
  have hneg : 2 * (-A) = z ^ 2 := by
    nlinarith
  obtain ⟨w, hw⟩ := Int.exists_eq_two_mul_sq_of_two_mul_eq_sq hneg
  use w
  nlinarith

/-- If an integer cube is one more than a square, then the square root is even. -/
-- Repository use: Cox's Gaussian-integer auxiliary equation uses this before
-- proving the two factors `z ± √-1` are coprime.
theorem Int.even_of_cube_eq_sq_add_one {n z : ℤ} (h : n ^ 3 = z ^ 2 + 1) :
    Even z := by
  by_contra hz_even
  have hz_odd : Odd z := Int.not_even_iff_odd.mp hz_even
  rcases hz_odd with ⟨k, hk⟩
  subst z
  have hn3_even : Even (n ^ 3) := by
    rw [h]
    use 2 * k ^ 2 + 2 * k + 1
    ring
  have hn_even : Even n := (Int.even_pow' (m := n) (n := 3) (by norm_num)).mp hn3_even
  rcases hn_even with ⟨m, hm⟩
  subst n
  have hhalf : 4 * m ^ 3 = 2 * k ^ 2 + 2 * k + 1 := by nlinarith
  have hleft_even : Even (4 * m ^ 3) := by
    use 2 * m ^ 3
    ring
  have hright_odd : Odd (2 * k ^ 2 + 2 * k + 1) := by
    use k ^ 2 + k
    ring
  rw [hhalf] at hleft_even
  exact (Int.not_even_iff_odd.mpr hright_odd) hleft_even

/-- If an integer cube is one more than a square, then the cube root is odd. -/
-- Repository use: Cox's Gaussian-integer auxiliary equation uses this together
-- with `Int.even_of_cube_eq_sq_add_one` to control common divisors of
-- `z ± √-1`.
theorem Int.odd_of_cube_eq_sq_add_one {n z : ℤ} (h : n ^ 3 = z ^ 2 + 1) :
    Odd n := by
  obtain ⟨k, hk⟩ := Int.even_of_cube_eq_sq_add_one h
  subst z
  exact (Int.odd_pow' (m := n) (n := 3) (by norm_num)).mp (by
    rw [h]
    use 2 * k ^ 2
    ring)

/-- If an integer cube is one more than twice a square, then the cube root is odd. -/
-- Repository use: Cox's `ℤ[√-2]` auxiliary equation uses this to control common
-- divisors of `1 ± z√-2`.
theorem Int.odd_of_cube_eq_two_mul_sq_add_one {n z : ℤ}
    (h : n ^ 3 = 2 * z ^ 2 + 1) :
    Odd n := by
  by_contra hn_odd
  have hn_even : Even n := Int.not_odd_iff_even.mp hn_odd
  have hn3_even : Even (n ^ 3) := (Int.even_pow' (m := n) (n := 3) (by norm_num)).mpr hn_even
  rw [h] at hn3_even
  exact (Int.not_even_iff_odd.mpr ⟨z ^ 2, rfl⟩) hn3_even
