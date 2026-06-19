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
  have hb_even : Even (b + 1) := by
    simpa using hb.add_odd (show Odd (1 : ℤ) by exact odd_one)
  exact Int.two_mul_ediv_two_of_even hb_even.neg

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
