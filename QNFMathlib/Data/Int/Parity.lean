/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Int.Even
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Linarith
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
