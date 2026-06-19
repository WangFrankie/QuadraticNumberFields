/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integer Square Helpers

Material destined for mathlib.
-/

namespace Int

/-- If two integer squares differ by `1`, and the smaller square is written
as `W ^ 2`, then `W = 0`. -/
-- Repository use: Cox's Heegner Diophantine reduction uses this to rule out
-- the case where `W ^ 2 + 1` is itself a square.
theorem eq_zero_of_sq_add_one_eq_sq {W U : ℤ} (h : W ^ 2 + 1 = U ^ 2) :
    W = 0 := by
  have hmul : (U - W) * (U + W) = 1 := by
    nlinarith
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · nlinarith
  · nlinarith

/-- If `n ≥ 0` and `n ^ 2 - n + 1` is a square, then `n` is `0` or `1`. -/
-- Repository use: Cox's Heegner Diophantine reduction applies this to
-- `n = W ^ 2` in the `W ^ 6 + 1 = 2 * Z ^ 2` branch.
theorem eq_zero_or_eq_one_of_nonneg_of_sq_sub_self_add_one_eq_sq
    {n k : ℤ} (hn : 0 ≤ n) (h : n ^ 2 - n + 1 = k ^ 2) :
    n = 0 ∨ n = 1 := by
  by_cases hn0 : n = 0
  · exact Or.inl hn0
  by_cases hn1 : n = 1
  · exact Or.inr hn1
  have hn2 : 2 ≤ n := by omega
  have hupper : k ^ 2 < n ^ 2 := by
    nlinarith
  have habs_lt : |k| < n := by
    have htmp := sq_lt_sq.mp hupper
    simpa [abs_of_nonneg hn] using htmp
  have habs_le : |k| ≤ n - 1 := by omega
  have hn1_nonneg : 0 ≤ n - 1 := by omega
  have hsq_le_abs : |k| ^ 2 ≤ (n - 1) ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hn1_nonneg] using habs_le)
  have hsq_le : k ^ 2 ≤ (n - 1) ^ 2 := by
    simpa [sq_abs] using hsq_le_abs
  have hlower : (n - 1) ^ 2 < k ^ 2 := by
    nlinarith
  omega

end Int
