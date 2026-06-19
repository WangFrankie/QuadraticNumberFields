/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.Ring

/-!
# Coprime Lemmas

Material destined for mathlib.
-/

namespace IsCoprime

variable {R : Type*} [CommSemiring R] {a b : R}

/-- If `a` is coprime to `2 * b`, then it is coprime to `4 * b`. -/
-- Repository use: Heegner's Diophantine reduction uses this after rewriting
-- `X ^ 3 + 1` as twice a square.
theorem four_mul_right_of_two_mul_right (h : IsCoprime a ((2 : R) * b)) :
    IsCoprime a ((4 : R) * b) := by
  have hparts := IsCoprime.mul_right_iff.mp h
  have hcop2 : IsCoprime a (2 : R) := hparts.1
  convert hcop2.mul_right h using 1
  ring

variable {S : Type*} [CommSemiring S] [GCDMonoid S] {x y z : S}

/-- If two coprime factors multiply to a `k`-th power, then the left factor is
associated to a `k`-th power. -/
-- Repository use: Cox's Gaussian-integer auxiliary equation applies this to
-- the coprime factors `z + √-1` and `z - √-1`.
theorem exists_associated_pow_left_of_mul_eq_pow (hcop : IsCoprime x y)
    {k : ℕ} (h : x * y = z ^ k) :
    ∃ w, Associated (w ^ k) x := by
  have hgcd : IsUnit (gcd x y) :=
    hcop.isUnit_of_dvd' (GCDMonoid.gcd_dvd_left x y) (GCDMonoid.gcd_dvd_right x y)
  exact exists_associated_pow_of_mul_eq_pow hgcd h

end IsCoprime

namespace Int

/-- A common divisor of an odd cube and `4` is an integer unit. -/
-- Repository use: Cox's Gaussian-integer auxiliary equation applies this to
-- the norm of a common divisor of `z + √-1` and `z - √-1`.
theorem isUnit_of_dvd_odd_cube_and_dvd_four {n m : ℤ} (hn : Odd n)
    (hmn : m ∣ n ^ 3) (hm4 : m ∣ (4 : ℤ)) :
    IsUnit m := by
  have hn3odd : Odd (n ^ 3) := by
    exact (Int.odd_pow' (m := n) (n := 3) (by norm_num)).mpr hn
  have hcop2 : IsCoprime (n ^ 3) (2 : ℤ) := by
    exact Int.isCoprime_two_right.mpr hn3odd
  have hcop4 : IsCoprime (n ^ 3) (4 : ℤ) := by
    simpa [show (4 : ℤ) = 2 ^ 2 by norm_num] using (hcop2.pow_right (n := 2))
  have hcop_nm : IsCoprime (n ^ 3) m := by
    exact IsCoprime.of_isCoprime_of_dvd_right hcop4 hm4
  exact hcop_nm.symm.isUnit_of_dvd hmn

end Int
