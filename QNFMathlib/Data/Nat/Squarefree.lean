/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Nat.Prime.Defs
import QNFMathlib.Algebra.Squarefree.Basic

/-!
# Squarefree Natural Number Helpers

Material destined for mathlib.
-/

namespace Nat

/-- An odd squarefree composite natural number has a prime divisor `q` with
`4 * q < n + 1`. -/
theorem exists_prime_dvd_and_four_mul_lt_succ_of_squarefree_of_odd_of_not_prime
    {n : ℕ} (hsq : Squarefree n) (hodd : Odd n) (hgt : 1 < n) (hnprime : ¬ n.Prime) :
    ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ 4 * q < n + 1 := by
  let q := Nat.minFac n
  have hqprime : q.Prime := Nat.minFac_prime hgt.ne'
  have hqdvd : q ∣ n := Nat.minFac_dvd n
  have hn2 : 2 ≤ n := by omega
  have hq_lt_n : q < n := (Nat.not_prime_iff_minFac_lt hn2).mp hnprime
  have hq_ne_two : q ≠ 2 := by
    intro hq2
    have h2dvd : 2 ∣ n := by simpa [q, hq2] using hqdvd
    exact hodd.not_two_dvd_nat h2dvd
  have hq_ge_three : 3 ≤ q := by
    have hq2le : 2 ≤ q := hqprime.two_le
    omega
  let r := n / q
  have hn_eq : n = q * r := by
    dsimp [r]
    exact (Nat.mul_div_cancel' hqdvd).symm
  have hr_pos : 0 < r := by
    dsimp [r]
    exact Nat.div_pos (Nat.le_of_dvd (by omega) hqdvd) hqprime.pos
  have hr_ne_one : r ≠ 1 := by
    intro hr1
    have hn_eq_q : n = q := by simp [hn_eq, hr1]
    exact hq_lt_n.ne (by simp [hn_eq_q])
  have hq_not_dvd_r : ¬ q ∣ r := by
    intro hqr
    have hq2dvd_n : q * q ∣ n := by
      rw [hn_eq]
      exact Nat.mul_dvd_mul_left q hqr
    exact Squarefree.not_mul_self_dvd_of_not_isUnit hsq
      (fun hu => hqprime.ne_one (isUnit_iff_eq_one.mp hu)) hq2dvd_n
  refine ⟨q, hqprime, hqdvd, ?_⟩
  by_cases hq3 : q = 3
  · have hrodd : Odd r := by
      rw [hn_eq] at hodd
      exact Nat.Odd.of_mul_right hodd
    have hr_ne_three : r ≠ 3 := by
      intro hr3
      exact hq_not_dvd_r (by simp [hq3, hr3])
    have hr5 : 5 ≤ r := by
      rcases hrodd with ⟨t, ht⟩
      omega
    rw [hn_eq, hq3]
    nlinarith
  · have hqr : q ≤ r := by
      by_contra hlt
      have hrlt : r < q := by omega
      rcases Nat.exists_prime_and_dvd hr_ne_one with ⟨s, hs, hsr⟩
      have hsq_le_r : s ≤ r := Nat.le_of_dvd hr_pos hsr
      have hsn : s ∣ n := by
        rw [hn_eq]
        exact hsr.trans (dvd_mul_left r q)
      have hq_le_s : q ≤ s := Nat.minFac_le_of_dvd hs.two_le hsn
      omega
    have hq_ne_four : q ≠ 4 := by
      exact fun hq4 => (by decide : ¬ Nat.Prime 4) (by simpa [hq4] using hqprime)
    have hq5 : 5 ≤ q := by omega
    rw [hn_eq]
    nlinarith

end Nat
