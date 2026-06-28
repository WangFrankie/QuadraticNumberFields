/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Int.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.FieldSimp
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
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    nlinarith

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

/-- An integer square plus one is coprime to `3`. -/
-- Repository use: Cox's Heegner Diophantine reduction uses this after reducing
-- the common divisor of `W ^ 2 + 1` and `W ^ 4 - W ^ 2 + 1` to a divisor of
-- `3`.
theorem isCoprime_sq_add_one_three (W : ℤ) : IsCoprime (W ^ 2 + 1) (3 : ℤ) := by
  have hcases : W % 3 = 0 ∨ W % 3 = 1 ∨ W % 3 = 2 := by omega
  rcases hcases with hW | hW | hW
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q := by
      omega
    refine ⟨1, -3 * q ^ 2, ?_⟩
    rw [hWdecomp]
    ring
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q + 1 := by
      omega
    refine ⟨-1, 3 * q ^ 2 + 2 * q + 1, ?_⟩
    rw [hWdecomp]
    ring
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q + 2 := by
      omega
    refine ⟨-1, 3 * q ^ 2 + 4 * q + 2, ?_⟩
    rw [hWdecomp]
    ring

/-- The two nontrivial factors in `W ^ 6 + 1` are coprime. -/
-- Repository use: Cox's Heegner Diophantine reduction factors
-- `W ^ 6 + 1` as `(W ^ 2 + 1) * (W ^ 4 - W ^ 2 + 1)`.
theorem isCoprime_sq_add_one_quartic_sub_sq_add_one (W : ℤ) :
    IsCoprime (W ^ 2 + 1) (W ^ 4 - W ^ 2 + 1) := by
  have hcop3 : IsCoprime (W ^ 2 + 1) (3 : ℤ) := Int.isCoprime_sq_add_one_three W
  convert IsCoprime.add_mul_right_right hcop3 (W ^ 2 - 2) using 1
  ring

/-- In the equation `W ^ 6 + 1 = 2 * Z ^ 2`, `W ^ 2 + 1` cannot itself be
a square. -/
-- Repository use: Cox's Heegner Diophantine reduction uses this to rule out
-- one of the coprime factorization branches.
theorem not_exists_sq_add_one_eq_sq_of_sixth_add_one_eq_two_mul_sq
    {W Z : ℤ} (h : W ^ 6 + 1 = 2 * Z ^ 2) :
    ¬ ∃ U : ℤ, W ^ 2 + 1 = U ^ 2 := by
  rintro ⟨U, hU⟩
  have hW0 : W = 0 := Int.eq_zero_of_sq_add_one_eq_sq hU
  subst W
  have hone : (1 : ℤ) = 2 * Z ^ 2 := by simpa using h
  have hone_even : Even (1 : ℤ) := by
    rw [hone]
    exact even_two_mul (Z ^ 2)
  exact Int.not_even_one hone_even

/-- If `W ^ 4 - W ^ 2 + 1` is a square, then `W` is `0`, `1`, or `-1`. -/
-- Repository use: Cox's Heegner Diophantine reduction applies this to the
-- second factor in `W ^ 6 + 1`.
theorem eq_zero_or_eq_one_or_neg_one_of_quartic_sub_sq_add_one_eq_sq
    {W K : ℤ} (h : W ^ 4 - W ^ 2 + 1 = K ^ 2) :
    W = 0 ∨ W = 1 ∨ W = -1 := by
  have hquad : (W ^ 2) ^ 2 - W ^ 2 + 1 = K ^ 2 := by
    convert h using 1
    ring
  rcases Int.eq_zero_or_eq_one_of_nonneg_of_sq_sub_self_add_one_eq_sq
      (sq_nonneg W) hquad with hWsq | hWsq
  · left
    nlinarith [sq_nonneg W]
  · right
    have hmul : W * W = 1 := by
      simpa [pow_two] using hWsq
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1

/-- If `9 * A` is a square, then `A` is a square. -/
-- Repository use: Cox's Exercise 12.29 divides a square identity by `3 ^ 2`
-- after Exercise 12.28 shows that one factor is divisible by `3`.
theorem exists_eq_sq_of_nine_mul_eq_sq {A z : ℤ} (h : 9 * A = z ^ 2) :
    ∃ w : ℤ, A = w ^ 2 := by
  have hzsq : (3 : ℤ) ∣ z ^ 2 := by
    rw [← h]
    exact ⟨3 * A, by ring⟩
  obtain ⟨w, hw⟩ := Int.Prime.dvd_pow' Nat.prime_three hzsq
  refine ⟨w, ?_⟩
  subst z
  ring_nf at h ⊢
  nlinarith

/-- If a nonzero square factor times `A` is a square, then `A` is a square. -/
theorem exists_eq_sq_of_sq_mul_eq_sq {A d z : ℤ} (hd : d ≠ 0)
    (h : d ^ 2 * A = z ^ 2) :
    ∃ w : ℤ, A = w ^ 2 := by
  have hrat : (A : ℚ) = ((z : ℚ) / d) ^ 2 := by
    have hcast : ((d : ℚ) ^ 2) * A = (z : ℚ) ^ 2 := by
      exact_mod_cast h
    have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    field_simp [hdq] at hcast ⊢
    nlinarith
  have hsquare_rat : IsSquare (A : ℚ) := by
    rw [isSquare_iff_exists_sq]
    exact ⟨(z : ℚ) / d, hrat⟩
  rw [Rat.isSquare_intCast_iff] at hsquare_rat
  rw [isSquare_iff_exists_sq] at hsquare_rat
  obtain ⟨w, hw⟩ := hsquare_rat
  exact ⟨w, by exact_mod_cast hw⟩

/-- If an integer is not divisible by `3`, then it is coprime to `3`. -/
theorem isCoprime_three_of_not_dvd {n : ℤ} (h : ¬ (3 : ℤ) ∣ n) :
    IsCoprime n (3 : ℤ) := by
  rw [Int.isCoprime_iff_nat_coprime]
  have hnat : ¬ 3 ∣ n.natAbs := by
    intro hd
    exact h (Int.natCast_dvd.mpr hd)
  simpa using ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnat).symm

/-- If three positive pairwise coprime integers have square product, then each
factor is a square. -/
theorem exists_sq_factors_of_pos_pairwise_isCoprime_mul_mul_eq_sq
    {a b d z : ℤ} (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hab : IsCoprime a b) (had : IsCoprime a d) (hbd : IsCoprime b d)
    (hprod : a * b * d = z ^ 2) :
    (∃ u : ℤ, a = u ^ 2) ∧ (∃ v : ℤ, b = v ^ 2) ∧ ∃ w : ℤ, d = w ^ 2 := by
  have ha_sq : ∃ u : ℤ, a = u ^ 2 := by
    have hacop : IsCoprime a (b * d) := IsCoprime.mul_right hab had
    have hprod_a : a * (b * d) = z ^ 2 := by
      nlinarith [hprod]
    obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hacop hprod_a
    · exact ⟨u, hu⟩
    · have : ¬ 0 < a := by
        rw [hu]
        nlinarith [sq_nonneg u]
      contradiction
  have hb_sq : ∃ v : ℤ, b = v ^ 2 := by
    have hbcop : IsCoprime b (a * d) := IsCoprime.mul_right hab.symm hbd
    have hprod_b : b * (a * d) = z ^ 2 := by
      nlinarith [hprod]
    obtain ⟨v, hv | hv⟩ := Int.sq_of_isCoprime hbcop hprod_b
    · exact ⟨v, hv⟩
    · have : ¬ 0 < b := by
        rw [hv]
        nlinarith [sq_nonneg v]
      contradiction
  have hd_sq : ∃ w : ℤ, d = w ^ 2 := by
    have hdcop : IsCoprime d (a * b) := IsCoprime.mul_right had.symm hbd.symm
    have hprod_d : d * (a * b) = z ^ 2 := by
      nlinarith [hprod]
    obtain ⟨w, hw | hw⟩ := Int.sq_of_isCoprime hdcop hprod_d
    · exact ⟨w, hw⟩
    · have : ¬ 0 < d := by
        rw [hw]
        nlinarith [sq_nonneg w]
      contradiction
  exact ⟨ha_sq, hb_sq, hd_sq⟩

/-- A natural prime is not a unit after coercion to `ℤ`. -/
theorem not_isUnit_natCast_of_prime {p : ℕ} (hp : Nat.Prime p) : ¬ IsUnit (p : ℤ) := by
  intro hunit
  have hp_unit_nat : IsUnit p := Int.ofNat_isUnit.mp hunit
  have hp_eq_one : p = 1 := by
    simpa using hp_unit_nat
  have hp_two : 2 ≤ p := hp.two_le
  omega

/-- If two positive coprime integers multiply to twice a square, then one is a
square and the other is twice a square. -/
-- Repository use: Cox's Heegner Diophantine reduction applies this to the
-- factorization `(W ^ 2 + 1) * (W ^ 4 - W ^ 2 + 1) = 2 * Z ^ 2`.
theorem sq_and_two_mul_sq_or_two_mul_sq_and_sq_of_isCoprime_mul_eq_two_mul_sq
    {a b z : ℤ} (ha : 0 < a) (hb : 0 < b) (hcop : IsCoprime a b)
    (hprod : a * b = 2 * z ^ 2) :
    ((∃ u : ℤ, a = u ^ 2) ∧ ∃ v : ℤ, b = 2 * v ^ 2) ∨
      ((∃ u : ℤ, a = 2 * u ^ 2) ∧ ∃ v : ℤ, b = v ^ 2) := by
  by_cases haeven : Even a
  · right
    obtain ⟨a0, ha0⟩ := haeven
    have ha0pos : 0 < a0 := by
      subst a
      nlinarith
    have hprod0 : a0 * b = z ^ 2 := by
      subst a
      nlinarith
    have hcop0 : IsCoprime a0 b := by
      refine IsCoprime.of_isCoprime_of_dvd_left hcop ?_
      subst a
      exact ⟨2, by ring⟩
    constructor
    · obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hcop0 hprod0
      · exact ⟨u, by subst a; rw [hu]; ring⟩
      · have : ¬ 0 < a0 := by
          rw [hu]
          nlinarith [sq_nonneg u]
        contradiction
    · obtain ⟨v, hv | hv⟩ := Int.sq_of_isCoprime hcop0.symm
        (by simpa [mul_comm] using hprod0)
      · exact ⟨v, hv⟩
      · have : ¬ 0 < b := by
          rw [hv]
          nlinarith [sq_nonneg v]
        contradiction
  · left
    have haodd : Odd a := Int.not_even_iff_odd.mp haeven
    rcases Int.even_or_odd b with hbeven | hbodd
    · obtain ⟨b0, hb0⟩ := hbeven
      have hb0pos : 0 < b0 := by
        subst b
        nlinarith
      have hprod0 : a * b0 = z ^ 2 := by
        subst b
        nlinarith
      have hcop0 : IsCoprime a b0 := by
        refine IsCoprime.of_isCoprime_of_dvd_right hcop ?_
        subst b
        exact ⟨2, by ring⟩
      constructor
      · obtain ⟨u, hu | hu⟩ := Int.sq_of_isCoprime hcop0 hprod0
        · exact ⟨u, hu⟩
        · have : ¬ 0 < a := by
            rw [hu]
            nlinarith [sq_nonneg u]
          contradiction
      · obtain ⟨v, hv | hv⟩ := Int.sq_of_isCoprime hcop0.symm
          (by simpa [mul_comm] using hprod0)
        · exact ⟨v, by subst b; rw [hv]; ring⟩
        · have : ¬ 0 < b0 := by
            rw [hv]
            nlinarith [sq_nonneg v]
          contradiction
    · exfalso
      have hprod_odd : Odd (a * b) := Int.odd_mul.mpr ⟨haodd, hbodd⟩
      have hprod_even : Even (a * b) := by
        rw [hprod]
        exact even_two_mul (z ^ 2)
      exact (Int.not_even_iff_odd.mpr hprod_odd) hprod_even

/-- Integer solutions of `W ^ 6 + 1 = 2 * Z ^ 2` have `W = ±1`. -/
-- Repository use: this is Cox's Exercise 12.27(b), used in the Heegner
-- Diophantine reduction after the `X = W ^ 2` square branch is isolated.
theorem eq_one_or_neg_one_of_sixth_add_one_eq_two_mul_sq
    {W Z : ℤ} (h : W ^ 6 + 1 = 2 * Z ^ 2) :
    W = 1 ∨ W = -1 := by
  have ha_pos : 0 < W ^ 2 + 1 := by
    nlinarith [sq_nonneg W]
  have hb_pos : 0 < W ^ 4 - W ^ 2 + 1 := by
    have hb_expr : W ^ 4 - W ^ 2 + 1 = (W ^ 2 - 1) ^ 2 + W ^ 2 := by ring
    rw [hb_expr]
    nlinarith [sq_nonneg (W ^ 2 - 1), sq_nonneg W]
  have hfactor : (W ^ 2 + 1) * (W ^ 4 - W ^ 2 + 1) = 2 * Z ^ 2 := by
    rw [← h]
    ring
  obtain hsquare | htwice :=
    Int.sq_and_two_mul_sq_or_two_mul_sq_and_sq_of_isCoprime_mul_eq_two_mul_sq
      ha_pos hb_pos (Int.isCoprime_sq_add_one_quartic_sub_sq_add_one W) hfactor
  · rcases hsquare.1 with ⟨U, hU⟩
    exact False.elim
      ((Int.not_exists_sq_add_one_eq_sq_of_sixth_add_one_eq_two_mul_sq h) ⟨U, hU⟩)
  · rcases htwice.2 with ⟨K, hK⟩
    rcases Int.eq_zero_or_eq_one_or_neg_one_of_quartic_sub_sq_add_one_eq_sq hK with
      hW | hW | hW
    · subst W
      have hone : (1 : ℤ) = 2 * Z ^ 2 := by simpa using h
      have hone_even : Even (1 : ℤ) := by
        rw [hone]
        exact even_two_mul (Z ^ 2)
      exact False.elim (Int.not_even_one hone_even)
    · exact Or.inl hW
    · exact Or.inr hW

end Int
