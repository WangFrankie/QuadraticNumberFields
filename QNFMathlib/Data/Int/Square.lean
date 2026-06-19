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

/-- An integer square plus one is coprime to `3`. -/
-- Repository use: Cox's Heegner Diophantine reduction uses this after reducing
-- the common divisor of `W ^ 2 + 1` and `W ^ 4 - W ^ 2 + 1` to a divisor of
-- `3`.
theorem isCoprime_sq_add_one_three (W : ℤ) : IsCoprime (W ^ 2 + 1) (3 : ℤ) := by
  have hcases : W % 3 = 0 ∨ W % 3 = 1 ∨ W % 3 = 2 := by omega
  rcases hcases with hW | hW | hW
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q := by
      calc
        W = W % 3 + 3 * (W / 3) := (Int.emod_add_mul_ediv W 3).symm
        _ = 3 * q := by rw [hW]; simp [q]
    refine ⟨1, -3 * q ^ 2, ?_⟩
    rw [hWdecomp]
    ring
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q + 1 := by
      calc
        W = W % 3 + 3 * (W / 3) := (Int.emod_add_mul_ediv W 3).symm
        _ = 3 * q + 1 := by rw [hW]; simp [q]; ring
    refine ⟨-1, 3 * q ^ 2 + 2 * q + 1, ?_⟩
    rw [hWdecomp]
    ring
  · let q : ℤ := W / 3
    have hWdecomp : W = 3 * q + 2 := by
      calc
        W = W % 3 + 3 * (W / 3) := (Int.emod_add_mul_ediv W 3).symm
        _ = 3 * q + 2 := by rw [hW]; simp [q]; ring
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

/-- The first Cox-Euler quadratic factor is coprime to `b` when `b` and `c`
are coprime. -/
theorem isCoprime_left_quadratic_factor {b c : ℤ} (hcop : IsCoprime b c) :
    IsCoprime b (c ^ 2 - 3 * b * c + 3 * b ^ 2) := by
  have hbc2 : IsCoprime b (c ^ 2) := hcop.pow_right
  convert IsCoprime.add_mul_left_right hbc2 (-3 * c + 3 * b) using 1
  ring

/-- The first Cox-Euler quadratic factor is coprime to `c` when `b` and `c`
are coprime and `3 ∤ c`. -/
theorem isCoprime_right_quadratic_factor {b c : ℤ} (hcop : IsCoprime b c)
    (h3c : ¬ (3 : ℤ) ∣ c) :
    IsCoprime c (c ^ 2 - 3 * b * c + 3 * b ^ 2) := by
  have hc3 : IsCoprime c (3 : ℤ) := isCoprime_three_of_not_dvd h3c
  have hcb2 : IsCoprime c (b ^ 2) := hcop.symm.pow_right
  have hc3b2 : IsCoprime c (3 * b ^ 2) := IsCoprime.mul_right hc3 hcb2
  convert IsCoprime.add_mul_left_right hc3b2 (c - 3 * b) using 1
  ring

/-- The Cox-Euler quadratic factor `c² - 3bc + 3b²` is positive for positive
`b`. -/
theorem quadratic_factor_pos {b c : ℤ} (hb : 0 < b) :
    0 < c ^ 2 - 3 * b * c + 3 * b ^ 2 := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hb_sq_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hbne
  have hs : 0 ≤ (2 * c - 3 * b) ^ 2 := sq_nonneg (2 * c - 3 * b)
  have hident : 4 * (c ^ 2 - 3 * b * c + 3 * b ^ 2) =
      (2 * c - 3 * b) ^ 2 + 3 * b ^ 2 := by
    ring
  nlinarith

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

/-- A positive rational number represented as `a / b` has coprime positive
integer numerator and denominator. -/
theorem exists_pos_isCoprime_mul_eq_mul_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ IsCoprime m n ∧ m * b = n * a := by
  let r : ℚ := (a : ℚ) / b
  refine ⟨r.num, (r.den : ℤ), ?_, ?_, ?_, ?_⟩
  · have hrpos : 0 < r := by
      dsimp [r]
      exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
    have hnum_nonneg : 0 ≤ r.num := Rat.num_nonneg.mpr hrpos.le
    have hnum_ne : r.num ≠ 0 := Rat.num_ne_zero.mpr (ne_of_gt hrpos)
    omega
  · exact_mod_cast r.den_pos
  · rw [Int.isCoprime_iff_nat_coprime]
    simpa using r.reduced
  · have hr : r = Rat.divInt a b := by
      dsimp [r]
      exact (Rat.divInt_eq_div a b).symm
    obtain ⟨t, ha_t, hb_t⟩ := Rat.num_den_mk hb.ne' hr
    rw [ha_t, hb_t]
    ring

/-- A positive integer pair has a positive coprime reduction. -/
theorem exists_pos_isCoprime_eq_mul_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
    ∃ d m n : ℤ, 0 < d ∧ 0 < m ∧ 0 < n ∧ IsCoprime m n ∧
      a = d * m ∧ b = d * n := by
  let r : ℚ := (a : ℚ) / b
  have hrpos : 0 < r := by
    dsimp [r]
    exact div_pos (by exact_mod_cast ha) (by exact_mod_cast hb)
  have hmpos : 0 < r.num := by
    have hnum_nonneg : 0 ≤ r.num := Rat.num_nonneg.mpr hrpos.le
    have hnum_ne : r.num ≠ 0 := Rat.num_ne_zero.mpr (ne_of_gt hrpos)
    omega
  have hnpos : 0 < (r.den : ℤ) := by exact_mod_cast r.den_pos
  have hr : r = Rat.divInt a b := by
    dsimp [r]
    exact (Rat.divInt_eq_div a b).symm
  obtain ⟨d, ha_d, hb_d⟩ := Rat.num_den_mk hb.ne' hr
  have hdpos : 0 < d := by
    rw [ha_d] at ha
    nlinarith
  refine ⟨d, r.num, (r.den : ℤ), hdpos, hmpos, hnpos, ?_, ha_d, hb_d⟩
  rw [Int.isCoprime_iff_nat_coprime]
  simpa using r.reduced

/-- Cox-Euler parameterization step: from
`k² = c² - 3bc + 3b²`, choose coprime positive `m,n` representing
`(k+c)/b` and obtain the linear identity used in the descent. -/
theorem exists_pos_isCoprime_quadratic_param
    {b c k : ℤ} (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hkq : c ^ 2 - 3 * b * c + 3 * b ^ 2 = k ^ 2) :
    ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ IsCoprime m n ∧
      m * b = n * (k + c) ∧
      (3 * n ^ 2 - m ^ 2) * b = (3 * n ^ 2 - 2 * m * n) * c := by
  obtain ⟨m, n, hmpos, hnpos, hmn_cop, hmn⟩ :=
    exists_pos_isCoprime_mul_eq_mul_of_pos (a := k + c) (b := b) (by nlinarith) hb
  refine ⟨m, n, hmpos, hnpos, hmn_cop, hmn, ?_⟩
  have hsq : (m * b - n * c) ^ 2 = (n * k) ^ 2 := by
    have hlin : m * b - n * c = n * k := by
      nlinarith
    rw [hlin]
  nlinarith [hsq, hkq, hb]

/-- In the Cox-Euler parameterization, the numerator `2mn - 3n²` is positive. -/
theorem two_mul_param_sub_three_mul_den_pos
    {b c k m n : ℤ} (hb : 0 < b) (hk : 0 < k)
    (hn : 0 < n) (hmul : m * b = n * (k + c))
    (hkq : c ^ 2 - 3 * b * c + 3 * b ^ 2 = k ^ 2) :
    0 < 2 * m - 3 * n := by
  have hbne : b ≠ 0 := ne_of_gt hb
  have hb_sq_pos : 0 < b ^ 2 := sq_pos_of_ne_zero hbne
  have hsq : (3 * b - 2 * c) ^ 2 < (2 * k) ^ 2 := by
    nlinarith
  have habs : |3 * b - 2 * c| < 2 * k := by
    have htmp := sq_lt_sq.mp hsq
    have hk2 : 0 < 2 * k := by nlinarith
    simpa [abs_of_pos hk2] using htmp
  have hlin : 3 * b - 2 * c < 2 * k := by
    have hle : 3 * b - 2 * c ≤ |3 * b - 2 * c| := le_abs_self _
    nlinarith
  have hpos_rhs : 0 < n * (2 * k + 2 * c - 3 * b) := by
    nlinarith
  have hident : (2 * m - 3 * n) * b = n * (2 * k + 2 * c - 3 * b) := by
    nlinarith
  nlinarith

/-- In the Cox-Euler parameterization, both denominator factors in the descent
fraction are positive. -/
theorem quadratic_param_num_den_pos
    {b c k m n : ℤ} (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hn : 0 < n) (hmul : m * b = n * (k + c))
    (hkq : c ^ 2 - 3 * b * c + 3 * b ^ 2 = k ^ 2)
    (hkey : (3 * n ^ 2 - m ^ 2) * b = (3 * n ^ 2 - 2 * m * n) * c) :
    0 < 2 * m * n - 3 * n ^ 2 ∧ 0 < m ^ 2 - 3 * n ^ 2 := by
  have h2m3n : 0 < 2 * m - 3 * n :=
    two_mul_param_sub_three_mul_den_pos hb hk hn hmul hkq
  have hnum : 0 < 2 * m * n - 3 * n ^ 2 := by
    nlinarith [mul_pos h2m3n hn]
  have hkey' : (m ^ 2 - 3 * n ^ 2) * b = (2 * m * n - 3 * n ^ 2) * c := by
    nlinarith
  have hden : 0 < m ^ 2 - 3 * n ^ 2 := by
    nlinarith [mul_pos hnum hc]
  exact ⟨hnum, hden⟩

/-- A natural prime is not a unit after coercion to `ℤ`. -/
theorem not_isUnit_natCast_of_prime {p : ℕ} (hp : Nat.Prime p) : ¬ IsUnit (p : ℤ) := by
  intro hunit
  have hp_unit_nat : IsUnit p := Int.ofNat_isUnit.mp hunit
  have hp_eq_one : p = 1 := by
    simpa using hp_unit_nat
  have hp_two : 2 ≤ p := hp.two_le
  omega

/-- Two positive coprime integer fractions that are equal by cross
multiplication have equal numerators and denominators. -/
theorem eq_of_pos_isCoprime_mul_eq_mul
    {a b c d : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hab : IsCoprime a b) (hcd : IsCoprime c d) (h : a * d = c * b) :
    a = c ∧ b = d := by
  have hrat : (a : ℚ) / b = (c : ℚ) / d := by
    rw [div_eq_div_iff]
    · exact_mod_cast h
    · exact_mod_cast hb.ne'
    · exact_mod_cast hd.ne'
  have hab_nat : Nat.Coprime a.natAbs b.natAbs := Int.isCoprime_iff_nat_coprime.mp hab
  have hcd_nat : Nat.Coprime c.natAbs d.natAbs := Int.isCoprime_iff_nat_coprime.mp hcd
  exact Rat.div_int_inj hb hd hab_nat hcd_nat hrat

/-- If `m,n` are coprime and `3 ∤ m`, then the two descent factors in Cox's
Euler parameterization are coprime. -/
theorem isCoprime_param_num_den_of_not_three_dvd {m n : ℤ}
    (hmn : IsCoprime m n) (h3m : ¬ (3 : ℤ) ∣ m) :
    IsCoprime (2 * m * n - 3 * n ^ 2) (m ^ 2 - 3 * n ^ 2) := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  obtain ⟨p, hp, hpA_nat, hpD_nat⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpA : (p : ℤ) ∣ 2 * m * n - 3 * n ^ 2 := Int.natCast_dvd.mpr hpA_nat
  have hpD : (p : ℤ) ∣ m ^ 2 - 3 * n ^ 2 := Int.natCast_dvd.mpr hpD_nat
  have hnot_unit : ¬ IsUnit (p : ℤ) := not_isUnit_natCast_of_prime hp
  by_cases hpm : (p : ℤ) ∣ m
  · have hpm2 : (p : ℤ) ∣ m ^ 2 := dvd_pow hpm (by decide)
    have hp3n2 : (p : ℤ) ∣ 3 * n ^ 2 := by
      have htmp : (p : ℤ) ∣ m ^ 2 - (m ^ 2 - 3 * n ^ 2) := dvd_sub hpm2 hpD
      convert htmp using 1
      ring
    rcases Int.Prime.dvd_mul' hp hp3n2 with hp3 | hpn2
    · have hp3_nat : p ∣ 3 := Int.natCast_dvd_natCast.mp hp3
      have hp_eq3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3_nat
      exact h3m (by simpa [hp_eq3] using hpm)
    · have hpn : (p : ℤ) ∣ n := Int.Prime.dvd_pow' hp hpn2
      exact hnot_unit (hmn.isUnit_of_dvd' hpm hpn)
  · have hp_diff : (p : ℤ) ∣ m * (m - 2 * n) := by
      have htmp : (p : ℤ) ∣ (m ^ 2 - 3 * n ^ 2) - (2 * m * n - 3 * n ^ 2) :=
        dvd_sub hpD hpA
      convert htmp using 1
      ring
    rcases Int.Prime.dvd_mul' hp hp_diff with hpm' | hpm2n
    · exact hpm hpm'
    · have hpA_minus : (p : ℤ) ∣ (2 * m * n - 3 * n ^ 2) - n ^ 2 := by
        have htmp : (p : ℤ) ∣ 2 * n * (m - 2 * n) := by
          obtain ⟨t, ht⟩ := hpm2n
          refine ⟨2 * n * t, ?_⟩
          rw [ht]
          ring
        convert htmp using 1
        ring
      have hpn2 : (p : ℤ) ∣ n ^ 2 := by
        have htmp : (p : ℤ) ∣ (2 * m * n - 3 * n ^ 2) -
            ((2 * m * n - 3 * n ^ 2) - n ^ 2) := dvd_sub hpA hpA_minus
        convert htmp using 1
        ring
      have hpn : (p : ℤ) ∣ n := Int.Prime.dvd_pow' hp hpn2
      have hpm_from_n : (p : ℤ) ∣ m := by
        have hp2n : (p : ℤ) ∣ 2 * n := by
          obtain ⟨t, ht⟩ := hpn
          refine ⟨2 * t, ?_⟩
          rw [ht]
          ring
        have htmp : (p : ℤ) ∣ (m - 2 * n) + 2 * n := dvd_add hpm2n hp2n
        convert htmp using 1
        ring
      exact hpm hpm_from_n

/-- If `r,n` are coprime and `3 ∤ n`, then the two descent factors in the
`3 ∣ m` Cox-Euler branch are coprime. -/
theorem isCoprime_three_dvd_param_num_den {r n : ℤ}
    (hrn : IsCoprime r n) (h3n : ¬ (3 : ℤ) ∣ n) :
    IsCoprime (2 * r * n - n ^ 2) (3 * r ^ 2 - n ^ 2) := by
  rw [Int.isCoprime_iff_nat_coprime]
  by_contra hnot
  obtain ⟨p, hp, hpA_nat, hpD_nat⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot
  have hpA : (p : ℤ) ∣ 2 * r * n - n ^ 2 := Int.natCast_dvd.mpr hpA_nat
  have hpD : (p : ℤ) ∣ 3 * r ^ 2 - n ^ 2 := Int.natCast_dvd.mpr hpD_nat
  have hnot_unit : ¬ IsUnit (p : ℤ) := not_isUnit_natCast_of_prime hp
  by_cases hpr : (p : ℤ) ∣ r
  · have hpr2 : (p : ℤ) ∣ r ^ 2 := dvd_pow hpr (by decide)
    have hpn2 : (p : ℤ) ∣ n ^ 2 := by
      have hp3r2 : (p : ℤ) ∣ 3 * r ^ 2 := by
        obtain ⟨t, ht⟩ := hpr2
        refine ⟨3 * t, ?_⟩
        rw [ht]
        ring
      have htmp : (p : ℤ) ∣ 3 * r ^ 2 - (3 * r ^ 2 - n ^ 2) := dvd_sub hp3r2 hpD
      convert htmp using 1
      ring
    have hpn : (p : ℤ) ∣ n := Int.Prime.dvd_pow' hp hpn2
    exact hnot_unit (hrn.isUnit_of_dvd' hpr hpn)
  · have hp_diff : (p : ℤ) ∣ r * (3 * r - 2 * n) := by
      have htmp : (p : ℤ) ∣ (3 * r ^ 2 - n ^ 2) - (2 * r * n - n ^ 2) :=
        dvd_sub hpD hpA
      convert htmp using 1
      ring
    rcases Int.Prime.dvd_mul' hp hp_diff with hpr' | hp3r2n
    · exact hpr hpr'
    · have hp_9r2_sub_4n2 : (p : ℤ) ∣ 9 * r ^ 2 - 4 * n ^ 2 := by
        have htmp : (p : ℤ) ∣ (3 * r - 2 * n) * (3 * r + 2 * n) := by
          obtain ⟨t, ht⟩ := hp3r2n
          refine ⟨t * (3 * r + 2 * n), ?_⟩
          rw [ht]
          ring
        convert htmp using 1
        ring
      have hp_9r2_sub_3n2 : (p : ℤ) ∣ 9 * r ^ 2 - 3 * n ^ 2 := by
        have htmp : (p : ℤ) ∣ 3 * (3 * r ^ 2 - n ^ 2) := by
          obtain ⟨t, ht⟩ := hpD
          refine ⟨3 * t, ?_⟩
          rw [ht]
          ring
        convert htmp using 1
        ring
      have hpn2 : (p : ℤ) ∣ n ^ 2 := by
        have htmp : (p : ℤ) ∣ (9 * r ^ 2 - 3 * n ^ 2) -
            (9 * r ^ 2 - 4 * n ^ 2) := dvd_sub hp_9r2_sub_3n2 hp_9r2_sub_4n2
        convert htmp using 1
        ring
      have hpn : (p : ℤ) ∣ n := Int.Prime.dvd_pow' hp hpn2
      have hp3r2 : (p : ℤ) ∣ 3 * r ^ 2 := by
        have htmp : (p : ℤ) ∣ (3 * r ^ 2 - n ^ 2) + n ^ 2 := dvd_add hpD hpn2
        convert htmp using 1
        ring
      rcases Int.Prime.dvd_mul' hp hp3r2 with hp3 | hpr2
      · have hp3_nat : p ∣ 3 := Int.natCast_dvd_natCast.mp hp3
        have hp_eq3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3_nat
        exact h3n (by simpa [hp_eq3] using hpn)
      · have hpr_from_sq : (p : ℤ) ∣ r := Int.Prime.dvd_pow' hp hpr2
        exact hpr hpr_from_sq

/-- If `x ≡ 0 [ZMOD 3]`, then `x² ≡ 0 [ZMOD 3]`. -/
theorem sq_emod_three_eq_zero_of_emod_eq_zero {x : ℤ} (hx : x % 3 = 0) :
    x ^ 2 % 3 = 0 := by
  let q : ℤ := x / 3
  have hxdecomp : x = 3 * q := by
    calc
      x = x % 3 + 3 * (x / 3) := (Int.emod_add_mul_ediv x 3).symm
      _ = 3 * q := by rw [hx]; simp [q]
  rw [hxdecomp]
  ring_nf
  omega

/-- If `x ≡ 1 [ZMOD 3]`, then `x² ≡ 1 [ZMOD 3]`. -/
theorem sq_emod_three_eq_one_of_emod_eq_one {x : ℤ} (hx : x % 3 = 1) :
    x ^ 2 % 3 = 1 := by
  let q : ℤ := x / 3
  have hxdecomp : x = 3 * q + 1 := by
    calc
      x = x % 3 + 3 * (x / 3) := (Int.emod_add_mul_ediv x 3).symm
      _ = 3 * q + 1 := by rw [hx]; simp [q]; ring
  rw [hxdecomp]
  ring_nf
  omega

/-- If `x ≡ 2 [ZMOD 3]`, then `x² ≡ 1 [ZMOD 3]`. -/
theorem sq_emod_three_eq_one_of_emod_eq_two {x : ℤ} (hx : x % 3 = 2) :
    x ^ 2 % 3 = 1 := by
  let q : ℤ := x / 3
  have hxdecomp : x = 3 * q + 2 := by
    calc
      x = x % 3 + 3 * (x / 3) := (Int.emod_add_mul_ediv x 3).symm
      _ = 3 * q + 2 := by rw [hx]; simp [q]; ring
  rw [hxdecomp]
  ring_nf
  omega

/-- If `3 ∤ n`, then `3r² - n²` cannot be an integer square. -/
theorem not_sq_eq_three_mul_sq_sub_sq_of_not_three_dvd {C r n : ℤ}
    (h3n : ¬ (3 : ℤ) ∣ n) :
    C ^ 2 ≠ 3 * r ^ 2 - n ^ 2 := by
  intro h
  have hdiv : (3 : ℤ) ∣ C ^ 2 + n ^ 2 := by
    refine ⟨r ^ 2, ?_⟩
    nlinarith
  have hmod : (C ^ 2 + n ^ 2) % 3 = 0 := by omega
  have hn_cases : n % 3 = 1 ∨ n % 3 = 2 := by
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases hcases with hn0 | hn1 | hn2
    · exfalso
      have hdiv : (3 : ℤ) ∣ n := by omega
      exact h3n hdiv
    · exact Or.inl hn1
    · exact Or.inr hn2
  have hC_cases : C % 3 = 0 ∨ C % 3 = 1 ∨ C % 3 = 2 := by omega
  have hn_sq : n ^ 2 % 3 = 1 := by
    rcases hn_cases with hn | hn
    · exact sq_emod_three_eq_one_of_emod_eq_one hn
    · exact sq_emod_three_eq_one_of_emod_eq_two hn
  have hC_sq : C ^ 2 % 3 = 0 ∨ C ^ 2 % 3 = 1 := by
    rcases hC_cases with hC | hC | hC
    · exact Or.inl (sq_emod_three_eq_zero_of_emod_eq_zero hC)
    · exact Or.inr (sq_emod_three_eq_one_of_emod_eq_one hC)
    · exact Or.inr (sq_emod_three_eq_one_of_emod_eq_two hC)
  rcases hC_sq with hC_sq | hC_sq <;> omega

/-- In the `3 ∤ m` branch of Cox's Euler descent, choose a positive
`p = m ± C` that is not divisible by `3`. -/
theorem exists_pos_not_three_dvd_param_of_sq_sub
    {m n C : ℤ} (hm : 0 < m) (hn : 0 < n) (h3m : ¬ (3 : ℤ) ∣ m)
    (hC : C ^ 2 = m ^ 2 - 3 * n ^ 2) :
    ∃ p : ℤ, 0 < p ∧ ¬ (3 : ℤ) ∣ p ∧ p ^ 2 + 3 * n ^ 2 = 2 * m * p := by
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have hn_sq_pos : 0 < n ^ 2 := sq_pos_of_ne_zero hn_ne
  have hC_lt : C ^ 2 < m ^ 2 := by nlinarith
  have h_abs_lt : |C| < m := by
    have htmp := sq_lt_sq.mp hC_lt
    simpa [abs_of_pos hm] using htmp
  have hC_lt_m : C < m := lt_of_le_of_lt (le_abs_self C) h_abs_lt
  have hnegC_lt_m : -C < m := by
    have hle : -C ≤ |C| := neg_le_abs C
    exact lt_of_le_of_lt hle h_abs_lt
  have hplus_pos : 0 < m + C := by nlinarith
  have hminus_pos : 0 < m - C := by nlinarith
  by_cases hplus : (3 : ℤ) ∣ m + C
  · have hminus_not : ¬ (3 : ℤ) ∣ m - C := by
      intro hminus
      have hsum : (3 : ℤ) ∣ (m + C) + (m - C) := dvd_add hplus hminus
      have h2m : (3 : ℤ) ∣ 2 * m := by
        convert hsum using 1
        ring
      rcases Int.Prime.dvd_mul' Nat.prime_three h2m with h32 | h3m'
      · norm_num at h32
      · exact h3m h3m'
    refine ⟨m - C, hminus_pos, hminus_not, ?_⟩
    nlinarith
  · refine ⟨m + C, hplus_pos, hplus, ?_⟩
    nlinarith

/-- In the `3 ∤ m` branch of Cox's Euler descent, the unreduced new product
is a square. -/
theorem exists_sq_unreduced_descent_product
    {b B m n p : ℤ} (hn : 0 < n) (hB : b = B ^ 2)
    (hb : b = 2 * m * n - 3 * n ^ 2) (hp : p ^ 2 + 3 * n ^ 2 = 2 * m * p) :
    ∃ w : ℤ, p * n * (p ^ 2 - 3 * p * n + 3 * n ^ 2) = w ^ 2 := by
  have hn_ne : n ≠ 0 := ne_of_gt hn
  have hsqmul : n ^ 2 * (p * n * (p ^ 2 - 3 * p * n + 3 * n ^ 2)) =
      (B * p * n) ^ 2 := by
    rw [hB] at hb
    apply sub_eq_zero.mp
    calc
      n ^ 2 * (p * n * (p ^ 2 - 3 * p * n + 3 * n ^ 2)) - (B * p * n) ^ 2
          = n ^ 3 * p * (p ^ 2 + 3 * n ^ 2 - 2 * m * p) := by
            ring_nf
            rw [hb]
            ring
      _ = 0 := by
        rw [hp]
        ring
  exact exists_eq_sq_of_sq_mul_eq_sq hn_ne hsqmul

/-- If the unreduced Cox-Euler descent product is a square, then the product
after reducing the positive pair is still a square. -/
theorem exists_sq_reduced_descent_product
    {p n d p0 q0 w : ℤ} (hd : d ≠ 0)
    (hp : p = d * p0) (hn : n = d * q0)
    (hsq : p * n * (p ^ 2 - 3 * p * n + 3 * n ^ 2) = w ^ 2) :
    ∃ w0 : ℤ, p0 * q0 * (p0 ^ 2 - 3 * p0 * q0 + 3 * q0 ^ 2) = w0 ^ 2 := by
  have hd2_ne : d ^ 2 ≠ 0 := pow_ne_zero 2 hd
  have hscaled : (d ^ 2) ^ 2 * (p0 * q0 * (p0 ^ 2 - 3 * p0 * q0 + 3 * q0 ^ 2)) =
      w ^ 2 := by
    rw [← hsq]
    rw [hp, hn]
    ring
  exact exists_eq_sq_of_sq_mul_eq_sq hd2_ne hscaled

/-- The reduced denominator in Cox's Euler descent is strictly smaller than
the original `b`. -/
theorem reduced_descent_den_lt
    {b c m n d q0 : ℤ} (hb : 0 < b) (hc : 0 < c) (hn : 0 < n) (hd : 0 < d)
    (hq0 : 0 < q0) (hn_dvd_b : n ∣ b)
    (hbA : b = 2 * m * n - 3 * n ^ 2) (hcD : c = m ^ 2 - 3 * n ^ 2)
    (hn_eq : n = d * q0) (hcb : ¬ c = b) :
    q0 < b := by
  have hq0_dvd_n : q0 ∣ n := by
    refine ⟨d, ?_⟩
    rw [hn_eq]
    ring
  have hq0_dvd_b : q0 ∣ b := hq0_dvd_n.trans hn_dvd_b
  have hq0_le_b : q0 ≤ b := by
    obtain ⟨t, ht⟩ := hq0_dvd_b
    have htpos : 0 < t := by nlinarith
    nlinarith
  have hq0_ne_b : q0 ≠ b := by
    intro hq0b
    have hn_le_b : n ≤ b := by
      obtain ⟨t, ht⟩ := hn_dvd_b
      have htpos : 0 < t := by nlinarith
      nlinarith
    have hq0_le_n : q0 ≤ n := by
      rw [hn_eq]
      nlinarith
    have hn_eq_b : n = b := by omega
    have h2m : 2 * m = 3 * b + 1 := by
      rw [hn_eq_b] at hbA
      nlinarith
    have hc_eq_bvar : c = m ^ 2 - 3 * b ^ 2 := by
      rw [hn_eq_b] at hcD
      exact hcD
    have hcb_eq : c = b := by
      have hb1 : b = 1 := by
        have h4c : 4 * c = -3 * b ^ 2 + 6 * b + 1 := by nlinarith
        have hb_lt3 : b < 3 := by
          nlinarith [sq_nonneg (b - 1)]
        have hodd : b % 2 = 1 := by omega
        omega
      subst b
      have hm : m = 2 := by omega
      subst m
      nlinarith
    exact hcb hcb_eq
  exact lt_of_le_of_ne hq0_le_b hq0_ne_b

/-- The reduced numerator and denominator produced by Cox's Euler descent are
not equal, unless the original pair was already the excluded diagonal case. -/
theorem reduced_descent_num_ne_den
    {b c m n d p p0 q0 : ℤ} (hn : 0 < n)
    (hp_id : p ^ 2 + 3 * n ^ 2 = 2 * m * p)
    (hbA : b = 2 * m * n - 3 * n ^ 2) (hcD : c = m ^ 2 - 3 * n ^ 2)
    (hp_eq : p = d * p0) (hn_eq : n = d * q0) (hcb : ¬ c = b) :
    p0 ≠ q0 := by
  intro hp0q0
  have hp_eq_n : p = n := by
    rw [hp_eq, hn_eq, hp0q0]
  have hm_eq : m = 2 * n := by
    rw [hp_eq_n] at hp_id
    nlinarith
  have hcb_eq : c = b := by
    rw [hm_eq] at hbA hcD
    nlinarith
  exact hcb hcb_eq

/-- Cox's Euler descent step: every counterexample to Exercise 12.28 yields a
strictly smaller counterexample. -/
private theorem exists_smaller_euler_counterexample
    {b c z : ℤ} (hb : 0 < b) (hc : 0 < c) (hcop : IsCoprime b c)
    (hcb : ¬ c = b) (h3c : ¬ (3 : ℤ) ∣ c)
    (hprod : b * c * (c ^ 2 - 3 * b * c + 3 * b ^ 2) = z ^ 2) :
    ∃ b' c' z' : ℤ,
      0 < b' ∧ 0 < c' ∧ IsCoprime b' c' ∧ c' ≠ b' ∧ ¬ (3 : ℤ) ∣ c' ∧
        b' * c' * (c' ^ 2 - 3 * b' * c' + 3 * b' ^ 2) = z' ^ 2 ∧
          b'.natAbs < b.natAbs := by
  let q : ℤ := c ^ 2 - 3 * b * c + 3 * b ^ 2
  have hqpos : 0 < q := by
    simpa [q] using quadratic_factor_pos (b := b) (c := c) hb
  have hbq : IsCoprime b q := by
    simpa [q] using isCoprime_left_quadratic_factor (b := b) (c := c) hcop
  have hcq : IsCoprime c q := by
    simpa [q] using isCoprime_right_quadratic_factor (b := b) (c := c) hcop h3c
  obtain ⟨⟨B, hB⟩, ⟨C, hC⟩, K, hK⟩ :=
    exists_sq_factors_of_pos_pairwise_isCoprime_mul_mul_eq_sq
      (a := b) (b := c) (d := q) hb hc hqpos hcop hbq hcq (by simpa [q] using hprod)
  have hK_ne_zero : K ≠ 0 := by
    intro hK0
    have : q = 0 := by simpa [hK0] using hK
    nlinarith
  let k : ℤ := |K|
  have hkpos : 0 < k := by
    simpa [k] using abs_pos.mpr hK_ne_zero
  have hkq : c ^ 2 - 3 * b * c + 3 * b ^ 2 = k ^ 2 := by
    simpa [q, k, sq_abs] using hK
  obtain ⟨m, n, hmpos, hnpos, hmn_cop, hmn, hkey⟩ :=
    exists_pos_isCoprime_quadratic_param (b := b) (c := c) (k := k) hb hc hkpos hkq
  have hnumden_pos : 0 < 2 * m * n - 3 * n ^ 2 ∧ 0 < m ^ 2 - 3 * n ^ 2 :=
    quadratic_param_num_den_pos hb hc hkpos hnpos hmn hkq hkey
  let A : ℤ := 2 * m * n - 3 * n ^ 2
  let D : ℤ := m ^ 2 - 3 * n ^ 2
  have hApos : 0 < A := by simpa [A] using hnumden_pos.1
  have hDpos : 0 < D := by simpa [D] using hnumden_pos.2
  have hDb_eq_Ac : D * b = A * c := by
    dsimp [A, D]
    nlinarith
  by_cases h3m : (3 : ℤ) ∣ m
  · have h3m_orig : (3 : ℤ) ∣ m := h3m
    obtain ⟨r, hr⟩ := h3m
    have hrn_cop : IsCoprime r n := by
      refine IsCoprime.of_isCoprime_of_dvd_left hmn_cop ?_
      exact ⟨3, by rw [hr]; ring⟩
    have h3n : ¬ (3 : ℤ) ∣ n := by
      intro h3n
      exact not_isUnit_natCast_of_prime Nat.prime_three (hmn_cop.isUnit_of_dvd' h3m_orig h3n)
    let A3 : ℤ := 2 * r * n - n ^ 2
    let D3 : ℤ := 3 * r ^ 2 - n ^ 2
    have hA_eq : A = 3 * A3 := by
      dsimp [A, A3]
      rw [hr]
      ring
    have hD_eq : D = 3 * D3 := by
      dsimp [D, D3]
      rw [hr]
      ring
    have hA3pos : 0 < A3 := by nlinarith
    have hD3pos : 0 < D3 := by nlinarith
    have hD3b_eq_A3c : D3 * b = A3 * c := by
      have hscaled := hDb_eq_Ac
      rw [hA_eq, hD_eq] at hscaled
      nlinarith
    have hA3D3 : IsCoprime A3 D3 := by
      simpa [A3, D3] using isCoprime_three_dvd_param_num_den hrn_cop h3n
    have hbD3_eq_A3c : b * D3 = A3 * c := by
      rw [mul_comm]
      exact hD3b_eq_A3c
    have hbc_eq_A3D3 : b = A3 ∧ c = D3 :=
      eq_of_pos_isCoprime_mul_eq_mul hc hD3pos hcop hA3D3 hbD3_eq_A3c
    obtain ⟨_, hcD3⟩ := hbc_eq_A3D3
    have hCsq : C ^ 2 = 3 * r ^ 2 - n ^ 2 := by
      dsimp [D3] at hcD3
      nlinarith
    exact False.elim (not_sq_eq_three_mul_sq_sub_sq_of_not_three_dvd h3n hCsq)
  · have hAD : IsCoprime A D := by
      simpa [A, D] using isCoprime_param_num_den_of_not_three_dvd hmn_cop h3m
    have hbD_eq_Ac : b * D = A * c := by
      rw [mul_comm]
      exact hDb_eq_Ac
    have hbc_eq_AD : b = A ∧ c = D :=
      eq_of_pos_isCoprime_mul_eq_mul hc hDpos hcop hAD hbD_eq_Ac
    obtain ⟨hbA, hcD⟩ := hbc_eq_AD
    have hCsub : C ^ 2 = m ^ 2 - 3 * n ^ 2 := by
      nlinarith
    obtain ⟨p, hp_pos, h3p, hp_id⟩ :=
      exists_pos_not_three_dvd_param_of_sq_sub hmpos hnpos h3m hCsub
    obtain ⟨w, hw⟩ :=
      exists_sq_unreduced_descent_product hnpos hB hbA hp_id
    obtain ⟨d, p0, q0, hdpos, hp0pos, hq0pos, hp0q0_cop, hp_eq, hn_eq⟩ :=
      exists_pos_isCoprime_eq_mul_of_pos hp_pos hnpos
    have hd_ne : d ≠ 0 := ne_of_gt hdpos
    have h3p0 : ¬ (3 : ℤ) ∣ p0 := by
      intro h3p0
      have h3p' : (3 : ℤ) ∣ p := by
        rw [hp_eq]
        obtain ⟨t, ht⟩ := h3p0
        refine ⟨d * t, ?_⟩
        rw [ht]
        ring
      exact h3p h3p'
    obtain ⟨w0, hw0⟩ :=
      exists_sq_reduced_descent_product hd_ne hp_eq hn_eq hw
    have hn_dvd_mb : n ∣ m * b := ⟨k + c, hmn⟩
    have hn_dvd_b : n ∣ b := hmn_cop.symm.dvd_of_dvd_mul_left hn_dvd_mb
    have hq0_lt_b : q0 < b :=
      reduced_descent_den_lt hb hc hnpos hdpos hq0pos hn_dvd_b hbA hcD hn_eq hcb
    have hp0_ne_q0 : p0 ≠ q0 :=
      reduced_descent_num_ne_den hnpos hp_id hbA hcD hp_eq hn_eq hcb
    have hprod_new : q0 * p0 * (p0 ^ 2 - 3 * q0 * p0 + 3 * q0 ^ 2) = w0 ^ 2 := by
      convert hw0 using 1
      ring
    refine ⟨q0, p0, w0, hq0pos, hp0pos, hp0q0_cop.symm, hp0_ne_q0, h3p0, ?_, ?_⟩
    · exact hprod_new
    · exact Int.natAbs_lt_natAbs_of_nonneg_of_lt hq0pos.le hq0_lt_b

/-- **Euler descent input, Cox Exercise 12.28.**  If `b` and `c` are positive
coprime integers and `b * c * (c ^ 2 - 3 * b * c + 3 * b ^ 2)` is a square,
then either `c = b` or `3 ∣ c`.

This is the reusable integer core of Euler's infinite descent for the rational
points on `X ^ 3 + 1 = Z ^ 2`. -/
-- Repository use: Cox's Exercise 12.29 applies this twice to classify the
-- square branch `X ^ 3 + 1 = Z ^ 2`.
theorem eq_or_three_dvd_of_pos_isCoprime_mul_quadratic_eq_sq
    {b c z : ℤ} (hb : 0 < b) (hc : 0 < c) (hcop : IsCoprime b c)
    (hprod : b * c * (c ^ 2 - 3 * b * c + 3 * b ^ 2) = z ^ 2) :
    c = b ∨ (3 : ℤ) ∣ c := by
  by_contra h
  have hcb : ¬ c = b := fun hcb => h (Or.inl hcb)
  have h3c : ¬ (3 : ℤ) ∣ c := fun h3c => h (Or.inr h3c)
  let Bad : ℤ → ℤ → ℤ → Prop := fun b c z =>
    0 < b ∧ 0 < c ∧ IsCoprime b c ∧ c ≠ b ∧ ¬ (3 : ℤ) ∣ c ∧
      b * c * (c ^ 2 - 3 * b * c + 3 * b ^ 2) = z ^ 2
  have step : ∀ {b c z : ℤ}, Bad b c z →
      ∃ b' c' z' : ℤ, Bad b' c' z' ∧ b'.natAbs < b.natAbs := by
    intro b c z hbad
    rcases hbad with ⟨hb, hc, hcop, hcb, h3c, hprod⟩
    obtain ⟨b', c', z', hb', hc', hcop', hcb', h3c', hprod', hlt⟩ :=
      exists_smaller_euler_counterexample hb hc hcop hcb h3c hprod
    exact ⟨b', c', z', ⟨hb', hc', hcop', hcb', h3c', hprod'⟩, hlt⟩
  have no_bad : ∀ n : ℕ, ¬ ∃ b c z : ℤ, Bad b c z ∧ b.natAbs = n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        rintro ⟨b, c, z, hbad, hbabs⟩
        obtain ⟨b', c', z', hbad', hlt⟩ := step hbad
        exact ih b'.natAbs (by rw [← hbabs]; exact hlt) ⟨b', c', z', hbad', rfl⟩
  exact no_bad b.natAbs ⟨b, c, z, ⟨hb, hc, hcop, hcb, h3c, hprod⟩, rfl⟩

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
