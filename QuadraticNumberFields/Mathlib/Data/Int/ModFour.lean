/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Mathlib.Algebra.Squarefree.Basic

/-!
# Integer Congruences Modulo Four

Material destined for mathlib.
-/

/-- The square of an even integer is `0 mod 4`. -/
-- Repository use: internal support for the mod-four parity criteria below.
lemma Int.sq_emod_four_of_even (n : ℤ) (h : 2 ∣ n) : n ^ 2 % 4 = 0 := by
  obtain ⟨k, rfl⟩ := h
  ring_nf
  omega

/-- The square of an odd integer is `1 mod 4`. -/
-- Repository use: internal support for the mod-four parity criteria below.
lemma Int.sq_emod_four_of_odd (n : ℤ) (h : ¬ 2 ∣ n) : n ^ 2 % 4 = 1 := by
  set k := n / 2
  have hk : n = 2 * k + 1 := by omega
  rw [hk]
  ring_nf
  omega

private lemma div4_iff_mod (a' b' d : ℤ) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (a' ^ 2 - d * b' ^ 2) % 4 = 0 := by
  omega

private lemma sq_eq_four_mul_div_of_even (n : ℤ) (h : 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) := by
  have hn2 : n ^ 2 % 4 = 0 := Int.sq_emod_four_of_even n h
  omega

private lemma sq_eq_four_mul_div_add_one_of_odd (n : ℤ) (h : ¬ 2 ∣ n) :
    n ^ 2 = 4 * (n ^ 2 / 4) + 1 := by
  have hn2 : n ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd n h
  omega

private lemma odd_eq_two_mul_div_add_one (n : ℤ) (h : ¬ 2 ∣ n) :
    n = 2 * (n / 2) + 1 := by
  omega

private lemma even_odd_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hd : Squarefree d)
    (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : 2 ∣ a') (hb : ¬ 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) := sq_eq_four_mul_div_of_even a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [hb_eq] at hmod'
  ring_nf at hmod'
  have hdvd : (4 : ℤ) ∣ d := by omega
  exact squarefree_int_not_dvd_four d hd hdvd

private lemma odd_even_impossible_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : 2 ∣ b') : False := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) := sq_eq_four_mul_div_of_even b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega

private lemma mod_four_eq_one_of_odd_odd_of_mod_eq_zero
    (d a' b' : ℤ) (hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0)
    (ha : ¬ 2 ∣ a') (hb : ¬ 2 ∣ b') : d % 4 = 1 := by
  have hmod' := hmod
  have ha_eq : a' ^ 2 = 4 * (a' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd a' ha
  have hb_eq : b' ^ 2 = 4 * (b' ^ 2 / 4) + 1 := sq_eq_four_mul_div_add_one_of_odd b' hb
  rw [ha_eq, hb_eq] at hmod'
  ring_nf at hmod'
  omega

/-- Main mod-4 criterion for the binary quadratic form `a'² − d·b'²`. -/
-- Repository use: internal support for the two branch-specific criteria used
-- by `RingOfIntegers/Integrality.lean`.
theorem dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one
    (d a' b' : ℤ) (hd : Squarefree d) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔
      (2 ∣ a' ∧ 2 ∣ b') ∨ (¬ 2 ∣ a' ∧ ¬ 2 ∣ b' ∧ d % 4 = 1) := by
  constructor
  · intro hdvd
    have hmod : (a' ^ 2 - d * b' ^ 2) % 4 = 0 := (div4_iff_mod a' b' d).1 hdvd
    by_cases ha : 2 ∣ a' <;> by_cases hb : 2 ∣ b'
    · exact Or.inl ⟨ha, hb⟩
    · exact (even_odd_impossible_of_mod_eq_zero d a' b' hd hmod ha hb).elim
    · exact (odd_even_impossible_of_mod_eq_zero d a' b' hmod ha hb).elim
    · exact Or.inr ⟨ha, hb, mod_four_eq_one_of_odd_odd_of_mod_eq_zero d a' b' hmod ha hb⟩
  · intro h
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb, hd1⟩
    · obtain ⟨p, rfl⟩ := ha
      obtain ⟨q, rfl⟩ := hb
      exact ⟨p ^ 2 - d * q ^ 2, by ring⟩
    · have ha_eq : a' = 2 * (a' / 2) + 1 := odd_eq_two_mul_div_add_one a' ha
      have hb_eq : b' = 2 * (b' / 2) + 1 := odd_eq_two_mul_div_add_one b' hb
      rw [ha_eq, hb_eq]
      ring_nf
      have hd_eq : d = 4 * (d / 4) + 1 := by omega
      rw [hd_eq]
      ring_nf
      omega

/-- If `d % 4 ≠ 1`, divisibility by `4` forces both numerators even. -/
-- Repository use: internal support for
-- `dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four`.
theorem even_even_of_dvd_four_sub_sq_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1)
    (h : 4 ∣ (a' ^ 2 - d * b' ^ 2)) :
    2 ∣ a' ∧ 2 ∣ b' := by
  rcases (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).mp h with
      hab | ⟨_, _, hd1⟩
  · exact hab
  · exact absurd hd1 hd4

/-- If `d % 4 ≠ 1`, divisibility by `4` is equivalent to both numerators even. -/
-- Repository use: `RingOfIntegers/Integrality.lean` uses this in the
-- `ℤ[√d]` branch of the integral-closure classification.
theorem dvd_four_sub_sq_iff_even_even_of_ne_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 ≠ 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ (2 ∣ a' ∧ 2 ∣ b') := by
  constructor
  · exact even_even_of_dvd_four_sub_sq_of_ne_one_mod_four d a' b' hd hd4
  · exact fun h => (dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd).2 (Or.inl h)

/-- If `d % 4 = 1`, divisibility by `4` is equivalent to same parity. -/
-- Repository use: `RingOfIntegers/Integrality.lean` uses this in the
-- `ℤ[(1+√d)/2]` branch of the integral-closure classification.
theorem dvd_four_sub_sq_iff_same_parity_of_one_mod_four
    (d a' b' : ℤ) (hd : Squarefree d) (hd4 : d % 4 = 1) :
    4 ∣ (a' ^ 2 - d * b' ^ 2) ↔ a' % 2 = b' % 2 := by
  rw [dvd_four_sub_sq_iff_even_even_or_odd_odd_mod_four_one d a' b' hd]
  constructor
  · rintro (⟨ha, hb⟩ | ⟨ha, hb, _⟩) <;> omega
  · intro h
    by_cases ha : 2 ∣ a'
    · left
      exact ⟨ha, by omega⟩
    · right
      exact ⟨ha, by omega, hd4⟩
