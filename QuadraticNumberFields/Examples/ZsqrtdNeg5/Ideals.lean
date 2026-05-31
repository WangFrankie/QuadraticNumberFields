/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang

Ideal factorization and primality results for ℤ[√-5].
Ported from the ANT project.
-/
import QuadraticNumberFields.Zsqrtd.Ideals

/-!
# Ideal Factorization in ℤ[√-5]

This file proves the ideal factorization identities and primality results
for the non-UFD ring `ℤ[√-5]`, demonstrating the general theory of
quadratic number fields on a concrete example.

## Main Results

* `factorization_of_two`: `(2) = (2, 1+√-5)²`
* `factorization_of_three`: `(3) = (3, 1+√-5) · (3, 1-√-5)`
* `factorization_of_one_plus_sqrtd`: `(1+√-5) = (2, 1+√-5) · (3, 1+√-5)`
* `factorization_of_one_minus_sqrtd`: `(1-√-5) = (2, 1-√-5) · (3, 1-√-5)`
* `isPrime_span_two_one_plus_sqrtd`: `(2, 1+√-5)` is prime
* `isPrime_span_three_one_plus_sqrtd`: `(3, 1+√-5)` is prime
* `isPrime_span_three_one_minus_sqrtd`: `(3, 1-√-5)` is prime
-/

open Ideal

namespace QuadraticNumberFields.Examples.ZsqrtdNeg5

/-- The working quadratic integer ring `ℤ[√-5]` used in this file. -/
abbrev R := _root_.Zsqrtd (-5)

local notation "sqrtd" => _root_.Zsqrtd.sqrtd

instance : Fact ((-5 : ℤ) < 0) := ⟨by decide⟩

-- ============================================================================
-- Arithmetic conditions for d = -5
-- ============================================================================

/-- Arithmetic input for the prime `2` in `ℤ[√-5]`: `2 ∣ (-5 - 1)`. -/
lemma neg5_dvd_two : 2 ∣ ((-5 : ℤ) - 1) := ⟨-3, by norm_num⟩

/-- Arithmetic input for the prime `3` in `ℤ[√-5]`: `3 ∣ (-5 - 1)`. -/
lemma neg5_dvd_three : 3 ∣ ((-5 : ℤ) - 1) := ⟨-2, by norm_num⟩

-- ============================================================================
-- Helper lemmas for factorization proofs
-- ============================================================================

private lemma in_span_of_eq
  {x y : R} (h : x = y) (hy : y ∈ (I : Ideal R)) :
  x ∈ I :=
by simpa [h] using hy

-- ============================================================================
-- Ideal factorizations (specific to d = -5)
-- ============================================================================

theorem factorization_of_two :
    span {(2 : R)} = (span {2, 1 + sqrtd}) ^ 2 := by
  -- Expand ⟨2, 1+√-5⟩² into the span of the four pairwise products of generators
  let J : Ideal R :=
    span ({(2 : R) * (2 : R), (2 : R) * (1 + sqrtd), (1 + sqrtd) * (2 : R),
      (1 + sqrtd) * (1 + sqrtd)} : Set R)
  -- Key computation: (1+√-5)² = 2·(-2+√-5), since (√-5)² = -5
  have hsq : (1 + sqrtd : R) * (1 + sqrtd) = (2 : R) * (-2 + sqrtd) := by
    ext <;> norm_num [_root_.Zsqrtd.sqrtd]
  -- Rewrite the square as J using `span_pair_mul_span_pair`
  have hpow : (span ({(2 : R), (1 + sqrtd)} : Set R) : Ideal R) ^ 2 = J := by
    simp [J, pow_two, Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion ⟨2⟩ ⊆ J: express 2 as a linear combination of generators
    --   2 = 2·(1+√-5) - (1+√-5)² - 2·2
    rw [Ideal.span_singleton_le_iff_mem, hpow]
    have h21 : (2 : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h11 : (1 + sqrtd : R) * (1 + sqrtd) ∈ J := Ideal.subset_span (by simp)
    have h22 : (2 : R) * (2 : R) ∈ J := Ideal.subset_span (by simp)
    -- Ideals are closed under subtraction, so this combination lies in J
    have hmem : (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) ∈ J :=
      J.sub_mem (J.sub_mem h21 h11) h22
    -- Verify the combination actually equals 2
    have hcalc :
        (2 : R) * (1 + sqrtd) - (1 + sqrtd) * (1 + sqrtd) - (2 : R) * (2 : R) = (2 : R) := by
      rw [hsq]
      ring
    exact hcalc ▸ hmem
  · -- Reverse inclusion J ⊆ ⟨2⟩: each of the four generators is divisible by 2
    rw [hpow]
    refine Ideal.span_le.2 ?_
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·2 is divisible by 2
      exact Ideal.mem_span_singleton.mpr ⟨(2 : R), rfl⟩
    · -- 2·(1+√-5) is divisible by 2
      exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), rfl⟩
    · -- (1+√-5)·2 = 2·(1+√-5) by commutativity
      exact Ideal.mem_span_singleton.mpr ⟨(1 + sqrtd : R), by simp [mul_comm]⟩
    · -- (1+√-5)² = 2·(-2+√-5) by `hsq`
      exact Ideal.mem_span_singleton.mpr ⟨(-2 + sqrtd : R), hsq⟩

theorem factorization_of_three :
    span {(3 : R)} = (span {3, 1 + sqrtd}) * (span {3, 1 - sqrtd}) := by
    -- Expand the ideal product into the span of four pairwise products
    rw [Ideal.span_pair_mul_span_pair]
    apply _root_.le_antisymm
    · -- Forward inclusion ⟨3⟩ ⊆ product: 3 = 3·3 - (1+√-5)(1-√-5)
      --   since (1+√-5)(1-√-5) = 1-(-5) = 6, we get 9 - 6 = 3
      rw [Ideal.span_singleton_le_iff_mem]
      have three_eq: (3 : R) = 3 * 3 - (1 + sqrtd) * (1 - sqrtd) := by
        ext <;> norm_num [_root_.Zsqrtd.sqrtd]
      exact in_span_of_eq three_eq
        ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
    · -- Reverse inclusion: each of the four generators is divisible by 3
      apply _root_.Zsqrtd.Ideal.span_le_span_singleton_of_forall_dvd
      intro x hx
      rcases hx with rfl  | rfl | rfl | rfl
      · simp  -- 3·3 is divisible by 3
      · simp  -- 3·(1-√-5) is divisible by 3
      · simp  -- (1+√-5)·3 is divisible by 3
      · -- (1+√-5)(1-√-5) = 6 = 3·2
        exact ⟨2, by ext <;> norm_num [_root_.Zsqrtd.sqrtd]⟩

theorem factorization_of_one_plus_sqrtd :
    span {(1 + sqrtd : R)} = (span {2, 1 + sqrtd}) * (span {3, 1 + sqrtd}) := by
  -- Expand the ideal product into the span of four pairwise products
  rw [Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion ⟨1+√-5⟩ ⊆ product:
    --   1+√-5 = (1+√-5)·3 - 2·(1+√-5)  (i.e., 3x - 2x = x)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_plus_sqrtd_eq :
        (1 + sqrtd : R) = (1 + sqrtd) * 3 - 2 * (1 + sqrtd) := by ring
    exact in_span_of_eq one_plus_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1+√-5)
    apply _root_.Zsqrtd.Ideal.span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1+√-5)(1-√-5), so (1+√-5) | 6
      exact ⟨1 - sqrtd, by ext <;> norm_num [_root_.Zsqrtd.sqrtd]⟩
    · -- 2·(1+√-5) = (1+√-5)·2
      simp
    · -- (1+√-5)·3
      simp
    · -- (1+√-5)² = (1+√-5)·(1+√-5)
      simp

theorem factorization_of_one_minus_sqrtd :
    span {(1 - sqrtd : R)} = (span {2, 1 - sqrtd}) * (span {3, 1 - sqrtd}) := by
  -- Symmetric to factorization_of_one_plus_sqrtd, replacing √-5 by -√-5
  rw [Ideal.span_pair_mul_span_pair]
  apply _root_.le_antisymm
  · -- Forward inclusion: 1-√-5 = (1-√-5)·3 - 2·(1-√-5)
    rw [Ideal.span_singleton_le_iff_mem]
    have one_mins_sqrtd_eq :
        (1 - sqrtd : R) = (1 - sqrtd) * 3 - 2 * (1 - sqrtd) := by ring
    exact in_span_of_eq one_mins_sqrtd_eq
      ((span _).sub_mem (Ideal.subset_span (by simp)) (Ideal.subset_span (by simp)))
  · -- Reverse inclusion: each of the four generators is divisible by (1-√-5)
    apply _root_.Zsqrtd.Ideal.span_le_span_singleton_of_forall_dvd
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · -- 2·3 = 6 = (1-√-5)(1+√-5), so (1-√-5) | 6
      exact ⟨1 + sqrtd, by ext <;> norm_num [_root_.Zsqrtd.sqrtd]⟩
    · simp  -- 2·(1-√-5) = (1-√-5)·2
    · simp  -- (1-√-5)·3
    · simp  -- (1-√-5)² = (1-√-5)·(1-√-5)

-- ============================================================================
-- Primality (instantiated from general theory)
-- ============================================================================

theorem isPrime_span_two_one_plus_sqrtd :
    IsPrime (span {2, 1 + sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  _root_.Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd 2 neg5_dvd_two

theorem isPrime_span_three_one_plus_sqrtd :
    IsPrime (span {3, 1 + sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  _root_.Zsqrtd.Ideal.isPrime_span_p_one_plus_sqrtd 3 neg5_dvd_three

theorem isPrime_span_three_one_minus_sqrtd :
    IsPrime (span {3, 1 - sqrtd} : Ideal R) :=
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  _root_.Zsqrtd.Ideal.isPrime_span_p_one_minus_sqrtd 3 neg5_dvd_three

end QuadraticNumberFields.Examples.ZsqrtdNeg5
