/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.LowerBound
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Class-Number-One Genus Sieve

This file transfers the genus-theory divisibility from the narrow class number
to the ordinary class number for imaginary quadratic fields and derives the
resulting restriction on squarefree parameters of class-number-one fields.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup


private theorem nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one {n : ℕ}
    (hsq : Squarefree n) (hcard : n.primeFactors.card ≤ 1) :
    n = 1 ∨ n.Prime := by
  by_cases hcard0 : n.primeFactors.card = 0
  · left
    have hprod := Nat.prod_primeFactors_of_squarefree hsq
    rw [Finset.card_eq_zero.mp hcard0] at hprod
    simpa using hprod.symm
  · right
    have hcard1 : n.primeFactors.card = 1 := by omega
    exact Nat.squarefree_and_prime_pow_iff_prime.mp
      ⟨hsq, isPrimePow_iff_card_primeFactors_eq_one.mpr hcard1⟩

private theorem nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two {n : ℕ}
    (hsq : Squarefree n) (hfactor : ∀ p ∈ n.primeFactors, p = 2) :
    n = 1 ∨ n = 2 := by
  have hcard : n.primeFactors.card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro p q hp hq
    exact (hfactor p hp).trans (hfactor q hq).symm
  rcases nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one hsq hcard with h1 | hn
  · exact Or.inl h1
  · exact Or.inr (hfactor n (hn.mem_primeFactors (dvd_refl n) hn.ne_zero))

private theorem two_mem_primeFactors_natAbs_four_mul {d : ℤ} (hd0 : d ≠ 0) :
    2 ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul, Nat.mem_primeFactors]
  exact ⟨Nat.prime_two, ⟨2 * d.natAbs, by ring⟩,
    mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hd0)⟩

private theorem mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs {d : ℤ} {p : ℕ}
    (hp : p ∈ d.natAbs.primeFactors) :
    p ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul]
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, dvd_mul_of_dvd_right hp.2.1 4, mul_ne_zero (by decide) hp.2.2⟩

private theorem prime_shape_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (hcount : ramifiedPrimeCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcard : d.natAbs.primeFactors.card ≤ 1 := by
    rw [ramifiedPrimeCount_eq_card, ramifiedPrimes_eq_discrFormula_primeFactors d,
      RingOfIntegers.discrFormula_of_mod_four_eq_one hd4] at hcount
    exact hcount
  have hsq_nat : Squarefree d.natAbs :=
    Int.squarefree_natAbs.mpr (Fact.out : Squarefree d)
  rcases nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one hsq_nat hcard with
    h1 | hp
  · left
    omega
  · right
    right
    exact ⟨d.natAbs, hp, by omega, by omega⟩


private theorem prime_shape_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (hcount : ramifiedPrimeCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcardD : (4 * d).natAbs.primeFactors.card ≤ 1 := by
    rw [ramifiedPrimeCount_eq_card, ramifiedPrimes_eq_discrFormula_primeFactors d,
      RingOfIntegers.discrFormula_of_mod_four_ne_one hd4] at hcount
    exact hcount
  have htwoD : 2 ∈ (4 * d).natAbs.primeFactors :=
    two_mem_primeFactors_natAbs_four_mul (by omega)
  have hfactor : ∀ p ∈ d.natAbs.primeFactors, p = 2 := by
    intro p hp
    exact (Finset.card_le_one_iff.mp hcardD)
      (mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs hp) htwoD
  have hsq_nat : Squarefree d.natAbs :=
    Int.squarefree_natAbs.mpr (Fact.out : Squarefree d)
  rcases nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two hsq_nat hfactor with
    h1 | h2
  · left
    omega
  · right
    left
    omega

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- If a squarefree negative parameter has at most one ramified rational prime,
then it has the class-number-one prime shape. -/
theorem parameter_prime_shape_of_ramifiedPrimeCount_le_one
    (hd : d < 0) (hcount : ramifiedPrimeCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨
      ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  by_cases hd4 : d % 4 = 1
  · exact prime_shape_of_mod_four_eq_one d hd hd4 hcount
  · exact prime_shape_of_mod_four_ne_one d hd hd4 hcount

private theorem le_one_of_two_pow_sub_one_dvd_one {t : ℕ} (h : 2 ^ (t - 1) ∣ 1) :
    t ≤ 1 := by
  by_contra hle
  exact (not_lt_of_ge (by rw [Nat.dvd_one.mp h]))
    (one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega : t - 1 ≠ 0))

/-- For an imaginary quadratic field, the genus-theory power of two divides
the ordinary class number. -/
theorem two_pow_sub_one_dvd_classNumber_of_neg (hd : d < 0) :
    2 ^ (ramifiedPrimeCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  have hdiv := two_pow_sub_one_dvd_narrowClassNumber d
  have hcard :
      Qsqrtd.narrowClassNumber d =
        NumberField.classNumber (Qsqrtd (d : ℚ)) := by
    simpa [Qsqrtd.narrowClassNumber, NumberField.classNumber] using
      Nat.card_congr (Qsqrtd.Imaginary.narrowMulEquivClassGroup d hd).toEquiv
  simpa [hcard] using hdiv

/-- Genus-theory sieve for class number one. An imaginary quadratic field
with class number one has squarefree parameter `d = -1`, `d = -2`, or
`d = -p` for a rational prime `p ≡ 3 (mod 4)`. -/
theorem classNumber_eq_one_imp_parameter_prime_shape
    (hd : d < 0)
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨
      ∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  apply parameter_prime_shape_of_ramifiedPrimeCount_le_one d hd
  apply le_one_of_two_pow_sub_one_dvd_one
  simpa [hclass] using two_pow_sub_one_dvd_classNumber_of_neg d hd

end GenusTheory
end ClassGroup
end QuadraticNumberFields
