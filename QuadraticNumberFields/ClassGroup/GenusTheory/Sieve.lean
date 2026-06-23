/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Surjectivity

/-!
# Class-Number-One Genus Sieve

This file contains the elementary arithmetic endpoint of the genus-theory sieve
and the class-number-one consequences built from `genusFormula`.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

open RingOfIntegers
open Splitting

local notation "𝓞" => _root_.NumberField.RingOfIntegers

private theorem nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one {n : ℕ}
    (hsq : Squarefree n) (hcard : n.primeFactors.card ≤ 1) :
    n = 1 ∨ n.Prime := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hnonempty : n.primeFactors.Nonempty
  · right
    obtain ⟨p, hpmem⟩ := hnonempty
    have huniq : n.primeFactors = {p} := by
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hpmem, fun q hqmem => (Finset.card_le_one_iff.mp hcard) hqmem hpmem⟩
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpmem
    have hn_eq : n = p := by
      rw [huniq] at hprod
      simpa using hprod.symm
    simpa [hn_eq] using hpprime
  · left
    have hcard0 : n.primeFactors.card = 0 := by
      rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.card_eq_zero] at hnonempty
    have hpf_empty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    rw [hpf_empty] at hprod
    simpa using hprod.symm

private theorem nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two {n : ℕ}
    (hsq : Squarefree n) (hfactor : ∀ p ∈ n.primeFactors, p = 2) :
    n = 1 ∨ n = 2 := by
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  by_cases hnonempty : n.primeFactors.Nonempty
  · right
    obtain ⟨p, hpmem⟩ := hnonempty
    have huniq : n.primeFactors = {2} := by
      exact Finset.eq_singleton_iff_unique_mem.mpr
        ⟨by simpa [hfactor p hpmem] using hpmem,
          fun q hqmem => hfactor q hqmem⟩
    rw [huniq] at hprod
    simpa using hprod.symm
  · left
    have hcard0 : n.primeFactors.card = 0 := by
      rwa [Finset.not_nonempty_iff_eq_empty, ← Finset.card_eq_zero] at hnonempty
    have hpf_empty : n.primeFactors = ∅ := Finset.card_eq_zero.mp hcard0
    rw [hpf_empty] at hprod
    simpa using hprod.symm

private theorem two_mem_primeFactors_natAbs_four_mul_of_neg {d : ℤ} (hdneg : d < 0) :
    2 ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul]
  rw [Nat.mem_primeFactors]
  constructor
  · exact Nat.prime_two
  constructor
  · exact ⟨2 * d.natAbs, by ring⟩
  · exact mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr (by omega))

private theorem mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs {d : ℤ} {p : ℕ}
    (hp : p ∈ d.natAbs.primeFactors) :
    p ∈ (4 * d).natAbs.primeFactors := by
  rw [Int.natAbs_mul]
  rw [Nat.mem_primeFactors] at hp ⊢
  exact ⟨hp.1, dvd_mul_of_dvd_right hp.2.1 4, mul_ne_zero (by decide) hp.2.2⟩

private theorem prime_shape_of_mod_four_eq_one
    (d : ℤ) (hsq : Squarefree d) (hdneg : d < 0) (hd4 : d % 4 = 1)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcard : d.natAbs.primeFactors.card ≤ 1 := by
    simpa [primeDiscriminantFactorCount, RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      using hcount
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  rcases nat_eq_one_or_prime_of_squarefree_of_primeFactors_card_le_one hsq_nat hcard with
    h1 | hp
  · left
    omega
  · right
    right
    refine ⟨d.natAbs, hp, ?_, ?_⟩
    · omega
    · omega

private theorem prime_shape_of_mod_four_ne_one
    (d : ℤ) (hsq : Squarefree d) (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hcardD : (4 * d).natAbs.primeFactors.card ≤ 1 := by
    simpa [primeDiscriminantFactorCount, RingOfIntegers.discrFormula_of_mod_four_ne_one hd4]
      using hcount
  have htwoD : 2 ∈ (4 * d).natAbs.primeFactors :=
    two_mem_primeFactors_natAbs_four_mul_of_neg hdneg
  have hfactor : ∀ p ∈ d.natAbs.primeFactors, p = 2 := by
    intro p hp
    exact (Finset.card_le_one_iff.mp hcardD)
      (mem_primeFactors_natAbs_four_mul_of_mem_primeFactors_natAbs hp) htwoD
  have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
  rcases nat_eq_one_or_eq_two_of_squarefree_of_forall_primeFactors_eq_two hsq_nat hfactor with
    h1 | h2
  · left
    omega
  · right
    left
    omega

/-- The elementary arithmetic endpoint of the genus-theory sieve. For squarefree
negative `d`, if the field-discriminant prime-factor count is at most one, then
`d` has the class-number-one prime shape. -/
theorem discriminant_prime_shape_of_primeDiscriminantFactorCount_le_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hcount : primeDiscriminantFactorCount d ≤ 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  by_cases hd4 : d % 4 = 1
  · exact prime_shape_of_mod_four_eq_one d (Fact.out : Squarefree d) hd hd4 hcount
  · exact prime_shape_of_mod_four_ne_one d (Fact.out : Squarefree d) hd hd4 hcount

/-- Genus divisibility plus class number one implies the prime-shape conclusion.
This is the reusable interface for the future genus-theory calculation
`2 ^ (t - 1) ∣ h(d)`. -/
theorem discriminant_prime_shape_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) :=
  discriminant_prime_shape_of_primeDiscriminantFactorCount_le_one d hd
    (primeDiscriminantFactorCount_le_one_of_genus_divisibility d hdiv hclass)

/-- In the odd field-discriminant branch, genus divisibility plus class number one
leaves only the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  rcases discriminant_prime_shape_of_genus_divisibility d hd hdiv h with
    hneg1 | hneg2 | hprime
  · exfalso
    subst hneg1
    have hd4 := (RingOfIntegers.discrFormula_odd_iff_mod_four_eq_one (-1)).mp hodd
    norm_num at hd4
  · exfalso
    subst hneg2
    have hd4 := (RingOfIntegers.discrFormula_odd_iff_mod_four_eq_one (-2)).mp hodd
    norm_num at hd4
  · exact hprime

/-- **Genus-theory sieve for class number one.** Assuming the standard genus
cardinality formula `genusFormula d`, if an imaginary quadratic field
`ℚ(√d)` has class number one, then its squarefree parameter has prime shape:
`d = -1`, `d = -2`, or `d = -p` for a rational prime `p ≡ 3 (mod 4)`.

The remaining genus-theory construction is the proof of `genusFormula d`,
namely the cardinality formula for the principal-genus quotient `Cl / Cl²`. -/
theorem classNumber_eq_one_imp_discriminant_prime_shape
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hgenus : genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) :=
    genus_divisibility_of_squareClassSubgroup_quotient_card d hgenus
  exact discriminant_prime_shape_of_genus_divisibility d hd hdiv h

/-- In the odd field-discriminant branch, the genus-theory sieve leaves only
the prime-discriminant family: `d = -p` for a rational prime `p ≡ 3 (mod 4)`.

This is the part of Cox Theorem 12.34 where genus theory is used.  The even
field-discriminant branch is handled separately by Landau's reduced-form
classification of the discriminants `-4n` with class number one. -/
theorem classNumber_eq_one_imp_exists_prime_of_odd_discr
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0)
    (hgenus : genusFormula d)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  exact classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility d hd hodd
    (genus_divisibility_of_squareClassSubgroup_quotient_card d hgenus) h

/-- For odd fundamental discriminants (`d % 4 = 1`), the weak genus-theory
divisibility reduces class number one to the prime-discriminant family. -/
theorem classNumber_eq_one_imp_exists_prime_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hd4 : d % 4 = 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
  exact classNumber_eq_one_imp_exists_prime_of_odd_discr_of_genus_divisibility d hd hodd
    (genus_divisibility_of_mod_four_eq_one d hd hd4) h

end ClassGroup
end QuadraticNumberFields
