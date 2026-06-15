/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Torsion
import QuadraticNumberFields.ClassNumber
import Mathlib.GroupTheory.Index

/-!
# Genus Theory

This file will contain genus-theory infrastructure for quadratic class groups.

The first intended application is the elementary genus-theory sieve in the
imaginary class-number-one problem: class number one forces the fundamental
discriminant to have only one prime-discriminant factor.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-! ## Class-number-one sieve -/

/-- The number of distinct rational prime factors of the closed discriminant
formula for `ℚ(√d)`. For squarefree `d`, this is the genus-theory parameter
usually denoted `t`, the number of prime-discriminant factors of the fundamental
discriminant. -/
def primeDiscriminantFactorCount (d : ℤ) : ℕ :=
  (RingOfIntegers.discrFormula d).natAbs.primeFactors.card

private theorem le_one_of_two_pow_sub_one_dvd_one {t : ℕ} (h : 2 ^ (t - 1) ∣ 1) :
    t ≤ 1 := by
  have hpow : 2 ^ (t - 1) = 1 := Nat.dvd_one.mp h
  by_contra hle
  have hsub_ne : t - 1 ≠ 0 := by omega
  have hpow_gt : 1 < 2 ^ (t - 1) :=
    one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) hsub_ne
  omega

/-- Once genus theory supplies the standard divisibility
`2 ^ (t - 1) ∣ h(d)`, class number one forces `t ≤ 1`. This isolates the
elementary arithmetic endpoint of the genus-theory sieve from the missing
genus-theory divisibility proof. -/
theorem primeDiscriminantFactorCount_le_one_of_genus_divisibility
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hdiv : 2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)))
    (hclass : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    primeDiscriminantFactorCount d ≤ 1 :=
  le_one_of_two_pow_sub_one_dvd_one (by simpa [hclass] using hdiv)

/-- A finite quotient of the ideal class group with cardinality `2 ^ (t - 1)`
gives the standard genus-theory divisibility `2 ^ (t - 1) ∣ h(d)`.

The missing genus-theory construction is exactly the production of such a
surjective quotient map, with `t = primeDiscriminantFactorCount d`. -/
theorem genus_divisibility_of_surjective_quotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (A : Type*) [Group A] [Finite A]
    (hcard : Nat.card A = 2 ^ (primeDiscriminantFactorCount d - 1))
    (φ : ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* A) (hφ : Function.Surjective φ) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [← hcard]
  simpa [NumberField.classNumber] using Subgroup.card_dvd_of_surjective φ hφ

/-- The subgroup of ideal classes that are squares. In genus theory this is the
principal genus, and the quotient `Cl / Cl²` is the genus quotient. -/
noncomputable def squareClassSubgroup (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup (ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :=
  (powMonoidHom (α := ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) 2).range

/-- The standard genus formula for the principal-genus quotient
`Cl(𝓞(ℚ(√d))) / Cl(𝓞(ℚ(√d)))²`: its cardinality is `2 ^ (t - 1)`, where `t` is the
number of prime-discriminant factors. In the literature this is the statement that
`Cl / Cl²` is the genus group and each genus contains exactly `2 ^ (t - 1)` classes,
or equivalently `#Cl[2] = 2 ^ (t - 1)`. -/
def genusFormula (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : Prop :=
  Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
    2 ^ (primeDiscriminantFactorCount d - 1)

/-- If the principal-genus quotient has the standard genus-theory cardinality,
then the standard genus-theory divisibility follows from Lagrange's theorem. -/
theorem genus_divisibility_of_squareClassSubgroup_quotient_card
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcard : Nat.card (ClassGroup (𝓞 (Qsqrtd (d : ℚ))) ⧸ squareClassSubgroup d) =
      2 ^ (primeDiscriminantFactorCount d - 1)) :
    2 ^ (primeDiscriminantFactorCount d - 1) ∣
      NumberField.classNumber (Qsqrtd (d : ℚ)) := by
  rw [← hcard]
  simpa [NumberField.classNumber, Subgroup.index_eq_card] using
    (squareClassSubgroup d).index_dvd_card

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

end ClassGroup
end QuadraticNumberFields
