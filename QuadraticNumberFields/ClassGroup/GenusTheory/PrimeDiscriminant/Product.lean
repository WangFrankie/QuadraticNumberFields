/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.PrimeDiscriminant.Basic

/-!
# Products Of Signed Prime Discriminants

This file proves that the signed prime discriminants indexed by the ramified
rational primes multiply to the field discriminant. It also records the
pairwise coprimality needed for the genus-theory CRT construction.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

private def primeDiscriminantFactorNat (d : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then twoPrimeDiscriminantFactor d else oddPrimeDiscriminantFactor p

private theorem prod_primeDiscriminantFactor_eq_prod_ramifiedPrimes
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p) =
      (ramifiedPrimes d).prod (primeDiscriminantFactorNat d) := by
  simpa [Finset.univ_eq_attach, primeDiscriminantFactor,
    primeDiscriminantFactorNat] using
    Finset.prod_attach (ramifiedPrimes d) (primeDiscriminantFactorNat d)

private theorem oddPrimeDiscriminantFactor_eq_legendreSym_neg_one_mul
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    oddPrimeDiscriminantFactor p = @legendreSym p ⟨hp⟩ (-1) * (p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  rw [legendreSym.at_neg_one hp2, oddPrimeDiscriminantFactor]
  by_cases hp4 : p % 4 = 1
  · simp [hp4, ZMod.χ₄_nat_one_mod_four hp4]
  · have hp4' : p % 4 = 3 := by omega
    simp [hp4, ZMod.χ₄_nat_three_mod_four hp4']

private theorem prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd
    {n : ℕ} (hn : Squarefree n) (hn_odd : Odd n) :
    n.primeFactors.prod oddPrimeDiscriminantFactor = ZMod.χ₄ n * (n : ℤ) := by
  have hprod_nat := Nat.prod_primeFactors_of_squarefree hn
  have hprod_int : n.primeFactors.prod (fun p : ℕ ↦ (p : ℤ)) = (n : ℤ) := by
    rw [← Finset.prod_natCast, hprod_nat]
  rw [← hprod_int, ← jacobiSym.at_neg_one hn_odd,
    jacobiSym.eq_prod_primeFactors_of_squarefree (-1) hn, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp2 : p ≠ 2 := by
    intro hp2
    have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have htwo_dvd : 2 ∣ n := by simpa [hp2] using hp_dvd
    obtain ⟨k, hk⟩ := hn_odd
    obtain ⟨m, hm⟩ := htwo_dvd
    omega
  simp [hp_prime, oddPrimeDiscriminantFactor_eq_legendreSym_neg_one_mul hp_prime hp2]

private theorem prod_primeDiscriminantFactor_eq_discrFormula_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hsq : Squarefree d) (hd4 : d % 4 = 1) :
    (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p) =
      RingOfIntegers.discrFormula d := by
  rw [prod_primeDiscriminantFactor_eq_prod_ramifiedPrimes, ramifiedPrimes,
    RingOfIntegers.discr_formula d,
    RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
  have hn_odd : Odd d.natAbs := by
    rw [Nat.odd_iff]
    omega
  have hprod :=
    prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd
      (Int.squarefree_natAbs.mpr hsq) hn_odd
  have hfactor :
      d.natAbs.primeFactors.prod (primeDiscriminantFactorNat d) =
        d.natAbs.primeFactors.prod oddPrimeDiscriminantFactor := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      intro hp2
      have hp_dvd : p ∣ d.natAbs := (Nat.mem_primeFactors.mp hp).2.1
      have htwo_dvd : 2 ∣ d.natAbs := by simpa [hp2] using hp_dvd
      obtain ⟨k, hk⟩ := hn_odd
      obtain ⟨m, hm⟩ := htwo_dvd
      omega
    simp [primeDiscriminantFactorNat, hp2]
  rw [hfactor, hprod]
  by_cases hdneg : d < 0
  · have hn4 : d.natAbs % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four hn4]
    omega
  · have hn4 : d.natAbs % 4 = 1 := by omega
    rw [ZMod.χ₄_nat_one_mod_four hn4]
    omega

private theorem primeFactors_four_eq_singleton_two :
    (4 : ℕ).primeFactors = {2} := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_pow]
  · exact Nat.Prime.primeFactors Nat.prime_two
  · norm_num

private theorem primeFactors_four_mul_erase_two (n : ℕ) :
    (4 * n).primeFactors.erase 2 = n.primeFactors.erase 2 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [Nat.primeFactors_mul (by decide : (4 : ℕ) ≠ 0) hn,
      primeFactors_four_eq_singleton_two]
    ext p
    by_cases hp2 : p = 2 <;> simp [hp2]

private theorem primeFactors_erase_two_eq_primeFactors_div_two_of_squarefree
    {n : ℕ} (hn : Squarefree n) (h2 : 2 ∣ n) :
    n.primeFactors.erase 2 = (n / 2).primeFactors := by
  have hnot_four : ¬2 * 2 ∣ n :=
    Squarefree.not_mul_self_dvd_of_not_isUnit hn (p := 2) (by norm_num)
  have hnot_two_div : ¬2 ∣ n / 2 := by
    intro h
    apply hnot_four
    obtain ⟨k, hk⟩ := h
    obtain ⟨m, hm⟩ := h2
    use k
    omega
  have hcop : Nat.Coprime 2 (n / 2) :=
    (Nat.prime_two.coprime_iff_not_dvd).mpr hnot_two_div
  have hn_eq : 2 * (n / 2) = n := by omega
  calc
    n.primeFactors.erase 2 = (2 * (n / 2)).primeFactors.erase 2 := by rw [hn_eq]
    _ = ({2} ∪ (n / 2).primeFactors).erase 2 := by
      rw [hcop.primeFactors_mul, Nat.Prime.primeFactors Nat.prime_two]
    _ = (n / 2).primeFactors := by
      ext p
      by_cases hp2 : p = 2 <;> simp [hp2, hnot_two_div]

private theorem prod_primeDiscriminantFactor_eq_discrFormula_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hsq : Squarefree d) (hd4 : d % 4 ≠ 1) :
    (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p) =
      RingOfIntegers.discrFormula d := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hdabs0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  rw [prod_primeDiscriminantFactor_eq_prod_ramifiedPrimes, ramifiedPrimes,
    RingOfIntegers.discr_formula d,
    RingOfIntegers.discrFormula_of_mod_four_ne_one hd4, Int.natAbs_mul]
  change (4 * d.natAbs).primeFactors.prod (primeDiscriminantFactorNat d) = 4 * d
  have htwo_mem : 2 ∈ (4 * d.natAbs).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, ⟨⟨2 * d.natAbs, by ring⟩,
      mul_ne_zero (by decide) hdabs0⟩⟩
  rw [← Finset.mul_prod_erase _ _ htwo_mem, primeFactors_four_mul_erase_two]
  have hfactor :
      (d.natAbs.primeFactors.erase 2).prod (primeDiscriminantFactorNat d) =
        (d.natAbs.primeFactors.erase 2).prod oddPrimeDiscriminantFactor := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp2 : p ≠ 2 := (Finset.mem_erase.mp hp).1
    simp [primeDiscriminantFactorNat, hp2]
  rw [hfactor]
  by_cases hd2 : d % 2 = 0
  · have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
    have h2dvd_int : (2 : ℤ) ∣ d := Int.dvd_of_emod_eq_zero hd2
    have h2dvd_abs : 2 ∣ d.natAbs := by
      have h := (Int.natAbs_dvd_natAbs (a := (2 : ℤ)) (b := d)).mpr h2dvd_int
      simpa using h
    rw [primeFactors_erase_two_eq_primeFactors_div_two_of_squarefree hsq_nat h2dvd_abs]
    have hnot_four_abs : ¬2 ∣ d.natAbs / 2 := by
      have hnot_four : ¬2 * 2 ∣ d.natAbs :=
        Squarefree.not_mul_self_dvd_of_not_isUnit hsq_nat (p := 2) (by norm_num)
      intro h
      apply hnot_four
      obtain ⟨k, hk⟩ := h
      obtain ⟨m, hm⟩ := h2dvd_abs
      use k
      omega
    have hquot_odd : Odd (d.natAbs / 2) := by
      rw [Nat.odd_iff]
      have hmod_ne : d.natAbs / 2 % 2 ≠ 0 := by
        intro hmod
        exact hnot_four_abs (Nat.dvd_of_mod_eq_zero hmod)
      omega
    have hquot_sq : Squarefree (d.natAbs / 2) :=
      Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd h2dvd_abs) hsq_nat
    have hprod :=
      prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd hquot_sq hquot_odd
    rw [hprod]
    simp only [primeDiscriminantFactorNat, twoPrimeDiscriminantFactor, hd2, if_pos]
    by_cases hd8 : d % 8 = 2
    · rw [if_pos hd8]
      by_cases hdneg : d < 0
      · have hq4 : d.natAbs / 2 % 4 = 3 := by omega
        rw [ZMod.χ₄_nat_three_mod_four hq4]
        omega
      · have hq4 : d.natAbs / 2 % 4 = 1 := by omega
        rw [ZMod.χ₄_nat_one_mod_four hq4]
        omega
    · rw [if_neg hd8]
      have hnot_four_int : ¬(4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hsq
      by_cases hdneg : d < 0
      · have hq4 : d.natAbs / 2 % 4 = 1 := by omega
        rw [ZMod.χ₄_nat_one_mod_four hq4]
        omega
      · have hq4 : d.natAbs / 2 % 4 = 3 := by omega
        rw [ZMod.χ₄_nat_three_mod_four hq4]
        omega
  · have hn_odd : Odd d.natAbs := by
      rw [Nat.odd_iff]
      omega
    have hnot_two_mem : 2 ∉ d.natAbs.primeFactors := by
      intro hmem
      have h2dvd_abs : 2 ∣ d.natAbs := (Nat.mem_primeFactors.mp hmem).2.1
      have h2dvd_int : (2 : ℤ) ∣ d := by
        rw [← Int.dvd_natAbs]
        exact_mod_cast h2dvd_abs
      exact hd2 (Int.emod_eq_zero_of_dvd h2dvd_int)
    rw [Finset.erase_eq_of_notMem hnot_two_mem]
    have hprod :=
      prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd
        (Int.squarefree_natAbs.mpr hsq) hn_odd
    rw [hprod]
    rw [show primeDiscriminantFactorNat d 2 = -4 by
      simp [primeDiscriminantFactorNat, twoPrimeDiscriminantFactor, hd2]]
    by_cases hdneg : d < 0
    · have hn4 : d.natAbs % 4 = 1 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hn4]
      omega
    · have hn4 : d.natAbs % 4 = 3 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hn4]
      omega

/-- The product of all signed prime discriminants is the field discriminant. -/
theorem prod_primeDiscriminantFactor_eq_discr
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p) =
      NumberField.discr (Qsqrtd (d : ℚ)) := by
  rw [RingOfIntegers.discr_formula d]
  by_cases hd4 : d % 4 = 1
  · exact prod_primeDiscriminantFactor_eq_discrFormula_of_mod_four_eq_one
      d (Fact.out : Squarefree d) hd4
  · exact prod_primeDiscriminantFactor_eq_discrFormula_of_mod_four_ne_one
      d (Fact.out : Squarefree d) hd4

/-- The positive product of the local conductors. -/
noncomputable def primeDiscriminantModulus
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℕ :=
  ∏ p : RamifiedPrimeIndex d, (primeDiscriminantFactor d p).natAbs

/-- Every local prime-discriminant modulus divides their total product. -/
theorem natAbs_primeDiscriminantFactor_dvd_primeDiscriminantModulus
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) :
    (primeDiscriminantFactor d p).natAbs ∣ primeDiscriminantModulus d := by
  rw [primeDiscriminantModulus]
  exact Finset.dvd_prod_of_mem
    (fun q : RamifiedPrimeIndex d ↦ (primeDiscriminantFactor d q).natAbs)
    (Finset.mem_univ p)

/-- The prime-discriminant modulus is the absolute field discriminant. -/
theorem primeDiscriminantModulus_eq_discr_natAbs
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    primeDiscriminantModulus d =
      (NumberField.discr (Qsqrtd (d : ℚ))).natAbs := by
  rw [primeDiscriminantModulus]
  calc
    (∏ p : RamifiedPrimeIndex d, (primeDiscriminantFactor d p).natAbs) =
        (∏ p : RamifiedPrimeIndex d, primeDiscriminantFactor d p).natAbs := by
      symm
      exact map_prod Int.natAbsHom (primeDiscriminantFactor d) Finset.univ
    _ = (NumberField.discr (Qsqrtd (d : ℚ))).natAbs := by
      rw [prod_primeDiscriminantFactor_eq_discr]

/-- The prime-discriminant modulus is nonzero. -/
theorem primeDiscriminantModulus_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    primeDiscriminantModulus d ≠ 0 := by
  rw [primeDiscriminantModulus, Finset.prod_ne_zero_iff]
  intro p _
  exact natAbs_primeDiscriminantFactor_ne_zero d p

/-- Distinct signed prime discriminants have coprime absolute values. -/
theorem pairwise_coprime_natAbs_primeDiscriminantFactor
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Pairwise fun p q : RamifiedPrimeIndex d ↦
      Nat.Coprime (primeDiscriminantFactor d p).natAbs
        (primeDiscriminantFactor d q).natAbs := by
  have two_coprime (r : RamifiedPrimeIndex d) (hr2 : r.1 ≠ 2) :
      Nat.Coprime (twoPrimeDiscriminantFactor d).natAbs r.1 := by
    have hbase : Nat.Coprime 2 r.1 :=
      (Nat.coprime_primes Nat.prime_two (prime_of_mem_ramifiedPrimeIndex d r)).2
        (Ne.symm hr2)
    rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
    · exact h4.symm ▸ hbase.pow_left 2
    · exact h8.symm ▸ hbase.pow_left 3
  intro p q hpq
  have hpq_val : p.1 ≠ q.1 := Subtype.coe_ne_coe.mpr hpq
  by_cases hp2 : p.1 = 2
  · have hq2 : q.1 ≠ 2 := fun hq2 ↦ hpq_val (hp2.trans hq2.symm)
    rw [primeDiscriminantFactor_of_val_eq_two d p hp2,
      natAbs_primeDiscriminantFactor_of_val_ne_two d q hq2]
    exact two_coprime q hq2
  · by_cases hq2 : q.1 = 2
    · rw [natAbs_primeDiscriminantFactor_of_val_ne_two d p hp2,
        primeDiscriminantFactor_of_val_eq_two d q hq2]
      exact (two_coprime p hp2).symm
    · rw [natAbs_primeDiscriminantFactor_of_val_ne_two d p hp2,
        natAbs_primeDiscriminantFactor_of_val_ne_two d q hq2]
      exact (Nat.coprime_primes (prime_of_mem_ramifiedPrimeIndex d p)
        (prime_of_mem_ramifiedPrimeIndex d q)).2 hpq_val

end GenusTheory
end ClassGroup
end QuadraticNumberFields
