/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QuadraticNumberFields.ClassGroup.Genus.Index

/-!
# Signed Prime-Discriminant Factors

This file defines the signed prime-discriminant factors used to index genus
characters. The rational ramified-prime set in `Genus.Index` remains the
ramification and counting layer; this file records the corresponding signed
factors `q*` in the factorization of a fundamental discriminant.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

/-- The signed odd prime discriminant attached to a rational prime `p`:
`p* = p` for `p ≡ 1 mod 4` and `p* = -p` otherwise. -/
def oddPrimeDiscriminantFactor (p : ℕ) : ℤ :=
  if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

@[simp]
theorem natAbs_oddPrimeDiscriminantFactor (p : ℕ) :
    (oddPrimeDiscriminantFactor p).natAbs = p := by
  rw [oddPrimeDiscriminantFactor]
  split <;> simp

/-- The odd signed prime-discriminant factor is congruent to `1` modulo `4`. -/
theorem oddPrimeDiscriminantFactor_emod_four_eq_one {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    oddPrimeDiscriminantFactor p % 4 = 1 := by
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  rw [oddPrimeDiscriminantFactor]
  by_cases hp4 : p % 4 = 1
  · simp [hp4]
    omega
  · have hp4' : p % 4 = 3 := by omega
    simp [hp4]
    omega

/-- Odd signed prime-discriminant factors evaluate as Legendre symbols. -/
theorem kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym
    {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat (oddPrimeDiscriminantFactor p) a = legendreSym p (a : ℤ) := by
  have hD4 :=
    oddPrimeDiscriminantFactor_emod_four_eq_one (Fact.out : p.Prime) hp2
  rw [kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one _ hD4,
    natAbs_oddPrimeDiscriminantFactor, ← jacobiSym.legendreSym.to_jacobiSym]

/-- The signed `2`-primary prime discriminant attached to `ℚ(√d)`.

For squarefree `d` with `d % 4 ≠ 1`, this is one of `-4`, `8`, or `-8`.
When `2` is unramified this value is unused by `signedPrimeDiscriminantFactors`. -/
def twoPrimeDiscriminantFactor (d : ℤ) : ℤ :=
  if d % 2 = 0 then
    if d % 8 = 2 then 8 else -8
  else
    -4

/-- The `2`-primary signed prime discriminant has absolute value `4` or `8`. -/
theorem natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight (d : ℤ) :
    (twoPrimeDiscriminantFactor d).natAbs = 4 ∨
      (twoPrimeDiscriminantFactor d).natAbs = 8 := by
  rw [twoPrimeDiscriminantFactor]
  by_cases h2 : d % 2 = 0
  · by_cases h8 : d % 8 = 2
    · simp [h2, h8]
    · simp [h2, h8]
  · simp [h2]

private theorem kroneckerSymNat_eight_seven : kroneckerSymNat (8 : ℤ) 7 = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · refine (legendreSym.eq_one_iff 7 ?_).mpr ?_
    · intro h
      have hdiv : (7 : ℤ) ∣ (8 : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd 8 7).mp h
      norm_num at hdiv
    · refine ⟨(1 : ZMod 7), ?_⟩
      rw [mul_one, ← sub_eq_zero]
      change (((8 : ℤ) - 1 : ℤ) : ZMod 7) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
  · norm_num

private theorem kroneckerSymNat_neg_eight_three : kroneckerSymNat (-8 : ℤ) 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two]
  · refine (legendreSym.eq_one_iff 3 ?_).mpr ?_
    · intro h
      have hdiv : (3 : ℤ) ∣ (-8 : ℤ) :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd (-8) 3).mp h
      norm_num at hdiv
    · refine ⟨(1 : ZMod 3), ?_⟩
      rw [mul_one, ← sub_eq_zero]
      change (((-8 : ℤ) - 1 : ℤ) : ZMod 3) = 0
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
  · norm_num

/-- The `-4` Kronecker character is `1` on natural denominators congruent to `1`
modulo `4`. -/
theorem kroneckerSymNat_neg_four_eq_one_of_mod_four_eq_one {n : ℕ}
    (hn : n % 4 = 1) :
    kroneckerSymNat (-4 : ℤ) n = 1 := by
  haveI : Fact (((-4 : ℤ) % 4 = 0) ∨ ((-4 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (-4 : ℤ) n]
  rw [show (-4 : ℤ).natAbs = 4 by norm_num, hn]
  simp [kroneckerSymNat]

/-- The `8` Kronecker character is `1` on natural denominators congruent to `1`
or `7` modulo `8`. -/
theorem kroneckerSymNat_eight_eq_one_of_mod_eight_eq_one_or_seven {n : ℕ}
    (hn : n % 8 = 1 ∨ n % 8 = 7) :
    kroneckerSymNat (8 : ℤ) n = 1 := by
  haveI : Fact (((8 : ℤ) % 4 = 0) ∨ ((8 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (8 : ℤ) n]
  rw [show (8 : ℤ).natAbs = 8 by norm_num]
  rcases hn with hn | hn
  · rw [hn]
    simp [kroneckerSymNat]
  · rw [hn]
    exact kroneckerSymNat_eight_seven

/-- The `-8` Kronecker character is `1` on natural denominators congruent to `1`
or `3` modulo `8`. -/
theorem kroneckerSymNat_neg_eight_eq_one_of_mod_eight_eq_one_or_three {n : ℕ}
    (hn : n % 8 = 1 ∨ n % 8 = 3) :
    kroneckerSymNat (-8 : ℤ) n = 1 := by
  haveI : Fact (((-8 : ℤ) % 4 = 0) ∨ ((-8 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (-8 : ℤ) n]
  rw [show (-8 : ℤ).natAbs = 8 by norm_num]
  rcases hn with hn | hn
  · rw [hn]
    simp [kroneckerSymNat]
  · rw [hn]
    exact kroneckerSymNat_neg_eight_three

/-- The `2`-primary signed factor has Kronecker value `1` once the denominator
satisfies the congruence condition matching the selected `-4`, `8`, or `-8`
case. -/
theorem kroneckerSymNat_twoPrimeDiscriminantFactor_eq_one_of_mod_conditions
    {d : ℤ} {n : ℕ}
    (hodd : d % 2 ≠ 0 → n % 4 = 1)
    (height : d % 2 = 0 → d % 8 = 2 → n % 8 = 1 ∨ n % 8 = 7)
    (hneight : d % 2 = 0 → d % 8 ≠ 2 → n % 8 = 1 ∨ n % 8 = 3) :
    kroneckerSymNat (twoPrimeDiscriminantFactor d) n = 1 := by
  rw [twoPrimeDiscriminantFactor]
  by_cases hd2 : d % 2 = 0
  · by_cases hd8 : d % 8 = 2
    · simp only [hd2, hd8, ↓reduceIte]
      exact kroneckerSymNat_eight_eq_one_of_mod_eight_eq_one_or_seven
        (height hd2 hd8)
    · simp only [hd2, hd8, ↓reduceIte]
      exact kroneckerSymNat_neg_eight_eq_one_of_mod_eight_eq_one_or_three
        (hneight hd2 hd8)
  · simp only [hd2, ↓reduceIte]
    exact kroneckerSymNat_neg_four_eq_one_of_mod_four_eq_one (hodd hd2)

/-- The signed prime discriminant attached to a rational ramified prime `p`. -/
def primeDiscriminantFactor (d : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then twoPrimeDiscriminantFactor d else oddPrimeDiscriminantFactor p

@[simp]
theorem primeDiscriminantFactor_two (d : ℤ) :
    primeDiscriminantFactor d 2 = twoPrimeDiscriminantFactor d := by
  simp [primeDiscriminantFactor]

theorem primeDiscriminantFactor_of_ne_two {d : ℤ} {p : ℕ} (hp2 : p ≠ 2) :
    primeDiscriminantFactor d p = oddPrimeDiscriminantFactor p := by
  simp [primeDiscriminantFactor, hp2]

/-- Away from `2`, a prime-discriminant factor evaluates as the Legendre symbol. -/
theorem kroneckerSymNat_primeDiscriminantFactor_eq_legendreSym_of_ne_two
    {d : ℤ} {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat (primeDiscriminantFactor d p) a = legendreSym p (a : ℤ) := by
  rw [primeDiscriminantFactor_of_ne_two hp2,
    kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym hp2]

/-- A ramified rational prime divides the absolute value of its signed
prime-discriminant factor. -/
theorem dvd_natAbs_primeDiscriminantFactor_of_mem_ramifiedPrimes
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] {p : ℕ}
    (hp : p ∈ ramifiedPrimes d) :
    p ∣ (primeDiscriminantFactor d p).natAbs := by
  by_cases hp2 : p = 2
  · subst p
    rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with htwo | htwo
    · rw [primeDiscriminantFactor, if_pos rfl, htwo]
      norm_num
    · rw [primeDiscriminantFactor, if_pos rfl, htwo]
      norm_num
  · rw [primeDiscriminantFactor, if_neg hp2, natAbs_oddPrimeDiscriminantFactor]

section RamifiedDiscriminantFactors

variable (d : ℤ) [hdSq : Fact (Squarefree d)] [hdNe : Fact (d ≠ 1)]
include hdSq hdNe

/-- Distinct ramified rational primes give distinct signed prime-discriminant
factors. -/
theorem primeDiscriminantFactor_injOn_ramifiedPrimes :
    Set.InjOn (primeDiscriminantFactor d) (ramifiedPrimes d) := by
  intro p hp q hq hpq
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  have hq_prime : q.Prime := prime_of_mem_ramifiedPrimes hq
  by_cases hp2 : p = 2
  · subst p
    by_cases hq2 : q = 2
    · exact hq2.symm
    · have habs := congrArg Int.natAbs hpq
      simp [primeDiscriminantFactor, hq2] at habs
      rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with htwo | htwo
      · have hq4 : q = 4 := by omega
        rw [hq4] at hq_prime
        norm_num at hq_prime
      · have hq8 : q = 8 := by omega
        rw [hq8] at hq_prime
        norm_num at hq_prime
  · by_cases hq2 : q = 2
    · subst q
      have habs := congrArg Int.natAbs hpq
      simp [primeDiscriminantFactor, hp2] at habs
      rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with htwo | htwo
      · have hp4 : p = 4 := by omega
        rw [hp4] at hp_prime
        norm_num at hp_prime
      · have hp8 : p = 8 := by omega
        rw [hp8] at hp_prime
        norm_num at hp_prime
    · have habs := congrArg Int.natAbs hpq
      simpa [primeDiscriminantFactor, hp2, hq2] using habs

/-- The signed prime-discriminant factors of the field discriminant of `ℚ(√d)`.

This is the character-indexing refinement of `ramifiedPrimes d`: odd primes are
replaced by `p* = (-1)^((p-1)/2) p`, while the ramified prime `2` contributes
one of `-4`, `8`, or `-8`. -/
noncomputable def signedPrimeDiscriminantFactors : Finset ℤ :=
  (ramifiedPrimes d).image (primeDiscriminantFactor d)

@[simp]
theorem mem_signedPrimeDiscriminantFactors_of_mem_ramifiedPrimes
    {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    primeDiscriminantFactor d p ∈ signedPrimeDiscriminantFactors d :=
  Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- A signed prime-discriminant factor is either the `2`-primary factor or comes
from an odd ramified rational prime. -/
theorem eq_twoPrimeDiscriminantFactor_or_exists_oddPrimeDiscriminantFactor_of_mem
    {q : ℤ} (hq : q ∈ signedPrimeDiscriminantFactors d) :
    (q = twoPrimeDiscriminantFactor d ∧ 2 ∈ ramifiedPrimes d) ∨
      ∃ p : ℕ, p ∈ ramifiedPrimes d ∧ p.Prime ∧ p ≠ 2 ∧
        q = oddPrimeDiscriminantFactor p := by
  rw [signedPrimeDiscriminantFactors] at hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  by_cases hp2 : p = 2
  · subst p
    left
    exact ⟨primeDiscriminantFactor_two d, hp⟩
  · right
    exact ⟨p, hp, prime_of_mem_ramifiedPrimes hp, hp2,
      primeDiscriminantFactor_of_ne_two hp2⟩

/-- The signed prime-discriminant factors are counted by the ramified rational
primes. This is the bridge that keeps `ramifiedPrimeCount` as the genus-theory
parameter `t`. -/
theorem card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount :
    (signedPrimeDiscriminantFactors d).card = ramifiedPrimeCount d := by
  rw [signedPrimeDiscriminantFactors,
    Finset.card_image_of_injOn (primeDiscriminantFactor_injOn_ramifiedPrimes d),
    ramifiedPrimeCount_eq_card]

/-- The signed prime-discriminant factor set is nonempty exactly when the
ramified rational-prime set is nonempty. -/
theorem signedPrimeDiscriminantFactors_nonempty_iff :
    (signedPrimeDiscriminantFactors d).Nonempty ↔ (ramifiedPrimes d).Nonempty := by
  rw [← Finset.card_pos, card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount,
    ramifiedPrimeCount_eq_card, Finset.card_pos]

/-- Every signed prime-discriminant factor has absolute value different from `1`. -/
theorem natAbs_ne_one_of_mem_signedPrimeDiscriminantFactors {q : ℤ}
    (hq : q ∈ signedPrimeDiscriminantFactors d) :
    q.natAbs ≠ 1 := by
  rw [signedPrimeDiscriminantFactors] at hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  by_cases hp2 : p = 2
  · subst p
    intro h
    rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
    · rw [primeDiscriminantFactor, if_pos rfl, h4] at h
      norm_num at h
    · rw [primeDiscriminantFactor, if_pos rfl, h8] at h
      norm_num at h
  · intro h
    have hp1 : p = 1 := by
      simpa [primeDiscriminantFactor, hp2] using h
    exact hp_prime.ne_one hp1

/-- Every signed prime-discriminant factor has nonzero absolute value. -/
theorem natAbs_ne_zero_of_mem_signedPrimeDiscriminantFactors {q : ℤ}
    (hq : q ∈ signedPrimeDiscriminantFactors d) :
    q.natAbs ≠ 0 := by
  rw [signedPrimeDiscriminantFactors] at hq
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  have hp_prime : p.Prime := prime_of_mem_ramifiedPrimes hp
  by_cases hp2 : p = 2
  · subst p
    rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
    · simp [primeDiscriminantFactor, h4]
    · simp [primeDiscriminantFactor, h8]
  · simp [primeDiscriminantFactor, hp2, natAbs_oddPrimeDiscriminantFactor,
      hp_prime.ne_zero]

end RamifiedDiscriminantFactors

private theorem oddPrimeDiscriminantFactor_eq_legendreSym_neg_one_mul {p : ℕ}
    (hp : p.Prime) (hp_ne_two : p ≠ 2) :
    oddPrimeDiscriminantFactor p = @legendreSym p ⟨hp⟩ (-1) * (p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp_odd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp_ne_two
  rw [legendreSym.at_neg_one hp_ne_two, oddPrimeDiscriminantFactor]
  by_cases hp4 : p % 4 = 1
  · simp [hp4, ZMod.χ₄_nat_one_mod_four hp4]
  · have hp4' : p % 4 = 3 := by omega
    simp [hp4, ZMod.χ₄_nat_three_mod_four hp4']

private theorem prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd
    {n : ℕ} (hn : Squarefree n) (hn_odd : Odd n) :
    n.primeFactors.prod (fun p => oddPrimeDiscriminantFactor p) = ZMod.χ₄ n * (n : ℤ) := by
  have hprod_nat := Nat.prod_primeFactors_of_squarefree hn
  have hprod_int : n.primeFactors.prod (fun p : ℕ => (p : ℤ)) = (n : ℤ) := by
    rw [← Finset.prod_natCast, hprod_nat]
  rw [← hprod_int, ← jacobiSym.at_neg_one hn_odd,
    jacobiSym.eq_prod_primeFactors_of_squarefree (-1) hn, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hp_dvd : p ∣ n := (Nat.mem_primeFactors.mp hp).2.1
    have htwo_dvd : 2 ∣ n := by simpa [hp2] using hp_dvd
    obtain ⟨k, hk⟩ := hn_odd
    obtain ⟨m, hm⟩ := htwo_dvd
    omega
  simp [hp_prime, oddPrimeDiscriminantFactor_eq_legendreSym_neg_one_mul hp_prime hp_ne_two]

section ProductFormulaModFourEqOne

variable (d : ℤ) [hdSq : Fact (Squarefree d)] [hdNe : Fact (d ≠ 1)]
include hdSq hdNe

private theorem prod_signedPrimeDiscriminantFactors_eq_prod_ramifiedPrimes :
    (signedPrimeDiscriminantFactors d).prod id =
      (ramifiedPrimes d).prod (primeDiscriminantFactor d) := by
  rw [signedPrimeDiscriminantFactors]
  exact Finset.prod_image (primeDiscriminantFactor_injOn_ramifiedPrimes d)

private theorem prod_signedPrimeDiscriminantFactors_eq_discrFormula_of_mod_four_eq_one
    (hsq : Squarefree d) (hd4 : d % 4 = 1) :
    (signedPrimeDiscriminantFactors d).prod id = RingOfIntegers.discrFormula d := by
  rw [prod_signedPrimeDiscriminantFactors_eq_prod_ramifiedPrimes, ramifiedPrimes,
    RingOfIntegers.discr_formula d,
    RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
  have hn_odd : Odd d.natAbs := by
    rw [Nat.odd_iff]
    omega
  have hprod :=
    prod_oddPrimeDiscriminantFactor_primeFactors_of_squarefree_odd
      (Int.squarefree_natAbs.mpr hsq) hn_odd
  have hfactor :
      d.natAbs.primeFactors.prod (primeDiscriminantFactor d) =
        d.natAbs.primeFactors.prod (fun p => oddPrimeDiscriminantFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      have hp_dvd : p ∣ d.natAbs := (Nat.mem_primeFactors.mp hp).2.1
      have htwo_dvd : 2 ∣ d.natAbs := by simpa [hp2] using hp_dvd
      obtain ⟨k, hk⟩ := hn_odd
      obtain ⟨m, hm⟩ := htwo_dvd
      omega
    simp [primeDiscriminantFactor, hp_ne_two]
  rw [hfactor, hprod]
  by_cases hdneg : d < 0
  · have hn4 : d.natAbs % 4 = 3 := by omega
    rw [ZMod.χ₄_nat_three_mod_four hn4]
    omega
  · have hn4 : d.natAbs % 4 = 1 := by omega
    rw [ZMod.χ₄_nat_one_mod_four hn4]
    omega

end ProductFormulaModFourEqOne

private theorem primeFactors_four_eq_singleton_two : (4 : ℕ).primeFactors = {2} := by
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
  have hnot_four : ¬ 2 * 2 ∣ n :=
    Squarefree.not_mul_self_dvd_of_not_isUnit hn (p := 2) (by norm_num)
  have hnot_two_div : ¬ 2 ∣ n / 2 := by
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

section ProductFormulaModFourNeOne

variable (d : ℤ) [hdSq : Fact (Squarefree d)] [hdNe : Fact (d ≠ 1)]
include hdSq hdNe

private theorem prod_signedPrimeDiscriminantFactors_eq_discrFormula_of_mod_four_ne_one
    (hsq : Squarefree d) (hd4 : d % 4 ≠ 1) :
    (signedPrimeDiscriminantFactors d).prod id = RingOfIntegers.discrFormula d := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hdabs0 : d.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hd0
  rw [prod_signedPrimeDiscriminantFactors_eq_prod_ramifiedPrimes, ramifiedPrimes,
    RingOfIntegers.discr_formula d,
    RingOfIntegers.discrFormula_of_mod_four_ne_one hd4, Int.natAbs_mul]
  change (4 * d.natAbs).primeFactors.prod (primeDiscriminantFactor d) = 4 * d
  have htwo_mem : 2 ∈ (4 * d.natAbs).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, ⟨⟨2 * d.natAbs, by ring⟩,
      mul_ne_zero (by decide) hdabs0⟩⟩
  rw [← Finset.mul_prod_erase _ _ htwo_mem, primeFactors_four_mul_erase_two]
  have hfactor :
      (d.natAbs.primeFactors.erase 2).prod (primeDiscriminantFactor d) =
        (d.natAbs.primeFactors.erase 2).prod (fun p => oddPrimeDiscriminantFactor p) := by
    apply Finset.prod_congr rfl
    intro p hp
    have hp_ne_two : p ≠ 2 := (Finset.mem_erase.mp hp).1
    simp [primeDiscriminantFactor, hp_ne_two]
  rw [hfactor]
  by_cases hd2 : d % 2 = 0
  · have hsq_nat : Squarefree d.natAbs := Int.squarefree_natAbs.mpr hsq
    have h2dvd_int : (2 : ℤ) ∣ d := Int.dvd_of_emod_eq_zero hd2
    have h2dvd_abs : 2 ∣ d.natAbs := by
      have := (Int.natAbs_dvd_natAbs (a := (2 : ℤ)) (b := d)).mpr h2dvd_int
      simpa using this
    rw [primeFactors_erase_two_eq_primeFactors_div_two_of_squarefree hsq_nat h2dvd_abs]
    have hnot_four_abs : ¬ 2 ∣ d.natAbs / 2 := by
      have hnot_four : ¬ 2 * 2 ∣ d.natAbs :=
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
    simp only [primeDiscriminantFactor, twoPrimeDiscriminantFactor, hd2, ↓reduceIte]
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
      have hnot_four_int : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hsq
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
    simp only [primeDiscriminantFactor, twoPrimeDiscriminantFactor, hd2, ↓reduceIte]
    by_cases hdneg : d < 0
    · have hn4 : d.natAbs % 4 = 1 := by omega
      rw [ZMod.χ₄_nat_one_mod_four hn4]
      omega
    · have hn4 : d.natAbs % 4 = 3 := by omega
      rw [ZMod.χ₄_nat_three_mod_four hn4]
      omega

/-- For squarefree `d ≠ 1`, the product of the signed prime-discriminant factors
is the field discriminant. -/
theorem prod_signedPrimeDiscriminantFactors_eq_discrFormula :
    (signedPrimeDiscriminantFactors d).prod id = RingOfIntegers.discrFormula d := by
  by_cases hd4 : d % 4 = 1
  · exact prod_signedPrimeDiscriminantFactors_eq_discrFormula_of_mod_four_eq_one
      d (Fact.out : Squarefree d) hd4
  · exact prod_signedPrimeDiscriminantFactors_eq_discrFormula_of_mod_four_ne_one
      d (Fact.out : Squarefree d) hd4

end ProductFormulaModFourNeOne

end Genus
end ClassGroup
end QuadraticNumberFields
