/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant

/-!
# Ramified Rational Primes for `Qsqrtd`

This file contains the common ramified-prime index used by both the ambiguous
class upper-bound layer and the genus-theory layer.
-/

open scoped NumberField QuadraticNumberFields.Splitting

namespace QuadraticNumberFields
namespace ClassGroup

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The rational primes ramified in `ℚ(√d)`: the distinct prime factors of the
field discriminant `NumberField.discr (Qsqrtd (d : ℚ))`. -/
noncomputable def ramifiedPrimes : Finset ℕ :=
  (NumberField.discr (Qsqrtd (d : ℚ))).natAbs.primeFactors

/-- The number of ramified rational primes in `ℚ(√d)`. This is the parameter `t`
in the narrow two-torsion upper bound and in genus theory. -/
noncomputable def ramifiedPrimeCount : ℕ :=
  (ramifiedPrimes d).card

/-- The index type for rational primes ramified in `ℚ(√d)`. -/
abbrev RamifiedPrimeIndex :=
  {p : ℕ // p ∈ ramifiedPrimes d}

/-- Membership in `ramifiedPrimes d` is membership in the prime-factor set of the
absolute field discriminant. -/
@[simp]
theorem mem_ramifiedPrimes_iff (p : ℕ) :
    p ∈ ramifiedPrimes d ↔
      p ∈ (NumberField.discr (Qsqrtd (d : ℚ))).natAbs.primeFactors :=
  Iff.rfl

/-- A prime divisor of `|d|` gives a ramified-prime index for `ℚ(√d)`. -/
noncomputable def ramifiedPrimeIndexOfNatAbsDvd
    {p : ℕ} (hp : p.Prime) (hpdvd : p ∣ d.natAbs) :
    RamifiedPrimeIndex d := by
  have hpdvd_int : (p : ℤ) ∣ d := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast hpdvd
  have hp_formula : (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
    by_cases hd4 : d % 4 = 1
    · rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
      exact hpdvd_int
    · rw [RingOfIntegers.discrFormula_of_mod_four_ne_one hd4]
      exact dvd_mul_of_dvd_right hpdvd_int 4
  have hp_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := by
    simpa [RingOfIntegers.discr_formula d] using hp_formula
  refine ⟨p, (mem_ramifiedPrimes_iff d p).mpr ?_⟩
  exact hp.mem_primeFactors (Int.natCast_dvd.mp hp_disc)
    (Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero (Qsqrtd (d : ℚ))))

/-- The ramified-prime set may be computed from the closed discriminant formula
for `ℚ(√d)`. -/
theorem ramifiedPrimes_eq_discrFormula_primeFactors :
    ramifiedPrimes d = (RingOfIntegers.discrFormula d).natAbs.primeFactors := by
  rw [ramifiedPrimes, RingOfIntegers.discr_formula d]

/-- The ramified-prime count is the cardinality of `ramifiedPrimes d`. -/
theorem ramifiedPrimeCount_eq_card :
    ramifiedPrimeCount d = (ramifiedPrimes d).card :=
  rfl

/-- For squarefree `d ≠ 1`, at least one rational prime ramifies. -/
theorem one_le_ramifiedPrimeCount :
    1 ≤ ramifiedPrimeCount d := by
  have hsq : Squarefree d := Fact.out
  have hd1 : d ≠ 1 := Fact.out
  have hd0 : d ≠ 0 := hsq.ne_zero
  rw [ramifiedPrimeCount, ramifiedPrimes, RingOfIntegers.discr_formula d,
    Finset.one_le_card, Nat.nonempty_primeFactors]
  by_cases hd4 : d % 4 = 1
  · rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    have hdm1 : d ≠ -1 := by rintro rfl; simp at hd4
    omega
  · rw [RingOfIntegers.discrFormula_of_mod_four_ne_one hd4]
    have h : (4 * d).natAbs = 4 * d.natAbs := by
      simpa using Int.natAbs_mul 4 d
    rw [h]
    have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    omega

/-- Members of `RamifiedPrimeIndex` are rational primes. -/
theorem prime_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    p.1.Prime :=
  Nat.prime_of_mem_primeFactors ((mem_ramifiedPrimes_iff d p.1).mp p.2)

/-- Members of `RamifiedPrimeIndex` divide the field discriminant. -/
theorem dvd_discr_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    (p.1 : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := by
  rw [← Int.dvd_natAbs]
  exact_mod_cast Nat.dvd_of_mem_primeFactors ((mem_ramifiedPrimes_iff d p.1).mp p.2)

/-- Members of `RamifiedPrimeIndex` divide the closed discriminant formula. -/
theorem dvd_discrFormula_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    (p.1 : ℤ) ∣ RingOfIntegers.discrFormula d := by
  rw [← RingOfIntegers.discr_formula d]
  exact dvd_discr_of_mem_ramifiedPrimeIndex d p

/-- Members of `RamifiedPrimeIndex` are ramified in `𝓞(ℚ(√d))`. -/
theorem isRamified_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    Ideal.IsRamifiedIn (𝔭(p.1)) 𝓞(d) := by
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
  exact (Splitting.isRamified_iff_dvd_disc d p.1).mpr
    (dvd_discr_of_mem_ramifiedPrimeIndex d p)

/-- When `d ≡ 1 (mod 4)`, the prime `2` is unramified in `ℚ(√d)`. -/
theorem ne_two_of_mem_ramifiedPrimeIndex_of_mod_four_eq_one
    (p : RamifiedPrimeIndex d) (hd4 : d % 4 = 1) :
    p.1 ≠ 2 := by
  intro hp2
  have hram := isRamified_of_mem_ramifiedPrimeIndex d p
  rw [hp2] at hram
  exact (Splitting.isRamified_two_iff_mod_four_ne_one d).mp hram hd4

/-- Every odd ramified rational prime of `ℚ(√d)` divides `d`. -/
theorem dvd_parameter_of_mem_ramifiedPrimeIndex_of_ne_two
    (p : RamifiedPrimeIndex d) (hp2 : p.1 ≠ 2) :
    (p.1 : ℤ) ∣ d := by
  letI : Fact p.1.Prime := ⟨prime_of_mem_ramifiedPrimeIndex d p⟩
  exact (Splitting.isRamified_iff_odd_dvd d p.1 hp2).mp
    (isRamified_of_mem_ramifiedPrimeIndex d p)

/-- Membership in `ramifiedPrimes d` is equivalent to ramification of `(p)` in
`𝓞(ℚ(√d))`. -/
theorem mem_ramifiedPrimes_iff_isRamifiedIn (p : ℕ) :
    p ∈ ramifiedPrimes d ↔ p.Prime ∧ Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) := by
  constructor
  · intro hp
    have hmem := Nat.mem_primeFactors.mp ((mem_ramifiedPrimes_iff d p).mp hp)
    letI : Fact p.Prime := ⟨hmem.1⟩
    have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := by
      rw [← Int.dvd_natAbs]
      exact_mod_cast hmem.2.1
    exact ⟨hmem.1, (Splitting.isRamified_iff_dvd_disc d p).mpr hp_dvd_disc⟩
  · rintro ⟨hp_prime, hram⟩
    letI : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) :=
      (Splitting.isRamified_iff_dvd_disc d p).mp hram
    rw [ramifiedPrimes]
    exact hp_prime.mem_primeFactors
      (by simpa using
        (Int.natAbs_dvd_natAbs (a := (p : ℤ))
          (b := NumberField.discr (Qsqrtd (d : ℚ)))).mpr hp_dvd_disc)
      (by rw [Int.natAbs_ne_zero]
          exact NumberField.discr_ne_zero (Qsqrtd (d : ℚ)))

/-- The number of `RamifiedPrimeIndex` terms is the ramified-prime count. -/
theorem fintype_card_ramifiedPrimeIndex :
    Fintype.card (RamifiedPrimeIndex d) = ramifiedPrimeCount d := by
  simp [RamifiedPrimeIndex, ramifiedPrimeCount]

/-- The closed discriminant formula and the field discriminant have the same
prime factors. -/
theorem mem_discrFormula_primeFactors_iff_fieldDiscrPrimeFactor (p : ℕ) :
    p ∈ (RingOfIntegers.discrFormula d).natAbs.primeFactors ↔
      p ∈ (NumberField.discr (Qsqrtd (d : ℚ))).natAbs.primeFactors := by
  rw [← ramifiedPrimes_eq_discrFormula_primeFactors d]
  rfl

/-! ### Concrete computation of the ramified-prime count

For squarefree `d`, the field discriminant is `d` when `d ≡ 1 (mod 4)` and
`4 * d` otherwise, so the ramified rational primes are the prime factors of
`|d|`, together with the wildly ramified prime `2` when `d ≡ 3 (mod 4)`.  The
classical subdivision of the even case by `d % 8` (prime discriminant `8`
versus `-8` at `2`) selects which genus character occurs at `2` but does not
affect the count.
-/

omit [Fact (d ≠ 1)] in
private theorem natAbs_primeFactors_four_mul :
    (4 * d).natAbs.primeFactors = {2} ∪ d.natAbs.primeFactors := by
  have hd0 : d.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Fact.out : Squarefree d).ne_zero
  have h4 : (4 : ℕ).primeFactors = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
  rw [Int.natAbs_mul, show (4 : ℤ).natAbs = 4 from rfl,
    Nat.primeFactors_mul (by norm_num) hd0, h4]

/-- When `d ≡ 1 (mod 4)`, the ramified rational primes are exactly the prime
factors of `|d|`: the prime `2` is unramified. -/
theorem ramifiedPrimes_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    ramifiedPrimes d = d.natAbs.primeFactors := by
  rw [ramifiedPrimes_eq_discrFormula_primeFactors d,
    RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]

/-- When `d ≡ 2 (mod 4)`, the ramified rational primes are exactly the prime
factors of `|d|`: the prime `2` ramifies but already divides `d`. -/
theorem ramifiedPrimes_of_mod_four_eq_two (hd4 : d % 4 = 2) :
    ramifiedPrimes d = d.natAbs.primeFactors := by
  have hd0 : d.natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (Fact.out : Squarefree d).ne_zero
  have h2 : 2 ∈ d.natAbs.primeFactors := by
    refine Nat.mem_primeFactors.mpr ⟨Nat.prime_two, ?_, hd0⟩
    exact Int.natAbs_dvd_natAbs.mpr (by omega : (2 : ℤ) ∣ d)
  rw [ramifiedPrimes_eq_discrFormula_primeFactors d,
    RingOfIntegers.discrFormula_of_mod_four_ne_one (by omega),
    natAbs_primeFactors_four_mul d,
    Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h2)]

/-- When `d ≡ 3 (mod 4)`, the ramified rational primes are the prime factors
of `|d|` together with the wildly ramified prime `2`. -/
theorem ramifiedPrimes_of_mod_four_eq_three (hd4 : d % 4 = 3) :
    ramifiedPrimes d = insert 2 d.natAbs.primeFactors := by
  rw [ramifiedPrimes_eq_discrFormula_primeFactors d,
    RingOfIntegers.discrFormula_of_mod_four_ne_one (by omega),
    natAbs_primeFactors_four_mul d, Finset.singleton_union]

/-- When `d ≡ 1 (mod 4)`, the ramified-prime count is the number of distinct
prime factors of `|d|`. -/
theorem ramifiedPrimeCount_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    ramifiedPrimeCount d = d.natAbs.primeFactors.card := by
  rw [ramifiedPrimeCount_eq_card, ramifiedPrimes_of_mod_four_eq_one d hd4]

/-- When `d ≡ 2 (mod 4)`, the ramified-prime count is the number of distinct
prime factors of `|d|`. -/
theorem ramifiedPrimeCount_of_mod_four_eq_two (hd4 : d % 4 = 2) :
    ramifiedPrimeCount d = d.natAbs.primeFactors.card := by
  rw [ramifiedPrimeCount_eq_card, ramifiedPrimes_of_mod_four_eq_two d hd4]

/-- When `d ≡ 3 (mod 4)`, the wild prime `2` contributes one ramified prime
beyond the prime factors of `|d|`. -/
theorem ramifiedPrimeCount_of_mod_four_eq_three (hd4 : d % 4 = 3) :
    ramifiedPrimeCount d = d.natAbs.primeFactors.card + 1 := by
  have h2 : 2 ∉ d.natAbs.primeFactors := by
    intro hmem
    have h2d : (2 : ℤ) ∣ d :=
      Int.natAbs_dvd_natAbs.mp (Nat.dvd_of_mem_primeFactors hmem)
    omega
  rw [ramifiedPrimeCount_eq_card, ramifiedPrimes_of_mod_four_eq_three d hd4,
    Finset.card_insert_of_notMem h2]

end Qsqrtd

end ClassGroup
end QuadraticNumberFields
