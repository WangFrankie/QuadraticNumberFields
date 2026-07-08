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

/-- The ramified-prime set may be computed from the closed discriminant formula
for `ℚ(√d)`. -/
theorem ramifiedPrimes_eq_discrFormula_primeFactors :
    ramifiedPrimes d = (RingOfIntegers.discrFormula d).natAbs.primeFactors := by
  rw [ramifiedPrimes, RingOfIntegers.discr_formula d]

/-- The ramified-prime count is the cardinality of `ramifiedPrimes d`. -/
theorem ramifiedPrimeCount_eq_card :
    ramifiedPrimeCount d = (ramifiedPrimes d).card :=
  rfl

/-- Members of `RamifiedPrimeIndex` are rational primes. -/
theorem prime_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    p.1.Prime :=
  Nat.prime_of_mem_primeFactors ((mem_ramifiedPrimes_iff d p.1).mp p.2)

/-- Members of `RamifiedPrimeIndex` divide the field discriminant. -/
theorem dvd_discr_of_mem_ramifiedPrimeIndex (p : RamifiedPrimeIndex d) :
    (p.1 : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := by
  have hmem := Nat.mem_primeFactors.mp ((mem_ramifiedPrimes_iff d p.1).mp p.2)
  rw [← Int.dvd_natAbs]
  exact_mod_cast hmem.2.1

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

end Qsqrtd

end ClassGroup
end QuadraticNumberFields
