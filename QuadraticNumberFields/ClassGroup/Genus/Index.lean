/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant

/-!
# Genus-Theory Index: ramified primes and the ramified-prime count `t`

This file is the index layer of the genus theory. It defines the finite set of
rational primes ramified in `ℚ(√d)` and the genus-theory parameter `t`, the number
of ramified rational primes.

The set `ramifiedPrimes d` is the distinct prime factors of the field discriminant
`discrFormula d`, so it includes `2` whenever `2` ramifies (`d % 4 ≠ 1`, where
`discrFormula d = 4 * d`). It is the full prime-discriminant index, valid for both
odd and even field discriminants, and `t = ramifiedPrimeCount d` is its
cardinality.

Mathematically, `t` is the number of prime discriminants in the factorization
`D = d₁ ⋯ d_t` of the fundamental discriminant. Every distinct rational prime
dividing `D` contributes exactly one prime discriminant (an odd prime `p`
contributes `p* = (-1)^((p-1)/2) p`; the prime `2`, when ramified, contributes one
of `-4, 8, -8`), so `t` equals the number of distinct prime factors of `D` and no
explicit prime-discriminant factorization is needed to compute it.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

/-- The rational primes ramified in `ℚ(√d)`: the distinct prime factors of the field
discriminant `discrFormula d`.

This includes `2` exactly when `2` ramifies (`d % 4 ≠ 1`, where
`discrFormula d = 4 * d`), so it indexes the full prime-discriminant factorization. -/
-- TODO change to NumberField.discr (Qsqrtd (d : ℚ)) maybe
def ramifiedPrimes (d : ℤ) : Finset ℕ :=
  (RingOfIntegers.discrFormula d).natAbs.primeFactors

/-- The genus-theory parameter `t`: the number of prime-discriminant factors of the
field discriminant for `ℚ(√d)`, equivalently the number of distinct rational primes
ramified in `ℚ(√d)`. -/
def ramifiedPrimeCount (d : ℤ) : ℕ :=
  (ramifiedPrimes d).card

@[simp]
theorem mem_ramifiedPrimes_iff (d : ℤ) (p : ℕ) :
    p ∈ ramifiedPrimes d ↔ p ∈ (RingOfIntegers.discrFormula d).natAbs.primeFactors :=
  Iff.rfl

theorem ramifiedPrimeCount_eq_card (d : ℤ) :
    ramifiedPrimeCount d = (ramifiedPrimes d).card :=
  rfl

/-- Members of `ramifiedPrimes d` are prime. -/
theorem prime_of_mem_ramifiedPrimes {d : ℤ} {p : ℕ}
    (hp : p ∈ ramifiedPrimes d) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors hp

/-- Members of `ramifiedPrimes d` divide the field discriminant. -/
theorem dvd_discr_of_mem_ramifiedPrimes {d : ℤ} {p : ℕ}
    (hp : p ∈ ramifiedPrimes d) :
    (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
  have hmem := Nat.mem_primeFactors.mp hp
  rw [← Int.dvd_natAbs]
  exact_mod_cast hmem.2.1

/-- Membership in `ramifiedPrimes d` is equivalent to ramification of `(p)` in
`𝓞(ℚ(√d))`. -/
theorem mem_ramifiedPrimes_iff_isRamifiedIn (d : ℤ) (p : ℕ)
    [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    p ∈ ramifiedPrimes d ↔ Nat.Prime p ∧ Ideal.IsRamifiedIn 𝔭(p) 𝓞(d) := by
  constructor
  · intro hp
    have hp_prime : Nat.Prime p := prime_of_mem_ramifiedPrimes hp
    letI : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd_disc : (p : ℤ) ∣ NumberField.discr (Qsqrtd (d : ℚ)) := by
      rw [RingOfIntegers.discr_formula d]
      exact dvd_discr_of_mem_ramifiedPrimes hp
    exact ⟨hp_prime, (Splitting.isRamified_iff_dvd_disc d p).mpr hp_dvd_disc⟩
  · rintro ⟨hp_prime, hram⟩
    letI : Fact p.Prime := ⟨hp_prime⟩
    have hp_dvd_disc : (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
      rw [← RingOfIntegers.discr_formula d]
      exact (Splitting.isRamified_iff_dvd_disc d p).mp hram
    rw [ramifiedPrimes]
    apply hp_prime.mem_primeFactors
    · simpa using
        (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := RingOfIntegers.discrFormula d)).mpr
          hp_dvd_disc
    · rw [Int.natAbs_ne_zero, ← RingOfIntegers.discr_formula d]
      exact NumberField.discr_ne_zero (Qsqrtd (d : ℚ))

/-- For squarefree `d ≠ 1` the field discriminant has absolute value `> 1`, so there is
at least one ramified prime and `t ≥ 1`. This makes the genus exponent `t - 1`
well-behaved. -/
theorem one_le_ramifiedPrimeCount (d : ℤ)
    [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    1 ≤ ramifiedPrimeCount d := by
  have hsq : Squarefree d := Fact.out
  have hd1 : d ≠ 1 := Fact.out
  have hd0 : d ≠ 0 := hsq.ne_zero
  rw [ramifiedPrimeCount, ramifiedPrimes, Finset.one_le_card,
    Nat.nonempty_primeFactors]
  by_cases hd4 : d % 4 = 1
  · rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    -- `d % 4 = 1` rules out `d = -1`, and `d ≠ 0, 1`, hence `|d| > 1`.
    have hdm1 : d ≠ -1 := by rintro rfl; simp at hd4
    omega
  · rw [RingOfIntegers.discrFormula_of_mod_four_ne_one hd4]
    -- `|4 * d| = 4 * |d| ≥ 4 > 1` since `d ≠ 0`.
    have : (4 * d).natAbs = 4 * d.natAbs := by
      rw [Int.natAbs_mul]; rfl
    rw [this]
    have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd0
    omega

end Genus
end ClassGroup
end QuadraticNumberFields
