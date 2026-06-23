/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

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

/-- The signed prime discriminant attached to a rational ramified prime `p`. -/
def primeDiscriminantFactor (d : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then twoPrimeDiscriminantFactor d else oddPrimeDiscriminantFactor p

/-- Distinct ramified rational primes give distinct signed prime-discriminant
factors. -/
theorem primeDiscriminantFactor_injOn_ramifiedPrimes (d : ℤ) :
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
def signedPrimeDiscriminantFactors (d : ℤ) : Finset ℤ :=
  (ramifiedPrimes d).image (primeDiscriminantFactor d)

@[simp]
theorem mem_signedPrimeDiscriminantFactors_of_mem_ramifiedPrimes
    {d : ℤ} {p : ℕ} (hp : p ∈ ramifiedPrimes d) :
    primeDiscriminantFactor d p ∈ signedPrimeDiscriminantFactors d :=
  Finset.mem_image.mpr ⟨p, hp, rfl⟩

/-- The signed prime-discriminant factors are counted by the ramified rational
primes. This is the bridge that keeps `ramifiedPrimeCount` as the genus-theory
parameter `t`. -/
theorem card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount (d : ℤ) :
    (signedPrimeDiscriminantFactors d).card = ramifiedPrimeCount d := by
  rw [signedPrimeDiscriminantFactors,
    Finset.card_image_of_injOn (primeDiscriminantFactor_injOn_ramifiedPrimes d),
    ramifiedPrimeCount_eq_card]

/-- The signed prime-discriminant factor set is nonempty exactly when the
ramified rational-prime set is nonempty. -/
theorem signedPrimeDiscriminantFactors_nonempty_iff (d : ℤ) :
    (signedPrimeDiscriminantFactors d).Nonempty ↔ (ramifiedPrimes d).Nonempty := by
  rw [← Finset.card_pos, card_signedPrimeDiscriminantFactors_eq_ramifiedPrimeCount,
    ramifiedPrimeCount_eq_card, Finset.card_pos]

/-- For squarefree `d ≠ 1`, the product of the signed prime-discriminant factors
is the field discriminant. -/
theorem prod_signedPrimeDiscriminantFactors_eq_discrFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (signedPrimeDiscriminantFactors d).prod id = RingOfIntegers.discrFormula d := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
