/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Genus-Theory Discriminant Factors

This file defines the discriminant prime-factor count and the odd rational prime
divisors used by the genus-theory sieve.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-! ## Class-number-one sieve -/

/-- The number of distinct rational prime factors of the closed discriminant
formula for `ℚ(√d)`. For squarefree `d ≠ 1`, where `discrFormula d` is the actual
field discriminant, this is the genus-theory parameter usually denoted `t`, the
number of prime-discriminant factors of the fundamental discriminant. -/
def primeDiscriminantFactorCount (d : ℤ) : ℕ :=
  (RingOfIntegers.discrFormula d).natAbs.primeFactors.card

/-! ## Discriminant prime factors -/

/-- The odd rational prime divisors of the closed discriminant formula for `ℚ(√d)`.

When `d` is squarefree and `d ≠ 1` — so that `discrFormula d` is the actual field
discriminant — these are precisely the odd rational primes ramified in `ℚ(√d)`,
equivalently the odd primes dividing `d` (see
`dvd_param_of_mem_oddPrimeDiscriminantDivisors`). For general `d` this is just the
odd prime divisors of `discrFormula d`, which need not be the ramified primes
(e.g. `d = 18`, where `discrFormula 18 = 72` contributes `3` although `ℚ(√18) = ℚ(√2)`
is unramified at `3`). -/
def oddPrimeDiscriminantDivisors (d : ℤ) : Finset ℕ :=
  ((RingOfIntegers.discrFormula d).natAbs.primeFactors).filter fun p => p ≠ 2

/-- Cardinality bound: the number of odd prime discriminant divisors is at most
`primeDiscriminantFactorCount d`. -/
theorem card_oddPrimeDiscriminantDivisors_le (d : ℤ) :
    (oddPrimeDiscriminantDivisors d).card ≤ primeDiscriminantFactorCount d := by
  dsimp [oddPrimeDiscriminantDivisors, primeDiscriminantFactorCount]
  exact Finset.card_filter_le _ _

/-- If the field discriminant is odd, the odd discriminant divisors are all
prime discriminant divisors. -/
theorem oddPrimeDiscriminantDivisors_eq_primeFactors_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    oddPrimeDiscriminantDivisors d =
      (RingOfIntegers.discrFormula d).natAbs.primeFactors := by
  apply Finset.filter_true_of_mem
  intro p hp hp2
  subst hp2
  have hmem := Nat.mem_primeFactors.mp hp
  have h2dvd_nat : 2 ∣ (RingOfIntegers.discrFormula d).natAbs := hmem.2.1
  have h2dvd_int : (2 : ℤ) ∣ RingOfIntegers.discrFormula d := by
    rw [← Int.dvd_natAbs]
    exact_mod_cast h2dvd_nat
  obtain ⟨k, hk⟩ := h2dvd_int
  apply hodd
  rw [hk]
  omega

/-- In the odd field-discriminant branch, the number of odd discriminant divisors
is exactly the genus-theory prime-discriminant count. -/
theorem card_oddPrimeDiscriminantDivisors_eq_primeDiscriminantFactorCount_of_discr_odd
    (d : ℤ) (hodd : RingOfIntegers.discrFormula d % 2 ≠ 0) :
    (oddPrimeDiscriminantDivisors d).card = primeDiscriminantFactorCount d := by
  rw [oddPrimeDiscriminantDivisors_eq_primeFactors_of_discr_odd d hodd]
  rfl

/-- In the odd fundamental-discriminant branch, the Jacobi symbol modulo `|d|`
is the product of the Legendre symbols over the odd discriminant prime divisors.
This is the finite-product bridge used by the odd genus-character product
relation. -/
theorem jacobiSym_natAbs_eq_prod_oddPrimeDiscriminantDivisors_of_mod_four_eq_one
    (d a : ℤ) (hsq : Squarefree d) (hd4 : d % 4 = 1) :
    jacobiSym a d.natAbs =
      (oddPrimeDiscriminantDivisors d).prod
        (fun p => if hp : p.Prime then @legendreSym p ⟨hp⟩ a else 1) := by
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 :=
    (RingOfIntegers.discrFormula_odd_iff_mod_four_eq_one d).2 hd4
  rw [jacobiSym.eq_prod_primeFactors_of_squarefree a (Int.squarefree_natAbs.mpr hsq)]
  rw [oddPrimeDiscriminantDivisors_eq_primeFactors_of_discr_odd d hodd]
  rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]

/-- In the odd fundamental-discriminant branch, the Jacobi symbol modulo `|d|`
is the Kronecker symbol of the field discriminant. This is the form that connects
the odd product relation to splitting and ideal-norm arguments. -/
theorem jacobiSym_natAbs_eq_kroneckerSymNat_discrFormula_of_mod_four_eq_one
    (d : ℤ) (n : ℕ) (hd4 : d % 4 = 1) :
    jacobiSym (n : ℤ) d.natAbs = kroneckerSymNat (RingOfIntegers.discrFormula d) n := by
  rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
  exact (kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one d hd4 n).symm

/-- Characterization of membership in `oddPrimeDiscriminantDivisors`. -/
@[simp]
theorem mem_oddPrimeDiscriminantDivisors_iff (d : ℤ) (p : ℕ) :
    p ∈ oddPrimeDiscriminantDivisors d ↔
      p ∈ ((RingOfIntegers.discrFormula d).natAbs.primeFactors) ∧ p ≠ 2 :=
  Finset.mem_filter

/-- Members of `oddPrimeDiscriminantDivisors d` are prime. -/
theorem prime_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors ((mem_oddPrimeDiscriminantDivisors_iff d p).mp hp).left

/-- Members of `oddPrimeDiscriminantDivisors d` are not `2`. -/
theorem ne_two_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : p ≠ 2 :=
  ((mem_oddPrimeDiscriminantDivisors_iff d p).mp hp).right

/-- Members of `oddPrimeDiscriminantDivisors d` divide the discriminant formula. -/
theorem dvd_discr_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) :
    (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
  have hmem := ((mem_oddPrimeDiscriminantDivisors_iff d p).mp hp).left
  have hmem' := Nat.mem_primeFactors.mp hmem
  have hdvd : p ∣ (RingOfIntegers.discrFormula d).natAbs := hmem'.2.1
  rw [← Int.dvd_natAbs]
  exact mod_cast hdvd

/-- For `p ∈ oddPrimeDiscriminantDivisors d` (an odd prime), `(p : ℤ) ∣ d`.
For `d % 4 = 1`, `discrFormula d = d` directly. For `d % 4 ≠ 1`,
`discrFormula d = 4 * d`; since `p` is an odd prime, `p ∤ 4`, so `p ∣ d`.

For squarefree `d ≠ 1` this is the statement that the odd discriminant divisors
are exactly the odd primes dividing `d`. -/
theorem dvd_param_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : (p : ℤ) ∣ d := by
  have hp_ne_two : p ≠ 2 := ne_two_of_mem_oddPrimeDiscriminantDivisors hp
  have hp_prime : Nat.Prime p := prime_of_mem_oddPrimeDiscriminantDivisors hp
  have hp_dvd_disc : (p : ℤ) ∣ RingOfIntegers.discrFormula d :=
    dvd_discr_of_mem_oddPrimeDiscriminantDivisors hp
  by_cases hd4 : d % 4 = 1
  · rwa [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4] at hp_dvd_disc
  · rw [RingOfIntegers.discrFormula_of_mod_four_ne_one hd4] at hp_dvd_disc
    have hp_prime_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp_prime
    rcases hp_prime_int.dvd_or_dvd hp_dvd_disc with h4 | hd'
    · exfalso
      have hp_dvd_four_nat : p ∣ (2 : ℕ) ^ 2 := by
        have : p ∣ (4 : ℕ) := by exact_mod_cast h4
        rwa [show (4 : ℕ) = 2 ^ 2 by norm_num] at this
      exact hp_ne_two
        ((Nat.prime_dvd_prime_iff_eq hp_prime Nat.prime_two).mp
          (hp_prime.dvd_of_dvd_pow hp_dvd_four_nat))
    · exact hd'

end ClassGroup
end QuadraticNumberFields
