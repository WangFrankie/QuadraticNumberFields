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
formula for `ℚ(√d)`. For squarefree `d`, this is the genus-theory parameter
usually denoted `t`, the number of prime-discriminant factors of the fundamental
discriminant. -/
def primeDiscriminantFactorCount (d : ℤ) : ℕ :=
  (RingOfIntegers.discrFormula d).natAbs.primeFactors.card

/-! ## Discriminant prime factors -/

/-- The set of odd rational primes dividing the discriminant of `ℚ(√d)`.
These are precisely the odd primes at which the Kronecker symbol of the discriminant
vanishes — i.e., the ramified odd primes. By `isRamified_iff_kroneckerSymNat_discr_eq_zero`
and the odd-prime bridge `legendreSym_discFormula_eq_legendreSym_param_of_ne_two`,
for an odd prime `p` this is equivalent to `p ∣ d`. -/
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
  have hodd : RingOfIntegers.discrFormula d % 2 ≠ 0 := by
    rw [RingOfIntegers.discrFormula_of_mod_four_eq_one hd4]
    omega
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
theorem mem_oddPrimeDiscriminantDivisors_iff (d : ℤ) (p : ℕ) :
    p ∈ oddPrimeDiscriminantDivisors d ↔
      p ∈ ((RingOfIntegers.discrFormula d).natAbs.primeFactors) ∧ p ≠ 2 :=
  Finset.mem_filter

/-- Members of `oddPrimeDiscriminantDivisors d` are prime. -/
theorem prime_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors ((Finset.mem_filter.mp hp).left)

/-- Members of `oddPrimeDiscriminantDivisors d` are not `2`. -/
theorem ne_two_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) : p ≠ 2 :=
  (Finset.mem_filter.mp hp).right

/-- Members of `oddPrimeDiscriminantDivisors d` divide the discriminant formula. -/
theorem dvd_discr_of_mem_oddPrimeDiscriminantDivisors {d : ℤ} {p : ℕ}
    (hp : p ∈ oddPrimeDiscriminantDivisors d) :
    (p : ℤ) ∣ RingOfIntegers.discrFormula d := by
  have hmem := (Finset.mem_filter.mp hp).left
  have hmem' := Nat.mem_primeFactors.mp hmem
  have hdvd : p ∣ (RingOfIntegers.discrFormula d).natAbs := hmem'.2.1
  rw [← Int.dvd_natAbs]
  exact mod_cast hdvd

end ClassGroup
end QuadraticNumberFields
