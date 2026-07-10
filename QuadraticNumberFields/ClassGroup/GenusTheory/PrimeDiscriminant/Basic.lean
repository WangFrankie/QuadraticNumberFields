/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import QNFMathlib.NumberTheory.LegendreSymbol.KroneckerSymbolPeriodicity
import QuadraticNumberFields.ClassGroup.RamifiedPrimes

/-!
# Signed Prime Discriminants

This file attaches the signed prime discriminant `p*` to each ramified rational
prime of `ℚ(√d)`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra

/-- The signed odd prime discriminant attached to `p`. -/
def oddPrimeDiscriminantFactor (p : ℕ) : ℤ :=
  if p % 4 = 1 then (p : ℤ) else -(p : ℤ)

@[simp]
theorem natAbs_oddPrimeDiscriminantFactor (p : ℕ) :
    (oddPrimeDiscriminantFactor p).natAbs = p := by
  rw [oddPrimeDiscriminantFactor]
  split <;> simp

/-- The odd signed prime discriminant is congruent to `1` modulo `4`. -/
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

/-- Odd signed prime discriminants evaluate as Legendre symbols. -/
theorem kroneckerSymNat_oddPrimeDiscriminantFactor_eq_legendreSym
    {p a : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat (oddPrimeDiscriminantFactor p) a = legendreSym p (a : ℤ) := by
  have hD4 := oddPrimeDiscriminantFactor_emod_four_eq_one (Fact.out : p.Prime) hp2
  rw [kroneckerSymNat_eq_jacobiSym_natAbs_of_emod_four_eq_one _ hD4,
    natAbs_oddPrimeDiscriminantFactor, ← jacobiSym.legendreSym.to_jacobiSym]

/-- The `2`-primary signed prime discriminant attached to `ℚ(√d)`. -/
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

private theorem kroneckerSymNat_eight_seven :
    kroneckerSymNat (8 : ℤ) 7 = 1 := by decide +kernel

private theorem kroneckerSymNat_neg_eight_three :
    kroneckerSymNat (-8 : ℤ) 3 = 1 := by decide +kernel

private theorem kroneckerSymNat_neg_four_eq_one_of_mod_four_eq_one
    {n : ℕ} (hn : n % 4 = 1) :
    kroneckerSymNat (-4 : ℤ) n = 1 := by
  haveI : Fact (((-4 : ℤ) % 4 = 0) ∨ ((-4 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (-4 : ℤ) n]
  rw [show (-4 : ℤ).natAbs = 4 by norm_num, hn]
  simp [kroneckerSymNat]

private theorem kroneckerSymNat_eight_eq_one_of_mod_eight_eq_one_or_seven
    {n : ℕ} (hn : n % 8 = 1 ∨ n % 8 = 7) :
    kroneckerSymNat (8 : ℤ) n = 1 := by
  haveI : Fact (((8 : ℤ) % 4 = 0) ∨ ((8 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (8 : ℤ) n]
  rw [show (8 : ℤ).natAbs = 8 by norm_num]
  rcases hn with hn | hn
  · rw [hn]
    simp [kroneckerSymNat]
  · rw [hn]
    exact kroneckerSymNat_eight_seven

private theorem kroneckerSymNat_neg_eight_eq_one_of_mod_eight_eq_one_or_three
    {n : ℕ} (hn : n % 8 = 1 ∨ n % 8 = 3) :
    kroneckerSymNat (-8 : ℤ) n = 1 := by
  haveI : Fact (((-8 : ℤ) % 4 = 0) ∨ ((-8 : ℤ) % 4 = 1)) := ⟨by norm_num⟩
  rw [← kroneckerSymNat_mod_natAbs_eq (-8 : ℤ) n]
  rw [show (-8 : ℤ).natAbs = 8 by norm_num]
  rcases hn with hn | hn
  · rw [hn]
    simp [kroneckerSymNat]
  · rw [hn]
    exact kroneckerSymNat_neg_eight_three

/-- The `2`-primary character is trivial under its matching congruence conditions. -/
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

/-- The signed prime discriminant attached to a ramified rational prime. -/
def primeDiscriminantFactor (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) : ℤ :=
  if p.1 = 2 then twoPrimeDiscriminantFactor d else oddPrimeDiscriminantFactor p.1

theorem primeDiscriminantFactor_of_val_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) (hp2 : p.1 = 2) :
    primeDiscriminantFactor d p = twoPrimeDiscriminantFactor d := by
  simp [primeDiscriminantFactor, hp2]

theorem primeDiscriminantFactor_of_val_ne_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) (hp2 : p.1 ≠ 2) :
    primeDiscriminantFactor d p = oddPrimeDiscriminantFactor p.1 := by
  simp [primeDiscriminantFactor, hp2]

@[simp]
theorem natAbs_primeDiscriminantFactor_of_val_ne_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) (hp2 : p.1 ≠ 2) :
    (primeDiscriminantFactor d p).natAbs = p.1 := by
  rw [primeDiscriminantFactor_of_val_ne_two d p hp2,
    natAbs_oddPrimeDiscriminantFactor]

/-- Every signed prime discriminant is congruent to `0` or `1` modulo `4`. -/
theorem primeDiscriminantFactor_emod_four_eq_zero_or_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) :
    primeDiscriminantFactor d p % 4 = 0 ∨
      primeDiscriminantFactor d p % 4 = 1 := by
  by_cases hp2 : p.1 = 2
  · left
    rw [primeDiscriminantFactor_of_val_eq_two d p hp2, twoPrimeDiscriminantFactor]
    by_cases hd2 : d % 2 = 0
    · simp only [hd2, if_pos]
      by_cases hd8 : d % 8 = 2 <;> simp [hd8]
    · simp [hd2]
  · right
    rw [primeDiscriminantFactor_of_val_ne_two d p hp2]
    exact oddPrimeDiscriminantFactor_emod_four_eq_one
      (prime_of_mem_ramifiedPrimeIndex d p) hp2

/-- Every signed prime discriminant has nonzero absolute value. -/
theorem natAbs_primeDiscriminantFactor_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : RamifiedPrimeIndex d) :
    (primeDiscriminantFactor d p).natAbs ≠ 0 := by
  by_cases hp2 : p.1 = 2
  · rw [primeDiscriminantFactor_of_val_eq_two d p hp2]
    rcases natAbs_twoPrimeDiscriminantFactor_eq_four_or_eight d with h4 | h8
    · simp [h4]
    · simp [h8]
  · rw [natAbs_primeDiscriminantFactor_of_val_ne_two d p hp2]
    exact (prime_of_mem_ramifiedPrimeIndex d p).ne_zero

end GenusTheory
end ClassGroup
end QuadraticNumberFields
