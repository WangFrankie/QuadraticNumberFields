/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Qsqrtd.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Ramification and the Discriminant for `Qsqrtd`

This file proves that a prime `p` ramifies in `𝓞(ℚ(√d))` if and only if
`p` divides the discriminant of `ℚ(√d)`.

## Main Results

* `isRamified_iff_dvd_disc`: `(p)` ramifies in `𝓞(ℚ(√d))` ↔
  `p ∣ NumberField.discr (ℚ(√d))`

Combined with the explicit discriminant formulas from `RingOfIntegers/Discriminant.lean`:
* `disc = 4d` when `d % 4 ≠ 1`
* `disc = d`  when `d % 4 = 1`

this gives an explicit characterization of ramified primes.

## Proof Strategy

Forward (ramified → p ∣ disc):
  ramified → legendreSym p d = 0 → p ∣ d → p ∣ disc (using disc formula)

Backward (p ∣ disc → ramified):
  p ∣ disc → p ∣ d (for odd p: gcd(p,4)=1; for p=2: case split) → ramified

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1. The discriminant formulas are Proposition 13.1.2; ramification is the
`p ∣ δ_F` case of Propositions 13.1.3 (odd `p`) and 13.1.4 (`p = 2`).
-/

open scoped NumberField
open Ideal

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝔭(p)` is shared from `Splitting.Defs`; `𝓞(d)` is shared from
-- `Splitting.Qsqrtd.Monogenic`.
/-- The discriminant of `ℚ(√d)`. -/
scoped notation3 "disc(" d ")" => NumberField.discr (Qsqrtd (d : ℚ))

private lemma dvd_of_odd_prime_dvd_four_mul
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {d : ℤ} (h : (p : ℤ) ∣ 4 * d) :
    (p : ℤ) ∣ d := by
  have hpNat : Nat.Prime p := Fact.out
  have hp4 : ¬ p ∣ 4 := by
    intro hp4
    have hp4pow : p ∣ 2 ^ 2 := by
      norm_num
      exact hp4
    have hp2dvd : p ∣ 2 := hpNat.dvd_of_dvd_pow hp4pow
    rcases (Nat.dvd_prime Nat.prime_two).mp hp2dvd with hp_one | hp_two
    · exact hpNat.ne_one hp_one
    · exact hp hp_two
  rcases Int.Prime.dvd_mul hpNat h with hp4' | hpd
  · exact False.elim (hp4 hp4')
  · exact (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := d)).mp (by simpa using hpd)

/-- For odd primes, ramification is equivalent to divisibility of the squarefree
parameter `d`. -/
theorem isRamified_iff_odd_dvd
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Ideal.IsRamifiedIn 𝔭(p) 𝓞(d) ↔ (p : ℤ) ∣ d := by
  constructor
  · intro hram
    change 1 < ramificationIdxIn 𝔭(p) 𝓞(d) at hram
    rcases splitting_classification d p with hsplit | hinert | hramified
    · have he : ramificationIdxIn 𝔭(p) 𝓞(d) = 1 := hsplit.2.1
      omega
    · have he : ramificationIdxIn 𝔭(p) 𝓞(d) = 1 := hinert.2.2
      omega
    · rcases hramified.1 with htwo | hodd
      · exact False.elim (hp htwo.1)
      · exact hodd.2
  · exact isRamified_of_dvd d p

/-- The prime `2` ramifies exactly when `d ≢ 1 (mod 4)`. -/
theorem isRamified_two_iff_mod_four_ne_one :
    Ideal.IsRamifiedIn 𝔭(2) 𝓞(d) ↔ d % 4 ≠ 1 := by
  constructor
  · intro hram hd4
    change 1 < ramificationIdxIn 𝔭(2) 𝓞(d) at hram
    rcases splitting_classification d 2 with hsplit | hinert | hramified
    · have he : ramificationIdxIn 𝔭(2) 𝓞(d) = 1 := hsplit.2.1
      omega
    · have he : ramificationIdxIn 𝔭(2) 𝓞(d) = 1 := hinert.2.2
      omega
    · rcases hramified.1 with htwo | hodd
      · exact htwo.2 hd4
      · exact hodd.1 rfl
  · exact isRamified_two_of_mod_four_ne_one d

/-- A prime ramifies in `𝓞(ℚ(√d))` if and only if it divides the field discriminant. -/
theorem isRamified_iff_dvd_disc (p : ℕ) [Fact p.Prime] :
    Ideal.IsRamifiedIn 𝔭(p) 𝓞(d) ↔ (p : ℤ) ∣ disc(d) := by
  constructor
  · intro hram
    by_cases hp : p = 2
    · subst p
      have hd4 := (isRamified_two_iff_mod_four_ne_one d).mp hram
      rw [RingOfIntegers.discr_of_mod_four_ne_one d hd4]
      exact ⟨2 * d, by ring⟩
    · have hpd := (isRamified_iff_odd_dvd d p hp).mp hram
      by_cases hd4 : d % 4 = 1
      · rw [RingOfIntegers.discr_of_mod_four_eq_one d hd4]
        exact hpd
      · rw [RingOfIntegers.discr_of_mod_four_ne_one d hd4]
        exact dvd_mul_of_dvd_right hpd 4
  · intro hdisc
    by_cases hp : p = 2
    · subst p
      by_cases hd4 : d % 4 = 1
      · rw [RingOfIntegers.discr_of_mod_four_eq_one d hd4] at hdisc
        have : ¬ (2 : ℤ) ∣ d := by omega
        exact False.elim (this hdisc)
      · exact isRamified_two_of_mod_four_ne_one d hd4
    · refine (isRamified_iff_odd_dvd d p hp).mpr ?_
      by_cases hd4 : d % 4 = 1
      · rw [RingOfIntegers.discr_of_mod_four_eq_one d hd4] at hdisc
        exact hdisc
      · rw [RingOfIntegers.discr_of_mod_four_ne_one d hd4] at hdisc
        exact dvd_of_odd_prime_dvd_four_mul p hp hdisc

end Splitting
end QuadraticNumberFields
