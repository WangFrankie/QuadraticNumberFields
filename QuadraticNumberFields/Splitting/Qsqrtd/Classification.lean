/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Qsqrtd.OddPrime
import QuadraticNumberFields.Splitting.Qsqrtd.Two

/-!
# Prime Splitting Classification for `Qsqrtd`

This file combines the odd-prime Legendre-symbol classification with the special
`p = 2` congruence classification.
-/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝓞(d)`, `𝔭(p)`, `θ(d)` are shared scoped notation.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard

/-- If `p ∣ d`, then `(p)` ramifies in `𝓞(ℚ(√d))`. -/
theorem isRamified_of_dvd
    (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) := by
  by_cases hp : p = 2
  · subst p
    apply isRamified_two_of_mod_four_ne_one d
    omega
  · exact isRamified_of_odd_dvd d p hp hpd

/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))`
satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ∨ Ideal.IsInertIn (𝔭(p)) 𝓞(d) ∨
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified (𝔭(p)) 𝓞(d) hchar hbot

/-- Complete splitting classification for `𝓞(ℚ(√d))`.

For odd primes this is the Legendre-symbol classification. At `p = 2`, the Legendre
symbol does not distinguish the two unramified odd congruence classes, so the statement
uses the standard `d mod 8` conditions. -/
theorem splitting_classification (p : ℕ) [Fact p.Prime] :
    (((p = 2 ∧ d % 8 = 1) ∨
        (p ≠ 2 ∧ ¬ (p : ℤ) ∣ d ∧ legendreSym p d = 1)) ∧
      e(p) = 1 ∧ f(p) = 1) ∨
    (((p = 2 ∧ d % 8 = 5) ∨
        (p ≠ 2 ∧ ¬ (p : ℤ) ∣ d ∧ legendreSym p d = -1)) ∧
      g(p) = 1 ∧ e(p) = 1) ∨
    (((p = 2 ∧ d % 4 ≠ 1) ∨
        (p ≠ 2 ∧ (p : ℤ) ∣ d)) ∧
      1 < e(p)) := by
  by_cases hp2 : p = 2
  · subst p
    by_cases hd4 : d % 4 = 1
    · have hd8_cases : d % 8 = 1 ∨ d % 8 = 5 := by omega
      rcases hd8_cases with hd8 | hd8
      · exact Or.inl ⟨Or.inl ⟨rfl, hd8⟩, isSplit_two_of_mod_eight_eq_one d hd8⟩
      · exact Or.inr
          (Or.inl ⟨Or.inl ⟨rfl, hd8⟩, isInert_two_of_mod_eight_eq_five d hd8⟩)
    · exact Or.inr
        (Or.inr ⟨Or.inl ⟨rfl, hd4⟩, isRamified_two_of_mod_four_ne_one d hd4⟩)
  · by_cases hpd : (p : ℤ) ∣ d
    · exact Or.inr (Or.inr ⟨Or.inr ⟨hp2, hpd⟩, isRamified_of_dvd d p hpd⟩)
    · have hpd0 : (d : ZMod p) ≠ 0 := fun h =>
        hpd ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h)
      rcases legendreSym.eq_one_or_neg_one p hpd0 with hleg | hleg
      · exact Or.inl ⟨Or.inr ⟨hp2, hpd, hleg⟩,
          (isSplit_iff_legendreSym_eq_one d p hp2 hpd).mpr hleg⟩
      · exact Or.inr (Or.inl ⟨Or.inr ⟨hp2, hpd, hleg⟩,
          (isInert_iff_legendreSym_eq_neg_one d p hp2 hpd).mpr hleg⟩)

end Splitting
end QuadraticNumberFields
