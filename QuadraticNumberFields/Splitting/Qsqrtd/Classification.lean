/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Splitting.Defs
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic
import QuadraticNumberFields.Splitting.MinpolyMod
import QuadraticNumberFields.QuadraticField.RingOfIntegers

/-!
# Prime Splitting Classification for `Qsqrtd` via the Legendre Symbol

This file proves the main classification theorem: for a squarefree integer `d ≠ 1`
and a prime `p`, the splitting behavior of `(p)` in `𝓞(ℚ(√d))` is determined
by the Legendre symbol `(d/p)`.

## Main Results

### Odd primes (p ≠ 2, p ∤ d)

* `isSplit_iff_legendreSym_eq_one`: `(p)` splits ↔ `legendreSym p d = 1`
* `isInert_iff_legendreSym_eq_neg_one`: `(p)` is inert ↔ `legendreSym p d = -1`
* `isRamified_of_dvd`: `p ∣ d` → `(p)` ramifies

### All primes (unified)

* `splitting_classification`: The complete trichotomy via `legendreSym p d`.

### p = 2

* Handled via `MinpolyMod.splitting_at_two_*` (d mod 4 and d mod 8 case analysis)

## Proof Strategy

```
Classification.lean (𝓞 = ℤ[θ])
         |
Monogenic.lean (exponent θ = 1)
         |
primesOverSpanEquivMonicFactorsMod   ← Kummer-Dedekind from mathlib
         |
monicFactorsMod θ p
= irreducible factors of minpoly ℤ θ mod p
         |
MinpolyMod.lean (X² - d mod p)
         |
legendreSym p d                      ← from mathlib
```
-/
attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal
open Polynomial
open UniqueFactorizationMonoid

namespace QuadraticNumberFields

namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-! ## Odd primes, p ∤ d -/

/-! ## Basic trichotomy for `𝓞(ℚ(√d))` -/

private lemma ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two
    (p : ℕ) [Fact p.Prime] :
    ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 2 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  rw [Ideal.ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
    (p := Ideal.span {(p : ℤ)})
    (S := 𝓞 (Qsqrtd (d : ℚ))) hchar hbot]
  constructor
  · rintro ⟨hg, _, _⟩
    exact hg
  · intro hg
    rcases Ideal.efg_trichotomy (p := Ideal.span {(p : ℤ)})
        (S := 𝓞 (Qsqrtd (d : ℚ))) hchar hbot with h | h | h
    · exact h
    · omega
    · omega

private lemma primesOver_ncard_eq_monicFactorsMod_card (p : ℕ) [Fact p.Prime] :
    (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard =
      (RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p).card := by
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    (K := Qsqrtd (d : ℚ)) (θ := ringOfIntegersGenerator d)
    (not_dvd_exponent_generator d p)
  simpa using Set.ncard_congr' e

/-- Odd-prime split criterion in the `ℤ[√d]` branch of the ring of integers. -/
theorem isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hd4 : d % 4 ≠ 1) :
    Ideal.IsSplitIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) ↔
      legendreSym p d = 1 := by
  change ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      legendreSym p d = 1
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p =
        (normalizedFactors ((X ^ 2 - C (d : ZMod p)) : (ZMod p)[X])).toFinset := by
    simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).1 hd4]
  rw [hmin]
  constructor
  · intro hcard
    by_contra hleg
    have hcard_one :=
      normalizedFactors_X_sq_sub_C_card_eq_one_of_legendre_ne_one d p hpd hleg
    omega
  · intro hleg
    exact normalizedFactors_X_sq_sub_C_card_eq_two_of_legendre_eq_one d p hp hpd hleg

/-- Odd-prime split criterion in the `ℤ[(1+√d)/2]` branch of the ring of integers. -/
theorem isSplit_iff_legendreSym_eq_one_of_mod_four_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) (hd4 : d % 4 = 1) :
    Ideal.IsSplitIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) ↔
      legendreSym p d = 1 := by
  change ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ↔
      legendreSym p d = 1
  rw [ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_primesOver_ncard_eq_two d p,
    primesOver_ncard_eq_monicFactorsMod_card d p]
  have hmin :
      RingOfIntegers.monicFactorsMod (ringOfIntegersGenerator d) p =
        (normalizedFactors ((X ^ 2 - X - C ((d / 4 : ℤ) : ZMod p)) : (ZMod p)[X])).toFinset := by
    simp [RingOfIntegers.monicFactorsMod, (minpoly_generator d).2 hd4]
  rw [hmin]
  constructor
  · intro hcard
    by_contra hleg
    have hcard_one :=
      normalizedFactors_X_sq_sub_X_sub_C_card_eq_one_of_legendre_ne_one d p hpd
        (show d = 1 + 4 * (d / 4) by omega) hleg
    omega
  · intro hleg
    exact normalizedFactors_X_sq_sub_X_sub_C_card_eq_two_of_legendre_eq_one d p hp hpd
      (show d = 1 + 4 * (d / 4) by omega) hleg

-- TODO: split ↔ legendreSym = 1
theorem isSplit_iff_legendreSym_eq_one
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
    Ideal.IsSplitIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) ↔
      legendreSym p d = 1 := by
  by_cases hd4 : d % 4 = 1
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_eq_one d p hp hpd hd4
  · exact isSplit_iff_legendreSym_eq_one_of_mod_four_ne_one d p hp hpd hd4

-- TODO: inert ↔ legendreSym = -1
-- theorem isInert_iff_legendreSym_eq_neg_one
--     (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (hpd : ¬ (p : ℤ) ∣ d) :
--     (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
--       ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1
--       ↔ legendreSym p d = -1 := ...

-- TODO: p ∣ d → ramified
-- theorem isRamified_of_dvd
--     (p : ℕ) [Fact p.Prime] (hpd : (p : ℤ) ∣ d) :
--     1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := ...



/-- For a squarefree `d ≠ 1` and any prime `p`, the ideal `(p)` in `𝓞(ℚ(√d))`
satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) ∨
    Ideal.IsInertIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) ∨
    Ideal.IsRamifiedIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified _ _ hchar hbot

/-! ## Unified classification -/

-- TODO: complete trichotomy
-- theorem splitting_classification (p : ℕ) [Fact p.Prime] :
--     ((legendreSym p d = 1  ∧
--        ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1 ∧
--        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
--      (legendreSym p d = -1 ∧
--        (primesOver (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ)))).ncard = 1 ∧
--        ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))) = 1) ∨
--      (legendreSym p d = 0  ∧
--        1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 (Qsqrtd (d : ℚ))))) := ...

end Splitting
end QuadraticNumberFields
