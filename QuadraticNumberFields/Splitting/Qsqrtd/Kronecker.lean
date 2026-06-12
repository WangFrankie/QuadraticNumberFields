/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Mathlib.NumberTheory.LegendreSymbol.KroneckerSymbol
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant

/-!
# Kronecker-Symbol Splitting Classification for `Qsqrtd`

This file repackages the prime splitting classification for `𝓞(ℚ(√d))` using the
Kronecker value of the field discriminant `NumberField.discr (ℚ(√d))`: the ideal
`(p)` splits, is inert, or ramifies according as `kroneckerSymNat (disc(d)) p`
is `1`, `-1`, or `0`. The closed discriminant formula is owned by
`RingOfIntegers.Discriminant` and used here through `RingOfIntegers.discrFormula`
and `RingOfIntegers.discr_formula`.

## Main Results

* `isSplit_iff_kroneckerSymNat_discr_eq_one`: `(p)` splits ↔ `(disc(d) / p) = 1`.
* `isInert_iff_kroneckerSymNat_discr_eq_neg_one`: `(p)` is inert ↔
  `(disc(d) / p) = -1`.
* `isRamified_iff_kroneckerSymNat_discr_eq_zero`: `(p)` ramifies ↔
  `(disc(d) / p) = 0`.

## Reference

K. Ireland, M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed.,
Chapter 13, §1. Propositions 13.1.3 and 13.1.4 state the splitting of `p` through
the symbol `(δ_F / p)` of the field discriminant `δ_F`.
-/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

-- `𝓞(d)` and `𝔭(p)` are shared scoped notation.
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) 𝓞(d)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) 𝓞(d)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) 𝓞(d)).ncard

/-! ## Arithmetic bridge from the discriminant to the parameter -/

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma legendreSym_discFormula_eq_legendreSym_param_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    legendreSym p (RingOfIntegers.discrFormula d) = legendreSym p d := by
  unfold RingOfIntegers.discrFormula
  by_cases hd4 : d % 4 = 1
  · rw [if_pos hd4]
  · have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
      simpa using zmod_two_ne_zero_of_prime_ne_two p hp2
    rw [if_neg hd4, show (4 : ℤ) * d = 2 ^ 2 * d by ring, legendreSym.mul,
      legendreSym.sq_one' p h2, one_mul]

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
private lemma kroneckerSymNat_discFormula_eq_legendreSym_param_of_ne_two
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    kroneckerSymNat (RingOfIntegers.discrFormula d) p = legendreSym p d := by
  rw [kroneckerSymNat_eq_legendreSym_of_ne_two _ hp2,
    legendreSym_discFormula_eq_legendreSym_param_of_ne_two d hp2]

/-! ## Private combined Kronecker classification -/

private theorem splitting_classification_kronecker_formula (p : ℕ) [Fact p.Prime] :
    (kroneckerSymNat (RingOfIntegers.discrFormula d) p = 1 ∧
      e(p) = 1 ∧ f(p) = 1) ∨
    (kroneckerSymNat (RingOfIntegers.discrFormula d) p = -1 ∧
      g(p) = 1 ∧ e(p) = 1) ∨
    (kroneckerSymNat (RingOfIntegers.discrFormula d) p = 0 ∧ 1 < e(p)) := by
  rcases splitting_classification d p with ⟨hcond, hef⟩ | ⟨hcond, hge⟩ | ⟨hcond, he⟩
  · refine Or.inl ⟨?_, hef⟩
    rcases hcond with ⟨rfl, hd8⟩ | ⟨hp2, -, hleg⟩
    · have hd4 : d % 4 = 1 := by omega
      have hD8 : RingOfIntegers.discrFormula d % 8 = 1 := by
        simp [RingOfIntegers.discrFormula, hd4, hd8]
      rw [kroneckerSymNat_two]
      exact (kroneckerTwo_eq_one_iff (RingOfIntegers.discrFormula d)).mpr (Or.inl hD8)
    · rw [kroneckerSymNat_discFormula_eq_legendreSym_param_of_ne_two d hp2]
      exact hleg
  · refine Or.inr (Or.inl ⟨?_, hge⟩)
    rcases hcond with ⟨rfl, hd8⟩ | ⟨hp2, -, hleg⟩
    · have hd4 : d % 4 = 1 := by omega
      have hD8 : RingOfIntegers.discrFormula d % 8 = 5 := by
        simp [RingOfIntegers.discrFormula, hd4, hd8]
      rw [kroneckerSymNat_two]
      exact (kroneckerTwo_eq_neg_one_iff (RingOfIntegers.discrFormula d)).mpr
        (Or.inr hD8)
    · rw [kroneckerSymNat_discFormula_eq_legendreSym_param_of_ne_two d hp2]
      exact hleg
  · refine Or.inr (Or.inr ⟨?_, he⟩)
    rcases hcond with ⟨rfl, hd4⟩ | ⟨hp2, hpd⟩
    · have hD2 : RingOfIntegers.discrFormula d % 2 = 0 := by
        unfold RingOfIntegers.discrFormula
        rw [if_neg hd4]
        omega
      rw [kroneckerSymNat_two]
      exact (kroneckerTwo_eq_zero_iff (RingOfIntegers.discrFormula d)).mpr hD2
    · rw [kroneckerSymNat_discFormula_eq_legendreSym_param_of_ne_two d hp2]
      exact (legendreSym.eq_zero_iff p d).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd)

private theorem splitting_classification_kronecker_discr (p : ℕ) [Fact p.Prime] :
    (kroneckerSymNat (disc(d)) p = 1 ∧ e(p) = 1 ∧ f(p) = 1) ∨
    (kroneckerSymNat (disc(d)) p = -1 ∧ g(p) = 1 ∧ e(p) = 1) ∨
    (kroneckerSymNat (disc(d)) p = 0 ∧ 1 < e(p)) := by
  rw [RingOfIntegers.discr_formula d]
  exact splitting_classification_kronecker_formula d p

/-! ## Iff wrappers -/

/-- `(p)` splits in `𝓞(ℚ(√d))` exactly when `NumberField.discr (ℚ(√d))` has Kronecker
value `1` at `p`. -/
theorem isSplit_iff_kroneckerSymNat_discr_eq_one (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔ kroneckerSymNat (disc(d)) p = 1 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  constructor
  · intro hsplit
    have hgef := (Ideal.ramificationIdxIn_eq_one_and_inertiaDegIn_eq_one_iff_efg
      (𝔭(p)) 𝓞(d) hchar hbot).mp hsplit
    rcases splitting_classification_kronecker_discr d p with
      ⟨hk, -, -⟩ | ⟨-, hg, -⟩ | ⟨-, he⟩
    · exact hk
    · omega
    · omega
  · intro hk
    rcases splitting_classification_kronecker_discr d p with
      ⟨-, he, hf⟩ | ⟨hk', -, -⟩ | ⟨hk', -⟩
    · exact ⟨he, hf⟩
    · omega
    · omega

/-- `(p)` is inert in `𝓞(ℚ(√d))` exactly when `NumberField.discr (ℚ(√d))` has
Kronecker value `-1` at `p`. -/
theorem isInert_iff_kroneckerSymNat_discr_eq_neg_one (p : ℕ) [Fact p.Prime] :
    Ideal.IsInertIn (𝔭(p)) 𝓞(d) ↔ kroneckerSymNat (disc(d)) p = -1 := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  constructor
  · intro hinert
    have hgef := (Ideal.ncard_primesOver_eq_one_and_ramificationIdxIn_eq_one_iff_efg
      (𝔭(p)) 𝓞(d) hchar hbot).mp hinert
    rcases splitting_classification_kronecker_discr d p with
      ⟨-, -, hf⟩ | ⟨hk, -, -⟩ | ⟨-, he⟩
    · omega
    · exact hk
    · omega
  · intro hk
    rcases splitting_classification_kronecker_discr d p with
      ⟨hk', -, -⟩ | ⟨-, hg, he⟩ | ⟨hk', -⟩
    · omega
    · exact ⟨hg, he⟩
    · omega

/-- `(p)` ramifies in `𝓞(ℚ(√d))` exactly when `NumberField.discr (ℚ(√d))` has
Kronecker value `0` at `p`. -/
theorem isRamified_iff_kroneckerSymNat_discr_eq_zero (p : ℕ) [Fact p.Prime] :
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) ↔ kroneckerSymNat (disc(d)) p = 0 := by
  constructor
  · intro hram
    have he : 1 < e(p) := hram
    rcases splitting_classification_kronecker_discr d p with
      ⟨-, he', -⟩ | ⟨-, -, he'⟩ | ⟨hk, -⟩
    · omega
    · omega
    · exact hk
  · intro hk
    rcases splitting_classification_kronecker_discr d p with
      ⟨hk', -, -⟩ | ⟨hk', -, -⟩ | ⟨-, he⟩
    · omega
    · omega
    · exact he

end Splitting
end QuadraticNumberFields
