/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Mathlib.NumberTheory.DirichletCharacter.Kronecker
import QuadraticNumberFields.Splitting.Qsqrtd.Discriminant
import QuadraticNumberFields.Splitting.Qsqrtd.Kronecker

/-!
# Kronecker Character Splitting Classification for `Qsqrtd`

This file repackages the prime splitting classification of `𝓞(ℚ(√d))` in terms
of the Dirichlet character attached to `NumberField.discr (ℚ(√d))`, alongside
the existing symbol-form statements in `Splitting/Qsqrtd/Kronecker.lean`.

The character form is a presentation refinement: every `kroneckerCharacter`
evaluation is rewritten back to `kroneckerSymNat` (or `kroneckerSym`) via the
evaluation lemmas, and the existing symbol-form theorems are then reused
unchanged.

## Main Results

* `disc_formula_emod_four_eq_zero_or_one`: the closed discriminant formula has
  residue `0` or `1` modulo `4`.
* `isSplit_iff_kroneckerCharacter_discr_eq_one`: `(p)` splits ↔
  the discriminant character has value `1` at `p`.
* `isInert_iff_kroneckerCharacter_discr_eq_neg_one`: inert ↔ value `-1`.
* `isRamified_iff_kroneckerCharacter_discr_eq_zero`: ramified ↔ value `0`.
-/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

/-! ## Auto-discharge instance for the discriminant `Fact` -/

/-- The closed quadratic discriminant formula has residue `0` or `1` modulo `4`. -/
lemma disc_formula_emod_four_eq_zero_or_one (d : ℤ) [Fact (Squarefree d)] :
    (if d % 4 = 1 then d else 4 * d) % 4 = 0 ∨
    (if d % 4 = 1 then d else 4 * d) % 4 = 1 := by
  by_cases h : d % 4 = 1
  · refine Or.inr ?_
    rw [if_pos h]; exact h
  · refine Or.inl ?_
    rw [if_neg h]
    exact Int.mul_emod_right 4 d

/-- Auto-discharged `Fact` for the `NumberField.discr` version, via
`RingOfIntegers.discr_formula`. -/
instance (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (NumberField.discr (Qsqrtd ((d : ℤ) : ℚ)) % 4 = 0 ∨
          NumberField.discr (Qsqrtd ((d : ℤ) : ℚ)) % 4 = 1) :=
  ⟨by
    rw [RingOfIntegers.discr_formula d]
    exact disc_formula_emod_four_eq_zero_or_one d⟩

/-! ## Character-form splitting iff theorems -/

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- `(p)` splits in `𝓞(ℚ(√d))` exactly when the Kronecker character of
`NumberField.discr (ℚ(√d))` evaluates to `1` at the prime `p`. -/
theorem isSplit_iff_kroneckerCharacter_discr_eq_one (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = 1 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isSplit_iff_kroneckerSymNat_discr_eq_one d p

/-- `(p)` is inert in `𝓞(ℚ(√d))` exactly when the Kronecker character of
`NumberField.discr (ℚ(√d))` evaluates to `-1` at the prime `p`. -/
theorem isInert_iff_kroneckerCharacter_discr_eq_neg_one (p : ℕ) [Fact p.Prime] :
    Ideal.IsInertIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = -1 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isInert_iff_kroneckerSymNat_discr_eq_neg_one d p

/-- `(p)` ramifies in `𝓞(ℚ(√d))` exactly when the Kronecker character of
`NumberField.discr (ℚ(√d))` evaluates to `0` at the prime `p`. -/
theorem isRamified_iff_kroneckerCharacter_discr_eq_zero (p : ℕ) [Fact p.Prime] :
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = 0 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isRamified_iff_kroneckerSymNat_discr_eq_zero d p

end Splitting
end QuadraticNumberFields
