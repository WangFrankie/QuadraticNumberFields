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

The symbol-form theorems in `Splitting/Qsqrtd/Kronecker.lean` are the canonical
API. The character form is a presentation refinement: every `kroneckerCharacter`
evaluation rewrites back to `kroneckerSymNat` (or `kroneckerSym`) via the
evaluation lemmas, after which the symbol-form theorems apply unchanged.

## Main Results

This module provides the `Fact` instance that lets `kroneckerCharacter (disc(d))`
elaborate at quadratic-field discriminants. The canonical splitting statements
remain the symbol-form theorems in `Splitting/Qsqrtd/Kronecker.lean`; character
goals reduce to those theorems by rewriting with `kroneckerCharacter_apply_intCast`.
-/

attribute [-instance] DivisionRing.toRatAlgebra
open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

/-! ## Auto-discharge instance for the discriminant `Fact` -/

/-- Auto-discharged `Fact` for the `NumberField.discr` version, via
`RingOfIntegers.discr_formula`. -/
instance (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Fact (NumberField.discr (Qsqrtd ((d : ℤ) : ℚ)) % 4 = 0 ∨
          NumberField.discr (Qsqrtd ((d : ℤ) : ℚ)) % 4 = 1) :=
  ⟨by
    rw [RingOfIntegers.discr_formula d]
    exact RingOfIntegers.discrFormula_emod_four_eq_zero_or_one d⟩

/-! ## Character-form examples over the canonical symbol theorems -/

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

example (p : ℕ) [Fact p.Prime] :
    Ideal.IsSplitIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = 1 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isSplit_iff_kroneckerSymNat_discr_eq_one d p

example (p : ℕ) [Fact p.Prime] :
    Ideal.IsInertIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = -1 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isInert_iff_kroneckerSymNat_discr_eq_neg_one d p

example (p : ℕ) [Fact p.Prime] :
    Ideal.IsRamifiedIn (𝔭(p)) 𝓞(d) ↔
      kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = 0 := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]
  exact isRamified_iff_kroneckerSymNat_discr_eq_zero d p

example (p : ℕ) [Fact p.Prime] :
    (kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = 1 ↔
      kroneckerSymNat (disc(d)) p = 1) := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]

example (p : ℕ) [Fact p.Prime] :
    (kroneckerCharacter (disc(d)) ((p : ℤ) : ZMod (disc(d)).natAbs) = -1 ↔
      kroneckerSymNat (disc(d)) p = -1) := by
  rw [kroneckerCharacter_apply_intCast, kroneckerSym_natCast]

end Splitting
end QuadraticNumberFields
