/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.RingOfIntegers
import QuadraticNumberFields.Splitting.Defs

/-!
# Abstract Prime-Splitting Interface for Quadratic Fields

This file gives the first abstract-field wrappers around the splitting API.
The explicit Legendre-symbol computations remain in
`QuadraticNumberFields.Splitting.Classification`; the results here expose the
same splitting conditions for an arbitrary `[QuadraticField K]`, stated directly
with mathlib's ramification API.

This module is part of the work-in-progress `Sketch` surface while the full
Legendre-symbol classification is still incomplete.
-/

open scoped NumberField
open Ideal

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and the explicit `Algebra ℚ K`.
-- NOTE: This is a file-local workaround matching the abstract quadratic-field surface.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace Splitting

section AbstractField

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]

local notation3 "𝔭(" p ")" => Ideal.span ({(p : ℤ)} : Set ℤ)
local notation3 "e(" p ")" => ramificationIdxIn (𝔭(p)) (𝓞 K)
local notation3 "f(" p ")" => inertiaDegIn (𝔭(p)) (𝓞 K)
local notation3 "g(" p ")" => (primesOver (𝔭(p)) (𝓞 K)).ncard

/-- For any abstract quadratic field and any rational prime `p`, `(p)` in
`𝓞 K` satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified_of_quadraticField
    (p : ℕ) [Fact p.Prime] :
    (e(p) = 1 ∧ f(p) = 1) ∨ (g(p) = 1 ∧ e(p) = 1) ∨ 1 < e(p) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : 𝔭(p) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified (𝔭(p)) (𝓞 K) hchar hbot

/-- The abstract splitting trichotomy together with a chosen standard model.

This packages the intended workflow for future explicit splitting theorems:
choose a standard squarefree parameter, compute in `Qsqrtd d`, and state the
splitting predicates back on the original `K`. -/
theorem exists_standardParameter_splitting_trichotomy
    (p : ℕ) [Fact p.Prime] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃+* Qsqrtd (d : ℚ)) ∧
      ((e(p) = 1 ∧ f(p) = 1) ∨ (g(p) = 1 ∧ e(p) = 1) ∨ 1 < e(p)) := by
  obtain ⟨d, hd_sf, hd_ne, hK⟩ := exists_ringEquiv_qsqrtd K
  exact ⟨d, hd_sf, hd_ne, hK,
    split_or_inert_or_ramified_of_quadraticField K p⟩

end AbstractField

end Splitting
end QuadraticNumberFields
