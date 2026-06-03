/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.Splitting.Classification

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

/-- The ring of integers of an abstract quadratic field is a quadratic extension
of `ℤ` in the sense needed by the splitting trichotomy. -/
instance ringOfIntegers_isQuadraticExtension
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℤ (𝓞 K) :=
  @Algebra.IsQuadraticExtension.mk ℤ _ _ _ _ _
    (inferInstance : Module.Free ℤ (𝓞 K))
    ((NumberField.RingOfIntegers.rank K).trans (by
      convert Algebra.IsQuadraticExtension.finrank_eq_two ℚ K using 1
      congr 1
      exact Subsingleton.elim _ _))

/-- For any abstract quadratic field and any rational prime `p`, `(p)` in
`𝓞 K` satisfies one of the numerical split, inert, or ramified conditions. -/
theorem split_or_inert_or_ramified_of_quadraticField
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]
    (p : ℕ) [Fact p.Prime] :
    (ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1 ∧
      inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1) ∨
    ((primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
      ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1) ∨
    1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) := by
  have hchar : ringChar ℤ ≠ 2 := by simp [ringChar.eq_zero]
  have hbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.split_or_inert_or_ramified _ _ hchar hbot

/-- The abstract splitting trichotomy together with a chosen standard model.

This packages the intended workflow for future explicit splitting theorems:
choose a standard squarefree parameter, compute in `Qsqrtd d`, and state the
splitting predicates back on the original `K`. -/
theorem exists_standardParameter_splitting_trichotomy
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]
    (p : ℕ) [Fact p.Prime] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃+* Qsqrtd (d : ℚ)) ∧
      ((ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1 ∧
        inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1) ∨
      ((primesOver (Ideal.span {(p : ℤ)}) (𝓞 K)).ncard = 1 ∧
        ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K) = 1) ∨
      1 < ramificationIdxIn (Ideal.span {(p : ℤ)}) (𝓞 K)) := by
  obtain ⟨d, hd_sf, hd_ne, hK⟩ := exists_ringEquiv_qsqrtd K
  exact ⟨d, hd_sf, hd_ne, hK,
    split_or_inert_or_ramified_of_quadraticField K p⟩

end Splitting
end QuadraticNumberFields
