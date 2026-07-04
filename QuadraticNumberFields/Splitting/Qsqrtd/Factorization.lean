/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Splitting.Factorization
import QuadraticNumberFields.Splitting.Qsqrtd.Classification

/-!
# Ramified Prime Factorization for `Qsqrtd`

This file specializes the degree-two ramified-prime factorization API to
`𝓞(ℚ(√d))`.
-/

open scoped NumberField
open Ideal

namespace QuadraticNumberFields
namespace Splitting

section Qsqrtd

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => 𝓞(d)

/-- A ramified rational prime has factorization `(p)𝓞 = P ^ 2` for some prime
ideal `P` above `(p)`. -/
theorem exists_primeOver_map_eq_sq_of_isRamifiedIn
    (p : ℕ) [Fact p.Prime] (hr : Ideal.IsRamifiedIn (𝔭(p)) OK) :
    ∃ P' ∈ Ideal.primesOver (𝔭(p)) OK,
      Ideal.map (algebraMap ℤ OK) (𝔭(p)) = P' ^ 2 := by
  have hchar : ringChar ℤ ≠ 2 := by
    simp [ringChar.eq_zero]
  have hpbot : 𝔭(p) ≠ (⊥ : Ideal ℤ) := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : Nat.Prime p).ne_zero
  haveI : (𝔭(p)).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      ((Nat.prime_iff_prime_int.mp (Fact.out : Nat.Prime p)).irreducible)
  exact Ideal.map_eq_sq_of_isRamifiedIn (𝔭(p)) OK hchar hpbot hr

end Qsqrtd

end Splitting
end QuadraticNumberFields
