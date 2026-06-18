/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.WeberData

/-!
# Framework Layer for the Baker-Heegner-Stark Proof

This file assembles the inert-prime branch of the Baker-Heegner-Stark theorem
from named interfaces: Weber/CM data, the integer-equation solution theorem, and
the finite gamma-to-prime lookup.  The final statement file imports this module
instead of carrying the inert-prime proof skeleton inline.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- **Gamma-to-prime lookup input.** If the Weber/CM gamma value associated to
an inert prime lies in the Heegner gamma list, then the prime is one of the six
positive odd Heegner primes. -/
theorem prime_mem_heegnerPrimeSet_of_associatedGamma
    (p : ℕ) (_hp : Nat.Prime p) (_hp8 : p % 8 = 3) {gamma : ℤ}
    (hassoc : IsAssociatedHeegnerGamma p gamma) (_hgamma : gamma ∈ heegnerGammaSet) :
    (p : ℤ) ∈ heegnerPrimeSet := by
  norm_num [IsAssociatedHeegnerGamma, heegnerGammaPrimePairs, heegnerPrimeSet] at hassoc ⊢
  omega

/-- If `p` is one of the positive odd Heegner primes, then `-p` is one of the
nine Heegner numbers. -/
theorem neg_natCast_mem_heegnerSet_of_natCast_mem_heegnerPrimeSet
    {p : ℕ} (hp : (p : ℤ) ∈ heegnerPrimeSet) :
    -(p : ℤ) ∈ heegnerSet := by
  norm_num [heegnerPrimeSet, heegnerSet] at hp ⊢
  omega

/-- The inert-prime core follows from the Weber/CM algebraic data and the
finite Diophantine/gamma lookup. -/
theorem inert_prime_core_of_weber_data
    (d : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hdp : d = -(p : ℤ))
    (hdata : StarkHeegnerAlgebraicData p) :
    d ∈ heegnerSet := by
  rw [hdp]
  exact neg_natCast_mem_heegnerSet_of_natCast_mem_heegnerPrimeSet
    (prime_mem_heegnerPrimeSet_of_associatedGamma p hp hp8 hdata.associatedGamma
      (gamma_mem_heegnerGammaSet_of_xy_solution hdata.xyEquation hdata.gamma_eq))

/-- **Baker-Heegner-Stark inert prime core.** This is the deep remaining input
after the elementary ideal-theoretic reductions and the genus-theory sieve: for
the inert-at-`2` prime family `d = -p`, `p ≡ 3 (mod 8)`, class number one
forces `d` to be a Heegner number.

The proof skeleton factors through the named Weber/CM data interface and the
finite Diophantine/gamma lookup. -/
theorem baker_heegner_stark_inert_prime_core
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hdp : d = -(p : ℤ))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  subst d
  change classNumberQsqrtd (-(p : ℤ)) = 1 at h
  rcases exists_weber_data_of_classNumber_one_inert_prime p hp hp8 h with ⟨hdata⟩
  exact inert_prime_core_of_weber_data (-(p : ℤ)) p hp hp8 rfl
    hdata

end Heegner
end QuadraticNumberFields
