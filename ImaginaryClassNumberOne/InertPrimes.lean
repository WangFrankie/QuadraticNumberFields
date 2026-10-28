/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import ImaginaryClassNumberOne.ClassNumberOne
import ImaginaryClassNumberOne.Weber.Heegner

/-!
# The Inert Prime Case of the Baker-Heegner-Stark Theorem

This file proves the inert prime case of the Baker-Heegner-Stark theorem under
`InertPrimeWeberHypothesis`, using the integral points on Heegner's curve and
the relation between their gamma values and the Heegner primes.
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- If the Weber/CM gamma value associated to
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

/-- An associated Heegner integral point implies that `-p` is a Heegner number. -/
theorem mem_heegnerSet_of_heegnerIntegralPoint
    (d : ℤ) (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hdp : d = -(p : ℤ))
    (P : HeegnerIntegralPoint p) :
    d ∈ heegnerSet := by
  rw [hdp]
  exact neg_natCast_mem_heegnerSet_of_natCast_mem_heegnerPrimeSet
    (prime_mem_heegnerPrimeSet_of_associatedGamma p hp hp8 P.associatedGamma
      (gamma_mem_heegnerGammaSet_of_xy_solution P.xyEquation P.gamma_eq))

/-- The inert prime case of Baker-Heegner-Stark under Weber's hypothesis:
if `d = -p` and `p ≡ 3 (mod 8)`, class number one implies that `d` is a
Heegner number. The case `p = 3` is treated separately. -/
theorem mem_heegnerSet_of_classNumber_eq_one_of_inert_prime
    (hweber : InertPrimeWeberHypothesis)
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (p : ℕ) (hp : Nat.Prime p) (hp8 : p % 8 = 3) (hdp : d = -(p : ℤ))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  subst d
  by_cases hp_ne_three : p ≠ 3
  · change NumberField.classNumber (Qsqrtd (((-(p : ℤ)) : ℤ) : ℚ)) = 1 at h
    rcases nonempty_heegnerIntegralPoint_of_classNumber_eq_one
      hweber p hp hp8 hp_ne_three h with ⟨P⟩
    exact mem_heegnerSet_of_heegnerIntegralPoint (-(p : ℤ)) p hp hp8 rfl
      P
  · have hp_eq_three : p = 3 := by omega
    subst p
    norm_num [heegnerSet]

end Heegner
end QuadraticNumberFields
