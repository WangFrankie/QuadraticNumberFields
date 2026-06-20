/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters

/-!
# Ideal Avoidance for Genus Characters

This file isolates the ideal-avoidance input needed by the odd-prime genus
characters: every ideal class should admit an integral representative whose
absolute norm is prime to the odd rational primes dividing the field
discriminant.

The main theorem is the standard Dedekind-domain approximation step behind
the genus-character construction. It is stated here as the next proof boundary
for the pure ideal-theoretic route.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-- **Ideal-avoidance representative theorem.** Every ideal class has an
integral ideal representative whose absolute norm is prime to every odd rational
prime dividing the field discriminant.

This is the Dedekind-domain approximation input needed before the odd genus
characters can be made unconditional. -/
theorem exists_mk0_eq_and_forall_not_dvd_absNorm_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      ClassGroup.mk0 I = C ∧
        ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) := by
  sorry

/-- Single-prime form of the ideal-avoidance representative theorem. -/
theorem exists_mk0_eq_and_not_dvd_absNorm_of_mem_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : ℕ) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      ClassGroup.mk0 I = C ∧
        ¬ (p : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) := by
  rcases exists_mk0_eq_and_forall_not_dvd_absNorm_oddPrimeDiscriminantDivisors d C with
    ⟨I, hC, hI⟩
  exact ⟨I, hC, hI ⟨p, hp_disc⟩⟩

/-- The ideal-avoidance representative theorem makes the restricted class-group
map on prime-to-`p` ideals surjective for every odd discriminant divisor `p`. -/
theorem mk0OnPrimeToNormIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : ℕ) [Fact p.Prime] (hp_disc : p ∈ oddPrimeDiscriminantDivisors d) :
    Function.Surjective (mk0OnPrimeToNormIdeals d p) :=
  mk0OnPrimeToNormIdeals_surjective_of_forall_mk0_eq_of_not_dvd_absNorm d p
    fun C => exists_mk0_eq_and_not_dvd_absNorm_of_mem_oddPrimeDiscriminantDivisors
      d p hp_disc C

end ClassGroup
end QuadraticNumberFields
