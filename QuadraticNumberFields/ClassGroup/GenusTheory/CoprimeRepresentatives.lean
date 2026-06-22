/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters

/-!
# Coprime Class Representatives for Genus Characters

This file isolates the coprime-representative input needed by the odd-prime
genus characters: every ideal class should admit an integral representative
whose absolute norm is prime to a prescribed finite set of rational primes.

The main theorem is the standard Dedekind-domain approximation step behind
the genus-character construction. It is stated here as the next proof boundary
for the pure ideal-theoretic route.
-/

namespace QuadraticNumberFields
namespace ClassGroup

open scoped NumberField nonZeroDivisors

attribute [-instance] DivisionRing.toRatAlgebra

local notation "𝓞" => _root_.NumberField.RingOfIntegers

/-- **Finite-prime coprime-representative theorem.** Every ideal class
has an integral ideal representative whose absolute norm is prime to every
rational prime in a prescribed finite set.

This is the Dedekind-domain approximation input needed before the odd genus
characters can be made unconditional. -/
theorem exists_mk0_eq_and_forall_not_dvd_absNorm_of_finset
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      ClassGroup.mk0 I = C ∧
        ∀ p ∈ S,
          ¬ (p : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) := by
  sorry

/-- **Coprime-representative theorem.** Every ideal class has an
integral ideal representative whose absolute norm is prime to every odd rational
prime dividing the field discriminant. -/
theorem exists_mk0_eq_and_forall_not_dvd_absNorm_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : (Ideal (𝓞 (Qsqrtd (d : ℚ))))⁰,
      ClassGroup.mk0 I = C ∧
        ∀ P : {p // p ∈ oddPrimeDiscriminantDivisors d},
          ¬ (P.1 : ℤ) ∣ (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℤ) := by
  rcases exists_mk0_eq_and_forall_not_dvd_absNorm_of_finset
      d (oddPrimeDiscriminantDivisors d)
      (fun p hp => prime_of_mem_oddPrimeDiscriminantDivisors hp) C with
    ⟨I, hC, hI⟩
  exact ⟨I, hC, fun P => hI P.1 P.2⟩

/-- Single-prime form of the coprime-representative theorem. -/
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

/-- The coprime-representative theorem makes the restricted class-group
map on prime-to-`p` ideals surjective for every odd discriminant divisor `p`. -/
theorem mk0OnAbsNormCoprimeIdeals_surjective_of_mem_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (p : ℕ) [Fact p.Prime] (hp_disc : p ∈ oddPrimeDiscriminantDivisors d) :
    Function.Surjective (mk0OnAbsNormCoprimeIdeals d p) :=
  mk0OnAbsNormCoprimeIdeals_surjective_of_forall_mk0_eq_of_not_dvd_absNorm d p
    fun C => exists_mk0_eq_and_not_dvd_absNorm_of_mem_oddPrimeDiscriminantDivisors
      d p hp_disc C

/-- Principal-multiplier approximation for the restricted class-group map.
If two absolute-norm-coprime ideals define the same restricted class, they can
be related by principal multipliers whose principal ideals still have absolute
norm prime to `p`. -/
theorem exists_absNorm_coprime_principal_multipliers_of_mk0_eq
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (I J : absNormCoprimeIdealSubmonoid d p)
    (hmk : mk0OnAbsNormCoprimeIdeals d p I = mk0OnAbsNormCoprimeIdeals d p J) :
    ∃ x y : 𝓞 (Qsqrtd (d : ℚ)),
      ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {x}) : ℤ) ∧
      ¬ (p : ℤ) ∣ (Ideal.absNorm (Ideal.span {y}) : ℤ) ∧
      Ideal.span {x} * (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) =
        Ideal.span {y} * (J : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
  sorry

/-- The raw genus character descends on absolute-norm-coprime representatives
in the odd-prime discriminant branch. -/
theorem genusCharacterRawDescendsOnAbsNormCoprimeIdeals_of_mem_oddPrimeDiscriminantDivisors
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d) :
    genusCharacterRawDescendsOnAbsNormCoprimeIdeals d p :=
  genusCharacterRawDescendsOnAbsNormCoprimeIdeals_of_principal_multipliers d p hd_neg hp_disc
    fun I J hmk => exists_absNorm_coprime_principal_multipliers_of_mk0_eq d p I J hmk

/-- The odd-prime genus character on the class group, built from
absolute-norm-coprime ideal representatives. -/
noncomputable def genusCharacterOfAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnAbsNormCoprimeIdeals d p)) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) →* ℤˣ :=
  genusCharacterOfAbsNormCoprimeDescent d p hsurj
    (genusCharacterRawDescendsOnAbsNormCoprimeIdeals_of_mem_oddPrimeDiscriminantDivisors
      d p hd_neg hp_disc)

/-- The genus character built from absolute-norm-coprime representatives agrees
with the raw genus character on such representatives. -/
theorem genusCharacterOfAbsNormCoprimeIdeals_apply_mk0OnAbsNormCoprimeIdeals
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (p : ℕ) [Fact p.Prime]
    (hd_neg : d < 0) (hp_disc : p ∈ oddPrimeDiscriminantDivisors d)
    (hsurj : Function.Surjective (mk0OnAbsNormCoprimeIdeals d p))
    (I : absNormCoprimeIdealSubmonoid d p) :
    genusCharacterOfAbsNormCoprimeIdeals d p hd_neg hp_disc hsurj
        (mk0OnAbsNormCoprimeIdeals d p I) =
      genusCharacterRawUnit d p I :=
  genusCharacterOfAbsNormCoprimeDescent_apply_mk0OnAbsNormCoprimeIdeals d p hsurj
    (genusCharacterRawDescendsOnAbsNormCoprimeIdeals_of_mem_oddPrimeDiscriminantDivisors
      d p hd_neg hp_disc) I

end ClassGroup
end QuadraticNumberFields
