/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QNFMathlib.RingTheory.DedekindDomain.Ideal
import QNFMathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Small-Norm Ideal Class Criteria

This file collects class-group closure criteria for situations where every ideal
class has a representative of very small absolute norm.  The main use is the
quadratic-field Minkowski bound `< 3`, where nonzero integral ideals have norm
`1` or `2`.
-/

open scoped NumberField

namespace QuadraticNumberFields

/-- The natural number `2` is irreducible, as a convenience for absolute-norm
arguments. -/
theorem irreducible_two_nat : Irreducible (2 : ℕ) :=
  (Nat.irreducible_iff_prime.mp Nat.prime_two).irreducible

/-- An ideal of absolute norm `2` is prime. -/
theorem Ideal.isPrime_of_absNorm_eq_two {R : Type*} [CommRing R] [Nontrivial R]
    [IsDedekindDomain R] [Module.Free ℤ R] {I : Ideal R} (hI : Ideal.absNorm I = 2) :
    I.IsPrime :=
  Ideal.isPrime_of_irreducible_absNorm
    (by rw [hI]; exact irreducible_two_nat)

/-- If every ideal class has a representative of absolute norm `< 3`, and all
norm-`2` ideals are principal, then every ideal class is trivial. -/
theorem classGroup_eq_one_of_exists_ideal_norm_lt_three
    {K : Type*} [Field K] [NumberField K]
    (hexists : ∀ C : ClassGroup (𝓞 K),
      ∃ I : nonZeroDivisors (Ideal (𝓞 K)),
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) < 3)
    (hprincipal_two : ∀ {I : Ideal (𝓞 K)}, Ideal.absNorm I = 2 → I.IsPrincipal)
    (C : ClassGroup (𝓞 K)) :
    C = 1 := by
  obtain ⟨I, hmk, hnorm⟩ := hexists C
  rw [← hmk, ClassGroup.mk0_eq_one_iff]
  have hIne : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hIne
  have hcase : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 ∨
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  rcases hcase with h1 | h2
  · rw [Ideal.absNorm_eq_one_iff] at h1
    rw [h1]
    exact ⟨1, Ideal.span_singleton_one.symm⟩
  · exact hprincipal_two h2

/-- If every ideal class has a representative of absolute norm `< 3`, and all
norm-`2` representatives have class `P`, then every ideal class is trivial or
equal to `P`. -/
theorem classGroup_eq_one_or_of_exists_ideal_norm_lt_three
    {K : Type*} [Field K] [NumberField K] (P : ClassGroup (𝓞 K))
    (hexists : ∀ C : ClassGroup (𝓞 K),
      ∃ I : nonZeroDivisors (Ideal (𝓞 K)),
        ClassGroup.mk0 I = C ∧ Ideal.absNorm (I : Ideal (𝓞 K)) < 3)
    (hclass_two : ∀ I : nonZeroDivisors (Ideal (𝓞 K)),
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 → ClassGroup.mk0 I = P)
    (C : ClassGroup (𝓞 K)) :
    C = 1 ∨ C = P := by
  obtain ⟨I, hmk, hnorm⟩ := hexists C
  rw [← hmk]
  have hIne : (I : Ideal (𝓞 K)) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h0 : Ideal.absNorm (I : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    simpa using hIne
  have hcase : Ideal.absNorm (I : Ideal (𝓞 K)) = 1 ∨
      Ideal.absNorm (I : Ideal (𝓞 K)) = 2 := by omega
  rcases hcase with h1 | h2
  · left
    rw [ClassGroup.mk0_eq_one_iff]
    rw [Ideal.absNorm_eq_one_iff] at h1
    rw [h1]
    exact ⟨1, Ideal.span_singleton_one.symm⟩
  · right
    exact hclass_two I h2

end QuadraticNumberFields
