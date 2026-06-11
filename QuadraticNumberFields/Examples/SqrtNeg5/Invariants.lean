/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Qsqrtd.Galois
import QuadraticNumberFields.ClassNumber
import QuadraticNumberFields.Zsqrtd.Dedekind
import QuadraticNumberFields.RingOfIntegers.CommonInstances

/-!
# Invariants of the imaginary quadratic field `ℚ(√-5)`

A panoramic instantiation of the completed library on the imaginary quadratic
field `ℚ(√-5)`. Since `-5 ≡ 3 (mod 4)`, this exercises the `mod 4 ≠ 1` branch of
every construction, complementing `Examples.Sqrt17.Invariants` (the `mod 4 = 1`
branch on the real field `ℚ(√17)`).

## Summary

* ring of integers `𝓞(ℚ(√-5)) ≅ ℤ[√-5]`;
* discriminant `D = -20`;
* totally complex, hence a CM field; automorphism group of order 2;
* the order `ℤ[√-5]` **is** Dedekind (it is the maximal order).
-/

open scoped NumberField
open QuadraticNumberFields

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields.Examples.SqrtNeg5

/-- The ring of integers of `ℚ(√-5)` is `ℤ[√-5]` (since `-5 ≡ 3 mod 4`). -/
noncomputable def ringOfIntegersEquiv :
    𝓞 (Qsqrtd ((-5 : ℤ) : ℚ)) ≃+* Zsqrtd (-5 : ℤ) :=
  RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one (-5) (by decide)

/-- The field discriminant of `ℚ(√-5)` is `-20`. -/
theorem discr_eq : NumberField.discr (Qsqrtd ((-5 : ℤ) : ℚ)) = -20 :=
  RingOfIntegers.discr_of_mod_four_ne_one (-5) (by decide)

/-- `ℚ(√-5)` is totally complex. -/
theorem isTotallyComplex : NumberField.IsTotallyComplex (Qsqrtd ((-5 : ℤ) : ℚ)) :=
  Qsqrtd.isTotallyComplex (-5) (by decide)

/-- `ℚ(√-5)` is a CM field. -/
theorem isCMField : NumberField.IsCMField (Qsqrtd ((-5 : ℤ) : ℚ)) :=
  Qsqrtd.isCMField (-5) (by decide)

/-- `ℚ(√-5)` has exactly one complex place. -/
theorem nrComplexPlaces_eq_one :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd ((-5 : ℤ) : ℚ)) = 1 :=
  Qsqrtd.nrComplexPlaces_eq_one_of_neg (-5) (by decide)

/-- The `ℚ`-automorphism group of `ℚ(√-5)` has order two. -/
theorem card_aut_eq_two :
    Nat.card (Qsqrtd ((-5 : ℤ) : ℚ) ≃ₐ[ℚ] Qsqrtd ((-5 : ℤ) : ℚ)) = 2 :=
  Qsqrtd.card_aut_eq_two (-5)

/-- The order `ℤ[√-5]` **is** a Dedekind domain: since `-5 ≡ 3 (mod 4)` it is the
maximal order, equal to the ring of integers. -/
theorem zsqrtd_isDedekindDomain :
    IsDedekindDomain (Zsqrtd (-5 : ℤ)) :=
  Zsqrtd.isDedekindDomain_of_mod_four_ne_one (-5) (by decide)

/-- The Minkowski bound of `ℚ(√-5)` is `(2/π)·√20 ≈ 2.85`, in particular `< 3`.
(Strictness comes from `9 < 3π`, i.e. `π > 3`, not from the `√` estimate.) -/
theorem minkowskiBound_lt_three : Qsqrtd.minkowskiBound (-5 : ℤ) < 3 := by
  rw [Qsqrtd.minkowskiBound, Qsqrtd.nrComplexPlaces_eq_one_of_neg (-5) (by decide),
    RingOfIntegers.discr_of_mod_four_ne_one (-5) (by decide)]
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsqrt : Real.sqrt |((4 * (-5) : ℤ) : ℝ)| ≤ 4.48 := by
    rw [show |((4 * (-5) : ℤ) : ℝ)| = 20 by norm_num]
    calc Real.sqrt 20 ≤ Real.sqrt (4.48 ^ 2) := Real.sqrt_le_sqrt (by norm_num)
      _ = 4.48 := Real.sqrt_sq (by norm_num)
  rw [pow_one, div_mul_eq_mul_div, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith [hsqrt, hpi, Real.sqrt_nonneg |((4 * (-5) : ℤ) : ℝ)|]

/-- **Minkowski bound for `ℚ(√-5)`, integer form.** Every ideal class has a
representative whose absolute norm is `< 3` (equivalently `≤ 2`), obtained from
the unified `Qsqrtd.exists_ideal_in_class_of_norm_le` and `minkowskiBound_lt_three`. -/
theorem exists_ideal_in_class_of_norm_le
    (C : ClassGroup (𝓞 (Qsqrtd ((-5 : ℤ) : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd ((-5 : ℤ) : ℚ)))),
      ClassGroup.mk0 I = C ∧
        Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd ((-5 : ℤ) : ℚ)))) < 3 := by
  obtain ⟨I, hC, hI⟩ := Qsqrtd.exists_ideal_in_class_of_norm_le (-5) C
  exact ⟨I, hC, by exact_mod_cast lt_of_le_of_lt hI minkowskiBound_lt_three⟩

/-! `ℚ(√-5)` has class number two — the classic non-UFD example.  A full
`classNumber = 2` proof awaits the class-number development; a first milestone
is `¬ IsPrincipalIdealRing (ℤ[√-5])` (hence `classNumber ≠ 1`), witnessed by
the non-principal ideal `(2, 1+√-5)` already constructed in
`Examples.SqrtNeg5.Ideals`. -/

end QuadraticNumberFields.Examples.SqrtNeg5
