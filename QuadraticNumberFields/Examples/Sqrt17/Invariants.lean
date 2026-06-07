/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.RingOfIntegers.Discriminant
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.Qsqrtd.Galois
import QuadraticNumberFields.ClassNumber.Minkowski
import QuadraticNumberFields.Zsqrtd.Dedekind
import QuadraticNumberFields.RingOfIntegers.CommonInstances

/-!
# Invariants of the real quadratic field `ℚ(√17)`

A panoramic instantiation of the completed library on the real quadratic field
`ℚ(√17)`. Since `17 ≡ 1 (mod 4)`, this exercises the `mod 4 = 1` branch of every
construction, complementing `Examples.SqrtNeg5.Invariants` (the `mod 4 ≠ 1`
branch on the imaginary field `ℚ(√-5)`).

## Summary

* ring of integers `𝓞(ℚ(√17)) ≅ ℤ[(1+√17)/2]`;
* discriminant `D = 17`;
* totally real, automorphism group of order 2;
* the suborder `ℤ[√17]` is **not** Dedekind (it is not the maximal order).
-/

open scoped NumberField
open QuadraticNumberFields

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields.Examples.Sqrt17

/-- The ring of integers of `ℚ(√17)` is `ℤ[(1+√17)/2]` (since `17 ≡ 1 mod 4`). -/
noncomputable def ringOfIntegersEquiv :
    𝓞 (Qsqrtd ((17 : ℤ) : ℚ)) ≃+* ZOnePlusSqrtOverTwo (17 / 4) :=
  RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one 17 (by decide)

/-- The field discriminant of `ℚ(√17)` is `17`. -/
theorem discr_eq : NumberField.discr (Qsqrtd ((17 : ℤ) : ℚ)) = 17 :=
  RingOfIntegers.discr_of_mod_four_eq_one 17 (by decide)

/-- `ℚ(√17)` is totally real. -/
theorem isTotallyReal : NumberField.IsTotallyReal (Qsqrtd ((17 : ℤ) : ℚ)) :=
  Qsqrtd.isTotallyReal 17 (by norm_num)

/-- `ℚ(√17)` has no complex places. -/
theorem nrComplexPlaces_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd ((17 : ℤ) : ℚ)) = 0 :=
  Qsqrtd.nrComplexPlaces_eq_zero_of_pos 17 (by norm_num)

/-- The `ℚ`-automorphism group of `ℚ(√17)` has order two. -/
theorem card_aut_eq_two :
    Nat.card (Qsqrtd ((17 : ℤ) : ℚ) ≃ₐ[ℚ] Qsqrtd ((17 : ℤ) : ℚ)) = 2 :=
  Qsqrtd.card_aut_eq_two 17

/-- The suborder `ℤ[√17]` is **not** a Dedekind domain: because `17 ≡ 1 (mod 4)`
the maximal order is `ℤ[(1+√17)/2]`, strictly larger than `ℤ[√17]`. -/
theorem zsqrtd_not_isDedekindDomain :
    ¬ IsDedekindDomain (QuadraticNumberFields.Zsqrtd (17 : ℤ)) :=
  QuadraticNumberFields.Zsqrtd.not_isDedekindDomain_of_mod_four_eq_one 17 (by decide)

/-- The Minkowski bound of `ℚ(√17)` is `(1/2)·√17 ≈ 2.06`, in particular `< 3`. -/
theorem minkowskiBound_lt_three : Qsqrtd.minkowskiBound (17 : ℤ) < 3 := by
  rw [Qsqrtd.minkowskiBound, Qsqrtd.nrComplexPlaces_eq_zero_of_pos 17 (by norm_num),
    RingOfIntegers.discr_of_mod_four_eq_one 17 (by decide)]
  have hsqrt : Real.sqrt |((17 : ℤ) : ℝ)| < 6 := by
    rw [abs_of_nonneg (by norm_num)]
    calc Real.sqrt ((17 : ℤ) : ℝ) < Real.sqrt 36 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
      _ = 6 := by rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  calc (4 / Real.pi) ^ 0 * (1 / 2) * Real.sqrt |((17 : ℤ) : ℝ)|
      = (1 / 2) * Real.sqrt |((17 : ℤ) : ℝ)| := by rw [pow_zero]; ring
    _ < (1 / 2) * 6 := by gcongr
    _ = 3 := by norm_num

/-- **Minkowski bound for `ℚ(√17)`, integer form.** Every ideal class has a
representative whose absolute norm is `< 3` (equivalently `≤ 2`), obtained from
the unified `Qsqrtd.exists_ideal_in_class_of_norm_le` and `minkowskiBound_lt_three`. -/
theorem exists_ideal_in_class_of_norm_le
    (C : ClassGroup (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))),
      ClassGroup.mk0 I = C ∧
        Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd ((17 : ℤ) : ℚ)))) < 3 := by
  obtain ⟨I, hC, hI⟩ := Qsqrtd.exists_ideal_in_class_of_norm_le 17 C
  exact ⟨I, hC, by exact_mod_cast lt_of_le_of_lt hI minkowskiBound_lt_three⟩

/- TODO (class number): upgrade the bound above to
`NumberField.classNumber (Qsqrtd ((17 : ℤ) : ℚ)) = 1`. Since `(1/2)·√17 ≈ 2.06`,
this requires showing every prime ideal of norm `≤ 2` is principal (2 splits, so
norm-2 primes exist). Deferred until the class-number development is complete. -/

end QuadraticNumberFields.Examples.Sqrt17
