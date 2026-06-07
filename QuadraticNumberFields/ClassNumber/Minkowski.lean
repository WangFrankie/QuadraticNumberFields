/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.ClassNumber.Qsqrtd
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Minkowski Bounds for Quadratic Fields

This file specializes mathlib's class-number and Minkowski-bound tools to
quadratic fields.  It starts with the signature constants used in the
quadratic Minkowski constants: an imaginary quadratic field has one complex
place, while a real quadratic field has none.  These constants then specialize
mathlib's ideal-class representative theorem to the usual quadratic
Minkowski bounds.

Source alignment: the Minkowski constants follow Boxer Notes, Lectures 23.1
and 23.2.  The explicit `d % 4` discriminant branches use the quadratic-field
discriminant formula from Ireland-Rosen, Chapter 13, via the existing
`RingOfIntegers.discr_of_mod_four_eq_one` and
`RingOfIntegers.discr_of_mod_four_ne_one` theorems.
-/

namespace QuadraticNumberFields

open scoped NumberField

namespace Qsqrtd

-- Resolve the local diamond between the canonical `QuadraticAlgebra` algebra
-- and the default rational algebra on a field.
attribute [-instance] DivisionRing.toRatAlgebra

private theorem finrank_defaultRatAlgebra_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    @Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
        (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) = 2 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  have hcompare :
      @Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) =
        @Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ QuadraticAlgebra.instAlgebra) := by
    symm
    refine @Algebra.finrank_eq_of_equiv_equiv ℚ (Qsqrtd (d : ℚ)) _ _
      QuadraticAlgebra.instAlgebra ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra
      (RingEquiv.refl ℚ) (RingEquiv.refl (Qsqrtd (d : ℚ))) ?_
    exact RingHom.ext_rat _ _
  rw [hcompare]
  exact QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

/-- An imaginary quadratic field `ℚ(√d)` has one complex place. -/
theorem nrComplexPlaces_eq_one_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 1 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  letI : NumberField.IsTotallyComplex (Qsqrtd (d : ℚ)) := Qsqrtd.isTotallyComplex d hd
  have hfin := finrank_defaultRatAlgebra_eq_two d
  have hc := NumberField.IsTotallyComplex.finrank (Qsqrtd (d : ℚ))
  have h : 2 = 2 * NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) :=
    hfin.symm.trans hc
  omega

/-- A real quadratic field `ℚ(√d)` has no complex places. -/
theorem nrComplexPlaces_eq_zero_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 0 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  letI : NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := Qsqrtd.isTotallyReal d hd
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (Qsqrtd (d : ℚ))

private theorem minkowskiConstant_eq_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) *
      (((@Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra)).factorial : ℝ) /
        ((@Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) : ℕ) : ℝ) ^
            @Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
              (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) *
          Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)|) =
        (2 / Real.pi) * Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_one_of_neg d hd]
  have hfin := finrank_defaultRatAlgebra_eq_two d
  rw [hfin]
  norm_num
  ring

private theorem minkowskiConstant_eq_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) *
      (((@Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra)).factorial : ℝ) /
        ((@Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
          (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) : ℕ) : ℝ) ^
            @Module.finrank ℚ (Qsqrtd (d : ℚ)) _ _
              (@Algebra.toModule ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra) *
          Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)|) =
        (1 / 2) * Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_zero_of_pos d hd]
  have hfin := finrank_defaultRatAlgebra_eq_two d
  rw [hfin]
  norm_num

private theorem sqrt_abs_four_mul_intCast (d : ℤ) :
    Real.sqrt |((4 * d : ℤ) : ℝ)| = 2 * Real.sqrt |(d : ℝ)| := by
  rw [show ((4 * d : ℤ) : ℝ) = (4 : ℝ) * (d : ℝ) by norm_num]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

/-- In an imaginary quadratic field `ℚ(√d)`, every ideal class has a representative
whose norm is at most `(2 / π) * √|D_K|`. -/
theorem exists_ideal_in_class_of_norm_le_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (2 / Real.pi) * Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  exact (minkowskiConstant_eq_imaginary d hd).symm

/-- In a real quadratic field `ℚ(√d)`, every ideal class has a representative whose
norm is at most `(1 / 2) * √|D_K|`. -/
theorem exists_ideal_in_class_of_norm_le_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (1 / 2) * Real.sqrt |(NumberField.discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  exact (minkowskiConstant_eq_real d hd).symm

/-- In an imaginary quadratic field `ℚ(√d)` with `d % 4 = 1`, every ideal class has
a representative whose norm is at most `(2 / π) * √|d|`. -/
theorem exists_ideal_in_class_of_norm_le_imaginary_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 = 1)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (2 / Real.pi) * Real.sqrt |(d : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_imaginary d hd C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  rw [RingOfIntegers.discr_of_mod_four_eq_one d hd4]

/-- In an imaginary quadratic field `ℚ(√d)` with `d % 4 ≠ 1`, every ideal class has
a representative whose norm is at most `(4 / π) * √|d|`. -/
theorem exists_ideal_in_class_of_norm_le_imaginary_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 ≠ 1)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (4 / Real.pi) * Real.sqrt |(d : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_imaginary d hd C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  rw [RingOfIntegers.discr_of_mod_four_ne_one d hd4]
  rw [sqrt_abs_four_mul_intCast]
  ring

/-- In a real quadratic field `ℚ(√d)` with `d % 4 = 1`, every ideal class has a
representative whose norm is at most `(1 / 2) * √|d|`. -/
theorem exists_ideal_in_class_of_norm_le_real_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) (hd4 : d % 4 = 1)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (1 / 2) * Real.sqrt |(d : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_real d hd C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  rw [RingOfIntegers.discr_of_mod_four_eq_one d hd4]

/-- In a real quadratic field `ℚ(√d)` with `d % 4 ≠ 1`, every ideal class has a
representative whose norm is at most `√|d|`. -/
theorem exists_ideal_in_class_of_norm_le_real_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) (hd4 : d % 4 ≠ 1)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (Ideal.absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          Real.sqrt |(d : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_real d hd C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  rw [RingOfIntegers.discr_of_mod_four_ne_one d hd4]
  rw [sqrt_abs_four_mul_intCast]
  ring

end Qsqrtd
end QuadraticNumberFields
