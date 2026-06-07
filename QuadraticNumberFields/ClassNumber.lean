/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Class Numbers of Quadratic Number Fields

This file specializes mathlib's Minkowski ideal-class representative bound to
the standard quadratic fields `Qsqrtd d`. General class-number facts such as
`NumberField.classNumber_eq_one_iff` should be used directly from mathlib.

Source alignment: the Minkowski constants follow Boxer Notes, Lectures 23.1
and 23.2.
-/

open scoped NumberField Real

open Module NumberField InfinitePlace Ideal Nat

namespace QuadraticNumberFields

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd`
-- calculations. Explicit bridges below still use `DivisionRing.toRatAlgebra`
-- when matching mathlib's generic number-field API.
attribute [-instance] DivisionRing.toRatAlgebra

local notation "N " K:70 => @finrank ℚ K _ _ (@Algebra.toModule ℚ K _ _ DivisionRing.toRatAlgebra)
local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  (((N K)! : ℝ) / (N K) ^ (N K) * √|discr K|)

namespace Qsqrtd

private theorem finrank_defaultRatAlgebra_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    N (Qsqrtd (d : ℚ)) = 2 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  have hcompare :
      N (Qsqrtd (d : ℚ)) =
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
    nrComplexPlaces (Qsqrtd (d : ℚ)) = 1 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  letI : NumberField.IsTotallyComplex (Qsqrtd (d : ℚ)) := Qsqrtd.isTotallyComplex d hd
  have hfin := finrank_defaultRatAlgebra_eq_two d
  have hc := NumberField.IsTotallyComplex.finrank (Qsqrtd (d : ℚ))
  have h : 2 = 2 * nrComplexPlaces (Qsqrtd (d : ℚ)) :=
    hfin.symm.trans hc
  omega

/-- A real quadratic field `ℚ(√d)` has no complex places. -/
theorem nrComplexPlaces_eq_zero_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    nrComplexPlaces (Qsqrtd (d : ℚ)) = 0 := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  letI : NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := Qsqrtd.isTotallyReal d hd
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (Qsqrtd (d : ℚ))

private theorem minkowskiConstant_eq_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    M (Qsqrtd (d : ℚ)) = (2 / π) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_one_of_neg d hd]
  have hfin := finrank_defaultRatAlgebra_eq_two d
  rw [hfin]
  norm_num
  ring

private theorem minkowskiConstant_eq_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    M (Qsqrtd (d : ℚ)) = (1 / 2) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  rw [nrComplexPlaces_eq_zero_of_pos d hd]
  have hfin := finrank_defaultRatAlgebra_eq_two d
  rw [hfin]
  norm_num

/-- In an imaginary quadratic field `ℚ(√d)`, every ideal class has a representative
whose norm is at most `(2 / π) * √|D_K|`. -/
theorem exists_ideal_in_class_of_norm_le_imaginary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (2 / π) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
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
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤
          (1 / 2) * √ |(discr (Qsqrtd (d : ℚ)) : ℝ)| := by
  obtain ⟨I, hC, hI⟩ := NumberField.exists_ideal_in_class_of_norm_le C
  refine ⟨I, hC, ?_⟩
  convert hI using 1
  exact (minkowskiConstant_eq_real d hd).symm

/-- The **Minkowski class-representative bound** of the quadratic field `ℚ(√d)`,
a first-class real invariant alongside `discr`. It specializes the general
number-field bound `(4/π)^{r₂} · (n!/nⁿ) · √|D|` to degree `2`
(`n!/nⁿ = 2/4 = 1/2`):

* imaginary `d < 0`: `(2/π)·√|D|`;
* real `d > 0`: `(1/2)·√|D|`. -/
noncomputable def minkowskiBound (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℝ :=
  (4 / π) ^ nrComplexPlaces (Qsqrtd (d : ℚ)) * (1 / 2) *
    √ |(discr (Qsqrtd (d : ℚ)) : ℝ)|

/-- Minkowski's bound for `ℚ(√d)` (unified form): every ideal class has a
representative whose absolute norm is at most `minkowskiBound d`. -/
theorem exists_ideal_in_class_of_norm_le
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (C : ClassGroup (𝓞 (Qsqrtd (d : ℚ)))) :
    ∃ I : nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))),
      ClassGroup.mk0 I = C ∧
        (absNorm (I : Ideal (𝓞 (Qsqrtd (d : ℚ)))) : ℝ) ≤ minkowskiBound d := by
  rcases lt_trichotomy d 0 with hneg | h0 | hpos
  · obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_imaginary d hneg C
    refine ⟨I, hC, ?_⟩
    rw [minkowskiBound, nrComplexPlaces_eq_one_of_neg d hneg]
    ring_nf at hI ⊢
    exact hI
  · exact absurd h0 (Fact.out : Squarefree d).ne_zero
  · obtain ⟨I, hC, hI⟩ := exists_ideal_in_class_of_norm_le_real d hpos C
    refine ⟨I, hC, ?_⟩
    rw [minkowskiBound, nrComplexPlaces_eq_zero_of_pos d hpos]
    ring_nf at hI ⊢
    exact hI

end Qsqrtd
end QuadraticNumberFields
