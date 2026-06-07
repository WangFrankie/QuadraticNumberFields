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
place, while a real quadratic field has none.
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

end Qsqrtd
end QuadraticNumberFields
