/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassNumber.Transport
import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# Class Numbers of Quadratic Number Fields

This file sets up the first class-number interface for the standard quadratic
models `Qsqrtd d`. The main point is to expose `classNumber = 1` in terms of the
explicit integral models already constructed by the ring-of-integers
classification.

The finite computations proving that specific quadratic fields have class
number one will live in later files.
-/

open scoped NumberField

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd` models.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace ClassNumber

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The class group of the standard quadratic field `ℚ(√d)`. -/
abbrev QsqrtdClassGroup : Type :=
  ClassGroup (𝓞 (Qsqrtd (d : ℚ)))

/-- The class number of the standard quadratic field `ℚ(√d)`. -/
noncomputable abbrev QsqrtdClassNumber : ℕ :=
  NumberField.classNumber (Qsqrtd (d : ℚ))

/-- Class number one for `ℚ(√d)` is equivalent to principality of its ring of
integers. -/
theorem QsqrtdClassNumber_eq_one_iff_ringOfIntegers_isPrincipalIdealRing :
    QsqrtdClassNumber d = 1 ↔ IsPrincipalIdealRing (𝓞 (Qsqrtd (d : ℚ))) :=
  eq_one_iff_ringOfIntegers_isPrincipalIdealRing

/-- In the `d % 4 ≠ 1` branch, class number one is equivalent to `ℤ[√d]` being a
principal ideal ring. -/
theorem QsqrtdClassNumber_eq_one_iff_zsqrtd_isPrincipalIdealRing
    (hd4 : d % 4 ≠ 1) :
    QsqrtdClassNumber d = 1 ↔ IsPrincipalIdealRing (Zsqrtd d) :=
  eq_one_iff_of_ringOfIntegers_equiv
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4)

/-- In the explicit `d = 1 + 4k` branch, class number one is equivalent to
`ℤ[(1+√d)/2]` being a principal ideal ring. -/
theorem QsqrtdClassNumber_eq_one_iff_zOnePlusSqrtOverTwo_isPrincipalIdealRing_of_eq
    (k : ℤ) (hk : d = 1 + 4 * k) :
    QsqrtdClassNumber d = 1 ↔ IsPrincipalIdealRing (ZOnePlusSqrtOverTwo k) :=
  eq_one_iff_of_ringOfIntegers_equiv
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hk)

/-- In the `d % 4 = 1` branch, class number one is equivalent to the canonical
model `ℤ[(1+√d)/2]` being a principal ideal ring. -/
theorem QsqrtdClassNumber_eq_one_iff_zOnePlusSqrtOverTwo_isPrincipalIdealRing
    (hd4 : d % 4 = 1) :
    QsqrtdClassNumber d = 1 ↔ IsPrincipalIdealRing (ZOnePlusSqrtOverTwo (d / 4)) :=
  eq_one_iff_of_ringOfIntegers_equiv
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4)

end SquarefreeIntegerParameter

end ClassNumber
end QuadraticNumberFields
