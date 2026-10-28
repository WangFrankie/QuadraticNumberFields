/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Examples.SqrtNeg5.Forms
import FormClassGroup.ClassGroup.ClassNumber
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Class Group Structure Computations

This file is the final layer of the class-group structure examples.  The
preceding example file checks the raw reduced-form multiplication tables.  This
file keeps the formal cyclic `MulEquiv` outputs for `d = -5` and `d = -23`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Input facts for the concrete fields -/

section ConcreteIsomorphisms

open scoped _root_.NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-- `-23` is squarefree. -/
instance : Fact (Squarefree (-23 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

/-- `-23` is not `1`. -/
instance : Fact ((-23 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `ℚ(√-23)` has class number three, computed by reduced forms. -/
theorem classNumber_qsqrtd_neg23 :
    NumberField.classNumber (Qsqrtd ((-23 : ℤ) : ℚ)) = 3 := by
  compute_class_number_qsqrtd

/-! ## Direct cyclic outputs -/

/-- `ℚ(√-5)`: the class group is cyclic of order 2, i.e. `ℤ/2ℤ`.
This follows from class number 2 (already proved in `Computed.lean`) and the
fact that any non-principal ideal generates the group. -/
noncomputable def classGroup_qsqrtd_neg5_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-5 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) :=
  Examples.SqrtNeg5.classGroupMulEquivZMod2

/-- `ℚ(√-23)`: the class group is cyclic of order 3, i.e. `ℤ/3ℤ`.
Class number 3 is already proved; any non-principal ideal has order 3. -/
noncomputable def classGroup_qsqrtd_neg23_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (p := 3)
    (G := ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))))
    (G' := Multiplicative (ZMod 3))
    (by
      simpa only [NumberField.classNumber, Nat.card_eq_fintype_card]
        using classNumber_qsqrtd_neg23)
    (by simp)

attribute [nolint defsWithUnderscore]
  classGroup_qsqrtd_neg5_mulEquiv classGroup_qsqrtd_neg23_mulEquiv

end ConcreteIsomorphisms

end BinaryQuadraticForm
end QuadraticNumberFields
