/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Examples.ClassGroupStructure.ReducedFormTables
import QuadraticNumberFields.Examples.SqrtNeg5.Forms
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Class Group Structure Computations

This file is the final layer of the class-group structure examples.  The
preceding example files check the standard finite-abelian targets and the raw
reduced-form multiplication tables.  This file keeps the formal cyclic
`MulEquiv` outputs for `d = -5` and `d = -23`, and records the non-cyclic
standard classifier outputs for `d = -21` and `d = -231`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open FiniteAbelianSmith

set_option linter.hashCommand false

/-! ## Input facts for the concrete fields -/

section ConcreteIsomorphisms

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

/-- `-23` is squarefree. -/
instance : Fact (Squarefree (-23 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

/-- `-23` is not `1`. -/
instance : Fact ((-23 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `-21` is squarefree. -/
instance : Fact (Squarefree (-21 : ℤ)) :=
  ⟨Int.squarefree_natAbs.mp (by
    change Squarefree (21 : ℕ)
    rw [show (21 : ℕ) = 3 * 7 by norm_num]
    rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 3 7)]
    exact ⟨Nat.prime_three.squarefree, Nat.prime_seven.squarefree⟩)⟩

/-- `-21` is not `1`. -/
instance : Fact ((-21 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `-231` is squarefree. -/
instance : Fact (Squarefree (-231 : ℤ)) :=
  ⟨Int.squarefree_natAbs.mp (by
    change Squarefree (231 : ℕ)
    rw [show (231 : ℕ) = 3 * (7 * 11) by norm_num]
    rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 3 (7 * 11))]
    constructor
    · exact Nat.prime_three.squarefree
    · rw [Nat.squarefree_mul (by norm_num : Nat.Coprime 7 11)]
      exact ⟨Nat.prime_seven.squarefree, Nat.prime_eleven.squarefree⟩)⟩

/-- `-231` is not `1`. -/
instance : Fact ((-231 : ℤ) ≠ 1) := ⟨by decide⟩

/-- `ℚ(√-23)` has class number three, computed by reduced forms. -/
theorem classNumber_qsqrtd_neg23 :
    NumberField.classNumber (Qsqrtd ((-23 : ℤ) : ℚ)) = 3 := by
  change classNumberQsqrtd (-23) = 3
  compute_class_number_qsqrtd

/-! ## Direct cyclic outputs -/

/-- **ℚ(√-5)**: the class group is cyclic of order 2, i.e. `ℤ/2ℤ`.
This follows from class number 2 (already proved in `Computed.lean`) and the
fact that any non-principal ideal generates the group. -/
noncomputable def classGroup_qsqrtd_neg5_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-5 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 2) :=
  Examples.SqrtNeg5.classGroupMulEquivZMod2

/-- **ℚ(√-23)**: the class group is cyclic of order 3, i.e. `ℤ/3ℤ`.
Class number 3 is already proved; any non-principal ideal has order 3. -/
noncomputable def classGroup_qsqrtd_neg23_mulEquiv :
    ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))) ≃*
      Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq (p := 3)
    (G := ClassGroup (NumberField.RingOfIntegers (Qsqrtd ((-23 : ℤ) : ℚ))))
    (G' := Multiplicative (ZMod 3))
    (by
      rw [Nat.card_eq_fintype_card]
      simpa [NumberField.classNumber] using classNumber_qsqrtd_neg23)
    (by
      rw [Nat.card_eq_fintype_card]
      simp)

/-! ## Non-cyclic standard-output checks

The non-cyclic examples below currently stop at the executable classifier
boundary.  Formal bundled `MulEquiv` certificates for these tables should be
added via proof-producing certificates, not by VM-only decision tactics.
-/

/-! ## Public standard-output checks -/

#guard classGroupStandardIsoTypeOfImaginaryParameter (-5) =
  StandardGroupIsoType.product [2]

#guard classGroupStandardIsoTypeOfImaginaryParameter (-23) =
  StandardGroupIsoType.product [3]

#guard classGroupStandardIsoTypeOfImaginaryParameter (-21) =
  StandardGroupIsoType.product [2, 2]

#guard classGroupStandardIsoTypeOfImaginaryParameter (-231) =
  StandardGroupIsoType.product [2, 6]

#guard (classGroupStandardIsoTypeOfImaginaryParameter (-231)).targetElems.length == 12

end ConcreteIsomorphisms

end BinaryQuadraticForm
end QuadraticNumberFields
