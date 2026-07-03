/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.QuadraticField.Basic

/-!
# Basic Class-Group Interface

This file contains the basic notation and class-number lemmas for ideal class
groups of the quadratic fields `ℚ(√d)`.
-/

open scoped NumberField

namespace QuadraticNumberFields

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd`
-- calculations.
attribute [-instance] DivisionRing.toRatAlgebra

/-- Scoped notation for the ideal class group `Cl(𝓞(ℚ(√d)))`. -/
scoped[QuadraticNumberFields.ClassGroup]
  notation "Cl(" d ")" => _root_.ClassGroup
    (_root_.NumberField.RingOfIntegers
      (_root_.Qsqrtd ((d : ℤ) : ℚ)))

/-- A number field has class number one iff its ideal class group is a
subsingleton. -/
theorem NumberField.classNumber_eq_one_iff_subsingleton_classGroup
      {K : Type*} [Field K] [NumberField K] :
      NumberField.classNumber K = 1 ↔ Subsingleton (ClassGroup (𝓞 K)) := by
    simpa [NumberField.classNumber] using
      (Nat.card_eq_one_iff_unique (α := ClassGroup (𝓞 K))).trans (and_iff_left ⟨1⟩)

/-- If every ideal class is trivial, then the field has class number one. -/
theorem NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    {K : Type*} [Field K] [NumberField K]
    (h : ∀ C : ClassGroup (𝓞 K), C = 1) :
    NumberField.classNumber K = 1 :=
  NumberField.classNumber_eq_one_iff_subsingleton_classGroup.mpr
    ⟨fun C D => (h C).trans (h D).symm⟩

end QuadraticNumberFields
