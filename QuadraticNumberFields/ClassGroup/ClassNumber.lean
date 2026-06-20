/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.QuadraticField.Basic

/-!
# Class Numbers and Ideal Class Groups

This file contains the core class-number interface used by the quadratic-number-field
library.  The declarations stay in the `QuadraticNumberFields` and `NumberField`
namespaces; this module owns them because they are class-group/cardinality facts.
-/

open scoped NumberField

namespace QuadraticNumberFields

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd`
-- calculations.
attribute [-instance] DivisionRing.toRatAlgebra

/-- The class number of the quadratic field `ℚ(√d)`, as a function of the
squarefree integer parameter `d`. Thin alias of `NumberField.classNumber`. -/
noncomputable def classNumberQsqrtd (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] : ℕ :=
  NumberField.classNumber (Qsqrtd (d : ℚ))

/-- If every ideal class of a number field is trivial, then the class number is
one. -/
theorem NumberField.classNumber_eq_one_of_forall_classGroup_eq_one
    {K : Type*} [Field K] [NumberField K]
    (h : ∀ C : ClassGroup (𝓞 K), C = 1) :
    NumberField.classNumber K = 1 := by
  haveI : Unique (ClassGroup (𝓞 K)) := ⟨⟨1⟩, h⟩
  simpa only [NumberField.classNumber] using
    Fintype.card_unique (α := ClassGroup (𝓞 K))

end QuadraticNumberFields
