/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.Order.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Rings of integers as orders

The ring of integers of a number field is a `ℤ`-order in the field: it is a finite
`ℤ`-module, and its integral basis spans the field over `ℚ`.
-/

open scoped NumberField

/-- The ring of integers of a number field is a `ℤ`-order in it. -/
theorem NumberField.isOrder_integralClosure (K : Type*) [Field K] [NumberField K] :
    (integralClosure ℤ K).IsOrder ℚ := by
  refine ⟨?_, ?_⟩
  · exact (inferInstance : Module.Finite ℤ (𝓞 K))
  · rw [eq_top_iff, ← (NumberField.integralBasis K).span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [NumberField.integralBasis_apply]
    exact Submodule.subset_span (RingOfIntegers.basis K i).2
