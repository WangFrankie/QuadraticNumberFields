/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.QuadraticField.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-!
# Rings of Integers of Abstract Quadratic Fields

This file collects basic structural facts about the ring of integers of an
abstract quadratic field.

## Main results

* `QuadraticField.ringOfIntegers_isQuadraticExtension`: `𝓞 K` is a quadratic
  extension of `ℤ` when `K` is a quadratic field over `ℚ`.
-/

open scoped NumberField

namespace QuadraticField

/-- The ring of integers of an abstract quadratic field is a quadratic extension
of `ℤ`. -/
instance ringOfIntegers_isQuadraticExtension
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℤ (𝓞 K) :=
  @Algebra.IsQuadraticExtension.mk ℤ _ _ _ _ _
    (inferInstance : Module.Free ℤ (𝓞 K))
    ((NumberField.RingOfIntegers.rank K).trans (by
      convert Algebra.IsQuadraticExtension.finrank_eq_two ℚ K using 1
      congr 1
      exact Subsingleton.elim _ _))

end QuadraticField
