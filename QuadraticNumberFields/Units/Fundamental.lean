/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Units.Pell

/-!
# Fundamental Units

This file sets up a project-level placeholder predicate for fundamental units in
real quadratic rings of integers.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace Units

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- Placeholder predicate for a chosen fundamental unit of `𝓞(ℚ(√d))`. -/
def IsFundamentalUnit (_u : (𝓞 (Qsqrtd (d : ℚ)))ˣ) : Prop :=
  0 < d

end Units
end QuadraticNumberFields
