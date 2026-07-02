/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Formula

/-!
# Class Number Divisibility

This file will hold divisibility statements of the form `n ∣ h(d)` for quadratic
class numbers.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for divisibility data in a quadratic class group. -/
def HasClassNumberDivisibilityData (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (n : ℕ) : Prop :=
  genusFormula d ∧ 0 < n

end ClassGroup
end QuadraticNumberFields
