/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.SquareClass

/-!
# The Number of Genera

This file defines the number of genera of a quadratic field as the cardinality
of the narrow class group modulo squares.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The number of genera of `ℚ(√d)`, defined as the cardinality of the quotient
of the narrow class group by its subgroup of squares. -/
noncomputable def numberOfGenera : ℕ :=
  Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)))

/-- Unfolding lemma for the number of genera. -/
theorem numberOfGenera_eq_card :
    numberOfGenera d = Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) :=
  rfl

end GenusTheory
end ClassGroup
end QuadraticNumberFields
