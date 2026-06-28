/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Index
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Narrow Square Classes

This file records the square-quotient cardinality comparison for the narrow
class group attached to a quadratic field. The generic square and two-torsion
objects live in the `NarrowClassGroup` namespace.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The square-class quotient of a finite narrow class group has the same
cardinality as the two-torsion subgroup. -/
theorem card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d))) =
      Nat.card (NarrowClassGroup.twoTorsion
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :=
  by
    simpa [NarrowClassGroup.squareQuotient, NarrowClassGroup.square] using
      (NarrowClassGroup.card_squareQuotient_eq_card_twoTorsion
        (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))

end GenusTheory
end ClassGroup
end QuadraticNumberFields
