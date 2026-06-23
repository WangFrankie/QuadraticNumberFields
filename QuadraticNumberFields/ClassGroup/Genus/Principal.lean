/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import QuadraticNumberFields.ClassGroup.Genus.Characters

/-!
# Principal Genus

This file states the principal-genus theorem for the new narrow-class-group
genus-theory layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- Principal genus theorem. The kernel of the genus-character map on the narrow
class group is the subgroup of squares. -/
theorem genusCharacterMap_ker_eq_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
