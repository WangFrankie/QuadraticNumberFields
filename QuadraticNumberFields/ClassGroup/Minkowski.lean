/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.ReducedIdeals

/-!
# Class Groups and Minkowski Bounds

This file will connect explicit ideal representatives with Minkowski-bound
criteria.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for class-group data controlled by a Minkowski bound. -/
def HasMinkowskiClassGroupData (d : ℤ) : Prop :=
  HasReducedIdealData d

end ClassGroup
end QuadraticNumberFields
