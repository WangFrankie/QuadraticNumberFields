/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Genus Theory

This file will contain genus-theory infrastructure for quadratic class groups.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for genus-theory data attached to `d`. -/
def HasGenusTheoryData (d : ℤ) : Prop :=
  HasClassGroupTorsionData d

end ClassGroup
end QuadraticNumberFields
