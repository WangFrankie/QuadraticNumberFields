/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Infrastructure

/-!
# Torsion in Class Groups

This file will organize statements about torsion and divisibility in quadratic
class groups.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for class group torsion data. -/
def HasClassGroupTorsionData (d : ℤ) : Prop :=
  HasExplicitClassGroupData d

end ClassGroup
end QuadraticNumberFields
