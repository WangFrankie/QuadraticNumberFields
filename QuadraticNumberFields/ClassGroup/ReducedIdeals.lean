/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Infrastructure

/-!
# Reduced Ideals

This file will define and study reduced ideals in quadratic orders/rings of
integers.
-/

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for reduced ideal data attached to `d`. -/
def HasReducedIdealData (d : ℤ) : Prop :=
  HasExplicitClassGroupData d

end ClassGroup
end QuadraticNumberFields
