/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.RichaudDegert
import QuadraticNumberFields.Units.Fundamental

/-!
# Units in Explicit Families

This file will hold candidate fundamental units for Yokoi, Chowla, and
Richaud-Degert type families.
-/

namespace QuadraticNumberFields
namespace Units

/-- Placeholder predicate for a family with an explicit candidate unit. -/
def HasExplicitUnitCandidate (d : ℤ) : Prop :=
  0 < d

end Units
end QuadraticNumberFields
