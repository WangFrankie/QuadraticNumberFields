/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassNumber.Basic
import QuadraticNumberFields.Families.Basic

/-!
# Class Group Infrastructure

This file will collect shared class-group infrastructure for quadratic fields.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassGroup

/-- Placeholder predicate for explicit class-group data of `𝓞(ℚ(√d))`. -/
def HasExplicitClassGroupData (d : ℤ) : Prop :=
  Families.IsAdmissibleParam d

end ClassGroup
end QuadraticNumberFields
