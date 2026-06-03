/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Qsqrtd.Basic

/-!
# Parameter Families for Quadratic Fields

This file contains lightweight shared definitions for explicit quadratic-field
families used in class-number-one and class-number-divisibility problems.
-/

namespace QuadraticNumberFields
namespace Families

/-- The standard field attached to an integer parameter `d`. -/
abbrev fieldOfParam (d : ℤ) : Type :=
  Qsqrtd (d : ℚ)

/-- Predicate packaging the standard squarefree hypotheses used by this project. -/
def IsAdmissibleParam (d : ℤ) : Prop :=
  Squarefree d ∧ d ≠ 1

end Families
end QuadraticNumberFields
