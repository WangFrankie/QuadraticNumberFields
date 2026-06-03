/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Qsqrtd.Basic

/-!
# Pell-Type Equations

This file provides the initial predicates for Pell-type equations used to build
units in real quadratic fields.
-/

namespace QuadraticNumberFields
namespace Units

/-- Integer solutions to `x^2 - d y^2 = n`. -/
def IsPellSolution (d n x y : ℤ) : Prop :=
  x ^ 2 - d * y ^ 2 = n

/-- Integer solutions to the norm-one Pell equation. -/
def IsPellUnitSolution (d x y : ℤ) : Prop :=
  IsPellSolution d 1 x y

end Units
end QuadraticNumberFields
