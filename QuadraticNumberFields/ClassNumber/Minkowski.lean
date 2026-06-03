/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import QuadraticNumberFields.ClassNumber.Qsqrtd
import QuadraticNumberFields.Families.Basic
import QuadraticNumberFields.RingOfIntegers.Discriminant

/-!
# Minkowski Bounds for Quadratic Fields

This file will specialize mathlib's class-number and Minkowski-bound tools to
quadratic fields.
-/

namespace QuadraticNumberFields
namespace ClassNumber

/-- Placeholder predicate for having simplified the Minkowski bound of `Qsqrtd d`. -/
def HasSimplifiedMinkowskiBound (d : ℤ) : Prop :=
  Families.IsAdmissibleParam d

end ClassNumber
end QuadraticNumberFields
