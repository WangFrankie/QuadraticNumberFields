/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassNumber.Basic
import QuadraticNumberFields.Families.Basic

/-!
# Class Number Interface for `Qsqrtd`

This file is reserved for refinements of the class-number interface specific to
the standard model `Qsqrtd d`.
-/

namespace QuadraticNumberFields
namespace ClassNumber

/-- Placeholder predicate for a field whose `Qsqrtd` class number data has been
made explicit. -/
def HasExplicitQsqrtdClassNumberData (d : ℤ) : Prop :=
  Families.IsAdmissibleParam d

end ClassNumber
end QuadraticNumberFields
