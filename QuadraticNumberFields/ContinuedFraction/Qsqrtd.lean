/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.Basic

/-!
# Continued Fractions for `Qsqrtd`

This file is the entry point for continued-fraction data attached to real
quadratic fields. The substantial periodicity theory will be developed later.
-/

namespace QuadraticNumberFields
namespace ContinuedFraction

/-- Placeholder predicate for having explicit continued-fraction data for
`√d`. -/
def HasSqrtContinuedFractionData (d : ℤ) : Prop :=
  0 < d

end ContinuedFraction
end QuadraticNumberFields
