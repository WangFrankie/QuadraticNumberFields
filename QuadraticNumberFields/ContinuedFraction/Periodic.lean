/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ContinuedFraction.Qsqrtd

/-!
# Periodic Continued Fractions

This file will hold the periodic continued-fraction interface for quadratic
irrationals.
-/

namespace QuadraticNumberFields
namespace ContinuedFraction

/-- A lightweight placeholder recording a period length for future explicit
continued-fraction computations. -/
structure PeriodData (d : ℤ) where
  /-- The proposed period length. -/
  periodLength : ℕ

end ContinuedFraction
end QuadraticNumberFields
