/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ContinuedFraction.Periodic
import QuadraticNumberFields.Families.RichaudDegert
import QuadraticNumberFields.Families.Yokoi

/-!
# Continued Fractions for Parameter Families

This file will collect explicit period data for Yokoi, Chowla, and
Richaud-Degert type families.
-/

namespace QuadraticNumberFields
namespace ContinuedFraction

/-- Placeholder for future family-specific period data. -/
def HasFamilyPeriodData (d : ℤ) : Prop :=
  HasSqrtContinuedFractionData d

end ContinuedFraction
end QuadraticNumberFields
