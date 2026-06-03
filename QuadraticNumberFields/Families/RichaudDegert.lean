/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.Basic

/-!
# Richaud-Degert Type Families

This file records the standard two-parameter Richaud-Degert shape
`(a * n)^2 + k * a`.
-/

namespace QuadraticNumberFields
namespace Families

/-- Richaud-Degert type parameter `(a * n)^2 + k * a`. -/
def richaudDegertD (a n k : ℤ) : ℤ :=
  (a * n) ^ 2 + k * a

/-- The usual finite set of Richaud-Degert shifts. -/
def IsRichaudDegertShift (k : ℤ) : Prop :=
  k = -4 ∨ k = -2 ∨ k = -1 ∨ k = 1 ∨ k = 2 ∨ k = 4

end Families
end QuadraticNumberFields
