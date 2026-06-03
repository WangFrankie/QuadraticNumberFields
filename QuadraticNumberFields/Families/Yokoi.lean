/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.Basic

/-!
# Yokoi-Type Families

This file records parameter families of the form `m^2 + r`, including the
classical Yokoi and Chowla-style real quadratic families.
-/

namespace QuadraticNumberFields
namespace Families

/-- The one-parameter family `m^2 + r`. -/
def quadraticShift (m r : ℤ) : ℤ :=
  m ^ 2 + r

/-- Yokoi's family `m^2 + 4`. -/
def yokoiD (m : ℤ) : ℤ :=
  quadraticShift m 4

/-- The family `m^2 + 1`. -/
def chowlaD (m : ℤ) : ℤ :=
  quadraticShift m 1

/-- The family `m^2 + 2r`. -/
def yokoiTwoParameterD (m r : ℤ) : ℤ :=
  quadraticShift m (2 * r)

end Families
end QuadraticNumberFields
