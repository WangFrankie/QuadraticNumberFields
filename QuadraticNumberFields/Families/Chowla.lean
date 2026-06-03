/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.Yokoi

/-!
# Chowla-Type Families

This file isolates Chowla-style parameter families for later class-number-one
experiments.
-/

namespace QuadraticNumberFields
namespace Families

/-- A Chowla-style shifted-square family `m^2 + c`. -/
def chowlaShiftD (m c : ℤ) : ℤ :=
  quadraticShift m c

end Families
end QuadraticNumberFields
