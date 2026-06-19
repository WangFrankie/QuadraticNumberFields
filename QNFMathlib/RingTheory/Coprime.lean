/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.Ring

/-!
# Coprime Lemmas

Material destined for mathlib.
-/

namespace IsCoprime

variable {R : Type*} [CommSemiring R] {a b : R}

/-- If `a` is coprime to `2 * b`, then it is coprime to `4 * b`. -/
-- Repository use: Heegner's Diophantine reduction uses this after rewriting
-- `X ^ 3 + 1` as twice a square.
theorem four_mul_right_of_two_mul_right (h : IsCoprime a ((2 : R) * b)) :
    IsCoprime a ((4 : R) * b) := by
  have hparts := IsCoprime.mul_right_iff.mp h
  have hcop2 : IsCoprime a (2 : R) := hparts.1
  convert hcop2.mul_right h using 1
  ring

end IsCoprime
