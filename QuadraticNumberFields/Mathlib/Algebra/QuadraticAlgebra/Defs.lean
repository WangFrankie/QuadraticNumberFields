/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Quadratic Algebra Defs

Material destined for mathlib.
-/

namespace QuadraticAlgebra

variable {R : Type*} [CommSemiring R] {a b : R}

/-- The left multiplication matrix of an element in `QuadraticAlgebra R a b`
with respect to the basis `{1, i}`.
PR#36347 this theorem will be in QuadraticAlgebra.Defs.lean -/
theorem leftMulMatrix_eq (x : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) x = !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  -- In the basis `{1, i}`, multiplication by `x = x.re + x.im * i`
  -- sends `1` and `i` to the two displayed columns.
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

end QuadraticAlgebra
