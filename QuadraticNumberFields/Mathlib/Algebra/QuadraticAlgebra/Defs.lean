/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Ring

/-!
# Quadratic Algebra Defs

Material destined for mathlib.
-/

namespace QuadraticAlgebra

section IsQuadraticExtension

variable {R : Type*} [CommSemiring R] [StrongRankCondition R] (a b : R)

/-- A quadratic algebra is a quadratic extension of its base ring. -/
instance instIsQuadraticExtension :
    Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

end IsQuadraticExtension

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}

/-- The left multiplication matrix of an element in `QuadraticAlgebra R a b`
with respect to the basis `{1, i}`. -/
theorem leftMulMatrix_eq (x : QuadraticAlgebra R a b) :
    Algebra.leftMulMatrix (basis a b) x = !![x.re, a * x.im; x.im, x.re + b * x.im] := by
  -- In the basis `{1, i}`, multiplication by `x = x.re + x.im * i`
  -- sends `1` and `i` to the two displayed columns.
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    rw [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply]
    simp [QuadraticAlgebra.basis]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {a : R}

/-- The fundamental identity for `re + im` of a product in
`QuadraticAlgebra R a 0`. -/
lemma mul_re_add_im_eq (x y : QuadraticAlgebra R a 0) :
    (x * y).re + (x * y).im =
      (x.re + x.im) * (y.re + y.im) + (a - 1) * x.im * y.im := by
  simp only [re_mul, im_mul]
  ring

/-- The fundamental identity for `re - im` of a product in
`QuadraticAlgebra R a 0`. -/
lemma mul_re_sub_im_eq (x y : QuadraticAlgebra R a 0) :
    (x * y).re - (x * y).im =
      (x.re - x.im) * (y.re - y.im) + (a - 1) * x.im * y.im := by
  simp only [re_mul, im_mul]
  ring

end CommRing

end QuadraticAlgebra
