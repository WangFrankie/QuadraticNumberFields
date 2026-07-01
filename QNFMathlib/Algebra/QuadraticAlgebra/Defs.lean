/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Discriminant
import Mathlib.Tactic.Ring

/-!
# Quadratic Algebra Defs

Material destined for mathlib.
-/

namespace QuadraticAlgebra

section IsQuadraticExtension

variable {R : Type*} [CommSemiring R] [StrongRankCondition R] (a b : R)

/-- A quadratic algebra is a quadratic extension of its base ring. -/
-- Repository use: this is an instance. It supplies
-- `Algebra.IsQuadraticExtension ℚ (Qsqrtd d)` through the `Qsqrtd` abbreviation,
-- and downstream `NumberField`/ring-of-integers instance search relies on it.
instance instIsQuadraticExtension :
    Algebra.IsQuadraticExtension R (QuadraticAlgebra R a b) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two a b

end IsQuadraticExtension

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}

/-- The left multiplication matrix of an element in `QuadraticAlgebra R a b`
with respect to the basis `{1, i}`. -/
-- Repository use: `Qsqrtd.trace_eq_re_add_re_star` uses this directly, and the
-- integer trace/discriminant computations below reuse it.
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
-- Repository use: this is a generic coordinate identity for
-- `QuadraticAlgebra R a 0` calculations.
lemma mul_re_add_im_eq (x y : QuadraticAlgebra R a 0) :
    (x * y).re + (x * y).im =
      (x.re + x.im) * (y.re + y.im) + (a - 1) * x.im * y.im := by
  simp only [re_mul, im_mul]
  ring

/-- The fundamental identity for `re - im` of a product in
`QuadraticAlgebra R a 0`. -/
-- Repository use: this is a generic coordinate identity for
-- `QuadraticAlgebra R a 0` calculations.
lemma mul_re_sub_im_eq (x y : QuadraticAlgebra R a 0) :
    (x * y).re - (x * y).im =
      (x.re - x.im) * (y.re - y.im) + (a - 1) * x.im * y.im := by
  simp only [re_mul, im_mul]
  ring

end CommRing

section Int

open Matrix

/-- The algebraic trace on `QuadraticAlgebra ℤ a b` is `2 * x.re + b * x.im`. -/
-- Repository use: `RingOfIntegers/Discriminant.lean` uses this to compute the
-- standard integral bases for `ℤ[√d]` and `ℤ[(1+√d)/2]`.
theorem trace_int (a b : ℤ) (x : QuadraticAlgebra ℤ a b) :
    Algebra.trace ℤ (QuadraticAlgebra ℤ a b) x = 2 * x.re + b * x.im := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis a b)]
  rw [leftMulMatrix_eq]
  simp [Matrix.trace, Fin.sum_univ_two]
  ring

/-- The trace matrix of the standard basis of `QuadraticAlgebra ℤ a b` is
`[[2, b], [b, 2 * a + b²]]`. -/
-- Repository use: `RingOfIntegers/Discriminant.lean` uses this through
-- `QuadraticAlgebra.discr_basis_int`.
theorem traceMatrix_basis_int (a b : ℤ) :
    Algebra.traceMatrix ℤ (QuadraticAlgebra.basis a b) =
      !![2, b; b, 2 * a + b ^ 2] := by
  ext i j
  simp only [Algebra.traceMatrix_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trace_int, QuadraticAlgebra.basis, pow_two]

/-- The discriminant of the standard basis of `QuadraticAlgebra ℤ a b` is `4a + b²`. -/
-- Repository use: `RingOfIntegers/Discriminant.lean` uses this for both
-- ring-of-integers branches.
theorem discr_basis_int (a b : ℤ) :
    Algebra.discr ℤ (QuadraticAlgebra.basis a b) = 4 * a + b ^ 2 := by
  rw [Algebra.discr_def, traceMatrix_basis_int]
  simp [Matrix.det_fin_two]
  ring

end Int

end QuadraticAlgebra
