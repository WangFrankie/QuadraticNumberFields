/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Right normalization of two-by-two invertible matrices

Material destined for mathlib.

Scale the second column by the supplied unit inverse determinant to obtain an
actual special-linear matrix over any commutative ring. Multiplication on the
right by `diag(1, det A)` recovers `A`. This is not a group homomorphism and does
not require a field, nontriviality, or any quadratic-algebra structure.

Extracted from `BakerHeegnerStark/LinearAlgebra/Matrix/QuadraticCentralizer.lean:74–94`
at BakerHeegnerStark commit `cd45b1c23ec3a3e630d5f36a058483c3fcbcc08d`.
-/

open scoped MatrixGroups

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R]

/-- Right-normalization of a two-by-two unit matrix to determinant one. -/
def specialLinearPart (A : GL (Fin 2) R) : SL(2, R) :=
  let r : R := A.det.inv
  ⟨!![A 0 0, A 0 1 * r; A 1 0, A 1 1 * r], by
    have hdet : (A 0 0 * A 1 1 - A 0 1 * A 1 0) * r = 1 := by
      simpa only [r, GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] using A.det.val_inv
    simp only [Matrix.det_fin_two]
    dsimp
    calc
      _ = (A 0 0 * A 1 1 - A 0 1 * A 1 0) * r := by ring
      _ = 1 := hdet⟩

/-- The right-normalized part recovers the original matrix with its determinant diagonal. -/
theorem specialLinearPart_mul_diagonal_det (A : GL (Fin 2) R) :
    (A.specialLinearPart : Matrix (Fin 2) (Fin 2) R) * !![1, 0; 0, (A.det : R)] =
      (A : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [specialLinearPart, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals dsimp
  all_goals simp only [mul_zero, add_zero, zero_add, mul_one, mul_assoc, Units.inv_mul]

end Matrix.GeneralLinearGroup
