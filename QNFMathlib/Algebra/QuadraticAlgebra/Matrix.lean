/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.Algebra.QuadraticAlgebra.Defs
import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Matrices commuting with a quadratic generator

Material destined for mathlib.

The centralizer of multiplication by `omega` is exactly the image of the existing
`Algebra.leftMulMatrix` representation in the basis `1, omega`. This holds over
commutative semirings, without a discriminant or nontriviality assumption. Over
commutative rings, the determinant is the existing quadratic-algebra norm.

Generalized from `BakerHeegnerStark/LinearAlgebra/Matrix/QuadraticCentralizer.lean`
at BakerHeegnerStark commit `cd45b1c23ec3a3e630d5f36a058483c3fcbcc08d`.
The trace-zero generator is the specialization `a = -m`, `b = 0`.
-/

namespace QuadraticAlgebra

section CommSemiring

variable {R : Type*} [CommSemiring R] {a b : R}

/-- The coordinate characterization of the quadratic generator's centralizer. -/
theorem commute_leftMulMatrix_omega_iff (A : Matrix (Fin 2) (Fin 2) R) :
    Commute A (Algebra.leftMulMatrix (basis a b) omega) ↔
      A 0 1 = a * A 1 0 ∧ A 1 1 = A 0 0 + b * A 1 0 := by
  have hgen : Algebra.leftMulMatrix (basis a b) omega = !![0, a; 1, b] := by
    simp [leftMulMatrix_eq]
  rw [hgen]
  constructor
  · intro h
    change A * !![0, a; 1, b] = !![0, a; 1, b] * A at h
    constructor
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ h 0 0
    · simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun₂ h 1 0
  · rintro ⟨h01, h11⟩
    change A * !![0, a; 1, b] = !![0, a; 1, b] * A
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_two, h01, h11]
    all_goals ring

/-- The first column recovers the element represented by a commuting matrix. -/
theorem leftMulMatrix_eq_of_commute (A : Matrix (Fin 2) (Fin 2) R)
    (h : Commute A (Algebra.leftMulMatrix (basis a b) omega)) :
    Algebra.leftMulMatrix (basis a b) (⟨A 0 0, A 1 0⟩ : QuadraticAlgebra R a b) = A := by
  obtain ⟨h01, h11⟩ := (commute_leftMulMatrix_omega_iff A).mp h
  rw [leftMulMatrix_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h01, h11]

/-- Every matrix in the centralizer represents exactly one quadratic element. -/
theorem commute_leftMulMatrix_omega_iff_existsUnique (A : Matrix (Fin 2) (Fin 2) R) :
    Commute A (Algebra.leftMulMatrix (basis a b) omega) ↔
      ∃! z : QuadraticAlgebra R a b, Algebra.leftMulMatrix (basis a b) z = A := by
  constructor
  · intro h
    refine ⟨⟨A 0 0, A 1 0⟩, leftMulMatrix_eq_of_commute A h, ?_⟩
    intro z hz
    exact Algebra.leftMulMatrix_injective (basis a b)
      (hz.trans (leftMulMatrix_eq_of_commute A h).symm)
  · rintro ⟨z, rfl, _⟩
    change Algebra.leftMulMatrix (basis a b) z * Algebra.leftMulMatrix (basis a b) omega =
      Algebra.leftMulMatrix (basis a b) omega * Algebra.leftMulMatrix (basis a b) z
    rw [← map_mul, ← map_mul, mul_comm]

/-- The full centralizer of the quadratic generator is commutative. -/
theorem commute_of_commute_leftMulMatrix_omega {A B : Matrix (Fin 2) (Fin 2) R}
    (hA : Commute A (Algebra.leftMulMatrix (basis a b) omega))
    (hB : Commute B (Algebra.leftMulMatrix (basis a b) omega)) : Commute A B := by
  obtain ⟨z, rfl, _⟩ := (commute_leftMulMatrix_omega_iff_existsUnique A).mp hA
  obtain ⟨w, rfl, _⟩ := (commute_leftMulMatrix_omega_iff_existsUnique B).mp hB
  change Algebra.leftMulMatrix (basis a b) z * Algebra.leftMulMatrix (basis a b) w =
    Algebra.leftMulMatrix (basis a b) w * Algebra.leftMulMatrix (basis a b) z
  rw [← map_mul, ← map_mul, mul_comm]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] {a b : R}

/-- The matrix determinant is the existing quadratic norm, not a second norm definition. -/
@[simp]
theorem det_leftMulMatrix (z : QuadraticAlgebra R a b) :
    (Algebra.leftMulMatrix (basis a b) z).det = z.norm := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.det_toMatrix]
  exact det_toLinearMap_eq_norm z

/-- A commuting matrix has the norm of its first-column element as determinant. -/
theorem det_eq_norm_of_commute_leftMulMatrix_omega (A : Matrix (Fin 2) (Fin 2) R)
    (h : Commute A (Algebra.leftMulMatrix (basis a b) omega)) :
    A.det = (⟨A 0 0, A 1 0⟩ : QuadraticAlgebra R a b).norm := by
  exact (congrArg Matrix.det (leftMulMatrix_eq_of_commute A h)).symm.trans
    (det_leftMulMatrix _)

open scoped MatrixGroups in
/-- A commuting invertible matrix supplies a genuine unit inverse for its norm. -/
theorem norm_mul_inv_det_eq_one_of_commute_leftMulMatrix_omega (A : GL (Fin 2) R)
    (h : Commute (A : Matrix (Fin 2) (Fin 2) R)
      (Algebra.leftMulMatrix (basis a b) omega)) :
    (⟨A 0 0, A 1 0⟩ : QuadraticAlgebra R a b).norm * (A.det.inv : R) = 1 := by
  rw [← det_eq_norm_of_commute_leftMulMatrix_omega _ h]
  exact A.det.val_inv

end CommRing

end QuadraticAlgebra
