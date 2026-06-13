/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proper Equivalence of Binary Quadratic Forms

This file defines the explicit `SL₂(ℤ)` coordinate action on binary quadratic
forms and proves the elementary invariants needed by proper equivalence.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

open Matrix

/-- The integral special linear group in dimension two. -/
abbrev SL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ

private abbrev m00 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0
private abbrev m01 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1
private abbrev m10 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0
private abbrev m11 (g : SL2Z) : ℤ := (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1

/-- Coordinate transform of a form by an `SL₂(ℤ)` matrix. -/
def transform (Q : BinaryQuadraticForm) (g : SL2Z) : BinaryQuadraticForm where
  a := Q.a * m00 g ^ 2 + Q.b * m00 g * m10 g + Q.c * m10 g ^ 2
  b := 2 * Q.a * m00 g * m01 g +
    Q.b * (m00 g * m11 g + m01 g * m10 g) +
    2 * Q.c * m10 g * m11 g
  c := Q.a * m01 g ^ 2 + Q.b * m01 g * m11 g + Q.c * m11 g ^ 2

@[simp] theorem transform_one (Q : BinaryQuadraticForm) :
    transform Q (1 : SL2Z) = Q := by
  cases Q
  ext <;> norm_num [transform, m00, m01, m10, m11]

/-- The coordinate transform is compatible with multiplication in `SL₂(ℤ)`. -/
theorem transform_mul (Q : BinaryQuadraticForm) (g h : SL2Z) :
    transform (transform Q g) h = transform Q (g * h) := by
  rcases Q with ⟨A, B, C⟩
  ext <;>
    simp [transform, m00, m01, m10, m11, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring_nf

/-- Proper equivalence: forms lie in the same `SL₂(ℤ)` orbit. -/
def ProperEquivalent (Q R : BinaryQuadraticForm) : Prop :=
  ∃ g : SL2Z, transform Q g = R

/-- Proper equivalence is reflexive. -/
theorem ProperEquivalent.refl (Q : BinaryQuadraticForm) : ProperEquivalent Q Q :=
  ⟨1, transform_one Q⟩

/-- Proper equivalence is symmetric. -/
theorem ProperEquivalent.symm {Q R : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) : ProperEquivalent R Q := by
  rcases hQR with ⟨g, rfl⟩
  refine ⟨g⁻¹, ?_⟩
  rw [transform_mul, mul_inv_cancel, transform_one]

/-- Proper equivalence is transitive. -/
theorem ProperEquivalent.trans {Q R S : BinaryQuadraticForm}
    (hQR : ProperEquivalent Q R) (hRS : ProperEquivalent R S) :
    ProperEquivalent Q S := by
  rcases hQR with ⟨g, rfl⟩
  rcases hRS with ⟨h, rfl⟩
  exact ⟨g * h, (transform_mul Q g h).symm⟩

private theorem disc_transform_aux (a b c p q r s : ℤ) (hdet : p * s - q * r = 1) :
    (2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s) ^ 2 -
        4 * (a * p ^ 2 + b * p * r + c * r ^ 2) *
          (a * q ^ 2 + b * q * s + c * s ^ 2) =
      b ^ 2 - 4 * a * c := by
  calc
    (2 * a * p * q + b * (p * s + q * r) + 2 * c * r * s) ^ 2 -
        4 * (a * p ^ 2 + b * p * r + c * r ^ 2) *
          (a * q ^ 2 + b * q * s + c * s ^ 2)
        = (b ^ 2 - 4 * a * c) * (p * s - q * r) ^ 2 := by ring
    _ = b ^ 2 - 4 * a * c := by
      rw [hdet]
      ring

/-- The `SL₂(ℤ)` coordinate transform preserves discriminants. -/
theorem disc_transform (Q : BinaryQuadraticForm) (g : SL2Z) :
    (transform Q g).disc = Q.disc := by
  let p : ℤ := m00 g
  let q : ℤ := m01 g
  let r : ℤ := m10 g
  let s : ℤ := m11 g
  have hdet : p * s - q * r = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa [p, q, r, s, m00, m01, m10, m11] using h
  rcases Q with ⟨A, B, C⟩
  simpa [transform, disc, p, q, r, s] using disc_transform_aux A B C p q r s hdet

end BinaryQuadraticForm
end QuadraticNumberFields
