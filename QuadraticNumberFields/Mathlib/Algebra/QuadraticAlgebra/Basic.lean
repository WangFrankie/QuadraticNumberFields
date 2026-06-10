/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic

/-!
# Units of Quadratic Algebras

Material destined for mathlib.

Explicit units of `QuadraticAlgebra R a b` attached to elements of norm `±1`:
the relation `z * star z = N(z)` makes the (negated) conjugate an explicit
inverse.
-/

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R] {a b : R}

/-- The norm of `⟨x, y⟩ : QuadraticAlgebra R a b` in coordinates. -/
-- Repository use: coordinate computations for units of `ℤ[√d]` and `ℤ[(1+√d)/2]`.
theorem norm_mk (x y : R) :
    norm (⟨x, y⟩ : QuadraticAlgebra R a b) = x * x + b * x * y - a * y * y :=
  rfl

/-- The unit of `QuadraticAlgebra R a b` attached to an element of norm `1`;
the inverse is the conjugate. -/
-- Repository use: explicit units of `ℤ[√d]` and `ℤ[(1+√d)/2]` from Pell-type solutions.
def unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (QuadraticAlgebra R a b)ˣ where
  val := z
  inv := star z
  val_inv := by rw [← algebraMap_norm_eq_mul_star, h, map_one]
  inv_val := by rw [mul_comm, ← algebraMap_norm_eq_mul_star, h, map_one]

@[simp]
theorem val_unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (unitOfNormOne z h : QuadraticAlgebra R a b) = z :=
  rfl

@[simp]
theorem val_inv_unitOfNormOne (z : QuadraticAlgebra R a b) (h : norm z = 1) :
    (((unitOfNormOne z h)⁻¹ : (QuadraticAlgebra R a b)ˣ) : QuadraticAlgebra R a b) = star z :=
  rfl

/-- The unit of `QuadraticAlgebra R a b` attached to an element of norm `-1`;
the inverse is the negated conjugate. -/
-- Repository use: explicit units of `ℤ[√d]` from norm-`-1` Pell solutions.
def unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (QuadraticAlgebra R a b)ˣ where
  val := z
  inv := -star z
  val_inv := by rw [mul_neg, ← algebraMap_norm_eq_mul_star, h, map_neg, map_one, neg_neg]
  inv_val := by
    rw [neg_mul, mul_comm (star z) z, ← algebraMap_norm_eq_mul_star, h, map_neg, map_one, neg_neg]

@[simp]
theorem val_unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (unitOfNormNegOne z h : QuadraticAlgebra R a b) = z :=
  rfl

@[simp]
theorem val_inv_unitOfNormNegOne (z : QuadraticAlgebra R a b) (h : norm z = -1) :
    (((unitOfNormNegOne z h)⁻¹ : (QuadraticAlgebra R a b)ˣ) : QuadraticAlgebra R a b) =
      -star z :=
  rfl

section Int

variable {a b : ℤ}

/-- Over `ℤ`, a nonpositive discriminant `b² + 4a ≤ 0` makes the norm
nonnegative: `4·N(z) = (2·re + b·im)² - (b² + 4a)·im²`. -/
-- Repository use: unit-group classification for imaginary quadratic orders.
theorem norm_nonneg_of_discr_nonpos (h : b ^ 2 + 4 * a ≤ 0) (z : QuadraticAlgebra ℤ a b) :
    0 ≤ norm z := by
  have hz := norm_def z
  nlinarith [sq_nonneg (2 * z.re + b * z.im), sq_nonneg z.im]

/-- Over `ℤ`, a discriminant `b² + 4a < -4` forces the unit group of
`QuadraticAlgebra ℤ a b` to be `{±1}`. -/
-- Repository use: the `±1` unit classifications for `ℤ[√d]` (`d < -1`) and
-- `ℤ[(1+√d)/2]` (`d ≤ -7`) are instances of this single statement.
theorem isUnit_iff_eq_one_or_neg_one_of_discr_lt_neg_four (h : b ^ 2 + 4 * a < -4)
    (z : QuadraticAlgebra ℤ a b) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  constructor
  · intro hz
    obtain ⟨x, y⟩ := z
    rcases Int.isUnit_iff.mp (isUnit_iff_norm_isUnit.mp hz) with hn | hn
    · rw [norm_mk] at hn
      have hy : y = 0 := by nlinarith [sq_nonneg (2 * x + b * y), sq_nonneg y]
      subst hy
      have hx : x * x = 1 := by linarith
      rcases mul_self_eq_one_iff.mp hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (by ext <;> simp)
    · have h0 : (0 : ℤ) ≤ norm (⟨x, y⟩ : QuadraticAlgebra ℤ a b) :=
        norm_nonneg_of_discr_nonpos (by linarith) _
      omega
  · rintro (rfl | rfl)
    · exact isUnit_one
    · exact isUnit_one.neg

end Int

end QuadraticAlgebra
