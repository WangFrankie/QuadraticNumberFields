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

end QuadraticAlgebra
