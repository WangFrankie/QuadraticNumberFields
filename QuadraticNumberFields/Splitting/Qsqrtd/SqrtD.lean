/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic

/-!
# The integral square root `√d`

This file provides the canonical integral square root `√d` of `K = ℚ(√d)` as an
element of the ring of integers `𝓞(ℚ(√d))`, together with the ideal identity
`(√d)² = (d)`.

Unlike the monogenic generator `θ(d)` (which is `(1 + √d)/2` when `d ≡ 1 [ZMOD 4]`),
`sqrtdInt d` is uniformly the image of the standard `QuadraticAlgebra.omega`, which
squares to `d`. It is the principal generator behind the genus-theory relation
`∏_{odd ramified p} 𝔭_p = (√d)`.
-/

namespace QuadraticNumberFields
namespace Splitting

open scoped NumberField QuadraticNumberFields.Splitting QuadraticAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- In `K = ℚ(√d)`, the standard square root `omega` squares to `d`. -/
theorem omega_sq_eq_intCast :
    (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) ^ 2 = algebraMap ℤ (Qsqrtd (d : ℚ)) d := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_add]
  apply QuadraticAlgebra.ext <;> simp

/-- The standard square root `omega` of `K = ℚ(√d)` is an algebraic integer. -/
theorem omega_isIntegral : IsIntegral ℤ (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d,
    Polynomial.monic_X_pow_sub_C d (by norm_num), ?_⟩
  change (Polynomial.aeval (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)))
      (Polynomial.X ^ 2 - Polynomial.C d) = 0
  simp [map_sub, map_pow, omega_sq_eq_intCast d]

/-- The integral square root `√d` as an element of `𝓞(ℚ(√d))`. -/
noncomputable def sqrtdInt : 𝓞(d) := ⟨QuadraticAlgebra.omega, omega_isIntegral d⟩

@[simp] theorem coe_sqrtdInt :
    (sqrtdInt d : Qsqrtd (d : ℚ)) = QuadraticAlgebra.omega := rfl

/-- `√d` squares to `d` in `𝓞(ℚ(√d))`. -/
theorem sqrtdInt_sq : sqrtdInt d ^ 2 = algebraMap ℤ (𝓞(d)) d := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_pow]
  simp only [coe_sqrtdInt]
  rw [omega_sq_eq_intCast d]
  simp

/-- The principal ideal `(√d)` squares to the ideal `(d)`. -/
theorem span_sqrtdInt_sq :
    (Ideal.span {sqrtdInt d}) ^ 2 = Ideal.span {algebraMap ℤ (𝓞(d)) d} := by
  rw [Ideal.span_singleton_pow, sqrtdInt_sq]

end Splitting
end QuadraticNumberFields
