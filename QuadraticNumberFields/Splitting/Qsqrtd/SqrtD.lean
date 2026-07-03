/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic

/-!
# The Integral Square Root `√d`

This file defines the element `√d` of `𝓞(ℚ(√d))` and proves the principal
ideal identity `(√d)² = (d)`.
-/

namespace QuadraticNumberFields
namespace Splitting

open scoped NumberField QuadraticNumberFields.Splitting QuadraticAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- In `ℚ(√d)`, `omega` squares to `d`. -/
theorem omega_sq_eq_intCast :
    (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) ^ 2 =
      algebraMap ℤ (Qsqrtd (d : ℚ)) d := by
  rw [sq, QuadraticAlgebra.omega_mul_omega_eq_add]
  apply QuadraticAlgebra.ext <;> simp

/-- In `ℚ(√d)`, `omega` is integral over `ℤ`. -/
theorem omega_isIntegral :
    IsIntegral ℤ (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C d,
    Polynomial.monic_X_pow_sub_C d (by norm_num), ?_⟩
  change (Polynomial.aeval (QuadraticAlgebra.omega : Qsqrtd (d : ℚ)))
      (Polynomial.X ^ 2 - Polynomial.C d) = 0
  simp [map_sub, map_pow, omega_sq_eq_intCast d]

/-- The integral square root `√d` as an element of `𝓞(ℚ(√d))`. -/
noncomputable def sqrtdInt : 𝓞(d) :=
  ⟨QuadraticAlgebra.omega, omega_isIntegral d⟩

@[simp]
theorem coe_sqrtdInt :
    (sqrtdInt d : Qsqrtd (d : ℚ)) = QuadraticAlgebra.omega :=
  rfl

/-- `√d` squares to `d` in `𝓞(ℚ(√d))`. -/
theorem sqrtdInt_sq :
    sqrtdInt d ^ 2 = algebraMap ℤ (𝓞(d)) d := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_pow]
  simp only [coe_sqrtdInt]
  rw [omega_sq_eq_intCast d]
  simp

/-- The principal ideal `(√d)` squares to the ideal `(d)`. -/
theorem span_sqrtdInt_sq :
    (Ideal.span {sqrtdInt d}) ^ 2 =
      Ideal.span {algebraMap ℤ (𝓞(d)) d} := by
  rw [Ideal.span_singleton_pow, sqrtdInt_sq]

end Splitting
end QuadraticNumberFields
