/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.Ideal.Span
import QuadraticNumberFields.RingOfIntegers.Conj
import QuadraticNumberFields.Splitting.Qsqrtd.Monogenic

/-!
# The Integral Square Root `√d`

This file defines the element `√d` of `𝓞(ℚ(√d))`, the canonical embedding
`ℤ[√d] → 𝓞(ℚ(√d))`, and the principal ideal identity `(√d)² = (d)`.
-/

namespace QuadraticNumberFields
namespace Splitting

open scoped NumberField nonZeroDivisors QuadraticNumberFields.Splitting QuadraticAlgebra

attribute [-instance] DivisionRing.toRatAlgebra

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

/-- Coercing the integral expression `x + y√d` to `ℚ(√d)` gives coordinates
`(x, y)`. -/
theorem coe_intCast_add_intCast_mul_sqrtdInt (x y : ℤ) :
    ((algebraMap ℤ 𝓞(d) x + algebraMap ℤ 𝓞(d) y * sqrtdInt d : 𝓞(d)) :
      Qsqrtd (d : ℚ)) =
      (⟨(x : ℚ), (y : ℚ)⟩ : Qsqrtd (d : ℚ)) := by
  apply QuadraticAlgebra.ext <;> simp [coe_sqrtdInt, QuadraticAlgebra.omega]

/-- Coercing the integral expression `x - y√d` to `ℚ(√d)` gives coordinates
`(x, -y)`. -/
theorem coe_intCast_sub_intCast_mul_sqrtdInt (x y : ℤ) :
    ((algebraMap ℤ 𝓞(d) x - algebraMap ℤ 𝓞(d) y * sqrtdInt d : 𝓞(d)) :
      Qsqrtd (d : ℚ)) =
      (⟨(x : ℚ), -(y : ℚ)⟩ : Qsqrtd (d : ℚ)) := by
  apply QuadraticAlgebra.ext <;> simp [coe_sqrtdInt, QuadraticAlgebra.omega]

/-- Conjugation negates the `√d` coordinate of an integral `√d`-linear
expression. -/
theorem conjAutRingOfIntegers_intCast_add_intCast_mul_sqrtdInt (x y : ℤ) :
    conjAutRingOfIntegers (Qsqrtd (d : ℚ))
        (algebraMap ℤ 𝓞(d) x + algebraMap ℤ 𝓞(d) y * sqrtdInt d) =
      algebraMap ℤ 𝓞(d) x - algebraMap ℤ 𝓞(d) y * sqrtdInt d := by
  let K := Qsqrtd (d : ℚ)
  apply NumberField.RingOfIntegers.ext
  rw [coe_conjAutRingOfIntegers_apply]
  change QuadraticField.conjAut K
      ((algebraMap ℤ 𝓞(d) x + algebraMap ℤ 𝓞(d) y * sqrtdInt d : 𝓞(d)) : K) =
    ((algebraMap ℤ 𝓞(d) x - algebraMap ℤ 𝓞(d) y * sqrtdInt d : 𝓞(d)) : K)
  rw [coe_intCast_add_intCast_mul_sqrtdInt, coe_intCast_sub_intCast_mul_sqrtdInt]
  change Qsqrtd.starAlgEquiv (d : ℚ) (⟨(x : ℚ), (y : ℚ)⟩ : K) = _
  rw [Qsqrtd.starAlgEquiv_apply]
  apply QuadraticAlgebra.ext <;> simp [QuadraticAlgebra.star_mk]

/-- The integral square root `√d` is nonzero in `𝓞(ℚ(√d))`. -/
theorem sqrtdInt_ne_zero : sqrtdInt d ≠ 0 := by
  intro h
  have hcoe : ((sqrtdInt d : 𝓞(d)) : Qsqrtd (d : ℚ)) = 0 := by
    rw [h]
    simp
  rw [coe_sqrtdInt] at hcoe
  have him := congrArg QuadraticAlgebra.im hcoe
  norm_num at him

/-- The principal ideal `(√d)`, bundled as a nonzero integral ideal. -/
noncomputable def sqrtdSpanNonzeroIdeal : (Ideal (𝓞(d)))⁰ :=
  Ideal.spanSingletonNonzero (sqrtdInt_ne_zero d)

@[simp]
theorem coe_sqrtdSpanNonzeroIdeal :
    (sqrtdSpanNonzeroIdeal d : Ideal (𝓞(d))) =
      Ideal.span ({sqrtdInt d} : Set (𝓞(d))) :=
  rfl

/-- `√d` squares to `d` in `𝓞(ℚ(√d))`. -/
theorem sqrtdInt_sq :
    sqrtdInt d ^ 2 = algebraMap ℤ (𝓞(d)) d := by
  apply NumberField.RingOfIntegers.ext
  rw [NumberField.RingOfIntegers.coe_eq_algebraMap, map_pow]
  simp only [coe_sqrtdInt]
  rw [omega_sq_eq_intCast d]
  simp

/-- The canonical embedding `ℤ[√d] → 𝓞(ℚ(√d))` sending the formal square root
to the integral element `√d`. -/
noncomputable def zsqrtdEmbedding : Zsqrtd d →+* 𝓞(d) :=
  Zsqrtd.lift (sqrtdInt d) (by simpa [pow_two] using sqrtdInt_sq d)

@[simp]
theorem zsqrtdEmbedding_apply (z : Zsqrtd d) :
    zsqrtdEmbedding d z =
      algebraMap ℤ (𝓞(d)) z.re + algebraMap ℤ (𝓞(d)) z.im * sqrtdInt d := by
  simp [zsqrtdEmbedding, Zsqrtd.lift_apply]

/-- The canonical embedding `ℤ[√d] → 𝓞(ℚ(√d))` is injective. -/
theorem zsqrtdEmbedding_injective : Function.Injective (zsqrtdEmbedding d) := by
  intro x y hxy
  have hcoe := congrArg (fun z : 𝓞(d) => ((z : Qsqrtd (d : ℚ)))) hxy
  apply QuadraticAlgebra.ext
  · have hre := congrArg QuadraticAlgebra.re hcoe
    exact_mod_cast (by simpa [zsqrtdEmbedding_apply, coe_sqrtdInt,
      QuadraticAlgebra.omega] using hre)
  · have him := congrArg QuadraticAlgebra.im hcoe
    exact_mod_cast (by simpa [zsqrtdEmbedding_apply, coe_sqrtdInt,
      QuadraticAlgebra.omega] using him)

/-- The principal ideal `(√d)` squares to the ideal `(d)`. -/
theorem span_sqrtdInt_sq :
    (Ideal.span {sqrtdInt d}) ^ 2 =
      Ideal.span {algebraMap ℤ (𝓞(d)) d} := by
  rw [Ideal.span_singleton_pow, sqrtdInt_sq]

/-- A rational prime remains nonzero in the ring of integers of `ℚ(√d)`. -/
theorem natCast_ne_zero_ringOfIntegers {p : ℕ} (hp : p.Prime) :
    (p : 𝓞(d)) ≠ 0 := by
  change algebraMap ℤ (𝓞(d)) (p : ℤ) ≠ 0
  exact (FaithfulSMul.algebraMap_injective ℤ (𝓞(d))).ne (by
    exact_mod_cast hp.ne_zero)

/-- The principal ideal generated by a rational prime in `𝓞(ℚ(√d))`, bundled as
a nonzero integral ideal. -/
def natCastSpanNonzeroIdeal (p : ℕ) (hp : p.Prime) : (Ideal (𝓞(d)))⁰ :=
  Ideal.spanSingletonNonzero (natCast_ne_zero_ringOfIntegers d hp)

@[simp]
theorem coe_natCastSpanNonzeroIdeal (p : ℕ) (hp : p.Prime) :
    (natCastSpanNonzeroIdeal d p hp : Ideal (𝓞(d))) =
      Ideal.span ({(p : 𝓞(d))} : Set (𝓞(d))) :=
  rfl

end Splitting
end QuadraticNumberFields
