/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification

/-!
# Norm Multiplicativity

This file formalizes norm properties for quadratic number fields and their
rings of integers, with sections separating explicit formulas from the
classification-dependent statements.
-/

open scoped NumberField

namespace QuadraticNumberFields

/-! ## Norm Multiplicativity on `Q(√d)` -/

/-- The norm on `Q(√d)` is multiplicative: `N(xy) = N(x) N(y)`. -/
theorem norm_mul (d : ℚ) (x y : Qsqrtd d) :
    Qsqrtd.norm (x * y) = Qsqrtd.norm x * Qsqrtd.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm maps `1` to `1`. -/
theorem norm_one (d : ℚ) : Qsqrtd.norm (1 : Qsqrtd d) = 1 :=
  QuadraticAlgebra.norm.map_one

namespace RingOfIntegers

/-! ## Explicit Norm Formulas -/

/-- The norm of an element of `Zsqrtd d` is an integer: `N(a + b√d) = a² - d·b²`. -/
theorem norm_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    Zsqrtd.norm z = z.re ^ 2 - d * z.im ^ 2 := by
  unfold Zsqrtd.norm QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- The norm on `Zsqrtd d` is multiplicative. -/
theorem norm_mul_zsqrtd (d : ℤ) (x y : Zsqrtd d) :
    Zsqrtd.norm (x * y) = Zsqrtd.norm x * Zsqrtd.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm of `a + b√d` embeds to `a² - d·b²` in `ℚ`. -/
theorem norm_zsqrtd_toQsqrtd (d : ℤ) (z : Zsqrtd d) :
    Qsqrtd.norm (Zsqrtd.toQsqrtd z) = (Zsqrtd.norm z : ℚ) := by
  unfold Zsqrtd.norm Qsqrtd.norm Zsqrtd.toQsqrtd QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  push_cast
  ring

/-- For `d % 4 ≠ 1`, elements of `ℤ[√d]` have integer norm after embedding. -/
theorem norm_mem_zsqrtd (d : ℤ) (z : Zsqrtd d) :
    ∃ n : ℤ, Qsqrtd.norm (Zsqrtd.toQsqrtd z) = n := by
  exact ⟨Zsqrtd.norm z, norm_zsqrtd_toQsqrtd d z⟩

/-- The norm on `ZOnePlusSqrtOverTwo k` is multiplicative. -/
theorem norm_mul_zOnePlusSqrtOverTwo (k : ℤ) (x y : ZOnePlusSqrtOverTwo k) :
    QuadraticAlgebra.norm (x * y) =
      QuadraticAlgebra.norm x * QuadraticAlgebra.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm of an element of `ZOnePlusSqrtOverTwo k` is `a² + a·b - k·b²`. -/
theorem norm_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    QuadraticAlgebra.norm z = z.re ^ 2 + z.re * z.im - k * z.im ^ 2 := by
  unfold QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- The norm of `a + b·ω` embeds correctly to `ℚ`. -/
theorem norm_zOnePlusSqrtOverTwo_toQsqrtd (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    Qsqrtd.norm (ZOnePlusSqrtOverTwo.toQsqrtdHom k z) =
      ((QuadraticAlgebra.norm z : ℤ) : ℚ) := by
  have h1 : (ZOnePlusSqrtOverTwo.toQsqrtdHom k z).re = (z.re : ℚ) + (z.im : ℚ) / 2 := rfl
  have h2 : (ZOnePlusSqrtOverTwo.toQsqrtdHom k z).im = (z.im : ℚ) / 2 := rfl
  simp only [Qsqrtd.norm, QuadraticAlgebra.norm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, h2]
  simp only [ZOnePlusSqrtOverTwo.qParam]
  push_cast
  ring

/-- For `d % 4 = 1`, elements of `ℤ[(1+√d)/2]` have integer norm after embedding. -/
theorem norm_mem_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    ∃ n : ℤ, Qsqrtd.norm (ZOnePlusSqrtOverTwo.toQsqrtdHom k z) = n := by
  exact ⟨QuadraticAlgebra.norm z, norm_zOnePlusSqrtOverTwo_toQsqrtd k z⟩

section ParamLevel

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- For `α ∈ 𝓞(Q(√d))`, the norm `N(α)` is an integer.

Elements of the ring of integers live in either `ℤ[√d]` or `ℤ[(1+√d)/2]`
(by `ringOfIntegers_classification`), both of which have integer-valued norm. -/
theorem norm_mem_ringOfIntegers (α : 𝓞 (Qsqrtd (d : ℚ))) :
    ∃ n : ℤ, Qsqrtd.norm (α : Qsqrtd (d : ℚ)) = n := by
  have hd_sf : Squarefree d := Fact.out
  have hd_ne : d ≠ 1 := Fact.out
  by_cases hd4 : d % 4 = 1
  · -- d % 4 = 1 branch: 𝓞 ≃ ℤ[(1 + √d)/2]
    obtain ⟨k, hk⟩ := exists_k_of_mod_four_eq_one hd4
    subst hk
    have hd_ne' : (1 + 4 * k : ℤ) ≠ 1 := hd_ne
    have happly := ringOfIntegers_equiv_of_embedding_apply
      (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom k)
      (_root_.ZOnePlusSqrtOverTwo.toQsqrtdHom_injective k)
      (fun _ hx => exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k
        hd_sf hd_ne' hx)
      (fun z => isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z) α
    rw [← happly]
    exact norm_mem_zOnePlusSqrtOverTwo k _
  · -- d % 4 ≠ 1 branch: 𝓞 ≃ ℤ[√d]
    have happly := ringOfIntegers_equiv_of_embedding_apply
      (Zsqrtd.toQsqrtdHom d)
      (Zsqrtd.toQsqrtdHom_injective d)
      (fun _ hx => exists_zsqrtd_of_isIntegral_of_ne_one_mod_four d hd_sf hd_ne hd4 hx)
      (fun z => isIntegral_toQsqrtd d z) α
    rw [← happly]
    exact norm_mem_zsqrtd d _

end ParamLevel

/-! ## Unit Criterion -/

/-- An element of `QuadraticAlgebra ℤ a b` is a unit iff its norm is `±1`. -/
theorem isUnit_iff_norm_eq_one_or_neg_one
    {a b : ℤ} (z : QuadraticAlgebra ℤ a b) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  constructor
  · intro h
    have h_norm_unit : IsUnit (QuadraticAlgebra.norm z) :=
      QuadraticAlgebra.isUnit_iff_norm_isUnit.mp h
    rcases Int.isUnit_iff.mp h_norm_unit with h1 | hneg1
    · exact Or.inl h1
    · exact Or.inr hneg1
  · intro h
    rcases h with h1 | hneg1
    · exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (h1 ▸ isUnit_one)
    · exact QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr (hneg1 ▸ isUnit_neg_one)

/-- An element of `ℤ[√d]` is a unit iff its norm is `±1`. -/
theorem isUnit_zsqrtd_iff_norm_eq_one_or_neg_one (d : ℤ) (z : Zsqrtd d) :
    IsUnit z ↔ Zsqrtd.norm z = 1 ∨ Zsqrtd.norm z = -1 := by
  simpa using isUnit_iff_norm_eq_one_or_neg_one z

/-- An element of `ℤ[(1+√(1+4k))/2]` is a unit iff its norm is `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one
    (k : ℤ) (z : ZOnePlusSqrtOverTwo k) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  simpa using isUnit_iff_norm_eq_one_or_neg_one z

end RingOfIntegers
end QuadraticNumberFields
