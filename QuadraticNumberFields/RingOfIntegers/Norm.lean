/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.RingOfIntegers.Classification
import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.QuadraticField.Conj
import QNFMathlib.Algebra.QuadraticAlgebra.Basic
import QuadraticNumberFields.Qsqrtd.TraceNorm
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Norm Multiplicativity

This file formalizes norm properties for quadratic number fields and their
rings of integers, with sections separating explicit formulas from the
classification-dependent statements.
-/

open scoped NumberField
open _root_.Qsqrtd

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields

/-! ## Norm Multiplicativity on `Q(√d)` -/

/-- The norm on `Q(√d)` is multiplicative: `N(xy) = N(x) N(y)`. -/
theorem norm_mul (d : ℚ) (x y : Qsqrtd d) :
    Qsqrtd.norm (x * y) = Qsqrtd.norm x * Qsqrtd.norm y :=
  QuadraticAlgebra.norm.map_mul x y

/-- The norm maps `1` to `1`. -/
theorem norm_one (d : ℚ) : Qsqrtd.norm (1 : Qsqrtd d) = 1 :=
  QuadraticAlgebra.norm.map_one

namespace Qsqrtd

/-- For the project's `Algebra ℚ` structure, the field norm equals the
coordinate norm `Qsqrtd.norm`. -/
theorem algebraNorm_eq_qsqrtdNorm
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (y : Qsqrtd (d : ℚ)) :
    @Algebra.norm ℚ _ _ _ QuadraticAlgebra.instAlgebra y = Qsqrtd.norm y := by
  haveI : Fact (¬ IsSquare ((d : ℤ) : ℚ)) :=
    ⟨not_isSquare_ratCast_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)⟩
  have hmul := QuadraticField.mul_conj_eq_norm_image y
  have hstar := RingOfIntegers.TraceNorm.Qsqrtd.norm_image_eq_mul_star y
  have hconj : QuadraticField.conjAut (Qsqrtd (d : ℚ)) y = star y := rfl
  apply (algebraMap ℚ (Qsqrtd (d : ℚ))).injective
  rw [← hmul, hstar, hconj]

/-- For mathlib's canonical `Algebra ℚ` structure, the field norm equals the
coordinate norm `Qsqrtd.norm`. -/
theorem algebraNorm_ratAlgebra_eq_qsqrtdNorm
    {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)] (y : Qsqrtd (d : ℚ)) :
    @Algebra.norm ℚ _ _ _ DivisionRing.toRatAlgebra y = Qsqrtd.norm y := by
  rw [show (@Algebra.norm ℚ (Qsqrtd (d : ℚ)) _ _ DivisionRing.toRatAlgebra)
        = @Algebra.norm ℚ _ _ _ QuadraticAlgebra.instAlgebra from by
        congr 1
        exact Subsingleton.elim _ _]
  exact algebraNorm_eq_qsqrtdNorm y

/-- If `d < 0`, the coordinate norm on `Q(√d)` is nonnegative. -/
theorem norm_nonneg_of_neg {d : ℤ} (hd : d < 0) (x : Qsqrtd (d : ℚ)) :
    0 ≤ Qsqrtd.norm x := by
  have hdq : ((d : ℤ) : ℚ) < 0 := by exact_mod_cast hd
  rw [RingOfIntegers.TraceNorm.norm_eq_sqr_minus_d_sqr]
  nlinarith [sq_nonneg x.re, sq_nonneg x.im]

end Qsqrtd

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
  (Zsqrtd.normHom d).map_mul x y

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

/-- The norm on `ZOnePlusSqrtdOverTwo k` is multiplicative. -/
theorem norm_mul_zOnePlusSqrtOverTwo (k : ℤ) (x y : ZOnePlusSqrtdOverTwo k) :
    QuadraticAlgebra.norm (x * y) =
      QuadraticAlgebra.norm x * QuadraticAlgebra.norm y :=
  (ZOnePlusSqrtdOverTwo.normHom k).map_mul x y

/-- The norm of an element of `ZOnePlusSqrtdOverTwo k` is `a² + a·b - k·b²`. -/
theorem norm_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtdOverTwo k) :
    QuadraticAlgebra.norm z = z.re ^ 2 + z.re * z.im - k * z.im ^ 2 := by
  unfold QuadraticAlgebra.norm
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  ring

/-- The norm of `a + b·ω` embeds correctly to `ℚ`. -/
theorem norm_zOnePlusSqrtOverTwo_toQsqrtd (k : ℤ) (z : ZOnePlusSqrtdOverTwo k) :
    Qsqrtd.norm (ZOnePlusSqrtdOverTwo.toQsqrtdHom k z) =
      ((QuadraticAlgebra.norm z : ℤ) : ℚ) := by
  have h1 : (ZOnePlusSqrtdOverTwo.toQsqrtdHom k z).re = (z.re : ℚ) + (z.im : ℚ) / 2 := rfl
  have h2 : (ZOnePlusSqrtdOverTwo.toQsqrtdHom k z).im = (z.im : ℚ) / 2 := rfl
  simp only [Qsqrtd.norm, QuadraticAlgebra.norm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [h1, h2]
  simp only [ZOnePlusSqrtdOverTwo.qParam]
  push_cast
  ring

/-- For `d % 4 = 1`, elements of `ℤ[(1+√d)/2]` have integer norm after embedding. -/
theorem norm_mem_zOnePlusSqrtOverTwo (k : ℤ) (z : ZOnePlusSqrtdOverTwo k) :
    ∃ n : ℤ, Qsqrtd.norm (ZOnePlusSqrtdOverTwo.toQsqrtdHom k z) = n := by
  exact ⟨QuadraticAlgebra.norm z, norm_zOnePlusSqrtOverTwo_toQsqrtd k z⟩

section SquarefreeIntegerParameter

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
      (_root_.ZOnePlusSqrtdOverTwo.toQsqrtdHom k)
      (_root_.ZOnePlusSqrtdOverTwo.toQsqrtdHom_injective k)
      (fun _ hx => exists_zOnePlusSqrtOverTwo_of_isIntegral_of_one_mod_four k
        hd_sf hd_ne' hx)
      (fun z => isIntegral_toQsqrtd_of_zOnePlusSqrtOverTwo k z) α
    rw [← happly]
    exact norm_mem_zOnePlusSqrtOverTwo k _
  · -- d % 4 ≠ 1 branch: 𝓞 ≃ ℤ[√d]
    rw [← ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 α]
    exact norm_mem_zsqrtd d _

/-- On the `d % 4 ≠ 1` branch, the integer norm of an algebraic integer agrees
with the explicit `Zsqrtd` norm after transporting to `ℤ[√d]`. -/
theorem algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one
    [NumberField (Qsqrtd (d : ℚ))] (hd4 : d % 4 ≠ 1) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    Algebra.norm ℤ α =
      Zsqrtd.norm ((ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4) α) := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd (d : ℚ)),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  rw [← ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 α]
  exact norm_zsqrtd_toQsqrtd d _

/-- On the `d = 1 + 4 * k` branch, the integer norm of an algebraic integer agrees
with the explicit `ZOnePlusSqrtdOverTwo` norm after transporting to
`ℤ[(1+√d)/2]`. -/
theorem algebraNorm_eq_zOnePlusSqrtOverTwo_norm_of_eq
    [NumberField (Qsqrtd (d : ℚ))] (k : ℤ) (hk : d = 1 + 4 * k)
    (α : 𝓞 (Qsqrtd (d : ℚ))) :
    Algebra.norm ℤ α =
      QuadraticAlgebra.norm ((ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq d k hk) α) := by
  subst hk
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := Qsqrtd (((1 + 4 * k : ℤ) : ℚ))),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  rw [← ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_eq_apply k α]
  exact norm_zOnePlusSqrtOverTwo_toQsqrtd k _

/-- If `d < 0`, the algebra norm of an algebraic integer in `𝓞(Q(√d))` is
nonnegative. -/
theorem algebraNorm_nonneg_of_neg
    [NumberField (Qsqrtd (d : ℚ))] (hd : d < 0) (α : 𝓞 (Qsqrtd (d : ℚ))) :
    0 ≤ Algebra.norm ℤ α := by
  have hcast : (0 : ℚ) ≤ (Algebra.norm ℤ α : ℚ) := by
    rw [Algebra.coe_norm_int (K := Qsqrtd (d : ℚ)),
      Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
    exact Qsqrtd.norm_nonneg_of_neg hd α
  exact_mod_cast hcast

end SquarefreeIntegerParameter

/-! ## Absolute norms of principal integer ideals -/

section SquarefreeIntegerParameter

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- A principal ideal in `𝓞(Q(√d))` has absolute norm equal to the absolute value
of the algebra norm of a principal generator. -/
theorem absNorm_eq_natAbs_algebraNorm_of_isPrincipal
    [NumberField (Qsqrtd (d : ℚ))]
    {I : Ideal (𝓞 (Qsqrtd (d : ℚ)))} (hI : I.IsPrincipal) :
    ∃ α : 𝓞 (Qsqrtd (d : ℚ)),
      I = Ideal.span ({α} : Set (𝓞 (Qsqrtd (d : ℚ)))) ∧
        Ideal.absNorm I = (Algebra.norm ℤ α).natAbs := by
  letI : I.IsPrincipal := hI
  refine ⟨Submodule.IsPrincipal.generator I, ?_, ?_⟩
  · exact (Ideal.span_singleton_generator I).symm
  · exact (congrArg Ideal.absNorm (Ideal.span_singleton_generator I).symm).trans
      (Ideal.absNorm_span_singleton _)

/-- If `(p : ℤ)` does not divide the absolute norm of a principal ideal, then one can
choose a principal generator whose algebra norm is also not divisible by `(p : ℤ)`. -/
theorem exists_generator_norm_not_dvd_of_isPrincipal
    [NumberField (Qsqrtd (d : ℚ))] {p : ℕ}
    {I : Ideal (𝓞 (Qsqrtd (d : ℚ)))} (hI : I.IsPrincipal)
    (hp_norm : ¬ (p : ℤ) ∣ (Ideal.absNorm I : ℤ)) :
    ∃ α : 𝓞 (Qsqrtd (d : ℚ)),
      I = Ideal.span ({α} : Set (𝓞 (Qsqrtd (d : ℚ)))) ∧
        ¬ (p : ℤ) ∣ Algebra.norm ℤ α := by
  obtain ⟨α, hspan, hnorm⟩ :=
    absNorm_eq_natAbs_algebraNorm_of_isPrincipal (d := d) hI
  refine ⟨α, hspan, ?_⟩
  intro hdiv
  have hnat : p ∣ (Algebra.norm ℤ α).natAbs := Int.natCast_dvd.mp hdiv
  apply hp_norm
  rw [hnorm]
  exact_mod_cast hnat

/-- In the quadratic ring of integers `𝓞(Q(√d))`, the absolute norm of the
principal ideal `(n)` is `|n²|`. -/
theorem absNorm_span_intCast [NumberField (Qsqrtd (d : ℚ))] (n : ℤ) :
    Ideal.absNorm (Ideal.span ({(n : 𝓞 (Qsqrtd (d : ℚ)))} : Set (𝓞 (Qsqrtd (d : ℚ))))) =
      (n ^ 2).natAbs := by
  rw [Ideal.absNorm_span_singleton]
  change (Algebra.norm ℤ (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ))) n)).natAbs = (n ^ 2).natAbs
  have hnorm :
      Algebra.norm ℤ (algebraMap ℤ (𝓞 (Qsqrtd (d : ℚ))) n) =
        n ^ Module.finrank ℤ (𝓞 (Qsqrtd (d : ℚ))) :=
    (Algebra.norm_algebraMap_of_basis
      (NumberField.RingOfIntegers.basis (Qsqrtd (d : ℚ))) n).trans (by
        rw [← Module.finrank_eq_card_chooseBasisIndex])
  rw [hnorm, NumberField.RingOfIntegers.rank, finrank_ratAlgebra_eq_two (d : ℚ)]

end SquarefreeIntegerParameter

/-! ## Unit Criterion -/

/-- An element of `ℤ[√d]` is a unit iff its norm is `±1`. -/
theorem isUnit_zsqrtd_iff_norm_eq_one_or_neg_one (d : ℤ) (z : Zsqrtd d) :
    IsUnit z ↔ Zsqrtd.norm z = 1 ∨ Zsqrtd.norm z = -1 := by
  simpa using QuadraticAlgebra.isUnit_iff_norm_eq_one_or_neg_one z

/-- An element of `ℤ[(1+√(1+4k))/2]` is a unit iff its norm is `±1`. -/
theorem isUnit_zOnePlusSqrtOverTwo_iff_norm_eq_one_or_neg_one
    (k : ℤ) (z : ZOnePlusSqrtdOverTwo k) :
    IsUnit z ↔ QuadraticAlgebra.norm z = 1 ∨ QuadraticAlgebra.norm z = -1 := by
  simpa using QuadraticAlgebra.isUnit_iff_norm_eq_one_or_neg_one z

end RingOfIntegers
end QuadraticNumberFields
