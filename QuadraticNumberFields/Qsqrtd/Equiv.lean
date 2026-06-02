/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Parameters

/-!
# Equivalences Between `Qsqrtd` Models

This work-in-progress file records the intended parameter-equivalence API for
the standard models `Qsqrtd d`.

The completed parameter uniqueness theorem for squarefree integer parameters
already lives in `QuadraticNumberFields.QuadraticField.Parameters`.  The goal
here is the more flexible rational-parameter statement: two standard models are
`ℚ`-algebra equivalent exactly when their parameters differ by a rational
square factor.

This module is currently imported only by `QuadraticNumberFields.Sketch`.

## Main definitions

* `Qsqrtd.IsSquareRatio`: `d' = a² d` for some `a : ℚˣ`.
* `Qsqrtd.IsSquareRatioByDivision`: `d' / d = a²` for some `a : ℚˣ`.
* `Qsqrtd.algEquiv_iff_isSquareRatio`: WIP classification interface for
  equivalences between standard models.
-/

namespace Qsqrtd

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and `QuadraticAlgebra.instAlgebra`.
-- NOTE: This is a file-local workaround for standard-model algebra equivalences.
attribute [-instance] DivisionRing.toRatAlgebra

/-- The parameters `d` and `d'` differ by a rational square factor. -/
def IsSquareRatio (d d' : ℚ) : Prop :=
  ∃ a : ℚˣ, d' = (a : ℚ) ^ 2 * d

/-- Division-form version of `Qsqrtd.IsSquareRatio`: `d' / d` is a rational
unit square. This is the shape usually used in informal statements. -/
def IsSquareRatioByDivision (d d' : ℚ) : Prop :=
  ∃ a : ℚˣ, d' / d = (a : ℚ) ^ 2

/-- Rescaling gives an algebra equivalence whenever the parameters differ by a
rational square factor. -/
theorem nonempty_algEquiv_of_isSquareRatio {d d' : ℚ} :
    IsSquareRatio d d' → Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') := by
  rintro ⟨a, rfl⟩
  exact ⟨Qsqrtd.rescale d a⟩

/-- Multiplicative and division forms of square-ratio equivalence agree away
from `d = 0`. -/
theorem isSquareRatio_iff_isSquareRatioByDivision {d d' : ℚ} (hd : d ≠ 0) :
    IsSquareRatio d d' ↔ IsSquareRatioByDivision d d' := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    field_simp [hd]
  · rintro ⟨a, ha⟩
    refine ⟨a, ?_⟩
    calc
      d' = d' / d * d := by field_simp [hd]
      _ = (a : ℚ) ^ 2 * d := by rw [ha]

/-- WIP classification interface: non-square standard models are equivalent
exactly when their parameters differ by a rational square factor.

The forward direction will extract the image of `√d` under an algebra
equivalence and show that its imaginary coefficient supplies the square ratio.
-/
theorem algEquiv_iff_isSquareRatio
    (d d' : ℚ) [Fact (¬ IsSquare d)] [Fact (¬ IsSquare d')] :
    Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') ↔ IsSquareRatio d d' := by
  constructor
  · rintro ⟨φ⟩
    set a := (φ ⟨0, 1⟩).re
    set b := (φ ⟨0, 1⟩).im
    have hε_sq : (⟨0, 1⟩ : Qsqrtd d) * ⟨0, 1⟩ = ⟨d, 0⟩ := by
      ext <;> simp [QuadraticAlgebra.mk_mul_mk]
    have hφ_sq : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = ⟨d, 0⟩ := by
      rw [← map_mul, hε_sq]
      show φ ⟨d, 0⟩ = ⟨d, 0⟩
      have hleft : (⟨d, 0⟩ : Qsqrtd d) = algebraMap ℚ (Qsqrtd d) d := by
        exact (QuadraticAlgebra.algebraMap_eq (R := ℚ) (a := d) (b := 0) d).symm
      have hright : (⟨d, 0⟩ : Qsqrtd d') = algebraMap ℚ (Qsqrtd d') d := by
        exact (QuadraticAlgebra.algebraMap_eq (R := ℚ) (a := d') (b := 0) d).symm
      rw [hleft, hright]
      exact φ.commutes d
    have hφ_eta : φ ⟨0, 1⟩ = ⟨a, b⟩ := by ext <;> rfl
    have hre : a ^ 2 + d' * b ^ 2 = d := by
      have := congr_arg QuadraticAlgebra.re hφ_sq
      rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
      simp at this
      nlinarith
    have him : 2 * a * b = 0 := by
      have := congr_arg QuadraticAlgebra.im hφ_sq
      rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
      simp at this
      linarith
    have hb : b ≠ 0 := by
      intro hb0
      simp [hb0] at hre
      exact (Fact.out : ¬ IsSquare d) ⟨a, by nlinarith⟩
    have ha : a = 0 := by
      rcases mul_eq_zero.mp him with h | h
      · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
      · exact absurd h hb
    have hr : d = d' * b ^ 2 := by nlinarith [hre, ha]
    refine ⟨Units.mk0 b⁻¹ (inv_ne_zero hb), ?_⟩
    change d' = (b⁻¹) ^ 2 * d
    rw [hr]
    field_simp [hb]
  · exact nonempty_algEquiv_of_isSquareRatio

/-- Division-form WIP classification interface matching the usual informal
statement `d' / d ∈ ℚ×²`. -/
theorem algEquiv_iff_isSquareRatioByDivision
    (d d' : ℚ) [Fact (¬ IsSquare d)] [Fact (¬ IsSquare d')] :
    Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd d') ↔ IsSquareRatioByDivision d d' := by
  have hd : d ≠ 0 := by
    intro hd
    exact (Fact.out : ¬ IsSquare d) (by rw [hd]; exact ⟨0, by ring⟩)
  exact (algEquiv_iff_isSquareRatio d d').trans (isSquareRatio_iff_isSquareRatioByDivision hd)

end Qsqrtd
