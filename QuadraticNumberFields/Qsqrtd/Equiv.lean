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
  exact fun ⟨a, h⟩ => h ▸ ⟨Qsqrtd.rescale d a⟩

/-- Multiplicative and division forms of square-ratio equivalence agree away
from `d = 0`. -/
theorem isSquareRatio_iff_isSquareRatioByDivision {d d' : ℚ} (hd : d ≠ 0) :
    IsSquareRatio d d' ↔ IsSquareRatioByDivision d d' := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, by field_simp [hd]⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by rw [← ha]; field_simp [hd]⟩

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
    obtain ⟨-, hb, hr⟩ := algEquiv_param_rel (Fact.out : ¬ IsSquare d) φ
    set b := (φ ⟨0, 1⟩).im
    -- `hr : d = d' * b²` with `b ≠ 0`, so `d' = (b⁻¹)² * d`.
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
    exact (Fact.out : ¬ IsSquare d) (by simp [hd])
  exact (algEquiv_iff_isSquareRatio d d').trans (isSquareRatio_iff_isSquareRatioByDivision hd)

end Qsqrtd
