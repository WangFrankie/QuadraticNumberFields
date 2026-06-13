/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.Reduction
import Mathlib.NumberTheory.Modular

/-!
# The Upper Half-Plane Point of a Positive Definite Binary Quadratic Form

This file attaches to each positive definite binary quadratic form `(a, b, c)` of
negative discriminant its root

`τ = (-b + √(4ac - b²) · i) / (2a)`

in the upper half-plane `ℍ`, and records the coordinate formulas

* `(tauOfForm Q hQ).re = -b / 2a`,
* `(tauOfForm Q hQ).im = √(4ac - b²) / 2a`,
* `normSq (tauOfForm Q hQ) = c / a`.

These feed the modular-domain proof of Gauss reduction: a positive definite form
is reduced exactly when its point lies in the standard fundamental domain `𝒟` of
the `SL(2, ℤ)` action on `ℍ`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-- The root in the upper half-plane of a positive definite form `(a, b, c)`,
namely `τ = (-b + √(4ac - b²) · i) / (2a)`. -/
noncomputable def tauOfForm (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    UpperHalfPlane :=
  ⟨⟨-(Q.b : ℝ) / (2 * (Q.a : ℝ)),
      Real.sqrt (4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2) / (2 * (Q.a : ℝ))⟩, by
    have ha : 0 < (Q.a : ℝ) := by exact_mod_cast hQ.1
    have hdR : (Q.b : ℝ) ^ 2 - 4 * (Q.a : ℝ) * (Q.c : ℝ) < 0 := by
      have h := hQ.2
      unfold disc at h
      exact_mod_cast h
    have hpos : (0 : ℝ) < 4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2 := by linarith
    exact div_pos (Real.sqrt_pos.mpr hpos) (by linarith)⟩

@[simp] theorem tauOfForm_re (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    (tauOfForm Q hQ).re = -(Q.b : ℝ) / (2 * (Q.a : ℝ)) := rfl

@[simp] theorem tauOfForm_im (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    (tauOfForm Q hQ).im =
      Real.sqrt (4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2) / (2 * (Q.a : ℝ)) := rfl

/-- The norm-square of the upper half-plane point is `c / a`; this is the
analytic shadow of the reduced-form bound `a ≤ c ⟺ 1 ≤ |τ|²`. -/
theorem normSq_tauOfForm (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    Complex.normSq (tauOfForm Q hQ : ℂ) = (Q.c : ℝ) / (Q.a : ℝ) := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hdR : (Q.b : ℝ) ^ 2 - 4 * (Q.a : ℝ) * (Q.c : ℝ) < 0 := by
    have h := hQ.2
    unfold disc at h
    exact_mod_cast h
  have hsq : Real.sqrt (4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2) *
      Real.sqrt (4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2) =
      4 * (Q.a : ℝ) * (Q.c : ℝ) - (Q.b : ℝ) ^ 2 :=
    Real.mul_self_sqrt (by linarith)
  simp only [Complex.normSq_apply, tauOfForm]
  rw [div_mul_div_comm, div_mul_div_comm, hsq]
  field_simp
  ring

end BinaryQuadraticForm
end QuadraticNumberFields
