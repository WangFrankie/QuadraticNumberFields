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

/-- The upper half-plane point as an explicit complex number. -/
theorem tauOfForm_coe (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    (tauOfForm Q hQ : ℂ) =
      (-(Q.b : ℂ) + (Real.sqrt (4 * (Q.a : ℝ) * Q.c - (Q.b : ℝ) ^ 2) : ℝ) * Complex.I) /
        (2 * (Q.a : ℂ)) := by
  have ha : (Q.a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have haR : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  rw [eq_div_iff (mul_ne_zero two_ne_zero ha)]
  apply Complex.ext <;>
    simp [tauOfForm, Complex.mul_re, Complex.mul_im] <;>
    field_simp

/-- The defining property: the form's quadratic `a X² + b X + c` vanishes at its
upper half-plane point. -/
theorem tauOfForm_root (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    (Q.a : ℂ) * (tauOfForm Q hQ : ℂ) ^ 2 + (Q.b : ℂ) * (tauOfForm Q hQ : ℂ) + (Q.c : ℂ) = 0 := by
  have ha : (Q.a : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hge : (0 : ℝ) ≤ 4 * (Q.a : ℝ) * Q.c - (Q.b : ℝ) ^ 2 := by
    have h := hQ.2
    unfold disc at h
    have h' : (Q.b : ℝ) ^ 2 - 4 * (Q.a : ℝ) * Q.c < 0 := by exact_mod_cast h
    linarith
  have hwI : ((Real.sqrt (4 * (Q.a : ℝ) * Q.c - (Q.b : ℝ) ^ 2) : ℝ) : ℂ) ^ 2 * Complex.I ^ 2 =
      (Q.b : ℂ) ^ 2 - 4 * Q.a * Q.c := by
    rw [Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hge]
    push_cast
    ring
  rw [tauOfForm_coe]
  field_simp
  linear_combination hwI

/-- **Uniqueness of the root in `ℍ`.** A positive definite form has exactly one
root in the upper half-plane: the conjugate root has negative imaginary part. -/
theorem eq_tauOfForm_of_root (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite)
    (z : UpperHalfPlane)
    (hz : (Q.a : ℂ) * (z : ℂ) ^ 2 + (Q.b : ℂ) * (z : ℂ) + (Q.c : ℂ) = 0) :
    z = tauOfForm Q hQ := by
  have hroot := tauOfForm_root Q hQ
  have hfactor : ((z : ℂ) - (tauOfForm Q hQ : ℂ)) *
      ((Q.a : ℂ) * ((z : ℂ) + (tauOfForm Q hQ : ℂ)) + (Q.b : ℂ)) = 0 := by
    linear_combination hz - hroot
  rcases mul_eq_zero.mp hfactor with h | h
  · exact UpperHalfPlane.ext (sub_eq_zero.mp h)
  · exfalso
    have hzi : 0 < (z : ℂ).im := z.2
    have hτi : 0 < (tauOfForm Q hQ : ℂ).im := (tauOfForm Q hQ).2
    have ha_pos : 0 < (Q.a : ℝ) := by exact_mod_cast hQ.1
    have him := congrArg Complex.im h
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
      Complex.zero_im, zero_mul, add_zero] at him
    nlinarith [him, hzi, hτi, ha_pos]

end BinaryQuadraticForm
end QuadraticNumberFields
