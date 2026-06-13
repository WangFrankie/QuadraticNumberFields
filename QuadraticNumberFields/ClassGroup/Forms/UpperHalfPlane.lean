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

/-- The `a`-coefficient of a transformed binary quadratic form. -/
@[simp] theorem transform_a (Q : BinaryQuadraticForm) (g : SL2Z) :
    (transform Q g).a = Q.a * g 0 0 ^ 2 + Q.b * g 0 0 * g 1 0 + Q.c * g 1 0 ^ 2 :=
  rfl

/-- The `b`-coefficient of a transformed binary quadratic form. -/
@[simp] theorem transform_b (Q : BinaryQuadraticForm) (g : SL2Z) :
    (transform Q g).b = 2 * Q.a * g 0 0 * g 0 1 +
      Q.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.c * g 1 0 * g 1 1 :=
  rfl

/-- The `c`-coefficient of a transformed binary quadratic form. -/
@[simp] theorem transform_c (Q : BinaryQuadraticForm) (g : SL2Z) :
    (transform Q g).c = Q.a * g 0 1 ^ 2 + Q.b * g 0 1 * g 1 1 + Q.c * g 1 1 ^ 2 :=
  rfl

private theorem denom_ne_zero_sl2z (g : SL2Z) (z : UpperHalfPlane) :
    ((g 1 0 : ℂ) * (z : ℂ) + (g 1 1 : ℂ)) ≠ 0 := by
  have hrow : (fun j : Fin 2 => (g 1 j : ℝ)) ≠ 0 := by
    intro h
    have hrowZ : g 1 = 0 := by
      funext j
      have hj0 : (g 1 j : ℝ) = 0 := by simpa using congrFun h j
      exact_mod_cast hj0
    exact Matrix.SpecialLinearGroup.row_ne_zero g 1 hrowZ
  simpa using UpperHalfPlane.linear_ne_zero z hrow

private theorem transform_polynomial_eq_eval (Q : BinaryQuadraticForm) (g : SL2Z) (z : ℂ) :
    ((transform Q g).a : ℂ) * z ^ 2 + ((transform Q g).b : ℂ) * z + (transform Q g).c =
      (Q.a : ℂ) * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) ^ 2 +
        (Q.b : ℂ) * ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) *
          ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) +
        (Q.c : ℂ) * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ 2 := by
  simp [transform]
  ring

/-- The upper half-plane point is contravariant for the form coordinate transform. -/
theorem tauOfForm_transform (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite)
    (g : SL2Z) (hQg : (transform Q g).IsPositiveDefinite) :
    tauOfForm (transform Q g) hQg = g⁻¹ • tauOfForm Q hQ := by
  let τH := tauOfForm Q hQ
  let zH := g⁻¹ • τH
  refine (eq_tauOfForm_of_root (transform Q g) hQg zH ?_).symm
  let τ : ℂ := τH
  let z : ℂ := zH
  have hroot : (Q.a : ℂ) * τ ^ 2 + (Q.b : ℂ) * τ + (Q.c : ℂ) = 0 := by
    simpa [τ, τH] using tauOfForm_root Q hQ
  have hgz : g • zH = τH := by
    simp [zH, τH]
  have hmob :
      ((g 0 0 : ℂ) * z + (g 0 1 : ℂ)) /
        ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) = τ := by
    have hcoe := congrArg ((↑) : UpperHalfPlane → ℂ) hgz
    rw [UpperHalfPlane.coe_specialLinearGroup_apply] at hcoe
    simpa [z, τ] using hcoe
  have hden : ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ≠ 0 := by
    simpa [z, zH] using denom_ne_zero_sl2z g zH
  have hlin :
      (g 0 0 : ℂ) * z + (g 0 1 : ℂ) =
        τ * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) := by
    rwa [div_eq_iff hden] at hmob
  rw [transform_polynomial_eq_eval Q g z]
  rw [hlin]
  calc
    (Q.a : ℂ) * (τ * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) ^ 2 +
          (Q.b : ℂ) * (τ * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ))) *
            ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) +
        (Q.c : ℂ) * ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ 2 =
        ((g 1 0 : ℂ) * z + (g 1 1 : ℂ)) ^ 2 *
          ((Q.a : ℂ) * τ ^ 2 + (Q.b : ℂ) * τ + (Q.c : ℂ)) := by
      ring
    _ = 0 := by
      rw [hroot, mul_zero]

private theorem one_le_div_iff_int {a c : ℤ} (ha : 0 < a) :
    (1 : ℝ) ≤ (c : ℝ) / (a : ℝ) ↔ a ≤ c := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  constructor
  · intro h
    rw [le_div_iff₀ haR] at h
    have hR : (a : ℝ) ≤ c := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : (a : ℝ) ≤ c := by exact_mod_cast h
    rw [le_div_iff₀ haR]
    nlinarith

private theorem one_lt_div_iff_int {a c : ℤ} (ha : 0 < a) :
    (1 : ℝ) < (c : ℝ) / (a : ℝ) ↔ a < c := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  constructor
  · intro h
    rw [lt_div_iff₀ haR] at h
    have hR : (a : ℝ) < c := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : (a : ℝ) < c := by exact_mod_cast h
    rw [lt_div_iff₀ haR]
    nlinarith

private theorem abs_re_le_half_iff {a b : ℤ} (ha : 0 < a) :
    |-(b : ℝ) / (2 * (a : ℝ))| ≤ (1 : ℝ) / 2 ↔ |b| ≤ a := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : 0 < 2 * (a : ℝ) := by positivity
  constructor
  · intro h
    rw [abs_div, abs_neg, abs_of_pos hden] at h
    rw [div_le_iff₀ hden] at h
    have hR : |(b : ℝ)| ≤ (a : ℝ) := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : |(b : ℝ)| ≤ (a : ℝ) := by exact_mod_cast h
    rw [abs_div, abs_neg, abs_of_pos hden]
    rw [div_le_iff₀ hden]
    nlinarith

private theorem abs_re_lt_half_iff {a b : ℤ} (ha : 0 < a) :
    |-(b : ℝ) / (2 * (a : ℝ))| < (1 : ℝ) / 2 ↔ |b| < a := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hden : 0 < 2 * (a : ℝ) := by positivity
  constructor
  · intro h
    rw [abs_div, abs_neg, abs_of_pos hden] at h
    rw [div_lt_iff₀ hden] at h
    have hR : |(b : ℝ)| < (a : ℝ) := by nlinarith
    exact_mod_cast hR
  · intro h
    have hR : |(b : ℝ)| < (a : ℝ) := by exact_mod_cast h
    rw [abs_div, abs_neg, abs_of_pos hden]
    rw [div_lt_iff₀ hden]
    nlinarith

/-- Membership of `tauOfForm` in the closed modular fundamental domain is the pair of
weak reduced-form inequalities. -/
theorem tauOfForm_mem_fd_iff (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    tauOfForm Q hQ ∈ ModularGroup.fd ↔ |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c := by
  rw [ModularGroup.fd]
  simp only [Set.mem_setOf_eq, normSq_tauOfForm, tauOfForm_re]
  rw [one_le_div_iff_int hQ.1, abs_re_le_half_iff hQ.1]
  exact and_comm

/-- Membership of `tauOfForm` in the open modular fundamental domain is the pair of
strict reduced-form inequalities. -/
theorem tauOfForm_mem_fdo_iff (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    tauOfForm Q hQ ∈ ModularGroup.fdo ↔ |Q.b| < Q.a ∧ Q.a < Q.c := by
  rw [ModularGroup.fdo]
  simp only [Set.mem_setOf_eq, normSq_tauOfForm, tauOfForm_re]
  rw [one_lt_div_iff_int hQ.1, abs_re_lt_half_iff hQ.1]
  exact and_comm

end BinaryQuadraticForm
end QuadraticNumberFields
