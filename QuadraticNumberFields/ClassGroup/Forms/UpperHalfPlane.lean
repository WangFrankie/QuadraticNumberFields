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

/-- For positive definite forms of the same discriminant, the upper half-plane point
determines the form. -/
theorem eq_of_tauOfForm_eq_of_disc_eq (Q R : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hR : R.IsPositiveDefinite) (hdisc : Q.disc = R.disc)
    (htau : tauOfForm Q hQ = tauOfForm R hR) : Q = R := by
  rcases Q with ⟨a, b, c⟩
  rcases R with ⟨A, B, C⟩
  change 0 < a ∧ b ^ 2 - 4 * a * c < 0 at hQ
  change 0 < A ∧ B ^ 2 - 4 * A * C < 0 at hR
  change b ^ 2 - 4 * a * c = B ^ 2 - 4 * A * C at hdisc
  have ha : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hA : (A : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hR.1)
  have ha_pos : 0 < (a : ℝ) := by exact_mod_cast hQ.1
  have hA_pos : 0 < (A : ℝ) := by exact_mod_cast hR.1
  have hdR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * c < 0 := by
    have h := hQ.2
    unfold disc at h
    exact_mod_cast h
  have hre0 := congrArg UpperHalfPlane.re htau
  have hre : (b : ℝ) * A = (B : ℝ) * a := by
    simp only [tauOfForm_re] at hre0
    field_simp [ha, hA] at hre0
    linarith
  have hnorm0 : (c : ℝ) / a = (C : ℝ) / A := by
    rw [← normSq_tauOfForm (BinaryQuadraticForm.mk a b c) hQ]
    rw [htau]
    rw [normSq_tauOfForm]
  have hnorm : (c : ℝ) * A = (C : ℝ) * a := by
    field_simp [ha, hA] at hnorm0
    linarith
  have hdiscR : (b : ℝ) ^ 2 - 4 * (a : ℝ) * c = (B : ℝ) ^ 2 - 4 * (A : ℝ) * C := by
    exact_mod_cast hdisc
  have haA : (a : ℝ) = A := by
    have hscaled : (A : ℝ) ^ 2 * ((b : ℝ) ^ 2 - 4 * (a : ℝ) * c) =
        (a : ℝ) ^ 2 * ((B : ℝ) ^ 2 - 4 * (A : ℝ) * C) := by
      calc
        (A : ℝ) ^ 2 * ((b : ℝ) ^ 2 - 4 * (a : ℝ) * c)
            = ((b : ℝ) * A) ^ 2 - 4 * (a : ℝ) * ((c : ℝ) * A) * A := by
          ring
        _ = ((B : ℝ) * a) ^ 2 - 4 * (a : ℝ) * ((C : ℝ) * a) * A := by
          rw [hre, hnorm]
        _ = (a : ℝ) ^ 2 * ((B : ℝ) ^ 2 - 4 * (A : ℝ) * C) := by
          ring
    have hmul :
        ((A : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((b : ℝ) ^ 2 - 4 * (a : ℝ) * c) = 0 := by
      nlinarith [hscaled, hdiscR]
    have hsquares : (A : ℝ) ^ 2 = (a : ℝ) ^ 2 := by
      have hDne : (b : ℝ) ^ 2 - 4 * (a : ℝ) * c ≠ 0 := by nlinarith [hdR]
      have hzero : (A : ℝ) ^ 2 - (a : ℝ) ^ 2 = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hDne
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquares with h | h
    · linarith
    · nlinarith [h, ha_pos, hA_pos]
  have hbB : (b : ℝ) = B := by
    have hre' : (b : ℝ) * (a : ℝ) = (B : ℝ) * (a : ℝ) := by
      simpa [← haA] using hre
    exact mul_right_cancel₀ ha hre'
  have hcC : (c : ℝ) = C := by
    have hnorm' : (c : ℝ) * (a : ℝ) = (C : ℝ) * (a : ℝ) := by
      simpa [← haA] using hnorm
    exact mul_right_cancel₀ ha hnorm'
  have haA_int : a = A := by exact_mod_cast haA
  have hbB_int : b = B := by exact_mod_cast hbB
  have hcC_int : c = C := by exact_mod_cast hcC
  simp [haA_int, hbB_int, hcC_int]

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

/-- A reduced positive definite form has its upper half-plane point in the closed
modular fundamental domain. -/
theorem tauOfForm_mem_fd_of_isReduced (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    tauOfForm Q hQ ∈ ModularGroup.fd :=
  (tauOfForm_mem_fd_iff Q hQ).2 ⟨hred.1, hred.2.1⟩

/-- Membership of `tauOfForm` in the open modular fundamental domain is the pair of
strict reduced-form inequalities. -/
theorem tauOfForm_mem_fdo_iff (Q : BinaryQuadraticForm) (hQ : Q.IsPositiveDefinite) :
    tauOfForm Q hQ ∈ ModularGroup.fdo ↔ |Q.b| < Q.a ∧ Q.a < Q.c := by
  rw [ModularGroup.fdo]
  simp only [Set.mem_setOf_eq, normSq_tauOfForm, tauOfForm_re]
  rw [one_lt_div_iff_int hQ.1, abs_re_lt_half_iff hQ.1]
  exact and_comm

private theorem isReduced_transform_T_of_neg_abs_eq_a (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hweak : |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c)
    (hbabs : |Q.b| = Q.a) (hbneg : Q.b < 0) :
    (transform Q ModularGroup.T).IsReduced := by
  rcases Q with ⟨a, b, c⟩
  simp only at hQ hweak hbabs hbneg
  have ha_pos : 0 < a := hQ.1
  have hb_eq : b = -a := by
    have hbabs' : -b = a := by simpa [abs_of_neg hbneg] using hbabs
    linarith
  have hT : transform (BinaryQuadraticForm.mk a b c) ModularGroup.T =
      BinaryQuadraticForm.mk a (2 * a + b) (a + b + c) := by
    ext <;> simp [ModularGroup.coe_T]
  rw [hT, isReduced_mk_iff, hb_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : |2 * a + -a| = a := by
      rw [show 2 * a + -a = a by ring, abs_of_nonneg ha_pos.le]
    exact h.le
  · nlinarith [hweak.2]
  · intro _
    nlinarith [ha_pos]
  · intro _
    nlinarith [ha_pos]

private theorem isReduced_transform_S_of_neg_a_eq_c (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hweak : |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c)
    (hac : Q.a = Q.c) (hbneg : Q.b < 0) :
    (transform Q ModularGroup.S).IsReduced := by
  rcases Q with ⟨a, b, c⟩
  simp only at hQ hweak hac hbneg
  have ha_pos : 0 < a := hQ.1
  have hneg_nonneg : 0 ≤ -b := by linarith
  have hb_abs_le : |b| ≤ a := hweak.1
  have hS : transform (BinaryQuadraticForm.mk a b c) ModularGroup.S =
      BinaryQuadraticForm.mk c (-b) a := by
    ext <;> simp [ModularGroup.coe_S]
  rw [hS, isReduced_mk_iff]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [← hac] using hb_abs_le
  · rw [← hac]
  · intro _
    exact hneg_nonneg
  · intro _
    exact hneg_nonneg

/-- A point of a positive definite form in the closed modular fundamental domain can be
boundary-normalized by one of the standard generators. -/
theorem exists_isReduced_transform_of_mem_fd (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hfd : tauOfForm Q hQ ∈ ModularGroup.fd) :
    ∃ g : SL2Z, (transform Q g).IsReduced := by
  have hweak : |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c := (tauOfForm_mem_fd_iff Q hQ).mp hfd
  by_cases hbadAbs : |Q.b| = Q.a ∧ Q.b < 0
  · exact ⟨ModularGroup.T,
      isReduced_transform_T_of_neg_abs_eq_a Q hQ hweak hbadAbs.1 hbadAbs.2⟩
  · by_cases hbadC : Q.a = Q.c ∧ Q.b < 0
    · exact ⟨ModularGroup.S,
        isReduced_transform_S_of_neg_a_eq_c Q hQ hweak hbadC.1 hbadC.2⟩
    · refine ⟨1, ?_⟩
      have hred : Q.IsReduced := by
        refine ⟨hweak.1, hweak.2, ?_, ?_⟩
        · intro hbabs
          by_contra hbnonneg
          exact hbadAbs ⟨hbabs, lt_of_not_ge hbnonneg⟩
        · intro hac
          by_contra hbnonneg
          exact hbadC ⟨hac, lt_of_not_ge hbnonneg⟩
      simpa using hred

end BinaryQuadraticForm
end QuadraticNumberFields
