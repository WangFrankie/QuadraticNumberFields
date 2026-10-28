/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.ModularForms.Discriminant

/-!
# Weber's Modular Functions

This file defines Weber's functions as quotients of the Dedekind eta function,

* `𝔣(z) = ζ₄₈⁻¹ η((z + 1) / 2) / η(z)`,
* `𝔣₁(z) = η(z / 2) / η(z)`,
* `𝔣₂(z) = √2 η(2z) / η(z)`,

and proves their transformation laws under `z ↦ z + 1` and `z ↦ -1 / z`
together with Weber's product identity `𝔣 𝔣₁ 𝔣₂ = √2`.  These functions carry
Heegner's proof of the class number one theorem.

## Main results

* `ModularForm.eta_add_one`: `η(z + 1) = e^{2πi/24} η(z)`.
* `ModularForm.weberF_add_one`, `ModularForm.weberF₁_add_one`,
  `ModularForm.weberF₂_add_one`: the translation laws.
* `ModularForm.weberF_neg_inv`, `ModularForm.weberF₁_neg_inv`,
  `ModularForm.weberF₂_neg_inv`: the inversion laws on the upper half-plane.
* `ModularForm.eta_half_add_mul_eta_half_mul_eta_two_mul`:
  `η((z + 1) / 2) η(z / 2) η(2z) = ζ₄₈ η(z)³`.
* `ModularForm.weberF_mul_weberF₁_mul_weberF₂`: `𝔣 𝔣₁ 𝔣₂ = √2`.

## References

* D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., §12.
-/

open Complex
open scoped Real ModularForm

local notation "𝕢" => Function.Periodic.qParam

namespace ModularForm

noncomputable section

/-- `η(z + 1) = e^{2πi/24} η(z)`. -/
theorem eta_add_one (z : ℂ) : η (z + 1) = cexp (2 * π * I / 24) * η z := by
  have hq : ∀ n : ℕ, eta_q n (z + 1) = eta_q n z := by
    intro n
    simp only [eta_q_eq_cexp]
    rw [show 2 * (π : ℂ) * I * ((n : ℂ) + 1) * (z + 1) =
        2 * π * I * (n + 1) * z + ((n + 1 : ℕ) : ℂ) * (2 * π * I) by push_cast; ring,
      Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  simp only [eta, hq, Function.Periodic.qParam, ← mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The square root of `2z` is `√2 √z` away from the negative real axis. -/
private theorem sqrt_two_mul {z : ℂ} (hz : z ≠ 0) :
    Complex.sqrt (2 * z) = (Real.sqrt 2 : ℂ) * Complex.sqrt z := by
  have h2 : (2 : ℂ) * z = ((2 : ℝ) : ℂ) * z := by norm_num
  rw [sqrt_eq_exp (mul_ne_zero two_ne_zero hz), sqrt_eq_exp hz, h2,
    Complex.log_ofReal_mul (by norm_num) hz, add_div, Complex.exp_add]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num), Complex.ofReal_exp]
  push_cast
  ring_nf

/-- The 48th root of unity `ζ₄₈ = e^{2πi/48}`. -/
def zeta48 : ℂ := cexp (2 * π * I / 48)

theorem zeta48_ne_zero : zeta48 ≠ 0 := Complex.exp_ne_zero _

theorem zeta48_sq : zeta48 ^ 2 = cexp (2 * π * I / 24) := by
  rw [zeta48, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Weber's function `𝔣₁(z) = η(z/2)/η(z)`. -/
def weberF₁ (z : ℂ) : ℂ := η (z / 2) / η z

/-- Weber's function `𝔣₂(z) = √2 η(2z)/η(z)`. -/
def weberF₂ (z : ℂ) : ℂ := (Real.sqrt 2 : ℂ) * (η (2 * z) / η z)

/-- Weber's function `𝔣(z) = ζ₄₈⁻¹ η((z+1)/2)/η(z)`. -/
def weberF (z : ℂ) : ℂ := zeta48⁻¹ * (η ((z + 1) / 2) / η z)

theorem weberF_add_one (z : ℂ) : weberF (z + 1) = zeta48⁻¹ * weberF₁ z := by
  rw [weberF, weberF₁, show (z + 1 + 1) / 2 = z / 2 + 1 by ring, eta_add_one, eta_add_one,
    mul_div_mul_left _ _ (Complex.exp_ne_zero _)]

theorem weberF₁_add_one (z : ℂ) : weberF₁ (z + 1) = zeta48⁻¹ * weberF z := by
  rw [weberF₁, weberF, eta_add_one, ← zeta48_sq]
  have := zeta48_ne_zero
  field_simp

theorem weberF₂_add_one (z : ℂ) :
    weberF₂ (z + 1) = cexp (2 * π * I / 24) * weberF₂ z := by
  rw [weberF₂, weberF₂, show 2 * (z + 1) = 2 * z + 1 + 1 by ring, eta_add_one, eta_add_one,
    eta_add_one]
  have := Complex.exp_ne_zero (2 * π * I / 24)
  by_cases hz : η z = 0
  · simp [hz]
  · field_simp

/-- `η(-1/z) = (√I)⁻¹ √z η(z)` on the upper half-plane. -/
theorem eta_neg_inv {z : ℂ} (hz : 0 < z.im) :
    η (-1 / z) = (Complex.sqrt I)⁻¹ * (Complex.sqrt z * η z) := by
  simpa using eta_comp_eq_csqrt_I_inv (show z ∈ UpperHalfPlane.upperHalfPlaneSet from hz)

private theorem sqrt_ne_zero' {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  rw [sqrt_eq_exp hz]
  exact Complex.exp_ne_zero _

theorem weberF₁_neg_inv {z : ℂ} (hz : 0 < z.im) : weberF₁ (-1 / z) = weberF₂ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h2z : 0 < (2 * z).im := by
    rw [show (2 * z).im = 2 * z.im by simp]
    positivity
  have hsI := sqrt_ne_zero' I_ne_zero
  have hsz := sqrt_ne_zero' hz0
  have hηz : η z ≠ 0 := eta_ne_zero hz
  rw [weberF₁, weberF₂, show -1 / z / 2 = -1 / (2 * z) by field_simp, eta_neg_inv h2z,
    eta_neg_inv hz, sqrt_two_mul hz0]
  field_simp

theorem weberF₂_neg_inv {z : ℂ} (hz : 0 < z.im) : weberF₂ (-1 / z) = weberF₁ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have hz2 : 0 < (z / 2).im := by
    rw [show (z / 2).im = z.im / 2 by simp]
    positivity
  have hs := sqrt_two_mul (z := z / 2) (div_ne_zero hz0 two_ne_zero)
  rw [show 2 * (z / 2) = z by ring] at hs
  have hsI := sqrt_ne_zero' I_ne_zero
  have hsz2 := sqrt_ne_zero' (div_ne_zero hz0 two_ne_zero)
  have hηz : η z ≠ 0 := eta_ne_zero hz
  have hsqrt2 : (Real.sqrt 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  rw [weberF₂, weberF₁, show 2 * (-1 / z) = -1 / (z / 2) by field_simp, eta_neg_inv hz2,
    eta_neg_inv hz, hs]
  field_simp

/-! ### The product identity `𝔣 𝔣₁ 𝔣₂ = √2` -/

/-- The Euler product `∏ (1 - w^(n+1))`. -/
private abbrev eulerProd (w : ℂ) : ℂ := ∏' n : ℕ, (1 - w ^ (n + 1))

/-- The odd-exponent product `∏ (1 - w^(2n+1))`. -/
private abbrev oddProd (w : ℂ) : ℂ := ∏' n : ℕ, (1 - w ^ (2 * n + 1))

private theorem multipliable_oddProd {w : ℂ} (hw : ‖w‖ < 1) :
    Multipliable fun n : ℕ ↦ 1 - w ^ (2 * n + 1) := by
  apply multipliable_one_add_of_summable (f := fun n ↦ -w ^ (2 * n + 1))
  have hw2 : ‖w‖ ^ 2 < 1 := by
    have := norm_nonneg w
    nlinarith
  refine ((summable_geometric_of_lt_one (by positivity) hw2).mul_left ‖w‖).congr fun n => ?_
  rw [norm_neg, norm_pow]
  ring

private theorem eulerProd_eq_oddProd_mul {w : ℂ} (hw : ‖w‖ < 1) :
    eulerProd w = oddProd w * eulerProd (w ^ 2) := by
  have hw2 : ‖w ^ 2‖ < 1 := by
    rw [norm_pow]
    have := norm_nonneg w
    nlinarith
  have heven : (fun k : ℕ ↦ 1 - w ^ (2 * k + 1 + 1)) = fun k ↦ 1 - (w ^ 2) ^ (k + 1) := by
    funext k
    rw [← pow_mul]
    ring_nf
  have := tprod_even_mul_odd (f := fun n : ℕ ↦ 1 - w ^ (n + 1)) (multipliable_oddProd hw)
    (by rw [heven]; exact multipliable_one_sub_pow hw2)
  rw [heven] at this
  exact this.symm

private theorem oddProd_mul_oddProd_neg {w : ℂ} (hw : ‖w‖ < 1) :
    oddProd w * oddProd (-w) = oddProd (w ^ 2) := by
  have hnw : ‖-w‖ < 1 := by rwa [norm_neg]
  rw [oddProd, oddProd, ← (multipliable_oddProd hw).tprod_mul (multipliable_oddProd hnw)]
  congr 1
  funext n
  rw [Odd.neg_pow ⟨n, rfl⟩, ← pow_mul]
  ring_nf

private theorem eulerProd_identity {r : ℂ} (hr : ‖r‖ < 1) :
    eulerProd (-r) * eulerProd r * eulerProd (r ^ 4) = eulerProd (r ^ 2) ^ 3 := by
  have hnr : ‖-r‖ < 1 := by rwa [norm_neg]
  have hr2 : ‖r ^ 2‖ < 1 := by
    rw [norm_pow]
    have := norm_nonneg r
    nlinarith
  have h1 := eulerProd_eq_oddProd_mul hr
  have h2 := eulerProd_eq_oddProd_mul hnr
  have h3 := eulerProd_eq_oddProd_mul hr2
  rw [neg_sq] at h2
  rw [← pow_mul] at h3
  rw [h1, h2, h3, ← oddProd_mul_oddProd_neg hr]
  ring

private theorem eta_eq (w : ℂ) : η w = 𝕢 24 w * eulerProd (𝕢 1 w) := rfl

/-- `η((z+1)/2) η(z/2) η(2z) = ζ₄₈ η(z)³` on the upper half-plane. -/
theorem eta_half_add_mul_eta_half_mul_eta_two_mul {z : ℂ} (hz : 0 < z.im) :
    η ((z + 1) / 2) * η (z / 2) * η (2 * z) = zeta48 * η z ^ 3 := by
  set r := 𝕢 2 z with hr
  have hr1 : ‖r‖ < 1 := Function.Periodic.norm_qParam_lt_one (by norm_num) hz
  have e1 : 𝕢 1 ((z + 1) / 2) = -r := by
    simp only [hr, Function.Periodic.qParam]
    rw [show 2 * (π : ℂ) * I * ((z + 1) / 2) / ((1 : ℝ) : ℂ) = 2 * π * I * z / ((2 : ℝ) : ℂ) +
      π * I by push_cast; ring, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  have e2 : 𝕢 1 (z / 2) = r := by
    simp only [hr, Function.Periodic.qParam]
    congr 1
    push_cast
    ring
  have e3 : 𝕢 1 (2 * z) = r ^ 4 := by
    simp only [hr, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e4 : 𝕢 1 z = r ^ 2 := by
    simp only [hr, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have e5 : 𝕢 24 ((z + 1) / 2) * 𝕢 24 (z / 2) * 𝕢 24 (2 * z) = zeta48 * 𝕢 24 z ^ 3 := by
    simp only [Function.Periodic.qParam, zeta48, ← Complex.exp_add, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [eta_eq, eta_eq, eta_eq, eta_eq, e1, e2, e3, e4]
  calc 𝕢 24 ((z + 1) / 2) * eulerProd (-r) * (𝕢 24 (z / 2) * eulerProd r) *
        (𝕢 24 (2 * z) * eulerProd (r ^ 4))
      = (𝕢 24 ((z + 1) / 2) * 𝕢 24 (z / 2) * 𝕢 24 (2 * z)) *
          (eulerProd (-r) * eulerProd r * eulerProd (r ^ 4)) := by ring
    _ = zeta48 * (𝕢 24 z * eulerProd (r ^ 2)) ^ 3 := by
      rw [e5, eulerProd_identity hr1]
      ring

/-- Weber's product identity `𝔣 𝔣₁ 𝔣₂ = √2`. -/
theorem weberF_mul_weberF₁_mul_weberF₂ {z : ℂ} (hz : 0 < z.im) :
    weberF z * weberF₁ z * weberF₂ z = (Real.sqrt 2 : ℂ) := by
  have hηz : η z ≠ 0 := eta_ne_zero hz
  have h := eta_half_add_mul_eta_half_mul_eta_two_mul hz
  have := zeta48_ne_zero
  simp only [weberF, weberF₁, weberF₂]
  rw [show zeta48⁻¹ * (η ((z + 1) / 2) / η z) * (η (z / 2) / η z) *
      ((Real.sqrt 2 : ℂ) * (η (2 * z) / η z)) =
      (Real.sqrt 2 : ℂ) * zeta48⁻¹ * (η ((z + 1) / 2) * η (z / 2) * η (2 * z)) / η z ^ 3 by ring,
    h]
  field_simp

theorem weberF₁_ne_zero {z : ℂ} (hz : 0 < z.im) : weberF₁ z ≠ 0 := by
  have hz2 : 0 < (z / 2).im := by
    rw [show (z / 2).im = z.im / 2 by simp]
    positivity
  exact div_ne_zero (eta_ne_zero hz2) (eta_ne_zero hz)

theorem weberF₂_ne_zero {z : ℂ} (hz : 0 < z.im) : weberF₂ z ≠ 0 := by
  have h2z : 0 < (2 * z).im := by
    rw [show (2 * z).im = 2 * z.im by simp]
    positivity
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num)))
    (div_ne_zero (eta_ne_zero h2z) (eta_ne_zero hz))

theorem weberF_neg_inv {z : ℂ} (hz : 0 < z.im) : weberF (-1 / z) = weberF z := by
  have hz' : 0 < (-1 / z).im := by
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    rw [neg_div, Complex.neg_im, one_div, Complex.inv_im]
    have : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
    rw [neg_div, neg_neg]
    positivity
  have h1 := weberF_mul_weberF₁_mul_weberF₂ hz'
  have h2 := weberF_mul_weberF₁_mul_weberF₂ hz
  rw [weberF₁_neg_inv hz, weberF₂_neg_inv hz] at h1
  have hf1 := weberF₁_ne_zero hz
  have hf2 := weberF₂_ne_zero hz
  have hprod : weberF₂ z * weberF₁ z ≠ 0 := mul_ne_zero hf2 hf1
  apply mul_right_cancel₀ hprod
  linear_combination h1 - h2

end

end ModularForm
