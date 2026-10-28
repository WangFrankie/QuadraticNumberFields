/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.ModularForms.WeberPolynomial

/-!
# Weber's `γ₂`-Identities

This file proves Weber's identities

`γ₂ = (𝔣²⁴ - 16) / 𝔣⁸ = (𝔣₁²⁴ + 16) / 𝔣₁⁸ = (𝔣₂²⁴ + 16) / 𝔣₂⁸`.

Weber's cubic gives the cubes `(𝔣₂²⁴ + 16)³ = j 𝔣₂²⁴ = (γ₂ 𝔣₂⁸)³`.  Both
`𝔣₂²⁴ + 16` and `γ₂ 𝔣₂⁸` tend to `16` at `i∞`, as the eta products show, so
they agree on a half-plane `Im τ > A`; the identity theorem extends the
equality to the whole upper half-plane.  The identities for `𝔣₁` and `𝔣` are its
transforms under `S` and `T`, using `γ₂(-1/τ) = γ₂(τ)` and
`γ₂(τ + 1) = e^{-2πi/3} γ₂(τ)`.

## Main results

* `ModularForm.gamma₂_mul_weberF₂_pow_8`: `γ₂ 𝔣₂⁸ = 𝔣₂²⁴ + 16`.
* `ModularForm.gamma₂_mul_weberF₁_pow_8`: `γ₂ 𝔣₁⁸ = 𝔣₁²⁴ + 16`.
* `ModularForm.gamma₂_mul_weberF_pow_8`: `γ₂ 𝔣⁸ = 𝔣²⁴ - 16`.
* `ModularForm.gamma₂_S_smul`, `ModularForm.gamma₂_add_one`: the transformation
  laws of `γ₂`.
-/

open Complex EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups Manifold

namespace ModularForm

noncomputable section

local notation "𝕢" => Function.Periodic.qParam

/-- `γ₂ = E₄ / η⁸` extended to `ℂ`, for the identity theorem. -/
private def gamma₂C (z : ℂ) : ℂ := E₄ (UpperHalfPlane.ofComplex z) / η z ^ 8

private theorem gamma₂C_eq {z : ℂ} (hz : 0 < z.im) : gamma₂C z = gamma₂ ⟨z, hz⟩ := by
  rw [gamma₂C, gamma₂, UpperHalfPlane.ofComplex_apply_of_im_pos hz]

/-! ### Choosing the cube root -/

/-- The Euler product `∏ (1 - w^(n+1))`. -/
private abbrev P (w : ℂ) : ℂ := ∏' n : ℕ, (1 - w ^ (n + 1))

private theorem tendsto_P : Filter.Tendsto P (nhds 0) (nhds 1) := by
  have hc : ContinuousAt P 0 :=
    (differentiableOn_tprod_one_sub_pow.differentiableAt
      (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  have h0 : P 0 = 1 := by simp [P]
  simpa [h0] using hc.tendsto

private theorem eta_eq' (w : ℂ) : η w = 𝕢 24 w * P (𝕢 1 w) := rfl

private theorem qParam_24_two_mul (z : ℂ) : 𝕢 24 (2 * z) = 𝕢 24 z ^ 2 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem qParam_1_two_mul (z : ℂ) : 𝕢 1 (2 * z) = 𝕢 1 z ^ 2 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem qParam_24_pow_24 (z : ℂ) : 𝕢 24 z ^ 24 = 𝕢 1 z := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem P_ne_zero {z : ℂ} (hz : 0 < z.im) : P (𝕢 1 z) ≠ 0 := by
  intro h
  exact eta_ne_zero hz (by rw [eta_eq', h, mul_zero])

private theorem ofReal_sqrt_two_pow_8 : (Real.sqrt 2 : ℂ) ^ 8 = 16 := by
  rw [show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem weberF₂_eq_prod {z : ℂ} (hz : 0 < z.im) :
    weberF₂ z = (Real.sqrt 2 : ℂ) * (𝕢 24 z * (P (𝕢 1 z ^ 2) / P (𝕢 1 z))) := by
  have hP := P_ne_zero hz
  have hq := Function.Periodic.qParam_ne_zero (h := 24) z
  rw [weberF₂, eta_eq' (2 * z), eta_eq' z, qParam_24_two_mul, qParam_1_two_mul]
  field_simp

theorem gamma₂C_mul_weberF₂_pow_8_eq_prod {z : ℂ} (hz : 0 < z.im) :
    gamma₂C z * weberF₂ z ^ 8 = 16 * E₄ ⟨z, hz⟩ * (P (𝕢 1 z ^ 2) ^ 8 / P (𝕢 1 z) ^ 16) := by
  have hP := P_ne_zero hz
  have hq := Function.Periodic.qParam_ne_zero (h := 24) z
  rw [gamma₂C, UpperHalfPlane.ofComplex_apply_of_im_pos hz, weberF₂_eq_prod hz, eta_eq' z]
  simp only [mul_pow, ofReal_sqrt_two_pow_8, div_pow]
  field_simp

theorem tendsto_weberF₂_pow_24 :
    Filter.Tendsto (fun τ : UpperHalfPlane ↦ weberF₂ τ ^ 24) UpperHalfPlane.atImInfty (nhds 0) := by
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos
  have hP1 := tendsto_P.comp hq
  have hP2 := tendsto_P.comp (by simpa using hq.pow 2)
  have hfun : (fun τ : UpperHalfPlane ↦ weberF₂ τ ^ 24) =
      fun τ : UpperHalfPlane ↦ 4096 * 𝕢 1 τ * (P (𝕢 1 τ ^ 2) / P (𝕢 1 τ)) ^ 24 := by
    funext τ
    rw [weberF₂_eq_prod τ.im_pos, mul_pow, mul_pow, ofReal_sqrt_two_pow_24, qParam_24_pow_24]
    ring
  rw [hfun]
  simpa using (tendsto_const_nhds (x := (4096 : ℂ))).mul hq |>.mul
    ((hP2.div hP1 one_ne_zero).pow 24)

theorem tendsto_gamma₂C_mul_weberF₂_pow_8 :
    Filter.Tendsto (fun τ : UpperHalfPlane ↦ gamma₂C τ * weberF₂ τ ^ 8)
      UpperHalfPlane.atImInfty (nhds 16) := by
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos
  have hP1 := tendsto_P.comp hq
  have hP2 := tendsto_P.comp (by simpa using hq.pow 2)
  have hE : Filter.Tendsto (fun τ : UpperHalfPlane ↦ E₄ τ) UpperHalfPlane.atImInfty (nhds 1) :=
    EisensteinSeries.tendsto_E_atImInfty
  have hfun : (fun τ : UpperHalfPlane ↦ gamma₂C τ * weberF₂ τ ^ 8) =
      fun τ : UpperHalfPlane ↦ 16 * E₄ τ * (P (𝕢 1 τ ^ 2) ^ 8 / P (𝕢 1 τ) ^ 16) := by
    funext τ
    exact gamma₂C_mul_weberF₂_pow_8_eq_prod τ.im_pos
  rw [hfun]
  simpa using ((tendsto_const_nhds (x := (16 : ℂ))).mul hE).mul
    ((hP2.pow 8).div (hP1.pow 16) (by norm_num))

private theorem differentiableAt_weberF₂ {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ weberF₂ z := by
  have h2z : 0 < (2 * z).im := by
    rw [show (2 * z).im = 2 * z.im by simp]
    positivity
  have h1 : DifferentiableAt ℂ (fun x : ℂ ↦ η (2 * x)) z :=
    DifferentiableAt.comp (g := eta) (f := fun x : ℂ ↦ 2 * x) z
      (differentiableAt_eta_of_mem_upperHalfPlaneSet h2z)
      ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (2 : ℂ))
  exact (h1.div (differentiableAt_eta_of_mem_upperHalfPlaneSet hz)
    (eta_ne_zero hz)).const_mul _

private theorem differentiableAt_gamma₂C {z : ℂ} (hz : 0 < z.im) :
    DifferentiableAt ℂ gamma₂C z := by
  have hE : DifferentiableAt ℂ (fun x : ℂ ↦ E₄ (UpperHalfPlane.ofComplex x)) z :=
    (UpperHalfPlane.mdifferentiable_iff.mp E₄.holo' z hz).differentiableAt
      (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
  exact hE.div ((differentiableAt_eta_of_mem_upperHalfPlaneSet hz).pow 8)
    (pow_ne_zero _ (eta_ne_zero hz))

private theorem gamma₂C_mul_weberF₂_pow_8 {z : ℂ} (hz : 0 < z.im) :
    gamma₂C z * weberF₂ z ^ 8 = weberF₂ z ^ 24 + 16 := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  let u : ℂ → ℂ := fun z ↦ weberF₂ z ^ 24 + 16
  let v : ℂ → ℂ := fun z ↦ gamma₂C z * weberF₂ z ^ 8
  have hcube : ∀ z : ℂ, 0 < z.im → u z ^ 3 = v z ^ 3 := by
    intro z hz
    simp only [u, v]
    rw [show weberF₂ z = weberF₂ (⟨z, hz⟩ : UpperHalfPlane) from rfl,
      weberF₂_cubic ⟨z, hz⟩, mul_pow, gamma₂C_eq hz, gamma₂_cube, ← pow_mul]
  have hu : Filter.Tendsto (fun τ : UpperHalfPlane ↦ u τ) UpperHalfPlane.atImInfty (nhds 16) := by
    simpa [u] using tendsto_weberF₂_pow_24.add_const (16 : ℂ)
  have hv : Filter.Tendsto (fun τ : UpperHalfPlane ↦ v τ) UpperHalfPlane.atImInfty (nhds 16) :=
    tendsto_gamma₂C_mul_weberF₂_pow_8
  have hW : Filter.Tendsto (fun τ : UpperHalfPlane ↦ u τ ^ 2 + u τ * v τ + v τ ^ 2)
      UpperHalfPlane.atImInfty (nhds 768) := by
    have := ((hu.pow 2).add (hu.mul hv)).add (hv.pow 2)
    norm_num at this
    exact this
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp
    (hW.eventually_ne (by norm_num : (768 : ℂ) ≠ 0))
  have heq : ∀ w : ℂ, max A 1 < w.im → u w = v w := by
    intro w hw
    have hw0 : 0 < w.im := by linarith [le_max_right A 1]
    have hne := hA ⟨w, hw0⟩ (by
      change A ≤ w.im
      linarith [le_max_left A 1])
    have h3 := hcube w hw0
    have hprod : (u w - v w) * (u w ^ 2 + u w * v w + v w ^ 2) = 0 := by
      linear_combination h3
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hne
  have hdiff : DifferentiableOn ℂ (fun w ↦ u w - v w) U := by
    intro w hw
    have hw : 0 < w.im := hw
    exact (((differentiableAt_weberF₂ hw).pow 24).add_const 16 |>.sub
      ((differentiableAt_gamma₂C hw).mul
        ((differentiableAt_weberF₂ hw).pow 8))).differentiableWithinAt
  have hanalytic : AnalyticOnNhd ℂ (fun w ↦ u w - v w) U :=
    hdiff.analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hconn : IsPreconnected U :=
    (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected
  set z₀ : ℂ := ((max A 1 + 1 : ℝ) : ℂ) * I with hz₀def
  have hz₀im : z₀.im = max A 1 + 1 := by simp [z₀]
  have hz₀ : z₀ ∈ U := by
    change 0 < z₀.im
    rw [hz₀im]
    linarith [le_max_right A 1]
  have hev : (fun w ↦ u w - v w) =ᶠ[nhds z₀] 0 := by
    have hopen : IsOpen {w : ℂ | max A 1 < w.im} :=
      isOpen_lt continuous_const Complex.continuous_im
    filter_upwards [hopen.mem_nhds (by
      change max A 1 < z₀.im
      rw [hz₀im]
      linarith)] with w hw
    simp [heq w hw]
  have hzero := hanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀ hev
    (show z ∈ U from hz)
  simp only [Pi.zero_apply, sub_eq_zero] at hzero
  exact hzero.symm

/-- **Weber's identity** `γ₂ 𝔣₂⁸ = 𝔣₂²⁴ + 16`, i.e. `γ₂ = (𝔣₂²⁴ + 16) / 𝔣₂⁸`.
The cubes agree by `weberF₂_cubic`; the cube root is fixed because both sides tend to
`16` at `i∞`, and the identity theorem extends the equality to all of `ℍ`. -/
theorem gamma₂_mul_weberF₂_pow_8 (τ : UpperHalfPlane) :
    gamma₂ τ * weberF₂ τ ^ 8 = weberF₂ τ ^ 24 + 16 := by
  rw [← gamma₂C_eq τ.im_pos]
  exact gamma₂C_mul_weberF₂_pow_8 τ.im_pos

/-! ### The other two Weber functions -/

private theorem csqrt_pow_eight {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 8 = z ^ 4 := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul,
    show ((8 : ℕ) : ℂ) * (log z / 2) = ((4 : ℕ) : ℂ) * log z by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_log hz]

set_option backward.isDefEq.respectTransparency.types false in
/-- `γ₂` is invariant under `S : τ ↦ -1/τ`. -/
theorem gamma₂_S_smul (τ : UpperHalfPlane) : gamma₂ (ModularGroup.S • τ) = gamma₂ τ := by
  have hg : Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S ∈ 𝒮ℒ := ⟨ModularGroup.S, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hg τ
  change E₄ (ModularGroup.S • τ) = _ at hE
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hcoe : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [neg_div]
  have hη : η ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) ^ 8 = (τ : ℂ) ^ 4 * η τ ^ 8 := by
    rw [hcoe, eta_neg_inv τ.im_pos, mul_pow, mul_pow, inv_pow, csqrt_pow_eight I_ne_zero,
      csqrt_pow_eight hτ0, I_pow_four, inv_one, one_mul]
  have hden : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ ModularGroup.S) τ =
      (τ : ℂ) := by
    simp [UpperHalfPlane.denom, ModularGroup.S]
  rw [gamma₂, gamma₂, hE, hη, hden]
  norm_num only [zpow_ofNat]
  have hη0 : η τ ≠ 0 := eta_ne_zero τ.im_pos
  field_simp

/-- `γ₂(τ + 1) = e^{-2πi/3} γ₂(τ)`, written as `e^{2πi/24}⁸ γ₂(τ + 1) = γ₂(τ)`. -/
theorem gamma₂_add_one (τ : UpperHalfPlane) :
    cexp (2 * π * I / 24) ^ 8 * gamma₂ ((1 : ℝ) +ᵥ τ) = gamma₂ τ := by
  have hE := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E₄ τ one_mem_strictPeriods_SL
  have hη0 : η τ ≠ 0 := eta_ne_zero τ.im_pos
  rw [gamma₂, gamma₂, hE, UpperHalfPlane.coe_vadd, show ((1 : ℝ) : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 by
    push_cast; ring, eta_add_one, mul_pow]
  have := Complex.exp_ne_zero (2 * π * I / 24)
  field_simp

/-- **Weber's identity** `γ₂ 𝔣₁⁸ = 𝔣₁²⁴ + 16`, i.e. `γ₂ = (𝔣₁²⁴ + 16) / 𝔣₁⁸`. It is the
`S`-transform of `gamma₂_mul_weberF₂_pow_8`. -/
theorem gamma₂_mul_weberF₁_pow_8 (τ : UpperHalfPlane) :
    gamma₂ τ * weberF₁ τ ^ 8 = weberF₁ τ ^ 24 + 16 := by
  have h := gamma₂_mul_weberF₂_pow_8 (ModularGroup.S • τ)
  have hcoe : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) = -1 / (τ : ℂ) := by
    rw [UpperHalfPlane.modular_S_smul]
    simp [neg_div]
  rwa [gamma₂_S_smul, hcoe, weberF₂_neg_inv τ.im_pos] at h

/-- **Weber's identity** `γ₂ 𝔣⁸ = 𝔣²⁴ - 16`, i.e. `γ₂ = (𝔣²⁴ - 16) / 𝔣⁸`. It is the
`T`-transform of `gamma₂_mul_weberF₁_pow_8`. -/
theorem gamma₂_mul_weberF_pow_8 (τ : UpperHalfPlane) :
    gamma₂ τ * weberF τ ^ 8 = weberF τ ^ 24 - 16 := by
  have h := gamma₂_mul_weberF₁_pow_8 ((1 : ℝ) +ᵥ τ)
  have hT := gamma₂_add_one τ
  rw [UpperHalfPlane.coe_vadd, show ((1 : ℝ) : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 by push_cast; ring,
    weberF₁_add_one] at h
  have hz := zeta48_ne_zero
  have hc : cexp (2 * π * I / 24) ^ 8 * zeta48 ^ 8 = -1 := by
    rw [← zeta48_sq, ← pow_mul, ← pow_add, show 2 * 8 + 8 = 24 by norm_num, zeta48_pow_24]
  have hc' : (zeta48⁻¹) ^ 24 = -1 := by rw [inv_pow, zeta48_pow_24]; norm_num
  rw [mul_pow, mul_pow, hc'] at h
  -- multiply `h` by `e^{2πi/24}⁸ ζ₄₈⁸` and use `hT`
  have key : gamma₂ τ * weberF τ ^ 8 =
      (cexp (2 * π * I / 24) ^ 8 * zeta48 ^ 8) *
        (gamma₂ ((1 : ℝ) +ᵥ τ) * ((zeta48⁻¹) ^ 8 * weberF τ ^ 8)) := by
    rw [← hT]
    field_simp
  rw [key, h, hc]
  ring

end

end ModularForm
