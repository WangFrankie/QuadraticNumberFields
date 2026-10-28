/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.ModularForms.DiscriminantCoeffs
import QNFMathlib.NumberTheory.ModularForms.Weber

/-!
# The Hecke Operator `T₂` on `Δ` and Weber's First Symmetric Identity

This file shows that the modular discriminant is an eigenform of the Hecke
operator `T₂` with eigenvalue `τ(2) = -24`, in the form
`Δ(τ/2) + Δ((τ+1)/2) + 2¹² Δ(2τ) = -48 Δ(τ)`, and deduces Weber's identity
`𝔣²⁴ - 𝔣₁²⁴ - 𝔣₂²⁴ = 48`.

The left-hand side is a level-one cusp form of weight `12`: the three points
`τ/2`, `(τ+1)/2`, `2τ` are permuted by `S` and `T`.  Weight-`12` cusp forms are
multiples of `Δ`, and comparing the coefficient of `q` gives the factor `2τ(2)`.

## Main results

* `ModularForm.heckeTwoSum_eq`: `Δ(τ/2) + Δ((τ+1)/2) + 2¹² Δ(2τ) = -48 Δ(τ)`.
* `ModularForm.weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24`:
  `𝔣²⁴ - 𝔣₁²⁴ - 𝔣₂²⁴ = 48`.
-/

open Complex EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups

namespace ModularForm

noncomputable section

/-- The discriminant `Δ = η²⁴`, extended to `ℂ` through the eta product. -/
def discriminantC (z : ℂ) : ℂ := η z ^ 24

local notation "D" => discriminantC

theorem discriminantC_add_one (z : ℂ) : D (z + 1) = D z := by
  rw [discriminantC, discriminantC, eta_add_one, mul_pow, ← Complex.exp_nat_mul,
    show ((24 : ℕ) : ℂ) * (2 * π * I / 24) = 2 * π * I by push_cast; ring, Complex.exp_two_pi_mul_I,
    one_mul]

theorem discriminantC_sub_one (z : ℂ) : D (z - 1) = D z := by
  rw [← discriminantC_add_one (z - 1), sub_add_cancel]

private theorem csqrt_pow_24 {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ^ 24 = z ^ 12 := by
  rw [sqrt_eq_exp hz, ← Complex.exp_nat_mul,
    show ((24 : ℕ) : ℂ) * (log z / 2) = ((12 : ℕ) : ℂ) * log z by push_cast; ring,
    Complex.exp_nat_mul, Complex.exp_log hz]

private theorem csqrt_I_pow_24' : Complex.sqrt I ^ 24 = 1 := by
  rw [csqrt_pow_24 I_ne_zero, show (12 : ℕ) = 4 * 3 by norm_num, pow_mul, I_pow_four, one_pow]

theorem discriminantC_neg_inv {z : ℂ} (hz : 0 < z.im) : D (-1 / z) = z ^ 12 * D z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [discriminantC, discriminantC, eta_neg_inv hz, mul_pow, mul_pow, inv_pow, csqrt_I_pow_24',
    csqrt_pow_24 hz0, inv_one, one_mul]

private theorem im_neg_inv_pos {z : ℂ} (hz : 0 < z.im) : 0 < (-1 / z).im := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz0
  rw [neg_div, Complex.neg_im, one_div, Complex.inv_im, neg_div, neg_neg]
  positivity

/-- The transformation of `Δ` under `w ↦ (w - 1)/(2w - 1)`, i.e. under the matrix
`!![1, -1; 2, -1] = S T⁻² S⁻¹ T⁻¹`. -/
theorem discriminantC_moebius {w : ℂ} (hw : 0 < w.im) :
    D ((w - 1) / (2 * w - 1)) = (2 * w - 1) ^ 12 * D w := by
  set a := w - 1 with ha
  have ha_im : 0 < a.im := by simpa [ha] using hw
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha_im
  set b := -1 / a with hb
  have hb_im : 0 < b.im := im_neg_inv_pos ha_im
  set c := b - 1 - 1 with hc
  have hc_im : 0 < c.im := by simpa [hc] using hb_im
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc_im
  have hpt : (w - 1) / (2 * w - 1) = -1 / c := by
    have h2 : 2 * w - 1 ≠ 0 := by
      intro h
      have : (2 * w - 1).im = 2 * w.im := by simp
      rw [h] at this
      simp at this
      linarith
    have hw1 : w - 1 ≠ 0 := ha0
    have hc' : c = -(2 * w - 1) / (w - 1) := by
      rw [hc, hb, ha]
      field_simp
      ring
    rw [hc']
    field_simp
  have hca : c * a = -(2 * w - 1) := by
    rw [hc, hb]
    field_simp
    rw [ha]
    ring
  rw [hpt, discriminantC_neg_inv hc_im, hc, discriminantC_sub_one, discriminantC_sub_one, hb,
    discriminantC_neg_inv ha_im, ha, discriminantC_sub_one, ← mul_assoc, ← mul_pow]
  rw [← hb, ← hc, ← ha, hca]
  ring

/-- The Hecke-type sum `Δ(z/2) + Δ((z+1)/2) + 2¹² Δ(2z)` on `ℂ`. -/
def heckeTwoSum (z : ℂ) : ℂ := D (z / 2) + D ((z + 1) / 2) + 4096 * D (2 * z)

theorem heckeTwoSum_add_one (z : ℂ) : heckeTwoSum (z + 1) = heckeTwoSum z := by
  rw [heckeTwoSum, heckeTwoSum, show (z + 1 + 1) / 2 = z / 2 + 1 by ring, discriminantC_add_one,
    show 2 * (z + 1) = 2 * z + 1 + 1 by ring, discriminantC_add_one, discriminantC_add_one]
  ring

theorem heckeTwoSum_neg_inv {z : ℂ} (hz : 0 < z.im) :
    heckeTwoSum (-1 / z) = z ^ 12 * heckeTwoSum z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h2z : 0 < (2 * z).im := by
    rw [show (2 * z).im = 2 * z.im by simp]
    positivity
  have hz2 : 0 < (z / 2).im := by
    rw [show (z / 2).im = z.im / 2 by simp]
    positivity
  have hw : 0 < ((z + 1) / 2).im := by
    rw [show ((z + 1) / 2).im = z.im / 2 by simp]
    positivity
  have e1 : -1 / z / 2 = -1 / (2 * z) := by field_simp
  have e2 : (-1 / z + 1) / 2 = ((z + 1) / 2 - 1) / (2 * ((z + 1) / 2) - 1) := by
    rw [show 2 * ((z + 1) / 2) - 1 = z by ring, show (z + 1) / 2 - 1 = (z - 1) / 2 by ring]
    field_simp
    ring
  have e3 : 2 * (-1 / z) = -1 / (z / 2) := by field_simp
  rw [heckeTwoSum, heckeTwoSum, e1, e2, e3, discriminantC_neg_inv h2z, discriminantC_moebius hw,
    discriminantC_neg_inv hz2, show 2 * ((z + 1) / 2) - 1 = z by ring]
  ring

/-! ### The `q`-expansion of the Hecke sum -/

local notation "𝕢" => Function.Periodic.qParam

/-- The `q`-expansion coefficients `τ(n)` of `Δ`. -/
private abbrev tau (n : ℕ) : ℂ := (UpperHalfPlane.qExpansion 1 ModularForm.discriminant).coeff n

private theorem qParam_one_div_two (z : ℂ) : 𝕢 1 (z / 2) = 𝕢 2 z := by
  simp only [Function.Periodic.qParam]
  congr 1
  push_cast
  ring

private theorem qParam_one_add_one_div_two (z : ℂ) : 𝕢 1 ((z + 1) / 2) = -𝕢 2 z := by
  simp only [Function.Periodic.qParam]
  rw [show 2 * (π : ℂ) * I * ((z + 1) / 2) / ((1 : ℝ) : ℂ) =
    2 * π * I * z / ((2 : ℝ) : ℂ) + π * I by push_cast; ring, Complex.exp_add,
    Complex.exp_pi_mul_I]
  ring

private theorem qParam_one_two_mul (z : ℂ) : 𝕢 1 (2 * z) = 𝕢 2 z ^ 4 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem qParam_one_eq_sq (z : ℂ) : 𝕢 1 z = 𝕢 2 z ^ 2 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

private theorem hasSum_discriminantC {w : ℂ} (hw : 0 < w.im) :
    HasSum (fun n : ℕ ↦ tau n * 𝕢 1 w ^ n) (D w) := by
  exact ModularForm.hasSum_qExpansion (f := CuspForm.discriminant) one_pos
    one_mem_strictPeriods_SL ⟨w, hw⟩

private theorem injective_two_mul : Function.Injective (fun m : ℕ ↦ 2 * m) :=
  fun x y h => by simpa using h

/-- Keep only the even-indexed terms of a series in `r` and `-r`. -/
private theorem hasSum_even_of_hasSum {a : ℕ → ℂ} {r S : ℂ}
    (h : HasSum (fun n ↦ a n * r ^ n + a n * (-r) ^ n) S) :
    HasSum (fun m ↦ 2 * a (2 * m) * (r ^ 2) ^ m) S := by
  have hzero : ∀ n ∉ Set.range (fun m : ℕ ↦ 2 * m), a n * r ^ n + a n * (-r) ^ n = 0 := by
    intro n hn
    have hodd : Odd n := by
      rcases Nat.even_or_odd n with ⟨k, hk⟩ | ho
      · exact absurd ⟨k, show 2 * k = n by omega⟩ hn
      · exact ho
    rw [hodd.neg_pow]
    ring
  have := (injective_two_mul.hasSum_iff hzero).mpr h
  convert this using 1
  funext m
  simp only [Function.comp_apply, Even.neg_pow ⟨m, two_mul m⟩, ← pow_mul]
  ring

/-- Spread a series in `r⁴` to a series in `r²` with vanishing odd coefficients. -/
private theorem hasSum_spread {a : ℕ → ℂ} {r S : ℂ}
    (h : HasSum (fun n ↦ a n * (r ^ 4) ^ n) S) :
    HasSum (fun m ↦ (if 2 ∣ m then a (m / 2) else 0) * (r ^ 2) ^ m) S := by
  have hzero : ∀ m ∉ Set.range (fun n : ℕ ↦ 2 * n),
      (if 2 ∣ m then a (m / 2) else 0) * (r ^ 2) ^ m = 0 := by
    intro m hm
    have : ¬ 2 ∣ m := fun ⟨k, hk⟩ => hm ⟨k, hk.symm⟩
    simp [this]
  rw [← injective_two_mul.hasSum_iff hzero]
  convert h using 1
  funext n
  simp only [Function.comp_apply, dvd_mul_right, ↓reduceIte,
    Nat.mul_div_cancel_left n two_pos, ← pow_mul]
  ring_nf

/-- The `q`-expansion of the Hecke sum: its `m`-th coefficient is
`2 τ(2m) + 2¹² τ(m/2)`, the second term only for even `m`. -/
theorem hasSum_heckeTwoSum (z : UpperHalfPlane) :
    HasSum (fun m ↦ (2 * tau (2 * m) + 4096 * (if 2 ∣ m then tau (m / 2) else 0)) •
      𝕢 1 (z : ℂ) ^ m) (heckeTwoSum z) := by
  have hz : 0 < (z : ℂ).im := z.im_pos
  have h1 := hasSum_discriminantC (w := (z : ℂ) / 2) (by
    rw [show ((z : ℂ) / 2).im = (z : ℂ).im / 2 by simp]
    positivity)
  have h2 := hasSum_discriminantC (w := ((z : ℂ) + 1) / 2) (by
    rw [show (((z : ℂ) + 1) / 2).im = (z : ℂ).im / 2 by simp]
    positivity)
  have h3 := hasSum_discriminantC (w := 2 * (z : ℂ)) (by
    rw [show (2 * (z : ℂ)).im = 2 * (z : ℂ).im by simp]
    positivity)
  rw [qParam_one_div_two] at h1
  rw [qParam_one_add_one_div_two] at h2
  rw [qParam_one_two_mul] at h3
  have h12 := hasSum_even_of_hasSum (h1.add h2)
  have h3' := hasSum_spread h3
  rw [qParam_one_eq_sq]
  convert h12.add (h3'.mul_left 4096) using 1
  · funext m
    simp only [smul_eq_mul]
    ring
  · rfl

/-! ### The Hecke sum as a cusp form -/

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeTwo_T_invariant :
    ((fun τ : UpperHalfPlane ↦ heckeTwoSum τ) ∣[(12 : ℤ)] ModularGroup.T) =
      fun τ : UpperHalfPlane ↦ heckeTwoSum τ := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [UpperHalfPlane.coe_vadd, add_comm, heckeTwoSum_add_one]

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeTwo_S_invariant :
    ((fun τ : UpperHalfPlane ↦ heckeTwoSum τ) ∣[(12 : ℤ)] ModularGroup.S) =
      fun τ : UpperHalfPlane ↦ heckeTwoSum τ := by
  ext z
  suffices heckeTwoSum (-((z : ℂ))⁻¹) * ((z : ℂ) ^ 12)⁻¹ = heckeTwoSum z by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [UpperHalfPlane.denom, ModularGroup.S]
  rw [show -((z : ℂ))⁻¹ = -1 / (z : ℂ) by ring, heckeTwoSum_neg_inv z.im_pos]
  have := z.ne_zero
  field_simp

private theorem differentiableAt_discriminantC {w : ℂ} (hw : 0 < w.im) :
    DifferentiableAt ℂ D w :=
  (differentiableAt_eta_of_mem_upperHalfPlaneSet hw).pow 24

theorem differentiableOn_heckeTwoSum :
    DifferentiableOn ℂ heckeTwoSum {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz : 0 < z.im := hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ D (z / 2)) z :=
    (differentiableAt_discriminantC (by
      rw [show (z / 2).im = z.im / 2 by simp]
      positivity)).comp z (differentiableAt_id.div_const 2)
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ D ((z + 1) / 2)) z :=
    (differentiableAt_discriminantC (by
      rw [show ((z + 1) / 2).im = z.im / 2 by simp]
      positivity)).comp z ((differentiableAt_id.add_const 1).div_const 2)
  have h3 : DifferentiableAt ℂ (fun z : ℂ ↦ D (2 * z)) z :=
    (differentiableAt_discriminantC (by
      rw [show (2 * z).im = 2 * z.im by simp]
      positivity)).comp z (differentiableAt_id.const_mul 2)
  exact ((h1.add h2).add (h3.const_mul 4096)).differentiableWithinAt

private theorem tau_zero : tau 0 = 0 := by
  exact CuspFormClass.qExpansion_coeff_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL

theorem heckeTwo_isZeroAtImInfty :
    UpperHalfPlane.IsZeroAtImInfty (fun τ : UpperHalfPlane ↦ heckeTwoSum τ) := by
  have := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion one_pos hasSum_heckeTwoSum
  simp only [tau_zero, mul_zero, zero_add, Nat.zero_div, dvd_zero, ↓reduceIte] at this
  exact this

/-- The Hecke sum `Δ(τ/2) + Δ((τ+1)/2) + 2¹² Δ(2τ)` as a level-one cusp form of
weight `12`. -/
def heckeTwoCuspForm : CuspForm 𝒮ℒ 12 where
  toFun τ := heckeTwoSum τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z heckeTwo_S_invariant
      heckeTwo_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine differentiableOn_heckeTwoSum.congr fun z hz => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z heckeTwo_S_invariant
      heckeTwo_T_invariant]
    exact heckeTwo_isZeroAtImInfty

/-- **`Δ` is a Hecke eigenform for `T₂` with eigenvalue `τ(2) = -24`:**
`Δ(τ/2) + Δ((τ+1)/2) + 2¹² Δ(2τ) = -48 Δ(τ)`. -/
theorem heckeTwoSum_eq {z : ℂ} (hz : 0 < z.im) : heckeTwoSum z = -48 * D z := by
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve heckeTwoCuspForm
  have hval : ∀ τ : UpperHalfPlane, heckeTwoSum τ = c * D τ := fun τ =>
    (congrArg (fun f : CuspForm 𝒮ℒ 12 ↦ f τ) hc).symm
  have hsum : ∀ τ : UpperHalfPlane, HasSum (fun m ↦ (c * tau m) • Function.Periodic.qParam 1
      (τ : ℂ) ^ m) (heckeTwoCuspForm τ) := by
    intro τ
    change HasSum _ (heckeTwoSum τ)
    rw [hval τ]
    simpa [smul_eq_mul, mul_assoc] using (hasSum_discriminantC τ.im_pos).mul_left c
  have h1 := ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := heckeTwoCuspForm) hasSum_heckeTwoSum 1
  have h2 := ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_SL
    (f := heckeTwoCuspForm) hsum 1
  have htau1 : tau 1 = 1 := ModularForm.discriminant_qExpansion_coeff_one
  have htau2 : tau 2 = -24 := discriminant_qExpansion_coeff_two
  have hc48 : c = -48 := by
    have := h1.trans h2.symm
    norm_num [htau1, htau2] at this
    linear_combination -this
  have := hval ⟨z, hz⟩
  rw [hc48] at this
  exact this

/-! ### Weber's first symmetric identity -/

theorem zeta48_pow_24 : zeta48 ^ 24 = -1 := by
  rw [zeta48, ← Complex.exp_nat_mul,
    show ((24 : ℕ) : ℂ) * (2 * π * I / 48) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

theorem ofReal_sqrt_two_pow_24 : (Real.sqrt 2 : ℂ) ^ 24 = 4096 := by
  rw [show (24 : ℕ) = 2 * 12 by norm_num, pow_mul, ← Complex.ofReal_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

/-- Weber's identity `𝔣²⁴ - 𝔣₁²⁴ - 𝔣₂²⁴ = 48`: the first symmetric function of
`𝔣²⁴, -𝔣₁²⁴, -𝔣₂²⁴`. It is the Hecke eigenvalue `τ(2) = -24` of `Δ`. -/
theorem weberF_pow_24_sub_weberF₁_pow_24_sub_weberF₂_pow_24 {z : ℂ} (hz : 0 < z.im) :
    weberF z ^ 24 - weberF₁ z ^ 24 - weberF₂ z ^ 24 = 48 := by
  have hη : η z ≠ 0 := eta_ne_zero hz
  have h := heckeTwoSum_eq hz
  simp only [heckeTwoSum, discriminantC] at h
  rw [weberF, weberF₁, weberF₂, mul_pow, inv_pow, zeta48_pow_24, div_pow, div_pow, mul_pow,
    ofReal_sqrt_two_pow_24, div_pow]
  field_simp
  simp only [mul_comm z 2]
  linear_combination -h

end

end ModularForm
