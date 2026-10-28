/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.NumberTheory.ModularForms.HeckeTwo

/-!
# The Second Symmetric Function of the `T₂`-Translates of `Δ`

This file proves
`Δ(τ/2) Δ((τ+1)/2) + 2¹² Δ(2τ) (Δ(τ/2) + Δ((τ+1)/2)) = -Δ E₄³ + 768 Δ²`.

The left-hand side is a level-one cusp form of weight `24`, so it equals
`Δ (h₀ E₄³ + c Δ)` for constants `h₀, c`.  The constants are read off from the
expansions in `e^{πiτ}` of `Δ(τ/2)`, `Δ((τ+1)/2)`, `Δ(2τ)`, `Δ` and `E₄`, which
are computed from `τ(1), τ(2), τ(3)` and the first coefficients of `E₄`.
Together with `ModularForm.heckeTwoSum_eq`, this identifies the cubic whose
roots are `Δ(τ/2)`, `Δ((τ+1)/2)` and `2¹² Δ(2τ)`, which is the source of Weber's
`γ₂`-identities.

## Main results

* `ModularForm.heckeTwoCuspForm₂`: the second symmetric function as a cusp form of
  weight `24`.
* `ModularForm.qExpansion_eq_mk_of_hasSum`: an explicit everywhere convergent
  expansion is the `q`-expansion of any period.
* `ModularForm.heckeTwoSum₂_eq`:
  `Δ(τ/2) Δ((τ+1)/2) + 2¹² Δ(2τ) (Δ(τ/2) + Δ((τ+1)/2)) = -Δ E₄³ + 768 Δ²`.
-/

open Complex EisensteinSeries
open UpperHalfPlane hiding I
open scoped Real ModularForm MatrixGroups Manifold ArithmeticFunction.sigma

namespace ModularForm

noncomputable section

local notation "D" => discriminantC
local notation "𝕢" => Function.Periodic.qParam

/-! ### The three translates under `S` -/

private theorem im_two_mul_pos {z : ℂ} (hz : 0 < z.im) : 0 < (2 * z).im := by
  rw [show (2 * z).im = 2 * z.im by simp]
  positivity

private theorem im_div_two_pos {z : ℂ} (hz : 0 < z.im) : 0 < (z / 2).im := by
  rw [show (z / 2).im = z.im / 2 by simp]
  positivity

private theorem im_add_one_div_two_pos {z : ℂ} (hz : 0 < z.im) : 0 < ((z + 1) / 2).im := by
  rw [show ((z + 1) / 2).im = z.im / 2 by simp]
  positivity

theorem discriminantC_neg_inv_div_two {z : ℂ} (hz : 0 < z.im) :
    D (-1 / z / 2) = 4096 * z ^ 12 * D (2 * z) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [show -1 / z / 2 = -1 / (2 * z) by field_simp, discriminantC_neg_inv (im_two_mul_pos hz)]
  ring

theorem discriminantC_neg_inv_add_one_div_two {z : ℂ} (hz : 0 < z.im) :
    D ((-1 / z + 1) / 2) = z ^ 12 * D ((z + 1) / 2) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have e : (-1 / z + 1) / 2 = ((z + 1) / 2 - 1) / (2 * ((z + 1) / 2) - 1) := by
    rw [show 2 * ((z + 1) / 2) - 1 = z by ring, show (z + 1) / 2 - 1 = (z - 1) / 2 by ring]
    field_simp
    ring
  rw [e, discriminantC_moebius (im_add_one_div_two_pos hz), show 2 * ((z + 1) / 2) - 1 = z by ring]

theorem discriminantC_two_mul_neg_inv {z : ℂ} (hz : 0 < z.im) :
    D (2 * (-1 / z)) = z ^ 12 / 4096 * D (z / 2) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  rw [show 2 * (-1 / z) = -1 / (z / 2) by field_simp, discriminantC_neg_inv (im_div_two_pos hz)]
  ring

/-! ### The second symmetric function -/

/-- The second elementary symmetric function of `Δ(z/2)`, `Δ((z+1)/2)` and `2¹²Δ(2z)`. -/
def heckeTwoSum₂ (z : ℂ) : ℂ :=
  D (z / 2) * D ((z + 1) / 2) + 4096 * D (2 * z) * (D (z / 2) + D ((z + 1) / 2))

theorem heckeTwoSum₂_add_one (z : ℂ) : heckeTwoSum₂ (z + 1) = heckeTwoSum₂ z := by
  rw [heckeTwoSum₂, heckeTwoSum₂, show (z + 1 + 1) / 2 = z / 2 + 1 by ring, discriminantC_add_one,
    show 2 * (z + 1) = 2 * z + 1 + 1 by ring, discriminantC_add_one, discriminantC_add_one]
  ring

theorem heckeTwoSum₂_neg_inv {z : ℂ} (hz : 0 < z.im) :
    heckeTwoSum₂ (-1 / z) = z ^ 24 * heckeTwoSum₂ z := by
  rw [heckeTwoSum₂, heckeTwoSum₂, discriminantC_neg_inv_div_two hz,
    discriminantC_neg_inv_add_one_div_two hz, discriminantC_two_mul_neg_inv hz]
  ring

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeTwo₂_T_invariant :
    ((fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) ∣[(24 : ℤ)] ModularGroup.T) =
      fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ := by
  ext z
  rw [SL_slash_apply, UpperHalfPlane.denom, UpperHalfPlane.modular_T_smul, ModularGroup.T]
  simp [UpperHalfPlane.coe_vadd, add_comm, heckeTwoSum₂_add_one]

set_option backward.isDefEq.respectTransparency.types false in
theorem heckeTwo₂_S_invariant :
    ((fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) ∣[(24 : ℤ)] ModularGroup.S) =
      fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ := by
  ext z
  suffices heckeTwoSum₂ (-((z : ℂ))⁻¹) * ((z : ℂ) ^ 24)⁻¹ = heckeTwoSum₂ z by
    rw [SL_slash_apply, UpperHalfPlane.modular_S_smul]
    simpa [UpperHalfPlane.denom, ModularGroup.S]
  rw [show -((z : ℂ))⁻¹ = -1 / (z : ℂ) by ring, heckeTwoSum₂_neg_inv z.im_pos]
  have := z.ne_zero
  field_simp

theorem differentiableOn_heckeTwoSum₂ :
    DifferentiableOn ℂ heckeTwoSum₂ {z : ℂ | 0 < z.im} := by
  intro z hz
  have hz : 0 < z.im := hz
  have h1 : DifferentiableAt ℂ (fun z : ℂ ↦ D (z / 2)) z :=
    DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ x / 2) z
      (differentiableAt_discriminantC (im_div_two_pos hz))
      ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const (2 : ℂ))
  have h2 : DifferentiableAt ℂ (fun z : ℂ ↦ D ((z + 1) / 2)) z :=
    DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ (x + 1) / 2) z
      (differentiableAt_discriminantC (im_add_one_div_two_pos hz))
      (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const (1 : ℂ)).div_const (2 : ℂ))
  have h3 : DifferentiableAt ℂ (fun z : ℂ ↦ D (2 * z)) z :=
    DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ 2 * x) z
      (differentiableAt_discriminantC (im_two_mul_pos hz))
      ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (2 : ℂ))
  exact ((h1.mul h2).add ((h3.const_mul 4096).mul (h1.add h2))).differentiableWithinAt

/-! ### `q`-expansions of period `2` -/

/-- A periodic holomorphic function on `ℍ` with an everywhere convergent expansion in
`𝕢 h` has an analytic cusp function. -/
theorem analyticAt_cuspFunction_of_hasSum {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ} {h : ℝ}
    (hh : 0 < h) (hper : ∀ τ : UpperHalfPlane, f (h +ᵥ τ) = f τ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ τ : UpperHalfPlane, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction h f) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero hh (UpperHalfPlane.periodic_comp_ofComplex hper)
    hhol (UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion hh hf)

/-- A periodic holomorphic function on `ℍ` with an everywhere convergent expansion in
`𝕢 h` has that expansion as its `q`-expansion. -/
theorem qExpansion_eq_mk_of_hasSum {f : UpperHalfPlane → ℂ} {c : ℕ → ℂ} {h : ℝ}
    (hh : 0 < h) (hper : ∀ τ : UpperHalfPlane, f (h +ᵥ τ) = f τ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ τ : UpperHalfPlane, HasSum (fun m ↦ c m • 𝕢 h τ ^ m) (f τ)) :
    UpperHalfPlane.qExpansion h f = PowerSeries.mk c := by
  have hfanalytic := analyticAt_cuspFunction_of_hasSum hh hper hhol hf
  have h1 := (UpperHalfPlane.hasFPowerSeriesOnBall_cuspFunction hh hfanalytic hf).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (UpperHalfPlane.cuspFunction h f)
      (.ofScalars ℂ fun m ↦ (UpperHalfPlane.qExpansion h f).coeff m) 0 := by
    simpa [UpperHalfPlane.qExpansion_coeff, div_eq_mul_inv, mul_comm] using
      hfanalytic.hasFPowerSeriesAt
  ext m
  rw [PowerSeries.coeff_mk]
  simpa using congr(FormalMultilinearSeries.coeff $(h2.eq_formalMultilinearSeries h1) m)

/-- Spread a series in `x ^ k` to a series in `x` whose coefficients vanish off
multiples of `k`. -/
theorem hasSum_spread_pow {a : ℕ → ℂ} {x S : ℂ} {k : ℕ} (hk : 0 < k)
    (h : HasSum (fun n ↦ a n * (x ^ k) ^ n) S) :
    HasSum (fun m ↦ (if k ∣ m then a (m / k) else 0) • x ^ m) S := by
  have hinj : Function.Injective (fun n : ℕ ↦ k * n) :=
    fun _ _ hxy => Nat.eq_of_mul_eq_mul_left hk hxy
  have hzero : ∀ m ∉ Set.range (fun n : ℕ ↦ k * n),
      (if k ∣ m then a (m / k) else 0) • x ^ m = 0 := by
    intro m hm
    have : ¬ k ∣ m := fun ⟨n, hn⟩ => hm ⟨n, hn.symm⟩
    simp [this]
  rw [← hinj.hasSum_iff hzero]
  convert h using 1
  funext n
  simp only [Function.comp_apply, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left n hk,
    smul_eq_mul, ← pow_mul]

/-- `f` is `2`-periodic, holomorphic on `ℍ` and bounded at `i∞`; such functions have an
analytic cusp function of period `2`. -/
structure IsPeriodTwoForm (f : UpperHalfPlane → ℂ) : Prop where
  periodic : ∀ τ : UpperHalfPlane, f ((2 : ℝ) +ᵥ τ) = f τ
  holo : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f
  bdd : UpperHalfPlane.IsBoundedAtImInfty f

namespace IsPeriodTwoForm

variable {f g : UpperHalfPlane → ℂ}

theorem analyticAt (hf : IsPeriodTwoForm f) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 2 f) 0 :=
  UpperHalfPlane.analyticAt_cuspFunction_zero two_pos
    (UpperHalfPlane.periodic_comp_ofComplex hf.periodic) hf.holo hf.bdd

theorem mul (hf : IsPeriodTwoForm f) (hg : IsPeriodTwoForm g) : IsPeriodTwoForm (f * g) where
  periodic τ := by simp [hf.periodic τ, hg.periodic τ]
  holo := hf.holo.mul hg.holo
  bdd := hf.bdd.mul hg.bdd

theorem add (hf : IsPeriodTwoForm f) (hg : IsPeriodTwoForm g) : IsPeriodTwoForm (f + g) where
  periodic τ := by simp [hf.periodic τ, hg.periodic τ]
  holo := hf.holo.add hg.holo
  bdd := hf.bdd.add hg.bdd

theorem const_smul (hf : IsPeriodTwoForm f) (c : ℂ) : IsPeriodTwoForm (c • f) where
  periodic τ := by simp [hf.periodic τ]
  holo := hf.holo.const_smul c
  bdd := hf.bdd.smul c

theorem of_hasSum {c : ℕ → ℂ} (hper : ∀ τ : UpperHalfPlane, f ((2 : ℝ) +ᵥ τ) = f τ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hf : ∀ τ : UpperHalfPlane, HasSum (fun m ↦ c m • 𝕢 2 τ ^ m) (f τ)) :
    IsPeriodTwoForm f :=
  ⟨hper, hhol, UpperHalfPlane.isBoundedAtImInfty_of_hasSum_qExpansion two_pos hf⟩

end IsPeriodTwoForm

/-! ### The factors and their expansions in `e^{πiτ}` -/

/-- `τ ↦ Δ(τ/2)` on `ℍ`. -/
def deltaHalf (τ : UpperHalfPlane) : ℂ := D ((τ : ℂ) / 2)

/-- `τ ↦ Δ((τ+1)/2)` on `ℍ`. -/
def deltaHalfShift (τ : UpperHalfPlane) : ℂ := D (((τ : ℂ) + 1) / 2)

/-- `τ ↦ Δ(2τ)` on `ℍ`. -/
def deltaTwice (τ : UpperHalfPlane) : ℂ := D (2 * (τ : ℂ))

private theorem mdifferentiable_of_differentiableOn {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F {z : ℂ | 0 < z.im}) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : UpperHalfPlane ↦ F τ) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  refine hF.congr fun z hz => ?_
  simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

theorem deltaHalf_vadd_two (τ : UpperHalfPlane) : deltaHalf ((2 : ℝ) +ᵥ τ) = deltaHalf τ := by
  simp only [deltaHalf, UpperHalfPlane.coe_vadd]
  rw [show ((2 : ℝ) + (τ : ℂ)) / 2 = (τ : ℂ) / 2 + 1 by push_cast; ring, discriminantC_add_one]

theorem mdifferentiable_deltaHalf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) deltaHalf :=
  mdifferentiable_of_differentiableOn (F := fun z ↦ D (z / 2)) fun z hz =>
    (DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ x / 2) z
      (differentiableAt_discriminantC (im_div_two_pos hz))
      ((differentiableAt_id (𝕜 := ℂ) (x := z)).div_const (2 : ℂ))).differentiableWithinAt

theorem hasSum_deltaHalf (τ : UpperHalfPlane) :
    HasSum (fun n ↦ tau n • 𝕢 2 τ ^ n) (deltaHalf τ) := by
  have := hasSum_discriminantC (im_div_two_pos τ.im_pos)
  rw [qParam_one_div_two] at this
  exact this

theorem deltaHalfShift_vadd_two (τ : UpperHalfPlane) :
    deltaHalfShift ((2 : ℝ) +ᵥ τ) = deltaHalfShift τ := by
  simp only [deltaHalfShift, UpperHalfPlane.coe_vadd]
  rw [show ((2 : ℝ) + (τ : ℂ) + 1) / 2 = ((τ : ℂ) + 1) / 2 + 1 by push_cast; ring,
    discriminantC_add_one]

theorem mdifferentiable_deltaHalfShift : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) deltaHalfShift :=
  mdifferentiable_of_differentiableOn (F := fun z ↦ D ((z + 1) / 2)) fun z hz =>
    (DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ (x + 1) / 2) z
      (differentiableAt_discriminantC (im_add_one_div_two_pos hz))
      (((differentiableAt_id (𝕜 := ℂ) (x := z)).add_const (1 : ℂ)).div_const
        (2 : ℂ))).differentiableWithinAt

theorem hasSum_deltaHalfShift (τ : UpperHalfPlane) :
    HasSum (fun n ↦ ((-1) ^ n * tau n) • 𝕢 2 τ ^ n) (deltaHalfShift τ) := by
  have := hasSum_discriminantC (im_add_one_div_two_pos τ.im_pos)
  rw [qParam_one_add_one_div_two] at this
  convert this using 1
  · funext n
    rw [smul_eq_mul, neg_pow]
    ring
  · rfl

theorem deltaTwice_vadd_two (τ : UpperHalfPlane) : deltaTwice ((2 : ℝ) +ᵥ τ) = deltaTwice τ := by
  simp only [deltaTwice, UpperHalfPlane.coe_vadd]
  rw [show 2 * ((2 : ℝ) + (τ : ℂ)) = 2 * (τ : ℂ) + 1 + 1 + 1 + 1 by push_cast; ring,
    discriminantC_add_one, discriminantC_add_one, discriminantC_add_one, discriminantC_add_one]

theorem mdifferentiable_deltaTwice : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) deltaTwice :=
  mdifferentiable_of_differentiableOn (F := fun z ↦ D (2 * z)) fun z hz =>
    (DifferentiableAt.comp (g := discriminantC) (f := fun x : ℂ ↦ 2 * x) z
      (differentiableAt_discriminantC (im_two_mul_pos hz))
      ((differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul (2 : ℂ))).differentiableWithinAt

theorem hasSum_deltaTwice (τ : UpperHalfPlane) :
    HasSum (fun n ↦ (if 4 ∣ n then tau (n / 4) else 0) • 𝕢 2 τ ^ n) (deltaTwice τ) := by
  have := hasSum_discriminantC (im_two_mul_pos τ.im_pos)
  rw [qParam_one_two_mul] at this
  exact hasSum_spread_pow (by norm_num) this

theorem discriminant_vadd_two (τ : UpperHalfPlane) :
    ModularForm.discriminant ((2 : ℝ) +ᵥ τ) = ModularForm.discriminant τ := by
  change D ((2 : ℝ) +ᵥ τ : UpperHalfPlane) = D τ
  rw [UpperHalfPlane.coe_vadd, show ((2 : ℝ) : ℂ) + (τ : ℂ) = (τ : ℂ) + 1 + 1 by push_cast; ring,
    discriminantC_add_one, discriminantC_add_one]

theorem hasSum_discriminant_two (τ : UpperHalfPlane) :
    HasSum (fun n ↦ (if 2 ∣ n then tau (n / 2) else 0) • 𝕢 2 τ ^ n)
      (ModularForm.discriminant τ) := by
  have := hasSum_discriminantC τ.im_pos
  rw [qParam_one_eq_sq] at this
  exact hasSum_spread_pow (by norm_num) this

theorem E₄_vadd_two (τ : UpperHalfPlane) : E₄ ((2 : ℝ) +ᵥ τ) = E₄ τ := by
  have h1 := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E₄ τ one_mem_strictPeriods_SL
  have h2 := SlashInvariantForm.vAdd_apply_of_mem_strictPeriods E₄ ((1 : ℝ) +ᵥ τ)
    one_mem_strictPeriods_SL
  rw [vadd_vadd, one_add_one_eq_two] at h2
  rw [h2, h1]

theorem hasSum_E₄_two (τ : UpperHalfPlane) :
    HasSum (fun n ↦ (if 2 ∣ n then (UpperHalfPlane.qExpansion 1 E₄).coeff (n / 2) else 0) •
      𝕢 2 τ ^ n) (E₄ τ) := by
  have := ModularForm.hasSum_qExpansion (f := E₄) one_pos one_mem_strictPeriods_SL τ
  rw [qParam_one_eq_sq] at this
  exact hasSum_spread_pow (a := fun m ↦ (UpperHalfPlane.qExpansion 1 E₄).coeff m)
    (x := 𝕢 2 τ) (S := E₄ τ) (k := 2) two_pos this

theorem isPeriodTwoForm_deltaHalf : IsPeriodTwoForm deltaHalf :=
  .of_hasSum deltaHalf_vadd_two mdifferentiable_deltaHalf hasSum_deltaHalf

theorem isPeriodTwoForm_deltaHalfShift : IsPeriodTwoForm deltaHalfShift :=
  .of_hasSum deltaHalfShift_vadd_two mdifferentiable_deltaHalfShift hasSum_deltaHalfShift

theorem isPeriodTwoForm_deltaTwice : IsPeriodTwoForm deltaTwice :=
  .of_hasSum deltaTwice_vadd_two mdifferentiable_deltaTwice hasSum_deltaTwice

theorem isPeriodTwoForm_discriminant : IsPeriodTwoForm ModularForm.discriminant :=
  .of_hasSum discriminant_vadd_two CuspForm.discriminant.holo' hasSum_discriminant_two

theorem isPeriodTwoForm_E₄ : IsPeriodTwoForm E₄ :=
  .of_hasSum E₄_vadd_two E₄.holo' hasSum_E₄_two

theorem qExpansion_deltaHalf :
    UpperHalfPlane.qExpansion 2 deltaHalf = PowerSeries.mk fun n ↦ tau n :=
  qExpansion_eq_mk_of_hasSum two_pos deltaHalf_vadd_two mdifferentiable_deltaHalf hasSum_deltaHalf

theorem qExpansion_deltaHalfShift :
    UpperHalfPlane.qExpansion 2 deltaHalfShift = PowerSeries.mk fun n ↦ (-1) ^ n * tau n :=
  qExpansion_eq_mk_of_hasSum two_pos deltaHalfShift_vadd_two mdifferentiable_deltaHalfShift
    hasSum_deltaHalfShift

theorem qExpansion_deltaTwice :
    UpperHalfPlane.qExpansion 2 deltaTwice =
      PowerSeries.mk fun n ↦ if 4 ∣ n then tau (n / 4) else 0 :=
  qExpansion_eq_mk_of_hasSum two_pos deltaTwice_vadd_two mdifferentiable_deltaTwice
    hasSum_deltaTwice

theorem qExpansion_discriminant_two :
    UpperHalfPlane.qExpansion 2 ModularForm.discriminant =
      PowerSeries.mk fun n ↦ if 2 ∣ n then tau (n / 2) else 0 :=
  qExpansion_eq_mk_of_hasSum two_pos discriminant_vadd_two CuspForm.discriminant.holo'
    hasSum_discriminant_two

theorem qExpansion_E₄_two :
    UpperHalfPlane.qExpansion 2 E₄ = PowerSeries.mk fun n ↦
      if 2 ∣ n then (UpperHalfPlane.qExpansion 1 E₄).coeff (n / 2) else 0 :=
  qExpansion_eq_mk_of_hasSum two_pos E₄_vadd_two E₄.holo' hasSum_E₄_two

/-! ### The `q`-expansion of the second symmetric function -/

theorem heckeTwoSum₂_eq_fun :
    (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) =
      deltaHalf * deltaHalfShift + (4096 : ℂ) • (deltaTwice * (deltaHalf + deltaHalfShift)) := by
  funext τ
  simp only [heckeTwoSum₂, deltaHalf, deltaHalfShift, deltaTwice, Pi.add_apply, Pi.mul_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem qExpansion_heckeTwoSum₂ :
    UpperHalfPlane.qExpansion 2 (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) =
      (PowerSeries.mk fun n ↦ tau n) * (PowerSeries.mk fun n ↦ (-1) ^ n * tau n) +
        (4096 : ℂ) • ((PowerSeries.mk fun n ↦ if 4 ∣ n then tau (n / 4) else 0) *
          ((PowerSeries.mk fun n ↦ tau n) + (PowerSeries.mk fun n ↦ (-1) ^ n * tau n))) := by
  have hA := isPeriodTwoForm_deltaHalf
  have hB := isPeriodTwoForm_deltaHalfShift
  have hC := isPeriodTwoForm_deltaTwice
  rw [heckeTwoSum₂_eq_fun, UpperHalfPlane.qExpansion_add (hA.mul hB).analyticAt
    ((hC.mul (hA.add hB)).const_smul 4096).analyticAt,
    UpperHalfPlane.qExpansion_mul hA.analyticAt hB.analyticAt,
    UpperHalfPlane.qExpansion_smul (hC.mul (hA.add hB)).analyticAt,
    UpperHalfPlane.qExpansion_mul hC.analyticAt (hA.add hB).analyticAt,
    UpperHalfPlane.qExpansion_add hA.analyticAt hB.analyticAt,
    qExpansion_deltaHalf, qExpansion_deltaHalfShift, qExpansion_deltaTwice]

private theorem tau_one : tau 1 = 1 := ModularForm.discriminant_qExpansion_coeff_one

private theorem tau_two : tau 2 = -24 := discriminant_qExpansion_coeff_two

private theorem tau_three : tau 3 = 252 := discriminant_qExpansion_coeff_three

theorem heckeTwoSum₂_coeff_two :
    (UpperHalfPlane.qExpansion 2 (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ)).coeff 2 = -1 := by
  rw [qExpansion_heckeTwoSum₂]
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
  norm_num [tau_zero, tau_one, tau_two]

theorem heckeTwoSum₂_coeff_four :
    (UpperHalfPlane.qExpansion 2 (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ)).coeff 4 = 72 := by
  rw [qExpansion_heckeTwoSum₂]
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Nat.succ_eq_add_one]
  norm_num [tau_zero, tau_one, tau_two, tau_three]

/-! ### The second symmetric function as a cusp form of weight `24` -/

theorem heckeTwo₂_isZeroAtImInfty :
    UpperHalfPlane.IsZeroAtImInfty (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) := by
  have hA := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion two_pos hasSum_deltaHalf
  have hB := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion two_pos hasSum_deltaHalfShift
  have hC := UpperHalfPlane.tendsto_atImInfty_of_hasSum_qExpansion two_pos hasSum_deltaTwice
  simp only [tau_zero, mul_zero, pow_zero, dvd_zero, ↓reduceIte, Nat.zero_div] at hA hB hC
  rw [heckeTwoSum₂_eq_fun]
  have := (hA.mul hB).add ((hC.mul (hA.add hB)).const_smul (4096 : ℂ))
  simp only [mul_zero, add_zero, smul_zero] at this
  exact this

/-- The second symmetric function of the `T₂`-translates of `Δ` as a level-one cusp
form of weight `24`. -/
def heckeTwoCuspForm₂ : CuspForm 𝒮ℒ 24 where
  toFun τ := heckeTwoSum₂ τ
  slash_action_eq' A hA := by
    obtain ⟨A, rfl⟩ := hA
    exact SlashInvariantForm.slash_action_generators_SL2Z heckeTwo₂_S_invariant
      heckeTwo₂_T_invariant A
  holo' := by
    rw [UpperHalfPlane.mdifferentiable_iff]
    refine differentiableOn_heckeTwoSum₂.congr fun z hz => ?_
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  zero_at_cusps' hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    intro γ _
    rw [SlashInvariantForm.slash_action_generators_SL2Z heckeTwo₂_S_invariant
      heckeTwo₂_T_invariant]
    exact heckeTwo₂_isZeroAtImInfty

private theorem E₄_coeff_zero : (UpperHalfPlane.qExpansion 1 E₄).coeff 0 = 1 :=
  E_qExpansion_coeff_zero _ ⟨2, rfl⟩

private theorem E₄_coeff_one : (UpperHalfPlane.qExpansion 1 E₄).coeff 1 = 240 := by
  rw [E₄_qExpansion_coeff 1 one_ne_zero]
  norm_num [show σ 3 1 = 1 by decide]

private theorem E₄_coeff_two : (UpperHalfPlane.qExpansion 1 E₄).coeff 2 = 2160 := by
  rw [E₄_qExpansion_coeff 2 two_ne_zero]
  norm_num [show σ 3 2 = 9 by decide]

/-- The second symmetric function of `Δ(z/2)`, `Δ((z+1)/2)` and `2¹²Δ(2z)` is
`-Δ E₄³ + 768 Δ²`. -/
theorem heckeTwoSum₂_eq (τ : UpperHalfPlane) :
    heckeTwoSum₂ τ = -(ModularForm.discriminant τ * E₄ τ ^ 3) +
      768 * ModularForm.discriminant τ ^ 2 := by
  set H : ModularForm 𝒮ℒ 12 :=
    ModularForm.mcast (by norm_num) (CuspForm.discriminantEquiv heckeTwoCuspForm₂) with hHdef
  have hH : ∀ τ : UpperHalfPlane, H τ = heckeTwoSum₂ τ / ModularForm.discriminant τ :=
    fun τ => rfl
  set E3 : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) with hE3def
  have hE3 : ∀ τ : UpperHalfPlane, E3 τ = E₄ τ ^ 3 := fun τ => by
    simp only [E3, ModularForm.coe_mcast, ModularForm.coe_pow, Pi.pow_apply]
  have hE3coeff : (UpperHalfPlane.qExpansion 1 E3).coeff 0 = 1 := by
    rw [hE3def, ModularForm.coe_mcast, ModularForm.qExpansion_pow one_pos
      one_mem_strictPeriods_SL]
    simp [pow_succ, PowerSeries.coeff_mul, E₄_coeff_zero,
      -PowerSeries.coeff_zero_eq_constantCoeff]
  set h₀ := (UpperHalfPlane.qExpansion 1 H).coeff 0 with hh₀
  obtain ⟨g, hg⟩ := ModularForm.sub_smul_isCuspForm H E3 hE3coeff
  obtain ⟨c, hc⟩ := CuspForm.exists_smul_discriminant_of_weight_eq_twelve g
  have hval : ∀ τ : UpperHalfPlane,
      heckeTwoSum₂ τ = h₀ * (ModularForm.discriminant τ * E₄ τ ^ 3) +
        c * (ModularForm.discriminant τ * ModularForm.discriminant τ) := by
    intro τ
    have h1 : g τ = H τ - h₀ * E3 τ := by
      have := congrArg (fun f : ModularForm 𝒮ℒ 12 ↦ f τ) hg
      simp only [CuspForm.toModularFormₗ_apply] at this
      exact this
    have h2 : g τ = c * ModularForm.discriminant τ := by
      rw [← hc]
      rfl
    rw [hH, hE3] at h1
    have hΔ := discriminant_ne_zero τ
    rw [h2] at h1
    field_simp at h1
    linear_combination -h1
  have hfun : (fun τ : UpperHalfPlane ↦ heckeTwoSum₂ τ) =
      h₀ • (ModularForm.discriminant * (⇑E₄ * ⇑E₄ * ⇑E₄)) +
        c • (ModularForm.discriminant * ModularForm.discriminant) := by
    funext τ
    rw [hval τ]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    ring
  have hD := isPeriodTwoForm_discriminant
  have hE := isPeriodTwoForm_E₄
  have hq := congrArg (UpperHalfPlane.qExpansion 2) hfun
  rw [UpperHalfPlane.qExpansion_add ((hD.mul ((hE.mul hE).mul hE)).const_smul h₀).analyticAt
      ((hD.mul hD).const_smul c).analyticAt,
    UpperHalfPlane.qExpansion_smul (hD.mul ((hE.mul hE).mul hE)).analyticAt,
    UpperHalfPlane.qExpansion_smul (hD.mul hD).analyticAt,
    UpperHalfPlane.qExpansion_mul hD.analyticAt ((hE.mul hE).mul hE).analyticAt,
    UpperHalfPlane.qExpansion_mul (hE.mul hE).analyticAt hE.analyticAt,
    UpperHalfPlane.qExpansion_mul hE.analyticAt hE.analyticAt,
    UpperHalfPlane.qExpansion_mul hD.analyticAt hD.analyticAt,
    qExpansion_discriminant_two, qExpansion_E₄_two] at hq
  have h2 := congrArg (PowerSeries.coeff 2) hq
  have h4 := congrArg (PowerSeries.coeff 4) hq
  rw [heckeTwoSum₂_coeff_two] at h2
  rw [heckeTwoSum₂_coeff_four] at h4
  simp only [map_add, PowerSeries.coeff_smul, PowerSeries.coeff_mul, PowerSeries.coeff_mk,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, smul_eq_mul] at h2 h4
  norm_num [Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, tau_zero, tau_one, tau_two, E₄_coeff_zero, E₄_coeff_one,
    E₄_coeff_two] at h2 h4
  have hh₀' : h₀ = -1 := by linear_combination -h2
  have hc' : c = 768 := by
    rw [hh₀'] at h4
    linear_combination -h4
  rw [hval τ, hh₀', hc']
  ring

end

end ModularForm
