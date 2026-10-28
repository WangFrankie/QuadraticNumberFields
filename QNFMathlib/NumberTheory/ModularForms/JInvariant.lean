/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
module

public import Mathlib.NumberTheory.ModularForms.Discriminant
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic

/-!
# The Modular `j`-Invariant and `γ₂`

Material destined for mathlib.

The normalization is `j = E₄³ / Δ`, with leading term `q⁻¹`, and
`γ₂ = E₄ / η⁸`. In particular `γ₂³ = j`. These definitions use the analytic
Eisenstein series and Dedekind eta function, independently of complex
multiplication or class-number hypotheses.
-/

@[expose] public section

open EisensteinSeries
open scoped ModularForm MatrixGroups Manifold

namespace ModularForm

noncomputable section

/-- The modular `j`-invariant, normalized as `E₄³ / Δ`. -/
def jInvariant (τ : UpperHalfPlane) : ℂ := E₄ τ ^ 3 / discriminant τ

/-- Weber's cube root `γ₂ = E₄ / η⁸` of the modular `j`-invariant. -/
def gamma₂ (τ : UpperHalfPlane) : ℂ := E₄ τ / η τ ^ 8

theorem gamma₂_cube (τ : UpperHalfPlane) : gamma₂ τ ^ 3 = jInvariant τ := by
  simp only [gamma₂, jInvariant, discriminant, div_pow, ← pow_mul]

/-- The `j`-invariant is invariant under the full modular group. -/
theorem jInvariant_smul (g : SL(2, ℤ)) (τ : UpperHalfPlane) :
    jInvariant (g • τ) = jInvariant τ := by
  have hg : Matrix.SpecialLinearGroup.mapGL ℝ g ∈ 𝒮ℒ := ⟨g, rfl⟩
  have hE := SlashInvariantForm.slash_action_eqn'' E₄ hg τ
  have hD := SlashInvariantForm.slash_action_eqn'' CuspForm.discriminant hg τ
  change E₄ (g • τ) = _ at hE
  change discriminant (g • τ) = _ at hD
  rw [jInvariant, jInvariant, hE, hD]
  norm_num only [zpow_ofNat, mul_pow, ← pow_mul]
  exact mul_div_mul_left _ _
    (pow_ne_zero _ (UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ g) τ))

theorem jInvariant_add_one (τ : UpperHalfPlane) :
    jInvariant ((1 : ℝ) +ᵥ τ) = jInvariant τ := by
  simpa only [UpperHalfPlane.modular_T_smul] using jInvariant_smul ModularGroup.T τ

/-- The `j`-invariant is holomorphic on the upper half-plane. -/
theorem mdifferentiable_jInvariant :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jInvariant :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero

end

end ModularForm
