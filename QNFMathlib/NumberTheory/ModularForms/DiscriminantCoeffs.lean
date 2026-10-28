/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.NumberTheory.ModularForms.LevelOne.GradedRing

/-!
# Low-Order `q`-Expansion Coefficients of `E₄`, `E₆` and `Δ`

This file writes the `q`-expansions of `E₄` and `E₆` as explicit power series and
computes the coefficients `τ(2) = -24` and `τ(3) = 252` of the modular
discriminant from `Δ = (E₄³ - E₆²) / 1728`.

## Main results

* `ModularForm.qExpansion_discriminant`: `qExpansion Δ = (qExpansion E₄³ - qExpansion E₆²) / 1728`.
* `ModularForm.qExpansion_E₄`, `ModularForm.qExpansion_E₆`: the explicit power series.
* `ModularForm.discriminant_qExpansion_coeff_two`: `τ(2) = -24`.
* `ModularForm.discriminant_qExpansion_coeff_three`: `τ(3) = 252`.
-/

open EisensteinSeries UpperHalfPlane
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

namespace ModularForm

theorem qExpansion_discriminant :
    qExpansion 1 ModularForm.discriminant =
      (1 / 1728 : ℂ) • ((qExpansion 1 E₄) ^ 3 - (qExpansion 1 E₆) ^ 2) := by
  have h := congrArg (qExpansionAlgHom 1 one_pos one_mem_strictPeriods_SL)
    discriminant_eq_E₄_cube_sub_E₆_sq_graded
  simpa [map_smul, map_sub, map_pow] using h

theorem E₄_qExpansion_coeff (m : ℕ) (hm : m ≠ 0) :
    (qExpansion 1 E₄).coeff m = 240 * (σ 3 m : ℂ) := by
  simp only [E_qExpansion_coeff _ ⟨2, rfl⟩, hm, ↓reduceIte,
    show bernoulli 4 = -1 / 30 by decide +kernel]
  norm_num

theorem E₆_qExpansion_coeff (m : ℕ) (hm : m ≠ 0) :
    (qExpansion 1 E₆).coeff m = -504 * (σ 5 m : ℂ) := by
  simp only [E_qExpansion_coeff _ ⟨3, rfl⟩, hm, ↓reduceIte,
    show bernoulli 6 = 1 / 42 by decide +kernel]
  norm_num

/-- The `q`-expansion of `E₄` as an explicit power series. -/
theorem qExpansion_E₄ :
    qExpansion 1 E₄ = PowerSeries.mk fun m ↦ if m = 0 then (1 : ℂ) else 240 * (σ 3 m : ℂ) := by
  ext m
  rw [PowerSeries.coeff_mk]
  split_ifs with hm
  · subst hm
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  · exact E₄_qExpansion_coeff m hm

/-- The `q`-expansion of `E₆` as an explicit power series. -/
theorem qExpansion_E₆ :
    qExpansion 1 E₆ = PowerSeries.mk fun m ↦ if m = 0 then (1 : ℂ) else -504 * (σ 5 m : ℂ) := by
  ext m
  rw [PowerSeries.coeff_mk]
  split_ifs with hm
  · subst hm
    exact E_qExpansion_coeff_zero _ ⟨3, rfl⟩
  · exact E₆_qExpansion_coeff m hm

theorem discriminant_qExpansion_coeff_two :
    (qExpansion 1 ModularForm.discriminant).coeff 2 = -24 := by
  rw [qExpansion_discriminant, qExpansion_E₄, qExpansion_E₆]
  have s1 : σ 3 1 = 1 := by decide
  have s1' : σ 5 1 = 1 := by decide
  have s2 : σ 3 2 = 9 := by decide
  have s2' : σ 5 2 = 33 := by decide
  simp only [PowerSeries.coeff_smul, map_sub, pow_succ, pow_zero, one_mul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, PowerSeries.coeff_mk]
  norm_num [s1, s1', s2, s2']

theorem discriminant_qExpansion_coeff_three :
    (qExpansion 1 ModularForm.discriminant).coeff 3 = 252 := by
  rw [qExpansion_discriminant, qExpansion_E₄, qExpansion_E₆]
  have s1 : σ 3 1 = 1 := by decide
  have s1' : σ 5 1 = 1 := by decide
  have s2 : σ 3 2 = 9 := by decide
  have s2' : σ 5 2 = 33 := by decide
  have s3 : σ 3 3 = 28 := by decide
  have s3' : σ 5 3 = 244 := by decide
  simp only [PowerSeries.coeff_smul, map_sub, pow_succ, pow_zero, one_mul, PowerSeries.coeff_mul,
    Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.sum_map, Function.Embedding.coe_prodMap, Prod.map,
    Function.Embedding.coeFn_mk, Nat.succ_eq_add_one, PowerSeries.coeff_mk]
  norm_num [s1, s1', s2, s2', s3, s3']

end ModularForm
