/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.Mathlib.Algebra.Squarefree.Basic

/-!
# Automorphisms of the Standard Model `Q(√d)`

This file proves that for a squarefree integer parameter `d ≠ 1`, the
`ℚ`-algebra automorphism group of the standard model `Q(√d)` has exactly
two elements: the identity `AlgEquiv.refl` and the conjugation
`Qsqrtd.starAlgEquiv`.

The proof mirrors `Qsqrtd.param_unique` in `QuadraticField.Parameters`:
any `ℚ`-algebra equivalence is determined by the image of the
distinguished element `√d = ⟨0, 1⟩`.  Writing `σ (⟨0, 1⟩) = ⟨a, b⟩`,
the relation `(⟨0, 1⟩)² = ⟨d, 0⟩` forces `a² + d·b² = d` and
`2ab = 0`.  Since `d` is squarefree (and `≠ 1`), `d` is not a perfect
square in `ℚ`, so `b ≠ 0` and hence `a = 0`; then `b² = 1` gives
`b = ±1`, which corresponds to the two cases `σ = AlgEquiv.refl`
(`b = 1`) and `σ = Qsqrtd.starAlgEquiv` (`b = -1`).

## Main Theorems

* `Qsqrtd.algEquiv_self_eq_refl_or_star`: for squarefree `d ≠ 1`, every
  `ℚ`-algebra endomorphism of `Q(√d)` is either `refl` or `star`.

## Note

The final two `AlgEquiv` equalities (showing `σ = refl` and
`σ = starAlgEquiv`) are currently `sorry`d.  The argument strategy is
clear: once we know `σ ⟨0, 1⟩ = ⟨0, 1⟩` (resp. `star ⟨0, 1⟩`), the
equality `σ x = refl x` (resp. `σ x = star x`) for all `x` follows from
the decomposition `x = algebraMap x.re + algebraMap x.im * ⟨0, 1⟩` and
`σ.commutes`.  The remaining work is a straightforward algebraic
computation using `QuadraticAlgebra.algebraMap_eq` and the
multiplication formula, with the conclusion assembled via
`AlgEquiv.ext`.  This will be completed as part of follow-up work
combining `algHom_ext` with `AlgEquiv.toAlgHom_eq_coe`.
-/

namespace Qsqrtd

section AutomorphismDichotomy

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- For squarefree `d ≠ 1`, the `ℚ`-algebra automorphism group of
`Q(√d)` has exactly two elements: `AlgEquiv.refl` and
`Qsqrtd.starAlgEquiv`. -/
theorem algEquiv_self_eq_refl_or_star
    (σ : Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) :
    σ = AlgEquiv.refl ∨ σ = Qsqrtd.starAlgEquiv (d : ℚ) := by
  -- `σ` is determined by the image of `√d = ⟨0, 1⟩`; let `σ ⟨0, 1⟩ = ⟨a, b⟩`.
  set a := (σ (⟨0, 1⟩ : Qsqrtd (d : ℚ))).re
  set b := (σ (⟨0, 1⟩ : Qsqrtd (d : ℚ))).im
  have hε_sq :
      (⟨0, 1⟩ : Qsqrtd (d : ℚ)) * ⟨0, 1⟩ = ⟨(d : ℚ), 0⟩ := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  -- Reduce `σ ⟨(d : ℚ), 0⟩ = ⟨(d : ℚ), 0⟩` to `σ.commutes`.
  have hφ_d : σ (⟨(d : ℚ), 0⟩ : Qsqrtd (d : ℚ)) = ⟨(d : ℚ), 0⟩ := by
    have hleft : (⟨(d : ℚ), 0⟩ : Qsqrtd (d : ℚ)) =
        algebraMap ℚ (Qsqrtd (d : ℚ)) (d : ℚ) := by
      ext <;> simp
    rw [hleft]
    exact σ.commutes (d : ℚ)
  have hφ_sq : σ (⟨0, 1⟩) * σ (⟨0, 1⟩) = ⟨(d : ℚ), 0⟩ := by
    rw [← map_mul, hε_sq, hφ_d]
  have hφ_eta : σ (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = ⟨a, b⟩ := by ext <;> rfl
  -- The real-part equation: `a² + d·b² = d`.
  have hre : a ^ 2 + (d : ℚ) * b ^ 2 = d := by
    have := congr_arg QuadraticAlgebra.re hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
    simp at this
    nlinarith
  -- The imaginary-part equation: `2ab = 0`.
  have him : 2 * a * b = 0 := by
    have := congr_arg QuadraticAlgebra.im hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this
    simp at this
    linarith
  -- `b ≠ 0`: if `b = 0`, then `a² = d`, contradicting squarefree `d ≠ 1`.
  have hb : b ≠ 0 := by
    intro hb0
    have hsq : a * a = (d : ℚ) := by
      have h := hre
      rw [hb0] at h
      linarith
    have : IsSquare ((d : ℤ) : ℚ) := ⟨a, hsq.symm⟩
    exact not_isSquare_int_of_squarefree_ne_one (Fact.out : Squarefree d)
      (Fact.out : d ≠ 1) (Rat.isSquare_intCast_iff.mp this)
  -- Since `b ≠ 0`, `2ab = 0` forces `a = 0`.
  have ha : a = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact absurd h hb
  -- With `a = 0`, `a² + d·b² = d` becomes `d·b² = d`, so `b² = 1`.
  have hbsq : b ^ 2 = 1 := by
    have h : (d : ℚ) * b ^ 2 = d := by nlinarith
    have hdQ : (d : ℚ) ≠ 0 := by
      exact_mod_cast (Squarefree.ne_zero (Fact.out : Squarefree d))
    field_simp [hdQ] at h
    linarith
  -- Branch on `b = 1` or `b = -1`.
  rcases sq_eq_one_iff.mp hbsq with hb1 | hbneg1
  · -- Case `b = 1` and `a = 0`: `σ ⟨0, 1⟩ = ⟨0, 1⟩ = AlgEquiv.refl ⟨0, 1⟩`.
    -- Need to show `σ = AlgEquiv.refl`.  This follows from the decomposition
    -- `x = algebraMap x.re + algebraMap x.im * ⟨0, 1⟩` plus `σ.commutes`
    -- and the fact that `σ` agrees with `AlgEquiv.refl` on `⟨0, 1⟩`.
    sorry
  · -- Case `b = -1` and `a = 0`: `σ ⟨0, 1⟩ = ⟨0, -1⟩ = starAlgEquiv ⟨0, 1⟩`.
    sorry

end AutomorphismDichotomy

end Qsqrtd
