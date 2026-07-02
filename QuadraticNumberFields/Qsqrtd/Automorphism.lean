/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.QuadraticField.Conj
import QNFMathlib.Algebra.Squarefree.Basic

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
  `ℚ`-algebra automorphism of `Q(√d)` is either `refl` or `star`.

## Implementation notes

Once we know `σ ⟨0, 1⟩ = ⟨0, 1⟩` (resp. `star ⟨0, 1⟩`), the equality
`σ x = refl x` (resp. `σ x = star x`) for all `x` follows from the
decomposition `x = algebraMap x.re + algebraMap x.im * ⟨0, 1⟩` together
with `σ.commutes`.
-/

-- Use the canonical `QuadraticAlgebra` algebra structure for standard `Qsqrtd` models.
attribute [-instance] DivisionRing.toRatAlgebra

namespace Qsqrtd

section AutomorphismDichotomy

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- For squarefree `d ≠ 1`, the `ℚ`-algebra automorphism group of
`Q(√d)` has exactly two elements: `AlgEquiv.refl` and
`Qsqrtd.starAlgEquiv`. -/
theorem algEquiv_self_eq_refl_or_star
    (σ : Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (d : ℚ)) :
    σ = AlgEquiv.refl ∨ σ = Qsqrtd.starAlgEquiv (d : ℚ) := by
  -- `σ ⟨0, 1⟩ = ⟨a, b⟩`. Feed the ring-level core `ringEquiv_param_rel`, which is
  -- instance-agnostic — so the `Field`-vs-canonical `Algebra ℚ` diamond on
  -- `Qsqrtd (d : ℚ)` is irrelevant. It gives `a = 0` and `(d : ℚ) = d * b²`,
  -- and `d ≠ 0` then forces `b² = 1`.
  have hφ_d : σ.toRingEquiv (⟨(d : ℚ), 0⟩ : Qsqrtd (d : ℚ)) = ⟨(d : ℚ), 0⟩ := by
    have hleft : (⟨(d : ℚ), 0⟩ : Qsqrtd (d : ℚ)) =
        algebraMap ℚ (Qsqrtd (d : ℚ)) (d : ℚ) := by ext <;> simp
    simp [hleft]
  obtain ⟨ha, -, hr⟩ :=
    ringEquiv_param_rel (not_isSquare_ratCast_of_squarefree_ne_one Fact.out Fact.out)
      σ.toRingEquiv hφ_d
  simp only [AlgEquiv.coe_ringEquiv] at ha hr
  set a := (σ (⟨0, 1⟩ : Qsqrtd (d : ℚ))).re
  set b := (σ (⟨0, 1⟩ : Qsqrtd (d : ℚ))).im
  have hφ_eta : σ (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = ⟨a, b⟩ := by ext <;> rfl
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Squarefree.ne_zero (Fact.out : Squarefree d))
  have hbsq : b ^ 2 = 1 := mul_left_cancel₀ hdQ (by simpa using hr.symm)
  -- The rational algebra map sends `q ↦ ⟨q, 0⟩`.
  have hAM :
      ∀ q : ℚ, algebraMap ℚ (Qsqrtd (d : ℚ)) q = (⟨q, 0⟩ : Qsqrtd (d : ℚ)) := by
    intro q
    rw [← QuadraticAlgebra.algebraMap_eq (R := ℚ) (a := (d : ℚ)) (b := 0) q]
  -- Every element decomposes as `x = algebraMap x.re + algebraMap x.im * ⟨0, 1⟩`.
  have hdecomp : ∀ x : Qsqrtd (d : ℚ),
      x = algebraMap ℚ (Qsqrtd (d : ℚ)) x.re +
        algebraMap ℚ (Qsqrtd (d : ℚ)) x.im * ⟨0, 1⟩ := by
    intro x
    rw [hAM x.re, hAM x.im]
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  -- Branch on `b = 1` or `b = -1`.
  rcases sq_eq_one_iff.mp hbsq with hb1 | hbneg1
  · -- Case `b = 1` and `a = 0`: `σ ⟨0, 1⟩ = ⟨0, 1⟩`, so `σ = AlgEquiv.refl`.
    refine Or.inl (AlgEquiv.ext fun x => ?_)
    have hσε : σ (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = ⟨0, 1⟩ := by rw [hφ_eta, ha, hb1]
    conv_lhs => rw [hdecomp x]
    rw [map_add, map_mul, σ.commutes, σ.commutes, hσε, ← hdecomp x]
    rfl
  · -- Case `b = -1` and `a = 0`: `σ ⟨0, 1⟩ = ⟨0, -1⟩ = star ⟨0, 1⟩`,
    -- so `σ = starAlgEquiv`.
    refine Or.inr (AlgEquiv.ext fun x => ?_)
    have hσε : σ (⟨0, 1⟩ : Qsqrtd (d : ℚ)) = ⟨0, -1⟩ := by rw [hφ_eta, ha, hbneg1]
    rw [Qsqrtd.starAlgEquiv_apply]
    conv_lhs => rw [hdecomp x]
    rw [map_add, map_mul, σ.commutes, σ.commutes, hσε, hAM x.re, hAM x.im]
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]

end AutomorphismDichotomy

end Qsqrtd
