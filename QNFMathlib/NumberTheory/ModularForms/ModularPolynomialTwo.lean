/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic.ComputeDegree
import QNFMathlib.NumberTheory.ModularForms.WeberPolynomial

/-!
# The Classical Modular Polynomial of Level Two

Material destined for mathlib.

We define `Φ₂ ∈ ℤ[X,Y]` and prove `Φ₂(j(τ), j(2τ)) = 0`. The proof eliminates
`t = 𝔣₂(τ)²⁴` from `j(τ) = (t + 16)³/t` and `j(2τ) = (t + 256)³/t²`.
The elimination is a polynomial identity verified by the Lean kernel.

## References

* Andrew V. Sutherland, [Classical modular polynomials]
  (https://math.mit.edu/~drew/ClassicalModPolys.html).
-/

open Polynomial
open scoped Polynomial.Bivariate

namespace ModularForm

noncomputable section

/-- The classical symmetric modular polynomial `Φ₂`, with integer coefficients. -/
def modularPolynomialTwo : ℤ[X][Y] :=
  C X ^ 3 + Y ^ 3 - C X ^ 2 * Y ^ 2 + 1488 * C X * Y * (C X + Y) -
    162000 * (C X ^ 2 + Y ^ 2) + 40773375 * C X * Y +
    8748000000 * (C X + Y) - 157464000000000

theorem modularPolynomialTwo_eval {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y modularPolynomialTwo =
      x ^ 3 + y ^ 3 - x ^ 2 * y ^ 2 + 1488 * x * y * (x + y) -
        162000 * (x ^ 2 + y ^ 2) + 40773375 * x * y +
        8748000000 * (x + y) - 157464000000000 := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    aevalAeval_X, aevalAeval_Y]

/-- Symmetry of `Φ₂` under interchange of its variables. -/
theorem modularPolynomialTwo_swap : Bivariate.swap modularPolynomialTwo = modularPolynomialTwo := by
  simp only [modularPolynomialTwo, map_add, map_sub, map_mul, map_pow, map_ofNat,
    Bivariate.swap_X, Bivariate.swap_Y]
  ring

theorem modularPolynomialTwo_eval_comm {R : Type*} [CommRing R] (x y : R) :
    aevalAeval x y modularPolynomialTwo = aevalAeval y x modularPolynomialTwo := by
  rw [modularPolynomialTwo_eval, modularPolynomialTwo_eval]
  ring

theorem modularPolynomialTwo_monic : modularPolynomialTwo.Monic := by
  unfold modularPolynomialTwo
  monicity!

theorem modularPolynomialTwo_natDegree : modularPolynomialTwo.natDegree = 3 := by
  unfold modularPolynomialTwo
  compute_degree!

/-- The rational parametrization of `Φ₂ = 0`, valid over any field. -/
theorem modularPolynomialTwo_param {K : Type*} [Field K] {t : K} (ht : t ≠ 0) :
    aevalAeval ((t + 16) ^ 3 / t) ((t + 256) ^ 3 / t ^ 2) modularPolynomialTwo = 0 := by
  rw [modularPolynomialTwo_eval]
  field_simp
  ring

/-- The modular equation relating `j(τ)` and `j(2τ)`. -/
theorem modularPolynomialTwo_jInvariant (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex (2 * (τ : ℂ))))
      modularPolynomialTwo = 0 := by
  rw [jInvariant_eq_weberF₂ τ, jInvariant_two_mul_eq_weberF₂]
  exact modularPolynomialTwo_param (pow_ne_zero _ (weberF₂_ne_zero τ.im_pos))

/-- The `j`-value at `τ/2` also satisfies the level-two modular equation. -/
theorem modularPolynomialTwo_jInvariant_half (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2)))
      modularPolynomialTwo = 0 := by
  have hpos : 0 < ((τ : ℂ) / 2).im := by simpa using half_pos τ.im_pos
  have hdouble : UpperHalfPlane.ofComplex
      (2 * (UpperHalfPlane.ofComplex ((τ : ℂ) / 2) : ℂ)) = τ := by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hpos,
      show 2 * ((τ : ℂ) / 2) = (τ : ℂ) by ring, UpperHalfPlane.ofComplex_apply]
  have h := modularPolynomialTwo_jInvariant (UpperHalfPlane.ofComplex ((τ : ℂ) / 2))
  rw [hdouble] at h
  rw [modularPolynomialTwo_eval_comm]
  exact h

/-- The `j`-value at `(τ+1)/2` satisfies the same level-two modular equation. -/
theorem modularPolynomialTwo_jInvariant_half_add_one (τ : UpperHalfPlane) :
    aevalAeval (jInvariant τ) (jInvariant (UpperHalfPlane.ofComplex (((τ : ℂ) + 1) / 2)))
      modularPolynomialTwo = 0 := by
  have h := modularPolynomialTwo_jInvariant_half ((1 : ℝ) +ᵥ τ)
  simpa only [jInvariant_add_one, UpperHalfPlane.coe_vadd, Complex.ofReal_one,
    add_comm (1 : ℂ)] using h

end

end ModularForm
