/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import QuadraticNumberFields.Basic
import QuadraticNumberFields.Mathlib.Data.Int.Squarefree

/-!
# Quadratic Field Parameters

This file collects the main results about integer parameters for quadratic
fields `ℚ(√d)`: rescaling by rational squares, normalization to integer or
squarefree integer parameters, and uniqueness of the squarefree parameter.

According to the uniqueness result,
`variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]`
will be sufficient to pin down a unique quadratic field `ℚ(√d)` up to isomorphism.

## Main Results

* `Qsqrtd.rescale`: `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` for `a ≠ 0`.
* `Qsqrtd_iso_int_param`: every quadratic field is isomorphic to one with an
  integer parameter.
* `Qsqrtd_iso_squarefree_int_param`: every quadratic field is isomorphic to one
  with a squarefree integer parameter.
* `Qsqrtd.param_unique`: The main uniqueness theorem.
* `squarefree_eq_of_rat_sq_mul`: Helper lemma relating squarefree integers
  connected by a rational square factor.

## Helper Lemmas

The general squarefree-integer helpers used here
(`not_isSquare_neg_one_rat`, `nat_eq_one_of_squarefree_intcast_of_isSquare`,
`int_dvd_of_ratio_square`) live under `QuadraticNumberFields.Mathlib.Data.Int.Squarefree`
because they are destined for mathlib.
-/

/-! ## Rescaling Isomorphisms -/

/-- `ℚ(√d) ≃ₐ[ℚ] ℚ(√(a²d))` via `⟨r, s⟩ ↦ ⟨r, s·a⁻¹⟩`.

This shows that scaling the parameter by a rational square yields an
isomorphic quadratic field. -/
def Qsqrtd.rescale (d : ℚ) (a : ℚ) (ha : a ≠ 0) :
    Qsqrtd d ≃ₐ[ℚ] Qsqrtd (a ^ 2 * d) := by
  have h1d : (1 : Qsqrtd d) = ⟨1, 0⟩ := by ext <;> rfl
  have h1a : (1 : Qsqrtd (a ^ 2 * d)) = ⟨1, 0⟩ := by
    ext <;> rfl
  -- This is the change of generator
  -- `√d ↦ a⁻¹ * √(a² d)`, with the real part unchanged.
  exact AlgEquiv.ofLinearEquiv
    { toFun := fun x => ⟨x.re, x.im * a⁻¹⟩
      invFun := fun y => ⟨y.re, y.im * a⟩
      map_add' := by intro x y; ext <;> simp [add_mul]
      map_smul' := by intro c x; ext <;> simp [mul_assoc]
      left_inv := by
        intro x; ext <;> simp [mul_assoc, inv_mul_cancel₀ ha]
      right_inv := by
        intro y; ext <;> simp [mul_assoc, mul_inv_cancel₀ ha] }
    (by simp [h1d, h1a])
    (by intro x y; ext <;> simp <;> field_simp)

/-- Every quadratic field `Q(√d)` is isomorphic to one with an integer parameter:
`∃ z ∈ ℤ, Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_int_param (d : ℚ) :
    ∃ z : ℤ, Nonempty (Qsqrtd d ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨m, n, hn0, hd⟩ : ∃ m n : ℤ, n ≠ 0 ∧ d = m / n := by
    have hd := ne_of_gt (Rat.den_pos d)
    exact ⟨d.num, d.den, Int.ofNat_ne_zero.mpr hd, (Rat.num_div_den d).symm⟩
  use m * n
  have ha : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
  -- Clearing the denominator replaces `d = m / n` by `n² d = mn`,
  -- so after rescaling the parameter becomes an integer.
  have hrescale : Qsqrtd d ≃ₐ[ℚ] Qsqrtd (n ^ 2 * d) := Qsqrtd.rescale d n ha
  have heq : (n : ℚ) ^ 2 * d = m * n := by
    rw [hd]
    field_simp [mul_assoc]
  have hcast : (m * n : ℚ) = (m * n : ℤ) := (Int.cast_mul m n).symm
  exact ⟨hrescale.trans (AlgEquiv.cast (by rw [heq, hcast]))⟩

/-- Every quadratic field `Q(√d)` is isomorphic to one with a squarefree integer
parameter: `∃ z ∈ ℤ, Squarefree z ∧ Q(√d) ≃ₐ[ℚ] Q(√z)`. -/
theorem Qsqrtd_iso_squarefree_int_param {d : ℤ} (hd : d ≠ 0) :
    ∃ z : ℤ, Squarefree z ∧ Nonempty (Qsqrtd (d : ℚ) ≃ₐ[ℚ] Qsqrtd (z : ℚ)) := by
  obtain ⟨a, b, heq, ha⟩ := Nat.sq_mul_squarefree d.natAbs
  have hb : b ≠ 0 := by
    intro h
    subst h
    simp at heq
    exact hd (Int.natAbs_eq_zero.mp heq.symm)
  refine ⟨d.sign * ↑a, ?_, ?_⟩
  · rw [← Int.squarefree_natAbs]
    rwa [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hd, Int.natAbs_natCast, one_mul]
  · have hbQ : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hb
    -- Write `|d| = b² a` with `a` squarefree, then absorb the square factor `b²`
    -- using the rescaling isomorphism.
    have hrescale := Qsqrtd.rescale (↑d) (↑b)⁻¹ (inv_ne_zero hbQ)
    have hd_int : d = d.sign * (↑b ^ 2 * ↑a) := by
      conv_lhs => rw [(Int.sign_mul_natAbs d).symm]
      congr 1
      exact_mod_cast heq.symm
    have hkey : ((↑b : ℚ)⁻¹) ^ 2 * (↑d : ℚ) = ↑(d.sign * (↑a : ℤ)) := by
      have hd_rat : (d : ℚ) = (d.sign : ℚ) * ((b : ℚ) ^ 2 * (a : ℚ)) := by
        exact_mod_cast hd_int
      rw [hd_rat]
      field_simp
      push_cast
      rfl
    exact ⟨hrescale.trans
      (AlgEquiv.cast (A := fun d => QuadraticAlgebra ℚ d 0) hkey)⟩

/-! ## Main Theorem -/

section ParameterUniqueness

variable (d₁ d₂ : ℤ)

/-- If two squarefree integers are related by `d₁ = d₂ · r²` for rational `r`,
then `d₁ = d₂`.

This is a **key rigidity result for squarefree integers**: two squarefree integers
that differ by a rational square factor must be equal. The proof reduces to mutual
divisibility via `int_dvd_of_ratio_square`, yielding `d₁ ∣ d₂` and `d₂ ∣ d₁`.
The sign ambiguity is resolved by the fact that `-1` is not a rational square. -/
lemma squarefree_eq_of_rat_sq_mul {d₁ d₂ : ℤ}
    (hd₁ : Squarefree d₁) (hd₂ : Squarefree d₂)
    {r : ℚ} (hr : (d₁ : ℚ) = d₂ * r ^ 2) : d₁ = d₂ := by
  have hd₁0 : d₁ ≠ 0 := Squarefree.ne_zero hd₁
  have hd₂0 : d₂ ≠ 0 := Squarefree.ne_zero hd₂
  have hd₁Q : (d₁ : ℚ) ≠ 0 := by exact_mod_cast hd₁0
  have hd₂Q : (d₂ : ℚ) ≠ 0 := by exact_mod_cast hd₂0
  have hratio : IsSquare ((d₁ : ℚ) / (d₂ : ℚ)) := by
    refine ⟨r, ?_⟩
    calc
      (d₁ : ℚ) / (d₂ : ℚ) = ((d₂ : ℚ) * r ^ 2) / (d₂ : ℚ) := by simp [hr]
      _ = r ^ 2 := by field_simp [hd₂Q]
      _ = r * r := by ring
  have hratio' : IsSquare ((d₂ : ℚ) / (d₁ : ℚ)) := by
    rcases hratio with ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    calc
      (d₂ : ℚ) / (d₁ : ℚ) = ((d₁ : ℚ) / (d₂ : ℚ))⁻¹ := by field_simp [hd₁Q, hd₂Q]
      _ = (s * s)⁻¹ := by simp [hs]
      _ = s⁻¹ * s⁻¹ := by
        have hs0 : s ≠ 0 := by
          intro hs0
          have : ((d₁ : ℚ) / (d₂ : ℚ)) = 0 := by simpa [hs0] using hs
          have hd10 : (d₁ : ℚ) = 0 := by
            field_simp [hd₂Q] at this
            simpa [mul_zero] using this
          exact hd₁Q hd10
        field_simp [hs0]
  have hd21 : d₂ ∣ d₁ := int_dvd_of_ratio_square d₁ d₂ hd₂0 hd₂ hratio
  have hd12 : d₁ ∣ d₂ := int_dvd_of_ratio_square d₂ d₁ hd₁0 hd₁ hratio'
  -- Mutual divisibility makes `d₁` and `d₂` associated, so over `ℤ`
  -- they differ by at most a sign.
  have hassoc : Associated d₁ d₂ := associated_of_dvd_dvd hd12 hd21
  rcases (Int.associated_iff.mp hassoc) with hEq | hNeg
  · exact hEq
  · have : ((d₁ : ℚ) / d₂) = -1 := by
      rw [hNeg]
      push_cast
      field_simp [hd₂Q]
    -- The negative sign is impossible because it would force `-1`
    -- to be a rational square.
    exfalso
    exact not_isSquare_neg_one_rat (by rwa [this] at hratio)

/-- The squarefree integer parameter of a quadratic field is unique:
    `ℚ(√d₁) ≃ₐ[ℚ] ℚ(√d₂)` with both squarefree and `≠ 1` implies `d₁ = d₂`. -/
theorem Qsqrtd.param_unique (φ : Qsqrtd (d₁ : ℚ) ≃ₐ[ℚ] Qsqrtd (d₂ : ℚ))
    (hsf₁ : Squarefree d₁) (h1₁ : d₁ ≠ 1) (hsf₂ : Squarefree d₂) : d₁ = d₂ := by
  -- The idea is to write `φ ⟨0, 1⟩ = ⟨a, b⟩`
  -- ⟨0, 1⟩² = ⟨d₁, 0⟩ implies `a² + d₂ b² = d₁` and `2ab = 0`.
  set a := (φ ⟨0, 1⟩).re
  set b := (φ ⟨0, 1⟩).im
  have hε_sq : (⟨0, 1⟩ : Qsqrtd (d₁ : ℚ)) * ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    ext <;> simp [QuadraticAlgebra.mk_mul_mk]
  have hφ_sq : φ ⟨0, 1⟩ * φ ⟨0, 1⟩ = ⟨(d₁ : ℚ), 0⟩ := by
    rw [← map_mul, hε_sq]
    show φ ⟨(d₁ : ℚ), 0⟩ = ⟨(d₁ : ℚ), 0⟩
    have hleft : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₁ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₁ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    have hright : (⟨(d₁ : ℚ), 0⟩ : Qsqrtd (d₂ : ℚ)) =
        algebraMap ℚ (Qsqrtd (d₂ : ℚ)) (d₁ : ℚ) := by
      ext <;> simp
    rw [hleft, hright]
    exact φ.commutes (d₁ : ℚ)
  have hφ_eta : φ ⟨0, 1⟩ = ⟨a, b⟩ := by ext <;> rfl
  --`a² + d₂ b² = d₁`
  have hre : a ^ 2 + (d₂ : ℚ) * b ^ 2 = d₁ := by
    have := congr_arg QuadraticAlgebra.re hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; nlinarith
  -- `2ab = 0`
  have him : 2 * a * b = 0 := by
    have := congr_arg QuadraticAlgebra.im hφ_sq
    rw [hφ_eta, QuadraticAlgebra.mk_mul_mk] at this; simp at this; linarith
  have hb : b ≠ 0 := by
    -- If `b = 0`, then the equation for the real part says `d₁ = a²`,
    -- contradicting that the squarefree integer parameter `d₁` is non-square.
    intro hb0; simp [hb0] at hre
    have : IsSquare ((d₁ : ℤ) : ℚ) := ⟨a, by nlinarith⟩
    exact not_isSquare_int_of_squarefree_ne_one hsf₁ h1₁
      (Rat.isSquare_intCast_iff.mp this)
  have ha : a = 0 := by
    -- Since `b ≠ 0`, the vanishing of the imaginary part forces `a = 0`.
    rcases mul_eq_zero.mp him with h | h
    · exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    · exact absurd h hb
  have hr : (d₁ : ℚ) = d₂ * b ^ 2 := by nlinarith [hre, ha]
  -- So the two parameters differ by a rational square factor, and squarefreeness
  -- removes that ambiguity.
  exact squarefree_eq_of_rat_sq_mul hsf₁ hsf₂ hr

end ParameterUniqueness
