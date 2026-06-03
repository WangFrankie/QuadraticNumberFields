/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Squarefree.Basic
import QuadraticNumberFields.Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree Integer Helpers

Material destined for mathlib.
-/

/-- `-1` is not a square in `ℚ`. -/
-- Repository use: `QuadraticField/Parameters.lean` uses this to rule out the
-- negative square-ratio case in squarefree parameter uniqueness.
lemma not_isSquare_neg_one_rat : ¬ IsSquare (- (1 : ℚ)) := by
  rintro ⟨r, hr⟩
  have hnonneg : 0 ≤ r ^ 2 := sq_nonneg r
  nlinarith [hr, hnonneg]

/-- A squarefree integer that is a perfect square (as an integer) must equal `1`. -/
-- Repository use: internal support for `int_dvd_of_ratio_square`.
lemma nat_eq_one_of_squarefree_intcast_of_isSquare (m : ℕ)
    (hsm : Squarefree (m : ℤ)) (hsq : IsSquare (m : ℤ)) : m = 1 := by
  have hmz : (m : ℤ) = 1 ∨ (m : ℤ) = -1 :=
    eq_one_of_squarefree_isSquare hsm hsq
  cases hmz with
  | inl h => exact_mod_cast h
  | inr h => simp only at h; omega

/-- If `d₁/d₂` is a rational square and `d₂` is squarefree, then `d₂ ∣ d₁`.

This is a **general number-theoretic fact** about squarefree integers: if a
squarefree integer divides the denominator of a reduced fraction that is a perfect
square, then the denominator must be `1` (since its square part is constrained
by squarefreeness). -/
-- Repository use: `QuadraticField/Parameters.lean` uses this for uniqueness of
-- squarefree parameters; `Qsqrtd/TraceNorm.lean` uses it in integrality
-- denominator control.
lemma int_dvd_of_ratio_square (d₁ d₂ : ℤ) (hd₂ : d₂ ≠ 0)
    (hsq_d₂ : Squarefree d₂) (hr : IsSquare ((d₁ : ℚ) / (d₂ : ℚ))) : d₂ ∣ d₁ := by
  -- A rational square has square numerator and denominator.
  -- Since the denominator divides the squarefree integer `d₂`,
  -- it must itself be `1`.
  have hsq_den_nat : IsSquare (((d₁ : ℚ) / (d₂ : ℚ)).den) := (Rat.isSquare_iff.mp hr).2
  have hsq_den_int : IsSquare ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) := by
    rcases hsq_den_nat with ⟨n, hn⟩
    refine ⟨(n : ℤ), by exact_mod_cast hn⟩
  have hden_dvd : ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) ∣ d₂ := by
    simpa [← Rat.divInt_eq_div] using (Rat.den_dvd d₁ d₂)
  have hsqf_den_int : Squarefree ((((d₁ : ℚ) / (d₂ : ℚ)).den : ℤ)) :=
    Squarefree.squarefree_of_dvd hden_dvd hsq_d₂
  have hden1_nat : ((d₁ : ℚ) / (d₂ : ℚ)).den = 1 :=
    nat_eq_one_of_squarefree_intcast_of_isSquare _ hsqf_den_int hsq_den_int
  exact (Rat.den_div_intCast_eq_one_iff d₁ d₂ hd₂).1 hden1_nat
