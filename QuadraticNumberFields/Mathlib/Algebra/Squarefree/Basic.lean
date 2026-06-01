/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Squarefree.Basic

/-!
# Squarefree Lemmas

Material destined for mathlib.
-/

/-- A squarefree integer that is a perfect square must equal `1` or `-1`. -/
lemma eq_one_of_squarefree_isSquare {d : ℤ} (hd : Squarefree d) (hsq : IsSquare d) :
    d = 1 ∨ d = -1 := by
  obtain ⟨z, rfl⟩ := hsq
  have hsqz2 : Squarefree (z ^ 2) := by simpa [pow_two] using hd
  have huz : IsUnit z := by
    by_contra hne
    have h01 : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
      Squarefree.eq_zero_or_one_of_pow_of_not_isUnit (x := z) (n := 2) hsqz2 hne
    norm_num at h01
  rcases Int.isUnit_iff.mp huz with rfl | rfl <;> simp
