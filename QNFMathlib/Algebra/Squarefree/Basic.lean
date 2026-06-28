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

/-- If `r` is squarefree and `p` is not a unit, then `p * p` does not divide `r`. -/
-- Repository use: internal support for `squarefree_int_not_dvd_four`; no direct
-- project use is expected because this is the generalized squarefree lemma.
lemma Squarefree.not_mul_self_dvd_of_not_isUnit {R : Type*} [Monoid R]
    {r p : R} (hr : Squarefree r) (hp : ¬ IsUnit p) : ¬ p * p ∣ r := by
  intro h
  have hsq : Squarefree (p ^ 2) := Squarefree.squarefree_of_dvd (by simpa [pow_two] using h) hr
  have hbad : (2 : ℕ) = 0 ∨ (2 : ℕ) = 1 :=
    Squarefree.eq_zero_or_one_of_pow_of_not_isUnit hsq hp
  omega

/-- A squarefree integer is not divisible by `4`. -/
-- Repository use: `Mathlib/Data/Int/ModFour.lean` uses this to rule out the
-- even/odd parity cases in half-integrality arguments.
lemma squarefree_int_not_dvd_four (d : ℤ) (hd : Squarefree d) : ¬ (4 : ℤ) ∣ d := by
  intro h
  exact Squarefree.not_mul_self_dvd_of_not_isUnit hd (p := (2 : ℤ))
    (fun hunit => absurd (Int.isUnit_iff.mp hunit) (by omega)) (by simpa using h)

/-- A squarefree integer has remainder `1`, `2`, or `3` modulo `4`. -/
-- Repository use: currently a reusable mod-four fact for the ring-of-integers
-- branch split; no direct non-patch reference at the moment.
lemma squarefree_int_emod_four (d : ℤ) (hd : Squarefree d) :
    d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
  have hnd : ¬ (4 : ℤ) ∣ d := squarefree_int_not_dvd_four d hd
  omega

/-- A squarefree integer that is a perfect square must equal `1` or `-1`. -/
-- Repository use: `Qsqrtd/Basic.lean` uses this to show squarefree `d ≠ 1`
-- is not an integer square; `Mathlib/Data/Int/Squarefree.lean` uses it for
-- the natural-number specialization.
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
