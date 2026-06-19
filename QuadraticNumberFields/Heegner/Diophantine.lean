/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic
import QNFMathlib.Data.Int.Parity
import QNFMathlib.Data.Int.Square
import QNFMathlib.RingTheory.Coprime

/-!
# Diophantine Layer for the Baker-Heegner-Stark Proof

This file isolates the elementary integer equation that appears in Cox's
Weber-function route through the Baker-Heegner-Stark theorem.  The hard
Diophantine theorem is kept as a named input; the finite check from its
solutions to the Heegner gamma list is proved here.

## Main definitions

* `HeegnerXYEquation`: the equation `Y ^ 2 = 2 * X * (X ^ 3 + 1)`.
* `heegnerXYSolutionSet`: the six known integral solutions.
* `heegnerGammaValue`: the gamma value obtained from a solution `(X, Y)`.
* `heegnerGammaSet`: the six gamma values arising from the known solutions.
* `heegnerPrimeSet`: the six positive odd Heegner primes in the inert branch.
-/

namespace QuadraticNumberFields
namespace Heegner

/-- The integer equation `Y ^ 2 = 2 * X * (X ^ 3 + 1)` arising in the
Cox-Weber proof of the inert-prime Baker-Heegner-Stark core. -/
def HeegnerXYEquation (X Y : ℤ) : Prop :=
  Y ^ 2 = 2 * X * (X ^ 3 + 1)

/-- The six integral solutions of `HeegnerXYEquation`. -/
def heegnerXYSolutionSet : Finset (ℤ × ℤ) :=
  {((0 : ℤ), 0), (-1, 0), (1, 2), (1, -2), (2, 6), (2, -6)}

/-- The six gamma values attached to the integral solutions of
`HeegnerXYEquation`. -/
def heegnerGammaSet : Finset ℤ :=
  {0, -32, -96, -960, -5280, -640320}

/-- The six positive odd Heegner primes that remain in the inert branch
`d = -p`, `p % 8 = 3`. -/
def heegnerPrimeSet : Finset ℤ :=
  {3, 11, 19, 43, 67, 163}

/-- The gamma value computed from an integer solution `(X, Y)` of
`HeegnerXYEquation`, written in the coordinate form used by Cox's proof. -/
def heegnerGammaValue (X Y : ℤ) : ℤ :=
  let a := -2 * X;
  let b := 4 * X ^ 2 + 2 * Y;
  -((b ^ 2 - 4 * a) ^ 2) - 8 * (2 * b - a ^ 2)

/-- The image of the known integral solutions under `heegnerGammaValue`. -/
def heegnerGammaImageSet : Finset ℤ :=
  heegnerXYSolutionSet.image fun xy => heegnerGammaValue xy.1 xy.2

/-- If an integer cube is `-1`, then the integer is `-1`. -/
theorem eq_neg_one_of_cube_add_one_eq_zero {X : ℤ} (hX : X ^ 3 + 1 = 0) :
    X = -1 := by
  have hpow : X ^ 3 = (-1 : ℤ) ^ 3 := by
    nlinarith
  exact (Odd.pow_inj (by norm_num : Odd 3)).mp hpow

/-- The two factors `X` and `X ^ 3 + 1` in Cox's equation are coprime. -/
theorem isCoprime_X_X_cube_add_one (X : ℤ) :
    IsCoprime X (X ^ 3 + 1) := by
  have h0 : IsCoprime X (1 : ℤ) := isCoprime_one_right
  convert IsCoprime.add_mul_right_right h0 (X ^ 2) using 1
  ring

/-- If `X` is even, then `2 * X` is still coprime to `X ^ 3 + 1`. -/
theorem isCoprime_two_mul_X_X_cube_add_one {X : ℤ} (hXeven : Even X) :
    IsCoprime (2 * X) (X ^ 3 + 1) := by
  have hodd : Odd (X ^ 3 + 1) := by
    rcases hXeven with ⟨k, rfl⟩
    use 4 * k ^ 3
    ring
  have hcop2 : IsCoprime (2 : ℤ) (X ^ 3 + 1) := by
    exact (Int.isCoprime_two_right.mpr hodd).symm
  exact hcop2.mul_left (isCoprime_X_X_cube_add_one X)

/-- If `X` is odd, then `X` is coprime to `2 * (X ^ 3 + 1)`. -/
theorem isCoprime_X_two_mul_X_cube_add_one {X : ℤ} (hXodd : Odd X) :
    IsCoprime X (2 * (X ^ 3 + 1)) := by
  have hcop2 : IsCoprime X (2 : ℤ) := Int.isCoprime_two_right.mpr hXodd
  exact hcop2.mul_right (isCoprime_X_X_cube_add_one X)

/-- Cox's first reduction: from the Heegner equation, `X ^ 3 + 1` is a square,
the negative of a square, twice a square, or negative twice a square. -/
theorem heegner_cube_add_one_square_or_twice_square {X Y : ℤ}
    (h : HeegnerXYEquation X Y) :
    ∃ Z : ℤ,
      X ^ 3 + 1 = Z ^ 2 ∨ X ^ 3 + 1 = -Z ^ 2 ∨
        X ^ 3 + 1 = 2 * Z ^ 2 ∨ X ^ 3 + 1 = -2 * Z ^ 2 := by
  rw [HeegnerXYEquation] at h
  rcases Int.even_or_odd X with hXeven | hXodd
  · have hprod : (2 * X) * (X ^ 3 + 1) = Y ^ 2 := by
      nlinarith [h]
    obtain ⟨Z, hZ | hZ⟩ := Int.sq_of_isCoprime
      (a := X ^ 3 + 1) (b := 2 * X) (c := Y)
      (isCoprime_two_mul_X_X_cube_add_one hXeven).symm
      (by simpa [mul_comm] using hprod)
    · exact ⟨Z, Or.inl hZ⟩
    · exact ⟨Z, Or.inr (Or.inl hZ)⟩
  · have hprod : X * (2 * (X ^ 3 + 1)) = Y ^ 2 := by
      nlinarith [h]
    obtain ⟨Z, hZ | hZ⟩ := Int.sq_of_isCoprime
      (a := 2 * (X ^ 3 + 1)) (b := X) (c := Y)
      (isCoprime_X_two_mul_X_cube_add_one hXodd).symm
      (by simpa [mul_comm] using hprod)
    · obtain ⟨W, hW⟩ := Int.exists_eq_two_mul_sq_of_two_mul_eq_sq hZ
      exact ⟨W, Or.inr (Or.inr (Or.inl hW))⟩
    · obtain ⟨W, hW⟩ := Int.exists_eq_neg_two_mul_sq_of_two_mul_eq_neg_sq hZ
      exact ⟨W, Or.inr (Or.inr (Or.inr hW))⟩

/-- If `X ^ 3 + 1` is twice a square along a solution of the Heegner equation,
then either this is the degenerate `X = -1` case, or `X` is itself a square.
This is the extra condition Cox uses to rewrite this branch as
`W ^ 6 + 1 = 2 * Z ^ 2`. -/
theorem heegner_x_eq_neg_one_or_square_of_cube_add_one_eq_two_mul_sq
    {X Y Z : ℤ} (h : HeegnerXYEquation X Y)
    (hZ : X ^ 3 + 1 = 2 * Z ^ 2) :
    X = -1 ∨ ∃ W : ℤ, X = W ^ 2 := by
  by_cases hZ0 : Z = 0
  · left
    apply eq_neg_one_of_cube_add_one_eq_zero
    rw [hZ, hZ0]
    norm_num
  · right
    have hprod : X * (4 * Z ^ 2) = Y ^ 2 := by
      rw [HeegnerXYEquation] at h
      rw [h, hZ]
      ring
    have hcop4Z : IsCoprime X (4 * Z ^ 2) := by
      have hcop2Z : IsCoprime X (2 * Z ^ 2) := by
        simpa [hZ] using isCoprime_X_X_cube_add_one X
      exact IsCoprime.four_mul_right_of_two_mul_right hcop2Z
    obtain ⟨W, hW | hW⟩ := Int.sq_of_isCoprime hcop4Z hprod
    · exact ⟨W, hW⟩
    · by_cases hW0 : W = 0
      · subst W
        subst X
        have hZsq_pos : 0 < Z ^ 2 := sq_pos_of_ne_zero hZ0
        nlinarith [hZ, hZsq_pos]
      · have hWsq_pos : 0 < W ^ 2 := sq_pos_of_ne_zero hW0
        have hZsq_pos : 0 < Z ^ 2 := sq_pos_of_ne_zero hZ0
        nlinarith [sq_nonneg Y, hprod, hW, hWsq_pos, hZsq_pos]

/-- Cox's auxiliary-equation split for a solution of the Heegner equation.
The twice-square branch is rewritten with the square `X = W ^ 2` condition,
which gives the equation `W ^ 6 + 1 = 2 * Z ^ 2`. -/
theorem heegner_auxiliary_equation_of_solution {X Y : ℤ}
    (h : HeegnerXYEquation X Y) :
    (∃ Z : ℤ, X ^ 3 + 1 = Z ^ 2) ∨
      (∃ Z : ℤ, X ^ 3 + 1 = -Z ^ 2) ∨
      (∃ W Z : ℤ, X = W ^ 2 ∧ W ^ 6 + 1 = 2 * Z ^ 2) ∨
      (∃ Z : ℤ, X ^ 3 + 1 = -2 * Z ^ 2) := by
  obtain ⟨Z, hZ | hZ | hZ | hZ⟩ := heegner_cube_add_one_square_or_twice_square h
  · exact Or.inl ⟨Z, hZ⟩
  · exact Or.inr (Or.inl ⟨Z, hZ⟩)
  · rcases heegner_x_eq_neg_one_or_square_of_cube_add_one_eq_two_mul_sq h hZ with
      hXm1 | ⟨W, hW⟩
    · subst X
      exact Or.inl ⟨0, by norm_num⟩
    · subst X
      refine Or.inr (Or.inr (Or.inl ⟨W, Z, rfl, ?_⟩))
      convert hZ using 1
      ring
  · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ⟩))

/-- In Cox's `W ^ 6 + 1 = 2 * Z ^ 2` branch, `W ^ 2 + 1` cannot itself be
a square. -/
theorem not_exists_sq_add_one_eq_sq_of_sixth_add_one_eq_two_mul_sq
    {W Z : ℤ} (h : W ^ 6 + 1 = 2 * Z ^ 2) :
    ¬ ∃ U : ℤ, W ^ 2 + 1 = U ^ 2 := by
  rintro ⟨U, hU⟩
  have hW0 : W = 0 := Int.eq_zero_of_sq_add_one_eq_sq hU
  subst W
  norm_num at h
  omega

/-- If the second integer factor in Cox's `W ^ 6 + 1` branch is a square,
then `W` is `0`, `1`, or `-1`. -/
theorem W_eq_zero_or_eq_one_or_neg_one_of_quartic_sub_sq_add_one_eq_sq
    {W K : ℤ} (h : W ^ 4 - W ^ 2 + 1 = K ^ 2) :
    W = 0 ∨ W = 1 ∨ W = -1 := by
  have hquad : (W ^ 2) ^ 2 - W ^ 2 + 1 = K ^ 2 := by
    convert h using 1
    ring
  rcases Int.eq_zero_or_eq_one_of_nonneg_of_sq_sub_self_add_one_eq_sq
      (sq_nonneg W) hquad with hWsq | hWsq
  · left
    nlinarith [sq_nonneg W]
  · right
    have hmul : W * W = 1 := by
      simpa [pow_two] using hWsq
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact Or.inl h1
    · exact Or.inr h1

/-- **Cox auxiliary Diophantine classification input.** Exercises 12.27-12.29
classify the auxiliary equations and leave only the `X`-coordinates
`0`, `-1`, `1`, and `2`. -/
theorem heegner_x_coordinate_of_auxiliary_equations {X : ℤ}
    (haux :
      (∃ Z : ℤ, X ^ 3 + 1 = Z ^ 2) ∨
        (∃ Z : ℤ, X ^ 3 + 1 = -Z ^ 2) ∨
        (∃ W Z : ℤ, X = W ^ 2 ∧ W ^ 6 + 1 = 2 * Z ^ 2) ∨
        (∃ Z : ℤ, X ^ 3 + 1 = -2 * Z ^ 2)) :
    X = 0 ∨ X = -1 ∨ X = 1 ∨ X = 2 := by
  sorry

/-- The `X`-coordinate classification for solutions of Cox's Heegner equation,
after reducing to the auxiliary Diophantine equations. -/
theorem heegner_x_coordinate_of_solution {X Y : ℤ}
    (h : HeegnerXYEquation X Y) :
    X = 0 ∨ X = -1 ∨ X = 1 ∨ X = 2 :=
  heegner_x_coordinate_of_auxiliary_equations
    (heegner_auxiliary_equation_of_solution h)

/-- The zero-`Y` branch of the Heegner integer equation. -/
theorem heegner_xy_solutions_of_Y_eq_zero
    {X : ℤ} (h : HeegnerXYEquation X 0) :
    (X, 0) ∈ heegnerXYSolutionSet := by
  rw [HeegnerXYEquation] at h
  norm_num at h
  have hcase : X = 0 ∨ X = -1 := by
    rcases h with hX | hX3
    · exact Or.inl hX
    · exact Or.inr (eq_neg_one_of_cube_add_one_eq_zero hX3)
  norm_num [heegnerXYSolutionSet]
  exact hcase

/-- Once Cox's Diophantine argument has restricted the `X`-coordinate to
`0`, `-1`, `1`, or `2`, the equation determines the listed `Y`-coordinates. -/
theorem heegner_xy_solutions_of_X_coordinate
    {X Y : ℤ} (h : HeegnerXYEquation X Y)
    (hX : X = 0 ∨ X = -1 ∨ X = 1 ∨ X = 2) :
    (X, Y) ∈ heegnerXYSolutionSet := by
  rcases hX with hX | hX | hX | hX
  · subst X
    rw [HeegnerXYEquation] at h
    norm_num at h
    subst Y
    norm_num [heegnerXYSolutionSet]
  · subst X
    rw [HeegnerXYEquation] at h
    norm_num at h
    subst Y
    norm_num [heegnerXYSolutionSet]
  · subst X
    have hY : Y = 2 ∨ Y = -2 := by
      rw [HeegnerXYEquation] at h
      norm_num at h
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases hY with rfl | rfl <;> norm_num [heegnerXYSolutionSet]
  · subst X
    have hY : Y = 6 ∨ Y = -6 := by
      rw [HeegnerXYEquation] at h
      norm_num at h
      exact sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases hY with rfl | rfl <;> norm_num [heegnerXYSolutionSet]

/-- The only integer solutions of `Y ^ 2 = 2 * X * (X ^ 3 + 1)` are the pairs
in `heegnerXYSolutionSet`, assuming Cox's auxiliary coordinate classification. -/
theorem heegner_xy_solutions
    {X Y : ℤ} (h : HeegnerXYEquation X Y) :
    (X, Y) ∈ heegnerXYSolutionSet := by
  by_cases hY : Y = 0
  · subst Y
    exact heegner_xy_solutions_of_Y_eq_zero h
  · exact heegner_xy_solutions_of_X_coordinate h
      (heegner_x_coordinate_of_solution h)

/-- Every pair in `heegnerXYSolutionSet` satisfies the Heegner integer equation. -/
theorem heegnerXYEquation_of_mem_heegnerXYSolutionSet
    {X Y : ℤ} (hmem : (X, Y) ∈ heegnerXYSolutionSet) :
    HeegnerXYEquation X Y := by
  norm_num [heegnerXYSolutionSet] at hmem
  rcases hmem with h | h | h | h | h | h <;>
    rcases h with ⟨rfl, rfl⟩ <;>
    norm_num [HeegnerXYEquation]

/-- The finite gamma table computed from `heegnerXYSolutionSet` is exactly
`heegnerGammaSet`. -/
theorem heegnerGammaImageSet_eq_heegnerGammaSet :
    heegnerGammaImageSet = heegnerGammaSet := by
  ext gamma
  norm_num [heegnerGammaImageSet, heegnerXYSolutionSet, heegnerGammaValue, heegnerGammaSet]
  tauto

/-- The gamma value attached to any listed integral solution belongs to
`heegnerGammaSet`. -/
theorem heegnerGammaValue_mem_heegnerGammaSet_of_mem_heegnerXYSolutionSet
    {X Y : ℤ} (hmem : (X, Y) ∈ heegnerXYSolutionSet) :
    heegnerGammaValue X Y ∈ heegnerGammaSet := by
  rw [← heegnerGammaImageSet_eq_heegnerGammaSet]
  exact Finset.mem_image.mpr ⟨(X, Y), hmem, rfl⟩

/-- Any gamma value produced from a solution of `HeegnerXYEquation` belongs to
the finite Heegner gamma set. -/
theorem gamma_mem_heegnerGammaSet_of_xy_solution
    {X Y gamma : ℤ} (hxy : HeegnerXYEquation X Y)
    (hgamma : gamma = heegnerGammaValue X Y) :
    gamma ∈ heegnerGammaSet := by
  subst gamma
  exact heegnerGammaValue_mem_heegnerGammaSet_of_mem_heegnerXYSolutionSet
    (heegner_xy_solutions hxy)

end Heegner
end QuadraticNumberFields
