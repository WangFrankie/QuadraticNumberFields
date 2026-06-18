/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

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

/-- **Heegner integer-equation input.** The only integer solutions of
`Y ^ 2 = 2 * X * (X ^ 3 + 1)` are the pairs in `heegnerXYSolutionSet`. -/
theorem heegner_xy_solutions
    {X Y : ℤ} (h : HeegnerXYEquation X Y) :
    (X, Y) ∈ heegnerXYSolutionSet := by
  sorry

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
