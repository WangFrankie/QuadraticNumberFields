/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Families.RichaudDegert
import QuadraticNumberFields.Units.Pell

/-!
# Units in Explicit Families

Explicit Pell-type unit candidates for the classical Richaud-Degert shapes
`d = n² ± 1` and `d = n² ± 2` (the `a = 1` Richaud-Degert families).

## Main definitions

* `HasExplicitUnitCandidate d`: `d` admits an explicit nontrivial solution of
  `x² - d·y² = ±1`.

## Main results

* `isPellUnitSolution_sq_sub_one` and friends: explicit solutions for the
  four families `d = n² ± 1`, `d = n² ± 2`.
* `hasExplicitUnitCandidate_richaudDegert_one`: every `a = 1` Richaud-Degert
  parameter with shift `k ∈ {-2, -1, 1, 2}` has an explicit unit candidate.
* `HasExplicitUnitCandidate.exists_unit_ne_one`: an explicit candidate yields
  a unit of `ℤ[√d]` different from `±1`.
-/

namespace QuadraticNumberFields
namespace Units

open QuadraticAlgebra

/-- `d` admits an explicit nontrivial solution of `x² - d·y² = ±1`, hence an
explicit unit of `ℤ[√d]` other than `±1`. -/
def HasExplicitUnitCandidate (d : ℤ) : Prop :=
  ∃ x y : ℤ, y ≠ 0 ∧ (IsPellSolution d 1 x y ∨ IsPellSolution d (-1) x y)

/-- `(n, 1)` solves the norm-one Pell equation for `d = n² - 1`. -/
theorem isPellUnitSolution_sq_sub_one (n : ℤ) : IsPellUnitSolution (n ^ 2 - 1) n 1 := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- `(n, 1)` solves the norm-`-1` Pell equation for `d = n² + 1`. -/
theorem isPellSolution_neg_one_sq_add_one (n : ℤ) : IsPellSolution (n ^ 2 + 1) (-1) n 1 := by
  unfold IsPellSolution
  ring

/-- `(n² + 1, n)` solves the norm-one Pell equation for `d = n² + 2`. -/
theorem isPellUnitSolution_sq_add_two (n : ℤ) :
    IsPellUnitSolution (n ^ 2 + 2) (n ^ 2 + 1) n := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- `(n² - 1, n)` solves the norm-one Pell equation for `d = n² - 2`. -/
theorem isPellUnitSolution_sq_sub_two (n : ℤ) :
    IsPellUnitSolution (n ^ 2 - 2) (n ^ 2 - 1) n := by
  unfold IsPellUnitSolution IsPellSolution
  ring

/-- The family `d = n² - 1` has an explicit unit candidate. -/
theorem hasExplicitUnitCandidate_sq_sub_one (n : ℤ) :
    HasExplicitUnitCandidate (n ^ 2 - 1) :=
  ⟨n, 1, one_ne_zero, Or.inl (isPellUnitSolution_sq_sub_one n)⟩

/-- The family `d = n² + 1` has an explicit unit candidate. -/
theorem hasExplicitUnitCandidate_sq_add_one (n : ℤ) :
    HasExplicitUnitCandidate (n ^ 2 + 1) :=
  ⟨n, 1, one_ne_zero, Or.inr (isPellSolution_neg_one_sq_add_one n)⟩

/-- The family `d = n² + 2` has an explicit unit candidate for `n ≠ 0`. -/
theorem hasExplicitUnitCandidate_sq_add_two {n : ℤ} (hn : n ≠ 0) :
    HasExplicitUnitCandidate (n ^ 2 + 2) :=
  ⟨n ^ 2 + 1, n, hn, Or.inl (isPellUnitSolution_sq_add_two n)⟩

/-- The family `d = n² - 2` has an explicit unit candidate for `n ≠ 0`. -/
theorem hasExplicitUnitCandidate_sq_sub_two {n : ℤ} (hn : n ≠ 0) :
    HasExplicitUnitCandidate (n ^ 2 - 2) :=
  ⟨n ^ 2 - 1, n, hn, Or.inl (isPellUnitSolution_sq_sub_two n)⟩

/-- The `a = 1` Richaud-Degert parameter is `n² + k`. -/
theorem richaudDegertD_one (n k : ℤ) : Families.richaudDegertD 1 n k = n ^ 2 + k := by
  unfold Families.richaudDegertD
  ring

/-- Every `a = 1` Richaud-Degert parameter `n² + k` with shift
`k ∈ {-2, -1, 1, 2}` and `n ≠ 0` has an explicit unit candidate. -/
theorem hasExplicitUnitCandidate_richaudDegert_one {k : ℤ} (n : ℤ) (hn : n ≠ 0)
    (hk : k = -2 ∨ k = -1 ∨ k = 1 ∨ k = 2) :
    HasExplicitUnitCandidate (Families.richaudDegertD 1 n k) := by
  rw [richaudDegertD_one]
  rcases hk with rfl | rfl | rfl | rfl
  · exact (by ring_nf : n ^ 2 + -2 = n ^ 2 - 2) ▸ hasExplicitUnitCandidate_sq_sub_two hn
  · exact (by ring_nf : n ^ 2 + -1 = n ^ 2 - 1) ▸ hasExplicitUnitCandidate_sq_sub_one n
  · exact hasExplicitUnitCandidate_sq_add_one n
  · exact hasExplicitUnitCandidate_sq_add_two hn

/-- An explicit unit candidate yields a unit of `ℤ[√d]` different from `±1`. -/
theorem HasExplicitUnitCandidate.exists_unit_ne_one {d : ℤ}
    (h : HasExplicitUnitCandidate d) :
    ∃ u : (Zsqrtd d)ˣ, u ≠ 1 ∧ u ≠ -1 := by
  obtain ⟨x, y, hy, hsol⟩ := h
  have hu : IsUnit (⟨x, y⟩ : Zsqrtd d) := isUnit_mk_iff_isPellSolution.mpr hsol
  refine ⟨hu.unit, fun heq => hy ?_, fun heq => hy ?_⟩
  · simpa [im_one] using
      congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq
  · simpa [im_one] using
      congrArg (fun u : (Zsqrtd d)ˣ => (u : Zsqrtd d).im) heq

end Units
end QuadraticNumberFields
