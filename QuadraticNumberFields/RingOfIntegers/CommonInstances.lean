/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Qsqrtd.Basic
import Mathlib.RingTheory.Int.Basic

/-!
# Common Fact Instances for Quadratic Fields

This file provides global `Fact` instances for frequently-used quadratic field parameters
(`d = -1, -3, -5`). These enable cleaner example theorems without verbose inline `letI` blocks.

## Main Instances

- `Fact (Squarefree (-1 : ℤ))` / `Fact ((-1 : ℤ) ≠ 1)` — Gaussian integers
- `Fact (Squarefree (-3 : ℤ))` / `Fact ((-3 : ℤ) ≠ 1)` — Eisenstein integers
- `Fact (Squarefree (-5 : ℤ))` / `Fact ((-5 : ℤ) ≠ 1)` — ℤ[√(-5)]
-/

namespace QuadraticNumberFields

/-! ## Common Fact instances for frequently-used quadratic fields -/

instance : Fact (Squarefree (-1 : ℤ)) := ⟨(isUnit_neg_one (α := ℤ)).squarefree⟩

instance : Fact ((-1 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-3 : ℤ)) := ⟨by
  intro p hp
  exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (3 : ℤ)).squarefree p (dvd_neg.mp hp)⟩

instance : Fact ((-3 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-5 : ℤ)) := ⟨by
  intro p hp
  exact (Int.prime_iff_natAbs_prime.mpr (by decide) : Prime (5 : ℤ)).squarefree p (dvd_neg.mp hp)⟩

instance : Fact ((-5 : ℤ) ≠ 1) := ⟨by decide⟩

end QuadraticNumberFields
