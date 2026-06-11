/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Qsqrtd.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# Common Fact Instances for Quadratic Fields

This file provides global `Fact` instances for frequently-used quadratic field parameters
(`d = -1, -3, -5`). These enable cleaner example theorems without verbose inline `letI` blocks.

## Main Instances

- `Fact (Squarefree (-1 : ℤ))` / `Fact ((-1 : ℤ) ≠ 1)` — Gaussian integers
- `Fact (Squarefree (-3 : ℤ))` / `Fact ((-3 : ℤ) ≠ 1)` — Eisenstein integers
- `Fact (Squarefree (-5 : ℤ))` / `Fact ((-5 : ℤ) ≠ 1)` — ℤ[√(-5)]
- `Fact (Squarefree (17 : ℤ))` / `Fact ((17 : ℤ) ≠ 1)` — real field ℚ(√17)
- the remaining Heegner parameters `d = -2, -7, -11, -19, -43, -67, -163`
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

instance : Fact (Squarefree (17 : ℤ)) := ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((17 : ℤ) ≠ 1) := ⟨by decide⟩

/-! The remaining Heegner parameters; each is the negative of a prime, hence
prime in `ℤ` (via `natAbs`), hence squarefree. -/

instance : Fact (Squarefree (-2 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-2 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-7 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-7 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-11 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-11 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-19 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-19 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-43 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-43 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-67 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by decide)).squarefree⟩

instance : Fact ((-67 : ℤ) ≠ 1) := ⟨by decide⟩

instance : Fact (Squarefree (-163 : ℤ)) :=
  ⟨(Int.prime_iff_natAbs_prime.mpr (by norm_num)).squarefree⟩

instance : Fact ((-163 : ℤ) ≠ 1) := ⟨by decide⟩

end QuadraticNumberFields
