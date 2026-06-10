/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Mathlib.Data.Int.ModFour

/-!
# Congruence Criteria Modulo 4

This file develops congruence criteria modulo 4 used in the classification of
rings of integers in quadratic fields. The key distinction is whether `d ≡ 1 (mod 4)`,
which determines whether `𝓞(Q(√d))` is `ℤ[√d]` or `ℤ[(1+√d)/2]`.

## Main Results

### Squarefree Properties
The basic squarefree integer modulo-four facts are imported from
`QuadraticNumberFields.Mathlib.Algebra.Squarefree.Basic`.

### Parity and Squares
The basic parity facts for squares modulo four are imported from
`QuadraticNumberFields.Mathlib.Data.Int.ModFour`.

### Divisibility Criteria
The basic divisibility criteria for `4 ∣ (a'² - d·b'²)` are imported from
`QuadraticNumberFields.Mathlib.Data.Int.ModFour`.

### Branch Utilities
* `exists_k_of_mod_four_eq_one`: Extract `k` from `d % 4 = 1` as `d = 1 + 4k`.
* `mod_four_eq_one_of_exists_k`: Converse of the above.
* `mod_four_branch_split`: Trivial case split `d % 4 = 1 ∨ d % 4 ≠ 1`.
-/

namespace QuadraticNumberFields
namespace RingOfIntegers

/-- Extract parameterization `d = 1 + 4k` from `d % 4 = 1`. -/
theorem exists_k_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    ∃ k : ℤ, d = 1 + 4 * k := by
  refine ⟨d / 4, ?_⟩
  omega

/-- The converse of `exists_k_of_mod_four_eq_one`. -/
theorem mod_four_eq_one_of_exists_k {d : ℤ} (h : ∃ k : ℤ, d = 1 + 4 * k) :
    d % 4 = 1 := by
  rcases h with ⟨k, hk⟩
  omega

/-- Canonical branch split by `d % 4 = 1`. -/
theorem mod_four_branch_split (d : ℤ) : d % 4 = 1 ∨ d % 4 ≠ 1 :=
  eq_or_ne (d % 4) 1

end RingOfIntegers
end QuadraticNumberFields
