/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.GenusTheory
import QuadraticNumberFields.Heegner.ClassNumberOne
import QuadraticNumberFields.Heegner.IdealReductions

/-!
# The Baker–Heegner–Stark Theorem (Statement)

This file states the full **Baker–Heegner–Stark theorem** (also known as the
Stark–Heegner theorem): an imaginary quadratic field `ℚ(√d)` (with `d < 0`
squarefree) has class number one if and only if `d` is one of the nine
Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The easy direction — each Heegner number gives class number one — is fully
proved in `QuadraticNumberFields.Heegner.ClassNumberOne` via Minkowski bounds
and inertness of small primes. The deep direction — there are **no further**
imaginary quadratic fields of class number one — was conjectured by Gauss and
proved by Heegner (1952), Baker (1966), and Stark (1967); its formalisation
(e.g. via the theory of modular functions or linear forms in logarithms) is far
beyond the current scope and is recorded here as a `sorry`.

## Reference

D. A. Cox, *Primes of the form x² + ny²*, 2nd ed., Theorem 12.34 (Heegner's
proof). H. M. Stark, *A complete determination of the complex quadratic fields
of class-number one*, Michigan Math. J. 14 (1967).
-/

attribute [-instance] DivisionRing.toRatAlgebra

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

/-- **Elementary non-half-integral branch of Baker-Heegner-Stark.** If
`d % 4 ≠ 1`, then the ideal-theoretic ramification-at-`2` argument already
forces `d = -1` or `d = -2`, hence `d` is a Heegner number. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd4 : d % 4 ≠ 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  rcases eq_neg_one_or_eq_neg_two_of_classNumber_eq_one_of_mod_four_ne_one
      d hd hd4 h with rfl | rfl <;>
    simp [heegnerSet]

/-- **Elementary split half-integral branch of Baker-Heegner-Stark.** If
`d % 8 = 1`, then the ideal-theoretic split-at-`2` argument already forces
`d = -7`, hence `d` is a Heegner number. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) (hd8 : d % 8 = 1)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  have hd_eq : d = -7 :=
    eq_neg_seven_of_classNumber_eq_one_of_mod_eight_eq_one d hd hd8 h
  rw [hd_eq]
  simp [heegnerSet]

/-- **Baker-Heegner-Stark prime-family step.** After the genus-theory sieve has
reduced the class-number-one problem to `d = -1`, `d = -2`, or `d = -p` with
`p ≡ 3 (mod 4)` prime, the deep Heegner/Baker/Stark theorem says that the
remaining class-number-one cases are exactly the Heegner numbers.

This is the genuinely deep step: it eliminates the infinite prime family
`d = -p`, leaving only `p = 3, 7, 11, 19, 43, 67, 163`. -/
theorem classNumber_eq_one_imp_mem_heegnerSet_of_discriminant_prime_shape
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (hshape :
      d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ))
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d ∈ heegnerSet := by
  sorry

/-- **Baker–Heegner–Stark theorem.** A negative squarefree integer `d` gives an
imaginary quadratic field `ℚ(√d)` of class number one if and only if `d` is one
of the nine Heegner numbers `-1, -2, -3, -7, -11, -19, -43, -67, -163`.

The reverse implication is `classNumber_eq_one_of_mem_heegnerSet`. The forward
implication (completeness of the list) is the deep theorem of Heegner, Baker,
and Stark and is not yet formalised. -/
theorem classNumber_eq_one_iff_mem_heegnerSet
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    NumberField.classNumber (Qsqrtd (d : ℚ)) = 1 ↔ d ∈ heegnerSet := by
  constructor
  · intro h
    by_cases hd4 : d % 4 = 1
    · have hd8_cases : d % 8 = 1 ∨ d % 8 = 5 := by omega
      rcases hd8_cases with hd8 | hd8
      · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_eight_eq_one d hd hd8 h
      · sorry
    · exact classNumber_eq_one_imp_mem_heegnerSet_of_mod_four_ne_one d hd hd4 h
  · exact fun h => classNumber_eq_one_of_mem_heegnerSet h

end Heegner
end QuadraticNumberFields
