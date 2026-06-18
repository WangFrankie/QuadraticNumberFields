/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.ClassGroup.GenusTheory
import QuadraticNumberFields.Heegner.ClassNumberOne

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
    sorry
  · exact fun h => classNumber_eq_one_of_mem_heegnerSet h

end Heegner
end QuadraticNumberFields
