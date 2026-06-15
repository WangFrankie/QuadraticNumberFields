/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Torsion
import QuadraticNumberFields.ClassNumber

/-!
# Genus Theory

This file will contain genus-theory infrastructure for quadratic class groups.

The first intended application is the elementary genus-theory sieve in the
imaginary class-number-one problem: class number one forces the fundamental
discriminant to have only one prime-discriminant factor.
-/

namespace QuadraticNumberFields
namespace ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- Placeholder predicate for genus-theory data attached to `d`. -/
def HasGenusTheoryData (d : ℤ) : Prop :=
  HasClassGroupTorsionData d

/-! ## Class-number-one sieve -/

/-- **Genus-theory sieve for class number one.** If an imaginary quadratic field
`ℚ(√d)` has class number one, then genus theory forces its field discriminant to
have only one prime-discriminant factor. For squarefree negative `d`, this means
`d = -1`, `d = -2`, or `d = -p` for a rational prime `p ≡ 3 (mod 4)`.

This is the elementary sieve step in the Baker-Heegner-Stark classification. It
is intentionally stated as a WIP theorem here; the missing proof is the genus
theory calculation that `2 ^ (t - 1)` divides the class number, where `t` is the
number of prime-discriminant factors of the fundamental discriminant. -/
theorem classNumber_eq_one_imp_discriminant_prime_shape
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0)
    (h : NumberField.classNumber (Qsqrtd (d : ℚ)) = 1) :
    d = -1 ∨ d = -2 ∨ ∃ p : ℕ, Nat.Prime p ∧ p % 4 = 3 ∧ d = -(p : ℤ) := by
  sorry

end ClassGroup
end QuadraticNumberFields
