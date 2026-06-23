/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.SquareClass

/-!
# Ambiguous Ideals

This file records the ambiguous-ideal upper bound for quadratic genus theory.
The proof will identify conjugation-fixed classes with two-torsion classes,
adjust fixed classes to fixed ideals, and then show that only ramified prime
ideals contribute non-principal generators.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- Ambiguous-ideal upper bound: the two-torsion in the narrow class group has
size at most `2 ^ (t - 1)`, where `t` is the number of ramified rational primes. -/
theorem card_narrowTwoTorsion_le_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowTwoTorsion d) ≤ 2 ^ (ramifiedPrimeCount d - 1) := by
  sorry

/-- Equivalent upper bound for the narrow square-class quotient. -/
theorem card_narrowSquareQuotient_le_genusBound
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) ≤ 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_narrowSquareQuotient_eq_card_narrowTwoTorsion]
  exact card_narrowTwoTorsion_le_genusBound d

end Genus
end ClassGroup
end QuadraticNumberFields
