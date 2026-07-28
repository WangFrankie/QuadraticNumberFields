/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.SquareClasses
import QuadraticNumberFields.ClassGroup.GenusTheory.Surjectivity.Dirichlet

/-!
# The Genus-Theory Lower Bound

This file derives the square-class lower bound and the standard divisibility of
the narrow class number from surjectivity of the genus-character map.
-/

open scoped QuadraticNumberFields.ClassGroup
open CommGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The genus-character map on narrow square classes is surjective. -/
theorem genusCharacterMapOnSquareClasses_surjective :
    Function.Surjective (genusCharacterMapOnSquareClasses d) :=
  QuotientGroup.lift_surjective_of_surjective
    (Subgroup.square (Cl⁺(d))) (genusCharacterMap d)
    (genusCharacterMap_surjective d) (square_le_genusCharacterMap_ker d)

/-- The number of narrow square classes is at least `2 ^ (t - 1)`, where `t`
is the number of ramified rational primes. -/
theorem two_pow_sub_one_le_card_narrowSquareClassGroup :
    2 ^ (ramifiedPrimeCount d - 1) ≤ Nat.card (squareQuotient (Cl⁺(d))) := by
  rw [← card_admissibleGenusSignVector d]
  exact Nat.card_le_card_of_surjective (genusCharacterMapOnSquareClasses d)
    (genusCharacterMapOnSquareClasses_surjective d)

/-- The genus-theory power of two divides the narrow class number. -/
theorem two_pow_sub_one_dvd_narrowClassNumber :
    2 ^ (ramifiedPrimeCount d - 1) ∣ Qsqrtd.narrowClassNumber d := by
  have htarget_dvd :
      Nat.card (AdmissibleGenusSignVector d) ∣
        Nat.card (squareQuotient (Cl⁺(d))) :=
    Subgroup.card_dvd_of_surjective (genusCharacterMapOnSquareClasses d)
      (genusCharacterMapOnSquareClasses_surjective d)
  have hquot_dvd :
      Nat.card (squareQuotient (Cl⁺(d))) ∣ Qsqrtd.narrowClassNumber d := by
    simpa [Subgroup.index_eq_card, Qsqrtd.narrowClassNumber,
      NumberField.narrowClassNumber, NarrowClassGroup.narrowClassNumber,
      Nat.card_eq_fintype_card] using
        (Subgroup.square (Cl⁺(d))).index_dvd_card
  rw [card_admissibleGenusSignVector d] at htarget_dvd
  exact htarget_dvd.trans hquot_dvd

end GenusTheory
end ClassGroup
end QuadraticNumberFields
