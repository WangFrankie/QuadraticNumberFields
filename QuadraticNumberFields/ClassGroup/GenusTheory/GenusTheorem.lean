/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.UpperBound
import QuadraticNumberFields.ClassGroup.GenusTheory.LowerBound
import QuadraticNumberFields.ClassGroup.TwoRank

/-!
# The Genus Theorem

This file combines the genus-character lower bound with the ramified-parity
upper bound. The resulting genus theorem computes the 2-rank of the narrow
class group of `ℚ(√d)` as `ramifiedPrimeCount d - 1`. It also identifies the
square classes with admissible genus sign vectors. The kernel calculation is
the principal genus theorem.

The comparison with the ordinary class group is kept separately in
`GenusTheory.Ordinary`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-! ### The 2-rank and equivalent cardinalities -/

/-- The narrow two-torsion subgroup has the exact genus-theory cardinality. -/
theorem card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one :
    Nat.card (NarrowClassGroup.twoTorsion OK) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  apply le_antisymm (Ambiguous.card_narrowClassGroupTwoTorsion_le_two_pow_sub_one d)
  calc
    2 ^ (ramifiedPrimeCount d - 1) ≤
        Nat.card (squareQuotient (Cl⁺(d))) :=
      two_pow_sub_one_le_card_narrowSquareClassGroup d
    _ = Nat.card (NarrowClassGroup.twoTorsion OK) := by
      simpa using
        (card_squareQuotient_eq_card_twoTorsion (G := Cl⁺(d)))

/-- Cardinality form of the genus theorem for the narrow square-class group. -/
theorem card_narrowSquareClassGroup_eq_two_pow_sub_one :
    Nat.card (squareQuotient (Cl⁺(d))) = 2 ^ (ramifiedPrimeCount d - 1) := by
  rw [card_squareQuotient_eq_card_twoTorsion,
    card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one d]

/-- Genus theorem, rank form: the 2-rank of the narrow class group is one less
than the number of finite ramified primes. -/
theorem twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one :
    NarrowClassGroup.twoRank OK = ramifiedPrimeCount d - 1 := by
  apply Nat.pow_right_injective (a := 2) (by norm_num)
  change 2 ^ CommGroup.twoRank (Cl⁺(d)) = 2 ^ (ramifiedPrimeCount d - 1)
  rw [← card_squareQuotient_eq_two_pow_twoRank,
    card_narrowSquareClassGroup_eq_two_pow_sub_one d]

/-! ### Genus theorem and principal genus theorem -/

/-- The genus-character map on narrow square classes is injective. -/
theorem genusCharacterMapOnSquareClasses_injective :
    Function.Injective (genusCharacterMapOnSquareClasses d) :=
  (MonoidHom.injective_iff_nat_card_eq_of_surjective
      (genusCharacterMapOnSquareClasses d)
      (genusCharacterMapOnSquareClasses_surjective d)).mpr
    (by rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d,
      card_admissibleGenusSignVector d])

/-- The genus-character map on narrow square classes is bijective. -/
theorem genusCharacterMapOnSquareClasses_bijective :
    Function.Bijective (genusCharacterMapOnSquareClasses d) :=
  ⟨genusCharacterMapOnSquareClasses_injective d,
    genusCharacterMapOnSquareClasses_surjective d⟩

/-- Genus theorem, isomorphism form: the genus-character map identifies the
group of narrow square classes with the group of admissible genus sign
vectors. -/
noncomputable def narrowSquareClassesMulEquivGenusSignVectors :
    squareQuotient (Cl⁺(d)) ≃* AdmissibleGenusSignVector d :=
  MulEquiv.ofBijective (genusCharacterMapOnSquareClasses d)
    (genusCharacterMapOnSquareClasses_bijective d)

/-- Principal genus theorem: the kernel of the genus character map is exactly
the subgroup of squares of narrow ideal classes. -/
theorem genusCharacterMap_ker_eq_square :
    (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  refine le_antisymm (fun C hC ↦ ?_) (square_le_genusCharacterMap_ker d)
  rw [← QuotientGroup.eq_one_iff]
  apply genusCharacterMapOnSquareClasses_injective d
  rwa [map_one, genusCharacterMapOnSquareClasses_mk]

/-- Principal genus theorem, elementwise form: a narrow ideal class has
trivial genus characters exactly when it is a square. -/
theorem genusCharacterMap_eq_one_iff (C : Cl⁺(d)) :
    genusCharacterMap d C = 1 ↔ IsSquare C := by
  rw [← MonoidHom.mem_ker, genusCharacterMap_ker_eq_square d, Subgroup.mem_square]

end GenusTheory
end ClassGroup
end QuadraticNumberFields
