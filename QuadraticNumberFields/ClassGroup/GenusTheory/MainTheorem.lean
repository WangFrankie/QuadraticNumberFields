/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.UpperBound
import QuadraticNumberFields.ClassGroup.GenusTheory.LowerBound
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# The Genus Theorem

This file combines the independent genus-character lower bound and
ramified-parity upper bound into the main results of genus theory for the
narrow class group of `ℚ(√d)`:

* the exact cardinalities of the narrow square-class quotient and the narrow
  two-torsion subgroup;
* the corrected cardinality formulas with the concrete exponent `ω(|d|)`
  determined by `d % 4`, valid without any sign hypothesis on `d`;
* bijectivity of the genus-character map on narrow square classes, and the
  resulting isomorphism with the admissible genus sign vectors;
* the principal genus theorem: the kernel of the genus character map is the
  subgroup of squares.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

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

/-- The narrow square-class quotient has the exact genus-theory cardinality. -/
theorem card_narrowSquareClassGroup_eq_two_pow_sub_one :
    Nat.card (squareQuotient (Cl⁺(d))) = 2 ^ (ramifiedPrimeCount d - 1) := by
  calc
    Nat.card (squareQuotient (Cl⁺(d))) =
        Nat.card (NarrowClassGroup.twoTorsion OK) := by
      simpa using
        (card_squareQuotient_eq_card_twoTorsion (G := Cl⁺(d)))
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
      card_narrowClassGroupTwoTorsion_eq_two_pow_sub_one d

/-- Corrected genus formula, `d ≡ 1 (mod 4)`: the narrow class group of
`ℚ(√d)` has `2 ^ (ω(|d|) - 1)` square classes, for real and imaginary fields
alike. -/
theorem card_narrowSquareClassGroup_of_mod_four_eq_one (hd4 : d % 4 = 1) :
    Nat.card (squareQuotient (Cl⁺(d))) =
      2 ^ (d.natAbs.primeFactors.card - 1) := by
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d,
    ramifiedPrimeCount_of_mod_four_eq_one d hd4]

/-- Corrected genus formula, `d ≡ 2 (mod 4)`: the narrow class group of
`ℚ(√d)` has `2 ^ (ω(|d|) - 1)` square classes, for real and imaginary fields
alike. -/
theorem card_narrowSquareClassGroup_of_mod_four_eq_two (hd4 : d % 4 = 2) :
    Nat.card (squareQuotient (Cl⁺(d))) =
      2 ^ (d.natAbs.primeFactors.card - 1) := by
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d,
    ramifiedPrimeCount_of_mod_four_eq_two d hd4]

/-- Corrected genus formula, `d ≡ 3 (mod 4)`: the wild prime `2` raises the
narrow square-class count to `2 ^ ω(|d|)`, for real and imaginary fields
alike. -/
theorem card_narrowSquareClassGroup_of_mod_four_eq_three (hd4 : d % 4 = 3) :
    Nat.card (squareQuotient (Cl⁺(d))) = 2 ^ d.natAbs.primeFactors.card := by
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d,
    ramifiedPrimeCount_of_mod_four_eq_three d hd4, Nat.add_sub_cancel]

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
  rw [map_one, genusCharacterMapOnSquareClasses_mk]
  exact hC

/-- Principal genus theorem, elementwise form: a narrow ideal class has
trivial genus characters exactly when it is a square. -/
theorem genusCharacterMap_eq_one_iff (C : Cl⁺(d)) :
    genusCharacterMap d C = 1 ↔ IsSquare C := by
  rw [← MonoidHom.mem_ker, genusCharacterMap_ker_eq_square d, Subgroup.mem_square]

end GenusTheory
end ClassGroup
end QuadraticNumberFields
