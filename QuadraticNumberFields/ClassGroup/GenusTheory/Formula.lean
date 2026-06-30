/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.QuotientEquiv

/-!
# Genus Formula

This file states the genus formula for the new narrow-class-group genus-theory
layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

private noncomputable def powTorsionMulEquiv {G H : Type*} [CommGroup G] [CommGroup H]
    (n : ℕ) (e : G ≃* H) :
    Subgroup.powTorsion G n ≃* Subgroup.powTorsion H n where
  toFun x := ⟨e x, by
    rw [Subgroup.mem_powTorsion_iff]
    rw [← map_pow, (Subgroup.mem_powTorsion_iff G n x).mp x.2, map_one]⟩
  invFun y := ⟨e.symm y, by
    rw [Subgroup.mem_powTorsion_iff]
    rw [← map_pow, (Subgroup.mem_powTorsion_iff H n y).mp y.2, map_one]⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_mul' x y := by
    ext
    simp

/-- The genus formula for quadratic fields, stated on the narrow class group. -/
theorem genusFormula
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) :=
  card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one d

/-- If the narrow and ordinary class groups are isomorphic, the ordinary
class-group square quotient satisfies the genus formula. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_nonempty_narrowMulEquivClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (h : Nonempty (Cl⁺(d) ≃* Cl(d))) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  rcases h with ⟨e⟩
  rw [_root_.ClassGroup.card_squareQuotient_eq_card_twoTorsion]
  rw [← Nat.card_congr (powTorsionMulEquiv 2 e).toEquiv]
  rw [← NarrowClassGroup.card_squareQuotient_eq_card_twoTorsion]
  exact card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one d

/-- For imaginary quadratic fields, the ordinary class-group square quotient
satisfies the genus formula. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_one_of_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : d < 0) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  exact card_classGroupSquareQuotient_eq_two_pow_sub_one_of_nonempty_narrowMulEquivClassGroup
    d (Qsqrtd.Imaginary.nonempty_narrowMulEquivClassGroup d hd)

/-- The genus formula is equivalent to the principal-genus kernel statement for the
genus-character map. -/
theorem genusFormula_iff_genusCharacterMap_ker_eq_square
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    numberOfGenera d = 2 ^ (ramifiedPrimeCount d - 1) ↔
      (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  constructor
  · intro _
    apply (genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d).mp
    exact (MonoidHom.ker_eq_bot_iff (genusCharacterMapOnSquareQuotient d)).mpr
      (genusQuotientEquiv d).injective
  · intro _
    exact genusFormula d

/-- The narrow two-torsion has cardinality equal to the number of genera. -/
theorem card_narrowClassGroupTwoTorsion_eq_numberOfGenera
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (NarrowClassGroup.twoTorsion
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) = numberOfGenera d :=
  (card_narrowClassGroupSquareQuotient_eq_card_narrowClassGroupTwoTorsion d).symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
