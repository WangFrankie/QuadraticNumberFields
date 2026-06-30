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

/-- The map on square quotients induced by the natural map `Cl⁺(d) → Cl(d)`. -/
noncomputable def narrowSquareQuotientToClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) →* Cl(d) ⧸ Subgroup.square (Cl(d)) :=
  QuotientGroup.map (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) (by
      intro C hC
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_square] at hC ⊢
      rcases hC with ⟨D, rfl⟩
      exact ⟨Qsqrtd.narrowToClassGroup d D, by simp [map_mul]⟩)

@[simp]
theorem narrowSquareQuotientToClassGroup_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    narrowSquareQuotientToClassGroup d
        (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      QuotientGroup.mk' (Subgroup.square (Cl(d))) (Qsqrtd.narrowToClassGroup d C) :=
  QuotientGroup.map_mk' (Subgroup.square (Cl⁺(d))) (Subgroup.square (Cl(d)))
    (Qsqrtd.narrowToClassGroup d) _ C

/-- The map on square quotients induced by `Cl⁺(d) → Cl(d)` is surjective. -/
theorem narrowSquareQuotientToClassGroup_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (narrowSquareQuotientToClassGroup d) := by
  apply QuotientGroup.map_surjective_of_surjective
  intro C
  obtain ⟨D, hD⟩ := QuotientGroup.mk'_surjective (Subgroup.square (Cl(d))) C
  rcases NarrowClassGroup.toClassGroup_surjective
      (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) D with ⟨Dplus, hDplus⟩
  exact ⟨Dplus, by
    rw [Function.comp_apply, hDplus]
    exact hD⟩

/-- Exact correction formula comparing the narrow and ordinary class-group
square-quotient genus formulas.

The correction term is the kernel of the map
`Cl⁺(d) / Cl⁺(d)^2 → Cl(d) / Cl(d)^2`. The later real-quadratic sign exact
sequence should identify this kernel as trivial or of order `2` in the positive
discriminant branches. -/
theorem card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotientToClassGroup d).ker *
        Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hcard := (narrowSquareQuotientToClassGroup d).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (narrowSquareQuotientToClassGroup_surjective d),
    Subgroup.card_top] at hcard
  rw [hcard, card_narrowClassGroupSquareQuotient_eq_two_pow_sub_one]

/-- If the narrow-to-wide map on square quotients has correction factor `2`, the
ordinary square quotient has the expected corrected genus-formula factor. -/
theorem two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2) :
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  calc
    2 * Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
        Nat.card (narrowSquareQuotientToClassGroup d).ker *
          Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) := by rw [hcor]
    _ = 2 ^ (ramifiedPrimeCount d - 1) :=
        card_classGroupSquareQuotient_mul_correction_eq_two_pow_sub_one d

/-- In the nontrivial correction branch, the ordinary class-group square quotient
has cardinality `2 ^ (t - 2)`, where `t = ramifiedPrimeCount d`. -/
theorem card_classGroupSquareQuotient_eq_two_pow_sub_two_of_correction_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hcor : Nat.card (narrowSquareQuotientToClassGroup d).ker = 2)
    (hcount : 2 ≤ ramifiedPrimeCount d) :
    Nat.card (Cl(d) ⧸ Subgroup.square (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 2) := by
  have hmain :=
    two_mul_card_classGroupSquareQuotient_eq_two_pow_sub_one_of_correction_eq_two d hcor
  have hpow : 2 ^ (ramifiedPrimeCount d - 1) = 2 * 2 ^ (ramifiedPrimeCount d - 2) := by
    have hs : ramifiedPrimeCount d - 1 = ramifiedPrimeCount d - 2 + 1 := by omega
    rw [hs, pow_succ, mul_comm]
  rw [hpow] at hmain
  exact Nat.mul_left_cancel (by norm_num : 0 < 2) hmain

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
