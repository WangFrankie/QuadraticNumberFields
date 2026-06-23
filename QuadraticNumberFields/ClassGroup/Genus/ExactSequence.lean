/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.QuotientGroup.Basic
import QuadraticNumberFields.ClassGroup.Genus.Characters

/-!
# Genus Character Exact Sequence

This file states the group-theoretic short-exact-sequence interface for the
narrow-class-group genus-character map.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- Genus characters kill the square subgroup of the narrow class group. -/
theorem square_le_genusCharacterMap_ker
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup.square (Cl⁺(d)) ≤ (genusCharacterMap d).ker := by
  sorry

/-- The genus-character map descended to the quotient by the square subgroup. -/
noncomputable def genusCharacterMapOnSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)) →* genusCharacterTargetRelation d :=
  QuotientGroup.lift (Subgroup.square (Cl⁺(d))) (genusCharacterMap d)
    (square_le_genusCharacterMap_ker d)

@[simp]
theorem genusCharacterMapOnSquareQuotient_mk'
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    genusCharacterMapOnSquareQuotient d
        (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C) =
      genusCharacterMap d C :=
  QuotientGroup.lift_mk' (Subgroup.square (Cl⁺(d))) (φ := genusCharacterMap d)
    (square_le_genusCharacterMap_ker d) C

/-- The genus-character sequence is exact on the right: the quotient map onto the
product-one sign relation is surjective. -/
theorem genusCharacterMapOnSquareQuotient_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) := by
  sorry

/-- Exactness at the square quotient is equivalent to the principal-genus kernel
statement for the original genus-character map. -/
theorem genusCharacterMapOnSquareQuotient_ker_eq_bot_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    (genusCharacterMapOnSquareQuotient d).ker = ⊥ ↔
      (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d)) := by
  constructor
  · intro hker
    apply le_antisymm
    · intro C hC
      have hmk :
          QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C ∈
            (genusCharacterMapOnSquareQuotient d).ker := by
        rw [MonoidHom.mem_ker, genusCharacterMapOnSquareQuotient_mk']
        exact hC
      have hmk_one :
          QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C = 1 := by
        have : QuotientGroup.mk' (Subgroup.square (Cl⁺(d))) C ∈
            (⊥ : Subgroup (Cl⁺(d) ⧸ Subgroup.square (Cl⁺(d)))) := by
          simpa [hker] using hmk
        simpa using this
      exact (QuotientGroup.eq_one_iff _).mp hmk_one
    · exact square_le_genusCharacterMap_ker d
  · intro hker
    apply le_antisymm
    · intro Q hQ
      obtain ⟨C, rfl⟩ :=
        QuotientGroup.mk'_surjective (Subgroup.square (Cl⁺(d))) Q
      rw [MonoidHom.mem_ker, genusCharacterMapOnSquareQuotient_mk'] at hQ
      have hC : C ∈ Subgroup.square (Cl⁺(d)) := by
        rw [← hker]
        exact hQ
      exact (QuotientGroup.eq_one_iff _).mpr hC
    · exact bot_le

/-- The short exact sequence attached to the genus-character map, expressed in the
group-theoretic form needed for the genus formula. -/
theorem genusCharacterMapOnSquareQuotient_shortExact
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) ∧
      ((genusCharacterMapOnSquareQuotient d).ker = ⊥ ↔
        (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d))) :=
  ⟨genusCharacterMapOnSquareQuotient_surjective d,
    genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d⟩

end Genus
end ClassGroup
end QuadraticNumberFields
