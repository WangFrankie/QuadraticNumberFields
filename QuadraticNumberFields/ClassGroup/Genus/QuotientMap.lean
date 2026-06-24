/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.QuotientGroup.Basic
import QuadraticNumberFields.ClassGroup.Genus.Characters

/-!
# Genus Character Quotient Map

This file contains the group-theoretic descent of the genus-character map to the
quotient of the narrow class group by squares.
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
  intro C hC
  rw [Subgroup.mem_square] at hC
  rcases hC with ⟨D, rfl⟩
  rw [MonoidHom.mem_ker, map_mul]
  ext q
  simp [Int.units_mul_self]

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

end Genus
end ClassGroup
end QuadraticNumberFields
