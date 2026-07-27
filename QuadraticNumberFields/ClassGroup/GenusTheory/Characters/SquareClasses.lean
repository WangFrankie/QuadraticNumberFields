/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Map
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Genus Characters On Narrow Square Classes

This file factors the genus character map through the quotient of the narrow
class group by its square subgroup.
-/

open scoped QuadraticNumberFields.ClassGroup
open CommGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

/-- The genus character map is trivial on squares of narrow ideal classes. -/
theorem square_le_genusCharacterMap_ker :
    Subgroup.square (Cl⁺(d)) ≤ (genusCharacterMap d).ker := by
  intro C hC
  obtain ⟨D, rfl⟩ := (Subgroup.mem_square_iff C).mp hC
  rw [MonoidHom.mem_ker, map_pow]
  ext p
  simp [pow_two, Int.units_mul_self]

/-- The genus character map factored through narrow square classes. -/
noncomputable def genusCharacterMapOnSquareClasses :
    squareQuotient (Cl⁺(d)) →* AdmissibleGenusSignVector d :=
  QuotientGroup.lift (Subgroup.square (Cl⁺(d))) (genusCharacterMap d)
    (square_le_genusCharacterMap_ker d)

/-- The square-class genus character map agrees with the original map on a
narrow class representative. -/
@[simp]
theorem genusCharacterMapOnSquareClasses_mk (C : Cl⁺(d)) :
    genusCharacterMapOnSquareClasses d (C : squareQuotient (Cl⁺(d))) =
      genusCharacterMap d C :=
  QuotientGroup.lift_mk' (Subgroup.square (Cl⁺(d))) (φ := genusCharacterMap d)
    (square_le_genusCharacterMap_ker d) C

end GenusTheory
end ClassGroup
end QuadraticNumberFields
