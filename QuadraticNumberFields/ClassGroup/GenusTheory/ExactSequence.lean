/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Surjectivity

/-!
# Genus Character Exact Sequence

This file states the group-theoretic short-exact-sequence interface for the
narrow-class-group genus-character map.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The genus-character sequence is exact on the right: the quotient map onto the
product-one sign relation is surjective. -/
theorem genusCharacterMapOnSquareQuotient_surjective
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) :=
  genusCharacterMapOnSquareQuotient_surjective_of_genusCharacterMap_surjective d

/-- The short exact sequence attached to the genus-character map, expressed in the
group-theoretic form needed for the genus formula. -/
theorem genusCharacterMapOnSquareQuotient_shortExact
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Surjective (genusCharacterMapOnSquareQuotient d) ∧
      ((genusCharacterMapOnSquareQuotient d).ker = ⊥ ↔
        (genusCharacterMap d).ker = Subgroup.square (Cl⁺(d))) :=
  ⟨genusCharacterMapOnSquareQuotient_surjective d,
    genusCharacterMapOnSquareQuotient_ker_eq_bot_iff d⟩

end GenusTheory
end ClassGroup
end QuadraticNumberFields
