/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Exact
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

/-- Exactness at the square quotient: the kernel inclusion has range exactly the
kernel of the descended genus-character map. -/
theorem genusCharacterMapOnSquareQuotient_mulExact
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.MulExact (genusCharacterMapOnSquareQuotient d).ker.subtype
      (genusCharacterMapOnSquareQuotient d) := by
  rw [MonoidHom.mulExact_iff, Subgroup.range_subtype]

/-- The short exact sequence attached to the genus-character map:
`1 → ker Φ → Cl⁺/Cl⁺² → genusCharacterTargetRelation → 1`. -/
theorem genusCharacterMapOnSquareQuotient_shortExact
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Function.Injective (genusCharacterMapOnSquareQuotient d).ker.subtype ∧
      Function.MulExact (genusCharacterMapOnSquareQuotient d).ker.subtype
        (genusCharacterMapOnSquareQuotient d) ∧
        Function.Surjective (genusCharacterMapOnSquareQuotient d) :=
  ⟨Subtype.coe_injective, genusCharacterMapOnSquareQuotient_mulExact d,
    genusCharacterMapOnSquareQuotient_surjective d⟩

end GenusTheory
end ClassGroup
end QuadraticNumberFields
