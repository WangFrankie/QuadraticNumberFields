/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Genus.Index
import QuadraticNumberFields.ClassGroup.Narrow

/-!
# Genus Characters

This file states the character target and the genus-character map for the new
narrow-class-group genus-theory layer.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The finite product of sign groups indexed by the ramified rational primes. -/
abbrev genusCharacterTarget (d : ℤ) :=
  (p : {p // p ∈ ramifiedPrimes d}) → ℤˣ

/-- The product of all ramified-prime signs. -/
noncomputable def genusSignProductHom (d : ℤ) :
    genusCharacterTarget d →* ℤˣ where
  toFun χ := Finset.univ.prod fun p : {p // p ∈ ramifiedPrimes d} => χ p
  map_one' := by
    simp
  map_mul' χ ψ := by
    simp [genusCharacterTarget, Finset.prod_mul_distrib]

/-- The relation subgroup of sign vectors whose total product is `1`. -/
noncomputable def genusCharacterTargetRelation (d : ℤ) :
    Subgroup (genusCharacterTarget d) :=
  (genusSignProductHom d).ker

/-- Membership in the relation subgroup is the product-one condition. -/
theorem mem_genusCharacterTargetRelation_iff
    (d : ℤ) (χ : genusCharacterTarget d) :
    χ ∈ genusCharacterTargetRelation d ↔
      Finset.univ.prod (fun p : {p // p ∈ ramifiedPrimes d} => χ p) = 1 :=
  Iff.rfl

/-- The genus-character map from the narrow class group to the product-one sign
relation subgroup. This is the main construction boundary for genus theory. -/
noncomputable def genusCharacterMap
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Cl⁺(d) →* genusCharacterTargetRelation d := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
