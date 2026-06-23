/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.Torsion
import QuadraticNumberFields.ClassGroup.Genus.Index
import QuadraticNumberFields.ClassGroup.Narrow

/-!
# Narrow Square Classes

This file names the square subgroup, square quotient, and two-torsion subgroup
of the narrow class group. These are the group-theoretic objects that appear in
the final genus-theory formula.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Genus

open scoped NumberField QuadraticNumberFields.ClassGroup

attribute [-instance] DivisionRing.toRatAlgebra

/-- The subgroup `Cl⁺(d)^2` of square narrow ideal classes. -/
noncomputable abbrev narrowSquareSubgroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup (Cl⁺(d)) :=
  Subgroup.square (Cl⁺(d))

/-- The narrow square-class quotient `Cl⁺(d) / Cl⁺(d)^2`. -/
abbrev narrowSquareQuotient
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :=
  Cl⁺(d) ⧸ narrowSquareSubgroup d

/-- The two-torsion subgroup `Cl⁺(d)[2]` of the narrow class group. -/
noncomputable abbrev narrowTwoTorsion
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Subgroup (Cl⁺(d)) :=
  MonoidHom.ker (powMonoidHom (α := Cl⁺(d)) 2)

/-- Membership in the two-torsion subgroup of the narrow class group. -/
theorem mem_narrowTwoTorsion_iff
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (C : Cl⁺(d)) :
    C ∈ narrowTwoTorsion d ↔ C ^ 2 = 1 :=
  Iff.rfl

/-- The square-class quotient of a finite narrow class group has the same
cardinality as the two-torsion subgroup. -/
theorem card_narrowSquareQuotient_eq_card_narrowTwoTorsion
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    Nat.card (narrowSquareQuotient d) = Nat.card (narrowTwoTorsion d) := by
  sorry

end Genus
end ClassGroup
end QuadraticNumberFields
