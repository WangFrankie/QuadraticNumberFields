/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# The 2-Rank of Class Groups

For a finite commutative group `G`, its **2-rank** is the dimension over the
field with two elements of the square-class group `G / G²`. This file defines
that invariant and records its cardinality interpretation, together with the
ordinary and narrow class-group specializations.
-/

namespace CommGroup

variable (G : Type*) [CommGroup G]

@[implicit_reducible]
private noncomputable def squareQuotientModule :
    Module (ZMod 2) (Additive (squareQuotient G)) :=
  AddCommGroup.zmodModule fun x ↦ by
    change x.toMul ^ 2 = 1
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (Subgroup.square G) x.toMul
    rw [← hg, ← map_pow]
    change ((g ^ 2 : G) : G ⧸ Subgroup.square G) = 1
    exact (QuotientGroup.eq_one_iff (g ^ 2)).mpr
      ((Subgroup.mem_square_iff (g ^ 2)).mpr ⟨g, rfl⟩)

/-- The 2-rank of a commutative group `G`, defined as
`dim_F₂ (G / G²)`. -/
noncomputable def twoRank : ℕ :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := squareQuotientModule G
  Module.finrank (ZMod 2) (Additive (squareQuotient G))

variable {G}

/-- The square-class group of a finite commutative group has cardinality
`2 ^ twoRank G`. -/
theorem card_squareQuotient_eq_two_pow_twoRank [Finite G] :
    Nat.card (squareQuotient G) = 2 ^ twoRank G := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI := squareQuotientModule G
  change Nat.card (squareQuotient G) =
    2 ^ Module.finrank (ZMod 2) (Additive (squareQuotient G))
  simpa using
    (Module.natCard_eq_pow_finrank
      (K := ZMod 2) (V := Additive (squareQuotient G)))

end CommGroup

namespace ClassGroup

variable (R) [CommRing R] [IsDomain R]

/-- The 2-rank of the ideal class group. -/
noncomputable abbrev twoRank : ℕ :=
  CommGroup.twoRank (ClassGroup R)

end ClassGroup

namespace NarrowClassGroup

variable (R) [CommRing R] [IsDomain R]

/-- The 2-rank of the narrow ideal class group. -/
noncomputable abbrev twoRank : ℕ :=
  CommGroup.twoRank (NarrowClassGroup R)

end NarrowClassGroup
