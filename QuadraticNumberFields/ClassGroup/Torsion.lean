/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.ClassGroup
import QuadraticNumberFields.ClassGroup.Narrow
/-!
# Torsion in Class Groups

This file organizes ideal-theoretic torsion criteria for mathlib's ideal class
group.
-/

namespace Subgroup

/-- The subgroup of elements killed by the `n`th-power map in a multiplicative
group. This is the multiplicative-group analogue of `AddSubgroup.torsionBy`. -/
noncomputable abbrev powTorsion (G : Type*) [CommGroup G] (n : ℕ) : Subgroup G :=
  MonoidHom.ker (powMonoidHom (α := G) n)

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_powTorsion_iff (G : Type*) [CommGroup G] (n : ℕ) (x : G) :
    x ∈ powTorsion G n ↔ x ^ n = 1 :=
  Iff.rfl

end Subgroup

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The subgroup of ideal classes killed by the `n`th-power map. This is the
multiplicative class-group version of `AddSubgroup.torsionBy`. -/
noncomputable abbrev torsionBy (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Subgroup (ClassGroup R) :=
  Subgroup.powTorsion (ClassGroup R) n

/-- The two-torsion subgroup `Cl[2]` of the ideal class group. -/
noncomputable abbrev twoTorsion (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (ClassGroup R) :=
  torsionBy R 2

/-- The subgroup `Cl²` of square ideal classes. -/
noncomputable abbrev square (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (ClassGroup R) :=
  Subgroup.square (ClassGroup R)

/-- The square-class quotient `Cl / Cl²`. -/
abbrev squareQuotient (R : Type*) [CommRing R] [IsDomain R] :=
  ClassGroup R ⧸ square R

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_torsionBy_iff (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (C : ClassGroup R) :
    C ∈ torsionBy R n ↔ C ^ n = 1 := by
  exact Subgroup.mem_powTorsion_iff (ClassGroup R) n C

/-- Membership in `Cl[2]`. -/
theorem mem_twoTorsion_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ twoTorsion R ↔ C ^ 2 = 1 := by
  exact mem_torsionBy_iff R 2 C

/-- Membership in `Cl²`. -/
theorem mem_square_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ square R ↔ ∃ D : ClassGroup R, D ^ 2 = C := by
  simp [square, Subgroup.mem_square, IsSquare, pow_two, eq_comm]

/-- The mathlib square-subgroup definition agrees with the range of the square map. -/
theorem square_eq_powMonoidHom_range (R : Type*) [CommRing R] [IsDomain R] :
    square R = (powMonoidHom (α := ClassGroup R) 2).range := by
  ext C
  simp [square, Subgroup.mem_square, IsSquare, pow_two, eq_comm]

/-- For a finite class group, the square-class quotient has the same cardinality as
the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion
    (R : Type*) [CommRing R] [IsDomain R] [Finite (ClassGroup R)] :
    Nat.card (squareQuotient R) = Nat.card (twoTorsion R) := by
  haveI : (powMonoidHom (α := ClassGroup R) 2).ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  change Nat.card (ClassGroup R ⧸ square R) =
    Nat.card (twoTorsion R)
  rw [← Subgroup.index_eq_card]
  rw [square_eq_powMonoidHom_range, twoTorsion, torsionBy, Subgroup.powTorsion]
  rw [Subgroup.index_range]

local notation "Cl[" R "][" n "]" =>
  Subgroup.powTorsion (ClassGroup R) n

variable [IsDedekindDomain R]

/-- The `n`th power of the ideal class `mk0 I` is trivial exactly when the `n`th
power of the ideal `I` is principal. -/
@[simp]
theorem mk0_pow_eq_one_iff_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) (n : ℕ) :
    (mk0 I : ClassGroup R) ^ n = 1 ↔ ((I : Ideal R) ^ n).IsPrincipal := by
  rw [← map_pow, mk0_eq_one_iff, SubmonoidClass.coe_pow]

/-- The ideal class `mk0 I` lies in the `n`-power torsion subgroup `Cl[n]` exactly
when `I ^ n` is principal. -/
@[simp]
theorem mk0_mem_torsionBy_iff
    (I : nonZeroDivisors (Ideal R)) (n : ℕ) :
    mk0 I ∈ torsionBy R n ↔ ((I : Ideal R) ^ n).IsPrincipal := by
  rw [mem_torsionBy_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

/-- The ideal class `mk0 I` lies in the two-torsion subgroup `Cl[2]` exactly when
`I ^ 2` is principal. -/
@[simp]
theorem mk0_mem_twoTorsion_iff
    (I : nonZeroDivisors (Ideal R)) :
    mk0 I ∈ twoTorsion R ↔ ((I : Ideal R) ^ 2).IsPrincipal := by
  rw [mem_twoTorsion_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

end ClassGroup

namespace NarrowClassGroup

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The subgroup of narrow ideal classes killed by the `n`th-power map. This is
the narrow-class-group analogue of `ClassGroup.torsionBy`. -/
noncomputable abbrev torsionBy (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Subgroup (NarrowClassGroup R) :=
  Subgroup.powTorsion (NarrowClassGroup R) n

/-- The two-torsion subgroup `Cl⁺[2]` of the narrow ideal class group. -/
noncomputable abbrev twoTorsion (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (NarrowClassGroup R) :=
  torsionBy R 2

/-- The subgroup `Cl⁺²` of square narrow ideal classes. -/
noncomputable abbrev square (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (NarrowClassGroup R) :=
  Subgroup.square (NarrowClassGroup R)

/-- The narrow square-class quotient `Cl⁺ / Cl⁺²`. -/
abbrev squareQuotient (R : Type*) [CommRing R] [IsDomain R] :=
  NarrowClassGroup R ⧸ square R

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_torsionBy_iff (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (C : NarrowClassGroup R) :
    C ∈ torsionBy R n ↔ C ^ n = 1 :=
  Subgroup.mem_powTorsion_iff (NarrowClassGroup R) n C

/-- Membership in `Cl⁺[2]`. -/
theorem mem_twoTorsion_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : NarrowClassGroup R) :
    C ∈ twoTorsion R ↔ C ^ 2 = 1 :=
  mem_torsionBy_iff R 2 C

/-- The narrow square subgroup agrees with the range of the square map. -/
theorem square_eq_powMonoidHom_range (R : Type*) [CommRing R] [IsDomain R] :
    square R = (powMonoidHom (α := NarrowClassGroup R) 2).range := by
  ext C
  simp [square, Subgroup.mem_square, IsSquare, pow_two, eq_comm]

/-- For a finite narrow class group, the square-class quotient has the same
cardinality as the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion
    (R : Type*) [CommRing R] [IsDomain R] [Finite (NarrowClassGroup R)] :
    Nat.card (squareQuotient R) = Nat.card (twoTorsion R) := by
  haveI : (powMonoidHom (α := NarrowClassGroup R) 2).ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  change Nat.card (NarrowClassGroup R ⧸ square R) = Nat.card (twoTorsion R)
  rw [← Subgroup.index_eq_card]
  rw [square_eq_powMonoidHom_range, twoTorsion, torsionBy, Subgroup.powTorsion]
  rw [Subgroup.index_range]

end NarrowClassGroup
