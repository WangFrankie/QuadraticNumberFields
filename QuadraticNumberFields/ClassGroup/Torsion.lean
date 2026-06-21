/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.ClassGroup
/-!
# Torsion in Class Groups

This file organizes ideal-theoretic torsion criteria for mathlib's ideal class
group.
-/

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The subgroup of ideal classes killed by the `n`th-power map. This is the
multiplicative class-group version of `AddSubgroup.torsionBy`. -/
noncomputable abbrev torsionBySubgroup (R : Type*) [CommRing R] [IsDomain R] (n : ℕ) :
    Subgroup (ClassGroup R) :=
  MonoidHom.ker (powMonoidHom (α :=ClassGroup R) n)

/-- The two-torsion subgroup `Cl[2]` of the ideal class group. -/
noncomputable abbrev twoTorsionSubgroup (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (ClassGroup R) :=
  torsionBySubgroup R 2

/-- The subgroup `Cl²` of square ideal classes. -/
noncomputable abbrev squareSubgroup (R : Type*) [CommRing R] [IsDomain R] :
    Subgroup (ClassGroup R) :=
  Subgroup.square (ClassGroup R)

/-- The square-class quotient `Cl / Cl²`. -/
abbrev squareQuotient (R : Type*) [CommRing R] [IsDomain R] :=
  ClassGroup R ⧸ squareSubgroup R

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_torsionBySubgroup_iff (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (C : ClassGroup R) :
    C ∈ torsionBySubgroup R n ↔ C ^ n = 1 := by
  rfl

/-- Membership in `Cl[2]`. -/
theorem mem_twoTorsionSubgroup_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ twoTorsionSubgroup R ↔ C ^ 2 = 1 := by
  rfl

/-- Membership in `Cl²`. -/
theorem mem_squareSubgroup_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ squareSubgroup R ↔ ∃ D : ClassGroup R, D ^ 2 = C := by
  rw [squareSubgroup, Subgroup.mem_square]
  constructor
  · rintro ⟨D, hD⟩
    exact ⟨D, by simpa [pow_two] using hD.symm⟩
  · rintro ⟨D, hD⟩
    exact ⟨D, by simpa [pow_two] using hD.symm⟩

/-- The mathlib square-subgroup definition agrees with the range of the square map. -/
theorem squareSubgroup_eq_powMonoidHom_range (R : Type*) [CommRing R] [IsDomain R] :
    squareSubgroup R = (powMonoidHom (α := ClassGroup R) 2).range := by
  ext C
  constructor
  · intro hC
    rcases (Subgroup.mem_square.mp hC) with ⟨D, hD⟩
    exact ⟨D, by simpa [pow_two] using hD.symm⟩
  · intro hC
    rcases hC with ⟨D, hD⟩
    exact Subgroup.mem_square.mpr ⟨D, by simpa [pow_two] using hD.symm⟩

/-- For a finite class group, the square-class quotient has the same cardinality as
the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsionSubgroup
    (R : Type*) [CommRing R] [IsDomain R] [Finite (ClassGroup R)] :
    Nat.card (squareQuotient R) = Nat.card (twoTorsionSubgroup R) := by
  haveI : (powMonoidHom (α := ClassGroup R) 2).ker.FiniteIndex :=
    Subgroup.finiteIndex_of_finite
  change Nat.card (ClassGroup R ⧸ squareSubgroup R) =
    Nat.card (twoTorsionSubgroup R)
  rw [← Subgroup.index_eq_card]
  rw [squareSubgroup_eq_powMonoidHom_range, twoTorsionSubgroup, torsionBySubgroup]
  rw [Subgroup.index_range]

local notation "Cl[" R "][" n "]" =>
  MonoidHom.ker (powMonoidHom (α := ClassGroup R) n)

variable [IsDedekindDomain R]
/-- If a power of a nonzero integral ideal is principal, then the same power of its
ideal class is trivial. -/
theorem mk0_pow_eq_one_of_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) {n : ℕ} (hI : ((I : Ideal R) ^ n).IsPrincipal) :
    (mk0 I : ClassGroup R) ^ n = 1 := by
  rw [← map_pow]
  rw [mk0_eq_one_iff]
  exact hI

/-- If a positive power of a nonzero integral ideal is principal, its ideal class is
torsion. -/
theorem mk0_mem_torsion_of_pow_isPrincipal
    (I : nonZeroDivisors (Ideal R)) {n : ℕ} (hn : 0 < n)
    (hI : ((I : Ideal R) ^ n).IsPrincipal) :
    mk0 I ∈ CommGroup.torsion (ClassGroup R) := by
  rw [CommGroup.mem_torsion]
  rw [isOfFinOrder_iff_pow_eq_one]
  exact ⟨n, hn, mk0_pow_eq_one_of_pow_isPrincipal I hI⟩

/-- If the square of a nonzero integral ideal is principal, then the square of its
ideal class is trivial. -/
theorem mk0_sq_eq_one_of_sq_isPrincipal
    (I : nonZeroDivisors (Ideal R)) (hI : ((I : Ideal R) ^ 2).IsPrincipal) :
    (mk0 I : ClassGroup R) ^ 2 = 1 :=
  mk0_pow_eq_one_of_pow_isPrincipal I hI

/-- If the square of a nonzero integral ideal is principal, its ideal class lies
in `Cl[2]`. -/
theorem mk0_mem_twoTorsionSubgroup_of_sq_isPrincipal
    (I : nonZeroDivisors (Ideal R)) (hI : ((I : Ideal R) ^ 2).IsPrincipal) :
    mk0 I ∈ twoTorsionSubgroup R := by
  rw [mem_twoTorsionSubgroup_iff]
  exact mk0_sq_eq_one_of_sq_isPrincipal I hI

/-- A span-shaped square relation is a convenient way to produce two-torsion
ideal classes. This is the ideal-theoretic shape used for ramified primes. -/
theorem mk0_mem_twoTorsionSubgroup_of_square_eq_span
    (I : nonZeroDivisors (Ideal R)) {a : R}
    (hI : (I : Ideal R) ^ 2 = Ideal.span ({a} : Set R)) :
    mk0 I ∈ twoTorsionSubgroup R := by
  refine mk0_mem_twoTorsionSubgroup_of_sq_isPrincipal I ?_
  rw [hI]
  change (Submodule.span R ({a} : Set R)).IsPrincipal
  exact ⟨a, rfl⟩

end ClassGroup
