/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.Algebra.Group.Subgroup.Even
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Torsion
import Mathlib.RingTheory.ClassGroup
import QNFMathlib.RingTheory.ClassGroup.Narrow
/-!
# Torsion in Class Groups

This file collects multiplicative torsion and square-subgroup helpers for
commutative groups, then specializes them to ordinary and narrow ideal class
groups. The ideal-theoretic lemmas at the end characterize torsion of
`ClassGroup.mk0` by principality of ideal powers.
-/

namespace Subgroup
variable (G) (n : ℕ)
variable [CommGroup G]

/-- The subgroup of elements killed by the `n`th-power map in a multiplicative
group. This is the multiplicative-group analogue of `AddSubgroup.torsionBy`. -/
noncomputable abbrev powTorsion : Subgroup G :=
  MonoidHom.ker (powMonoidHom (α := G) n)

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_powTorsion_iff (x : G) :
    x ∈ powTorsion G n ↔ x ^ n = 1 :=
  Iff.rfl

/-- The two-torsion subgroup of a multiplicative commutative group. -/
noncomputable abbrev twoTorsion : Subgroup G :=
  powTorsion G 2

/-- The quotient of a multiplicative commutative group by its square subgroup. -/
abbrev squareQuotient :=
  G ⧸ square G

/-- Membership in the two-torsion subgroup. -/
theorem mem_twoTorsion_iff (x : G) :
    x ∈ twoTorsion G ↔ x ^ 2 = 1 :=
  mem_powTorsion_iff G 2 x

/-- Membership in the square subgroup. -/
theorem mem_square_iff (x : G) :
    x ∈ square G ↔ ∃ y : G, y ^ 2 = x := by
  simp [Subgroup.square, IsSquare, pow_two, eq_comm]

/-- The square subgroup agrees with the range of the square map. -/
theorem square_eq_powMonoidHom_range :
    square G = (powMonoidHom (α := G) 2).range := by
  ext x
  simp [Subgroup.square, IsSquare, pow_two, eq_comm]

variable {G}
/-- For a finite commutative group, the square quotient has the same cardinality
as the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion [Finite G] :
    Nat.card (squareQuotient G) = Nat.card (twoTorsion G) := by
  simpa [squareQuotient, square_eq_powMonoidHom_range] using
    (Subgroup.index_range (f := powMonoidHom (α := G) 2))

/-- A two-torsion element has square one. -/
theorem twoTorsion_mul_self_eq_one (x : twoTorsion G) :
    (x.1 : G) * x.1 = 1 := by
  have hpow : (x.1 : G) ^ 2 = 1 :=
    (mem_twoTorsion_iff G x.1).mp x.2
  simpa [pow_two] using hpow

/-- A two-torsion element is fixed by inversion. -/
theorem twoTorsion_eq_inv (x : twoTorsion G) :
    (x.1 : G) = x.1⁻¹ :=
  (eq_inv_iff_mul_eq_one).2 (twoTorsion_mul_self_eq_one x)

end Subgroup

namespace ClassGroup

variable (R)
variable [CommRing R] [IsDomain R]

/-- The subgroup of ideal classes killed by the `n`th-power map. This is the
multiplicative class-group version of `AddSubgroup.torsionBy`. -/
noncomputable abbrev torsionBy (n : ℕ) : Subgroup (ClassGroup R) :=
  Subgroup.powTorsion (ClassGroup R) n

/-- The two-torsion subgroup `Cl[2]` of the ideal class group. -/
noncomputable abbrev twoTorsion : Subgroup (ClassGroup R) :=
  Subgroup.twoTorsion (ClassGroup R)

/-- The subgroup `Cl²` of square ideal classes. -/
noncomputable abbrev square : Subgroup (ClassGroup R) :=
  Subgroup.square (ClassGroup R)

/-- The square-class quotient `Cl / Cl²`. -/
abbrev squareQuotient :=
  Subgroup.squareQuotient (ClassGroup R)

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_torsionBy_iff (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (C : ClassGroup R) :
    C ∈ torsionBy R n ↔ C ^ n = 1 :=
  Subgroup.mem_powTorsion_iff (ClassGroup R) n C

/-- Membership in `Cl[2]`. -/
theorem mem_twoTorsion_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ twoTorsion R ↔ C ^ 2 = 1 :=
  Subgroup.mem_twoTorsion_iff (ClassGroup R) C

/-- Membership in `Cl²`. -/
theorem mem_square_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : ClassGroup R) :
    C ∈ square R ↔ ∃ D : ClassGroup R, D ^ 2 = C :=
  Subgroup.mem_square_iff (ClassGroup R) C

/-- The mathlib square-subgroup definition agrees with the range of the square map. -/
theorem square_eq_powMonoidHom_range (R : Type*) [CommRing R] [IsDomain R] :
    square R = (powMonoidHom (α := ClassGroup R) 2).range :=
  Subgroup.square_eq_powMonoidHom_range (ClassGroup R)

/-- For a finite class group, the square-class quotient has the same cardinality as
the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion
    (R : Type*) [CommRing R] [IsDomain R]
    [Finite (ClassGroup R)] :
    Nat.card (squareQuotient R) = Nat.card (twoTorsion R) := by
  simpa [squareQuotient, twoTorsion] using
    (Subgroup.card_squareQuotient_eq_card_twoTorsion)

variable {R}

/-- A two-torsion ideal class has square one. -/
theorem twoTorsion_mul_self_eq_one (C : twoTorsion R) :
    (C.1 : ClassGroup R) * C.1 = 1 :=
  Subgroup.twoTorsion_mul_self_eq_one C

/-- A two-torsion ideal class is fixed by inversion. -/
theorem twoTorsion_eq_inv (C : twoTorsion R) :
    (C.1 : ClassGroup R) = C.1⁻¹ :=
  Subgroup.twoTorsion_eq_inv C

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
  rw [mem_torsionBy_iff R n, mk0_pow_eq_one_iff_pow_isPrincipal]

/-- The ideal class `mk0 I` lies in the two-torsion subgroup `Cl[2]` exactly when
`I ^ 2` is principal. -/
@[simp]
theorem mk0_mem_twoTorsion_iff
    (I : nonZeroDivisors (Ideal R)) :
    mk0 I ∈ twoTorsion R ↔ ((I : Ideal R) ^ 2).IsPrincipal := by
  rw [mem_twoTorsion_iff R, mk0_pow_eq_one_iff_pow_isPrincipal]

end ClassGroup

namespace NarrowClassGroup

variable (R)
variable [CommRing R] [IsDomain R]

/-- The subgroup of narrow ideal classes killed by the `n`th-power map. This is
the narrow-class-group analogue of `ClassGroup.torsionBy`. -/
noncomputable abbrev torsionBy (n : ℕ) : Subgroup (NarrowClassGroup R) :=
  Subgroup.powTorsion (NarrowClassGroup R) n

/-- The two-torsion subgroup `Cl⁺[2]` of the narrow ideal class group. -/
noncomputable abbrev twoTorsion : Subgroup (NarrowClassGroup R) :=
  Subgroup.twoTorsion (NarrowClassGroup R)

/-- The subgroup `Cl⁺²` of square narrow ideal classes. -/
noncomputable abbrev square : Subgroup (NarrowClassGroup R) :=
  Subgroup.square (NarrowClassGroup R)

/-- The narrow square-class quotient `Cl⁺ / Cl⁺²`. -/
abbrev squareQuotient :=
  Subgroup.squareQuotient (NarrowClassGroup R)

/-- Membership in the subgroup killed by the `n`th-power map. -/
theorem mem_torsionBy_iff (R : Type*) [CommRing R] [IsDomain R]
    (n : ℕ) (C : NarrowClassGroup R) :
    C ∈ torsionBy R n ↔ C ^ n = 1 :=
  Subgroup.mem_powTorsion_iff (NarrowClassGroup R) n C

/-- Membership in `Cl⁺[2]`. -/
theorem mem_twoTorsion_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : NarrowClassGroup R) :
    C ∈ twoTorsion R ↔ C ^ 2 = 1 :=
  Subgroup.mem_twoTorsion_iff (NarrowClassGroup R) C

/-- Membership in `Cl⁺²`. -/
theorem mem_square_iff (R : Type*) [CommRing R] [IsDomain R]
    (C : NarrowClassGroup R) :
    C ∈ square R ↔ ∃ D : NarrowClassGroup R, D ^ 2 = C :=
  Subgroup.mem_square_iff (NarrowClassGroup R) C

/-- The narrow square subgroup agrees with the range of the square map. -/
theorem square_eq_powMonoidHom_range (R : Type*) [CommRing R] [IsDomain R] :
    square R = (powMonoidHom (α := NarrowClassGroup R) 2).range :=
  Subgroup.square_eq_powMonoidHom_range (NarrowClassGroup R)

/-- For a finite narrow class group, the square-class quotient has the same
cardinality as the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion
    (R : Type*) [CommRing R] [IsDomain R]
    [Finite (NarrowClassGroup R)] :
    Nat.card (squareQuotient R) = Nat.card (twoTorsion R) := by
  simpa [squareQuotient, twoTorsion] using
    (Subgroup.card_squareQuotient_eq_card_twoTorsion)

variable {R}

/-- A narrow two-torsion class has square one. -/
theorem twoTorsion_mul_self_eq_one (C : twoTorsion R) :
    (C.1 : NarrowClassGroup R) * C.1 = 1 :=
  Subgroup.twoTorsion_mul_self_eq_one C

/-- A narrow two-torsion class is fixed by inversion. -/
theorem twoTorsion_eq_inv (C : twoTorsion R) :
    (C.1 : NarrowClassGroup R) = C.1⁻¹ :=
  Subgroup.twoTorsion_eq_inv C

end NarrowClassGroup

/-
Exact Sequence
1 → Cl⁺(R)[2] → Cl⁺(R) → Cl⁺(R)² → 1
Definition of narrow class group. 1 → P⁺(R) → I(R) → Cl⁺(R) → 1.
1 → (O R)ˣ⁺ → (Rˣ)⁺ → P⁺(R) → 1
rank F₂ Cl⁺(R)[2] =t-1
-/
