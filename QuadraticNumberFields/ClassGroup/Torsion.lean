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

variable {G}

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

/-- For a finite commutative group, the square quotient has the same cardinality
as the two-torsion subgroup. -/
theorem card_squareQuotient_eq_card_twoTorsion [Finite G] :
    Nat.card (squareQuotient G) = Nat.card (twoTorsion G) := by
  simpa [squareQuotient, square_eq_powMonoidHom_range] using
    (Subgroup.index_range (f := powMonoidHom (α := G) 2))

/-- A two-torsion element has square one. -/
theorem twoTorsion_mul_self_eq_one (x : twoTorsion G) :
    (x.1 : G) * x.1 = 1 := by
  simpa [pow_two] using (mem_twoTorsion_iff x.1).mp x.2

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

variable {R}

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
theorem mk0_mem_torsionBy_iff
    (I : nonZeroDivisors (Ideal R)) (n : ℕ) :
    mk0 I ∈ torsionBy R n ↔ ((I : Ideal R) ^ n).IsPrincipal := by
  rw [torsionBy, Subgroup.mem_powTorsion_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

/-- The ideal class `mk0 I` lies in the two-torsion subgroup `Cl[2]` exactly when
`I ^ 2` is principal. -/
theorem mk0_mem_twoTorsion_iff
    (I : nonZeroDivisors (Ideal R)) :
    mk0 I ∈ twoTorsion R ↔ ((I : Ideal R) ^ 2).IsPrincipal := by
  rw [twoTorsion, Subgroup.mem_twoTorsion_iff, mk0_pow_eq_one_iff_pow_isPrincipal]

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

variable {R}

section DedekindDomain

variable [IsDedekindDomain R]

/-- If `[I] = C` and `C ∈ Cl⁺(R)[2]`, then `[I]² = 1`. -/
theorem mk0_mul_self_eq_one_of_twoTorsion
    {C : twoTorsion R} {I : nonZeroDivisors (Ideal R)}
    (hI : mk0 I = C.1) :
    mk0 (I * I) = 1 := by
  simpa only [map_mul, hI] using Subgroup.twoTorsion_mul_self_eq_one C

/-- Choose a representative `I` of a strict two-torsion class `C` and a totally
positive principal multiplier `P⁺(x)` with `[I] = C` and `I² · P⁺(x) = 1`. -/
theorem exists_integralIdeal_square_principal_relation_of_twoTorsion
    (C : twoTorsion R) :
    ∃ I : nonZeroDivisors (Ideal R),
      mk0 I = C.1 ∧
        ∃ x : totallyPositiveUnits (FractionRing R),
          (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 *
              toNarrowPrincipalIdeal R (FractionRing R) x =
            1 := by
  obtain ⟨I, hI⟩ := mk0_surjective C.1
  obtain ⟨x, hxpos, hx⟩ :=
    (mk0_eq_one_iff_exists_fraction_ring (I := I * I)).mp
      (mk0_mul_self_eq_one_of_twoTorsion hI)
  exact ⟨I, hI, ⟨⟨x, hxpos⟩, by
    simpa [pow_two, toNarrowPrincipalIdeal] using hx⟩⟩

end DedekindDomain

end NarrowClassGroup

/-
Exact Sequence
1 → Cl⁺(R)[2] → Cl⁺(R) → Cl⁺(R)² → 1
Definition of narrow class group. 1 → P⁺(R) → I(R) → Cl⁺(R) → 1.
1 → (O R)ˣ⁺ → (Rˣ)⁺ → P⁺(R) → 1
rank F₂ Cl⁺(R)[2] =t-1
-/
