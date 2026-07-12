/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import QuadraticNumberFields.ClassGroup.GenusTheory.GenusTheorem
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Ordinary Square Classes and the Narrow-to-Wide Correction

This file compares the square-class quotients of the narrow and ordinary class
groups of `ℚ(√d)`.  The ordinary genus formula differs from the uniform narrow
formula only by the kernel of the induced map

`Cl⁺(d) / Cl⁺(d)² → Cl(d) / Cl(d)²`.

The statements use `ramifiedPrimeCount d` directly and do not split into cases
according to the residue class of `d`.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped NumberField QuadraticNumberFields.ClassGroup
open CommGroup

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" =>
  NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The natural map `Cl⁺(d) → Cl(d)` descends to square quotients. -/
noncomputable def narrowSquareQuotientToClassGroup :
    squareQuotient (Cl⁺(d)) →* squareQuotient (Cl(d)) :=
  squareQuotientMap (Qsqrtd.narrowToClassGroup d)

@[simp]
theorem narrowSquareQuotientToClassGroup_mk' (C : Cl⁺(d)) :
    narrowSquareQuotientToClassGroup d
        (C : squareQuotient (Cl⁺(d))) =
      QuotientGroup.mk' (Subgroup.square (Cl(d))) (Qsqrtd.narrowToClassGroup d C) :=
  squareQuotientMap_mk (Qsqrtd.narrowToClassGroup d) C

/-- The map from narrow to ordinary square classes is surjective. -/
theorem narrowSquareQuotientToClassGroup_surjective :
    Function.Surjective (narrowSquareQuotientToClassGroup d) :=
  squareQuotientMap_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- The map from narrow to ordinary square classes as a linear map over `ZMod 2`. -/
noncomputable def narrowSquareQuotientLinearMap :
    Additive (squareQuotient (Cl⁺(d))) →ₗ[ZMod 2]
      Additive (squareQuotient (Cl(d))) :=
  squareQuotientLinearMap (Qsqrtd.narrowToClassGroup d)

/-- The linear map from narrow to ordinary square classes is surjective. -/
theorem narrowSquareQuotientLinearMap_surjective :
    Function.Surjective (narrowSquareQuotientLinearMap d) :=
  squareQuotientLinearMap_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- The correction kernel is the image of `ker(Cl⁺(d) → Cl(d))` in the narrow
square-class quotient. -/
theorem narrowSquareQuotientToClassGroup_ker_eq_map_narrowToClassGroup_ker :
    (narrowSquareQuotientToClassGroup d).ker =
      Subgroup.map (QuotientGroup.mk' (Subgroup.square (Cl⁺(d))))
        (Qsqrtd.narrowToClassGroup d).ker :=
  squareQuotientMap_ker_eq_map_ker_of_surjective (Qsqrtd.narrowToClassGroup d)
    (NarrowClassGroup.toClassGroup_surjective OK)

/-- The ordinary 2-rank plus the dimension of the correction kernel is `t - 1`. -/
theorem twoRank_classGroup_add_correction_eq_ramifiedPrimeCount_sub_one :
    ClassGroup.twoRank OK +
        Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker =
      ramifiedPrimeCount d - 1 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hrank := (narrowSquareQuotientLinearMap d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (narrowSquareQuotientLinearMap_surjective d),
    finrank_top] at hrank
  calc
    ClassGroup.twoRank OK +
          Module.finrank (ZMod 2) (narrowSquareQuotientLinearMap d).ker =
        NarrowClassGroup.twoRank OK := by
      simpa [ClassGroup.twoRank, NarrowClassGroup.twoRank, CommGroup.twoRank] using hrank
    _ = ramifiedPrimeCount d - 1 :=
      twoRank_narrowClassGroup_eq_ramifiedPrimeCount_sub_one d

/-- The cardinalities of the ordinary square-class group and the correction
kernel multiply to `2 ^ (t - 1)`. -/
theorem card_squareClassGroup_mul_correction_eq_two_pow_sub_one :
    Nat.card (narrowSquareQuotientToClassGroup d).ker *
        Nat.card (squareQuotient (Cl(d))) =
      2 ^ (ramifiedPrimeCount d - 1) := by
  have hcard :=
    MonoidHom.nat_card_eq_card_ker_mul_card_of_surjective
      (narrowSquareQuotientToClassGroup d)
      (narrowSquareQuotientToClassGroup_surjective d)
  rw [card_narrowSquareClassGroup_eq_two_pow_sub_one d] at hcard
  exact hcard.symm

end GenusTheory
end ClassGroup
end QuadraticNumberFields
