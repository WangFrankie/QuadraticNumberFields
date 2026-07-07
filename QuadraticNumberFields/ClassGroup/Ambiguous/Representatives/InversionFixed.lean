/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.Conjugation
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Strict Two-Torsion Class Representatives

First step of the representative-recovery layer: turn strict two-torsion narrow
classes into integral ideal representatives related to their conjugates by
totally positive principal multipliers.

The lemmas record the formulas used downstream:

* if `[I] = C` and `C ∈ Cl⁺(R)[2]`, then `[I]² = 1`;
* one can choose `I` and a totally positive multiplier `x` with
  `I² · P⁺(x) = 1`;
* over a quadratic field, one can choose `I` and totally positive `x` with
  `I · (x) = conj(I)`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors

section DedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- If `[I] = C` and `C ∈ Cl⁺(R)[2]`, then `[I]² = 1`.

Equivalently, a representative of a strict two-torsion class has square in the
trivial narrow class. -/
theorem narrowClassGroup_mk0_mul_self_eq_one_of_twoTorsion
    {C : NarrowClassGroup.twoTorsion R} {I : (Ideal R)⁰}
    (hI : NarrowClassGroup.mk0 I = C.1) :
    NarrowClassGroup.mk0 (I * I) = 1 := by
  simpa [map_mul, hI] using NarrowClassGroup.twoTorsion_mul_self_eq_one C

/-- Choose a representative `I` of a strict two-torsion class `C` and a totally
positive principal multiplier `P⁺(x)` with `[I] = C` and `I² · P⁺(x) = 1`.

This is the fractional-ideal version of `[I]² = 1`. -/
theorem exists_integralIdeal_square_principal_relation_of_twoTorsion
    (C : NarrowClassGroup.twoTorsion R) :
    ∃ I : (Ideal R)⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : NarrowClassGroup.totallyPositiveUnits (FractionRing R),
          (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 *
              NarrowClassGroup.toNarrowPrincipalIdeal R (FractionRing R) x =
            1 := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  obtain ⟨x, hxpos, hx⟩ :=
    (NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring (I := I * I)).mp
      (narrowClassGroup_mk0_mul_self_eq_one_of_twoTorsion hI)
  exact ⟨I, hI, ⟨⟨x, hxpos⟩, by
    simpa [pow_two, NarrowClassGroup.toNarrowPrincipalIdeal] using hx⟩⟩

end DedekindDomain

section QuadraticField

variable {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
  [QuadraticField K] [QuadraticField.Conj K]

/-- Over a quadratic field, choose an integral representative `I` of a strict
two-torsion class and a totally positive `x ∈ Frac(𝓞 K)ˣ` with
`[I] = C` and `I · (x) = conj(I)`.

This is the representative relation used before clearing denominators. -/
theorem exists_integralIdeal_tp_multiplier_to_conjAut_of_twoTorsion
    (C : NarrowClassGroup.twoTorsion (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : (FractionRing (𝓞 K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (x : FractionRing (𝓞 K)) ∧
            FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
                toPrincipalIdeal (𝓞 K)
                  (FractionRing (𝓞 K)) x =
              FractionalIdeal.mk0 (FractionRing (𝓞 K))
                (conjAutNonzeroIdealMulEquiv K I) := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  refine ⟨I, hI, ?_⟩
  have hconj :
      NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) = C.1 := by
    rw [narrowClassGroup_mk0_map_conjAut_eq_inv K I, hI]
    exact (NarrowClassGroup.twoTorsion_eq_inv C).symm
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp
    (hI.trans hconj.symm)

end QuadraticField

end Ambiguous
end ClassGroup
end QuadraticNumberFields
