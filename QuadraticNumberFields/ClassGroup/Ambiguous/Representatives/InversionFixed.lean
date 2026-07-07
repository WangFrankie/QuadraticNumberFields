/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Ambiguous.Conjugation
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.ClassGroup.Torsion

/-!
# Quadratic Representatives of Strict Two-Torsion Classes

Quadratic-field step of the representative-recovery layer: start from the
generic two-torsion representative API in `NarrowClassGroup` and turn a strict
two-torsion narrow class into an integral ideal representative related to its
conjugate by a totally positive principal multiplier.

The main lemma records the formula used before clearing denominators:
for `C ∈ Cl⁺(𝓞 K)[2]`, choose `I` and totally positive `x` with
`[I] = C` and `I · (x) = conj(I)`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors

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
    exact (Subgroup.twoTorsion_eq_inv C).symm
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp
    (hI.trans hconj.symm)

end QuadraticField

end Ambiguous
end ClassGroup
end QuadraticNumberFields
