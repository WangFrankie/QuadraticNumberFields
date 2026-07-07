/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.FractionalIdeal.RingEquiv
import QuadraticNumberFields.ClassGroup.Ambiguous.RamifiedParity
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

/-!
# Inversion-Fixed Class Representatives

First step of the representative-recovery layer: turn inversion-fixed narrow
classes into integral ideal representatives related to their conjugates by totally
positive principal multipliers.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors NumberField Pointwise

section ClassLevel

/-- If a nonzero integral ideal represents an inversion-fixed narrow class, then
its square represents the trivial narrow class. -/
theorem narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {C : InversionFixedClass R} {I : (Ideal R)⁰}
    (hI : NarrowClassGroup.mk0 I = C.1) :
    NarrowClassGroup.mk0 (I * I) = 1 := by
  have hmul : (C.1 : NarrowClassGroup R) * C.1 = 1 := by
    nth_rewrite 1 [C.2]
    rw [inv_mul_cancel]
  rw [map_mul, hI]
  exact hmul

/-- An inversion-fixed narrow class has a nonzero integral ideal representative
whose square is cancelled by a totally positive principal fractional ideal. -/
theorem exists_integralIdeal_square_principal_relation_of_inversionFixedClass
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (C : InversionFixedClass R) :
    ∃ I : (Ideal R)⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : NarrowClassGroup.totallyPositiveUnits (FractionRing R),
          (FractionalIdeal.mk0 (FractionRing R) I) ^ 2 *
              NarrowClassGroup.toNarrowPrincipalIdeal R (FractionRing R) x =
            1 := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  refine ⟨I, hI, ?_⟩
  have hsq :
      NarrowClassGroup.mk0 (I * I) = (1 : NarrowClassGroup R) :=
    narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed hI
  obtain ⟨x, hxpos, hx⟩ :=
    (NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring (I := I * I)).mp hsq
  refine ⟨⟨x, hxpos⟩, ?_⟩
  simpa [pow_two, NarrowClassGroup.toNarrowPrincipalIdeal] using hx

/-- An inversion-fixed narrow class has an integral ideal representative whose
conjugate differs from it by a totally positive principal fractional ideal. -/
theorem exists_integralIdeal_tp_multiplier_to_conjAut_of_inversionFixedClass
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (C : InversionFixedClass (NumberField.RingOfIntegers K)) :
    ∃ I : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 I = C.1 ∧
        ∃ x : (FractionRing (NumberField.RingOfIntegers K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (x : FractionRing (NumberField.RingOfIntegers K)) ∧
            FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) x =
              FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
                (conjAutNonzeroIdealMulEquiv K I) := by
  obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C.1
  refine ⟨I, hI, ?_⟩
  have hconj :
      NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) = C.1 := by
    calc
      NarrowClassGroup.mk0 (conjAutNonzeroIdealMulEquiv K I) =
          (NarrowClassGroup.mk0 I)⁻¹ :=
        narrowClassGroup_mk0_map_conjAut_eq_inv K I
      _ = C.1⁻¹ := by rw [hI]
      _ = C.1 := C.2.symm
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp
    (hI.trans hconj.symm)


end ClassLevel

end Ambiguous
end ClassGroup
end QuadraticNumberFields
