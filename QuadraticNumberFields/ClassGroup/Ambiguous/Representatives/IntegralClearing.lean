/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QNFMathlib.RingTheory.FractionalIdeal.RingEquiv
import QuadraticNumberFields.ClassGroup.Ambiguous.RamifiedParity
import QuadraticNumberFields.ClassGroup.Ambiguous.Representatives.Coboundary
import QuadraticNumberFields.ClassGroup.Ambiguous.Representatives.InversionFixed
import QuadraticNumberFields.ClassGroup.Narrow.Basic

/-!
# Integral Clearing for Inversion-Fixed Narrow Classes

This file clears denominators to obtain conjugation-invariant integral
representatives, assembles ambiguous integral ideals in the same narrow class,
and proves `twoTorsion_le_fullRamifiedParityNarrowClassHom_range`.

The final cardinality estimate lives in
`QuadraticNumberFields.ClassGroup.Ambiguous.UpperBound`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace ClassGroup
namespace Ambiguous

open scoped nonZeroDivisors
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

section Hilbert90

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
local notation "conjOK" => conjAutRingOfIntegers (Qsqrtd (d : ℚ))

/-- A coboundary multiplier turns the relation `I * (x) = σ(I)` into the
fractional-ideal equality `I * (y) = σ(I) * (σ y)`. -/
private theorem fractionalRep_eq_conjAutFractionalRep_of_coboundary
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (𝓞 K))⁰)
    {x y : (FractionRing (𝓞 K))ˣ}
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K)) x =
        FractionalIdeal.mk0 (FractionRing (𝓞 K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
        toPrincipalIdeal (𝓞 K)
          (FractionRing (𝓞 K)) y =
      FractionalIdeal.mk0 (FractionRing (𝓞 K))
          (conjAutNonzeroIdealMulEquiv K I) *
        toPrincipalIdeal (𝓞 K)
          (FractionRing (𝓞 K))
          (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) := by
  let R := 𝓞 K
  let σy : (FractionRing R)ˣ :=
    Units.mapEquiv
      ((conjAutFractionRingAlgEquiv K).toRingEquiv : FractionRing R ≃* FractionRing R) y
  have hy' : y = x * σy := by
    rw [hy, mul_assoc, inv_mul_cancel, mul_one]
  conv_lhs => rw [hy', map_mul, ← mul_assoc, hconj]

/-- Rephrase the explicit conjugate-factorization equality as fixedness under
the fractional-ideal map induced by ring-of-integers conjugation. -/
private theorem ringEquivMap_conjAut_fractionalRep_eq_self_of_eq_conjAutFractionalRep
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (𝓞 K))⁰)
    (y : (FractionRing (𝓞 K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K)) y =
        FractionalIdeal.mk0 (FractionRing (𝓞 K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (𝓞 K))
        (L := FractionRing (𝓞 K))
        (conjAutRingOfIntegers K)
        (FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K)) y) =
      FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
        toPrincipalIdeal (𝓞 K)
          (FractionRing (𝓞 K)) y := by
  let R := 𝓞 K
  rw [FractionalIdeal.ringEquivMap_mul]
  have hmk0 :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R)
          (conjAutRingOfIntegers K)
          (FractionalIdeal.mk0 (FractionRing R) I) =
        FractionalIdeal.mk0 (FractionRing R) (conjAutNonzeroIdealMulEquiv K I) := by
    change
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R)
          (conjAutRingOfIntegers K)
          ((I : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) =
        (((conjAutNonzeroIdealMulEquiv K I : (Ideal R)⁰) : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R))
    rw [FractionalIdeal.ringEquivMap_coeIdeal]
    simp [coe_conjAutNonzeroIdealMulEquiv_apply]
  have hprincipal :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R)
          (conjAutRingOfIntegers K)
          (toPrincipalIdeal R (FractionRing R) y :
            FractionalIdeal R⁰ (FractionRing R)) =
        (toPrincipalIdeal R (FractionRing R)
          (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
            FractionalIdeal R⁰ (FractionRing R)) := by
    rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal,
      FractionalIdeal.ringEquivMap_spanSingleton]
    rfl
  rw [hmk0, hprincipal]
  exact (congrArg Units.val hfixed).symm

/-- A denominator-cleared integral representative using a conjugation-invariant
square denominator. If `a` is a denominator for `F`, this is
`(a * σ a ^ 2) * F.num`, whose associated fractional ideal is
`(a * σ a)^2 * F`. -/
private noncomputable def conjInvariantIntegralRep
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (𝓞 K)⁰
      (FractionRing (𝓞 K))) :
    Ideal (𝓞 K) :=
  let a : 𝓞 K := F.den
  let b : 𝓞 K := conjAutRingOfIntegers K a
  Ideal.span ({a * b ^ 2} : Set (𝓞 K)) * F.num

/-- The conjugation-invariant integral representative is nonzero when the
fractional ideal is nonzero. -/
private theorem conjInvariantIntegralRep_mem_nonZeroDivisors
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {F : FractionalIdeal (𝓞 K)⁰
      (FractionRing (𝓞 K))}
    (hF : F ≠ 0) :
    conjInvariantIntegralRep K F ∈ (Ideal (𝓞 K))⁰ := by
  let R := 𝓞 K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.den.prop
  have hb0 : b ≠ 0 :=
    fun hb => ha0 ((conjAutRingOfIntegers K).injective (by simpa [b] using hb))
  rw [conjInvariantIntegralRep]
  exact mul_mem
    ((Ideal.span_singleton_nonZeroDivisors (r := a * b ^ 2)).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr (mul_ne_zero ha0 (pow_ne_zero 2 hb0))))
    (by rwa [mem_nonZeroDivisors_iff_ne_zero, ne_eq, FractionalIdeal.num_eq_zero_iff])

/-- As a fractional ideal, the conjugation-invariant integral representative is
the original fractional ideal multiplied by a square denominator. -/
private theorem coe_conjInvariantIntegralRep
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (𝓞 K)⁰
      (FractionRing (𝓞 K))) :
    ((conjInvariantIntegralRep K F : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰
          (FractionRing (𝓞 K))) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K)
            (FractionRing (𝓞 K))
            (((F.den : 𝓞 K) *
              conjAutRingOfIntegers K (F.den : 𝓞 K)) ^ 2)) *
        F := by
  let R := 𝓞 K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  change ((Ideal.span ({a * b ^ 2} : Set R) * F.num : Ideal R) :
      FractionalIdeal R⁰ (FractionRing R)) =
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R (FractionRing R) ((a * b) ^ 2)) * F
  rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
    show (F.num : FractionalIdeal R⁰ (FractionRing R)) =
      FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a) * F by
        rw [FractionalIdeal.den_mul_self_eq_num'],
    ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
  congr 1
  simp [pow_two, mul_left_comm, mul_comm]

/-- The product of an algebraic integer and its conjugate is fixed by
ring-of-integers conjugation. -/
private theorem conjAutRingOfIntegers_mul_conj_fixed
    (K : Type) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (a : 𝓞 K) :
    conjAutRingOfIntegers K (a * conjAutRingOfIntegers K a) =
      a * conjAutRingOfIntegers K a := by
  rw [map_mul, conjAutRingOfIntegers_apply_apply, mul_comm]

/-- The conjugation-invariant integral representative is an ambiguous ideal when
the original fractional ideal is fixed by fractional-ideal conjugation. -/
private theorem conjInvariantIntegralRep_isAmbiguous
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (𝓞 K)⁰
      (FractionRing (𝓞 K)))ˣ)
    (hFfixed :
      FractionalIdeal.ringEquivMap
          (K := FractionRing (𝓞 K))
          (L := FractionRing (𝓞 K))
          (conjAutRingOfIntegers K) F.1 = F.1) :
    IsAmbiguousIdeal (conjAutRingOfIntegers K)
      (conjInvariantIntegralRep K F.1) := by
  let R := 𝓞 K
  let σ := conjAutRingOfIntegers K
  let c : R := (F.1.den : R) * σ (F.1.den : R)
  have hc : σ c = c := by
    simpa [c, σ] using conjAutRingOfIntegers_mul_conj_fixed K (F.1.den : R)
  have hzc :
      IsFractionRing.ringEquivOfRingEquiv
          (K := FractionRing R) (L := FractionRing R) σ
          (algebraMap R (FractionRing R) (c ^ 2)) =
        algebraMap R (FractionRing R) (c ^ 2) := by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap, map_pow, hc]
  have hmap :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R) σ
          ((conjInvariantIntegralRep K F.1 : Ideal R) :
            FractionalIdeal R⁰ (FractionRing R)) =
        ((conjInvariantIntegralRep K F.1 : Ideal R) :
          FractionalIdeal R⁰ (FractionRing R)) := by
    rw [coe_conjInvariantIntegralRep, FractionalIdeal.ringEquivMap_mul,
      FractionalIdeal.ringEquivMap_spanSingleton, hFfixed, hzc]
  have hmapIdeal :
      ((Ideal.map (σ : R →+* R) (conjInvariantIntegralRep K F.1) : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) =
      ((conjInvariantIntegralRep K F.1 : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) := by
    simpa [σ, FractionalIdeal.ringEquivMap_coeIdeal] using hmap
  exact (FractionalIdeal.coeIdeal_inj (K := FractionRing R)).mp hmapIdeal

/-- The conjugation-invariant integral representative differs from the original
fractional ideal by a totally positive principal multiplier. -/
private theorem exists_tp_multiplier_conjInvariantIntegralRep
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (𝓞 K)⁰
      (FractionRing (𝓞 K)))ˣ) :
    ∃ t : (FractionRing (𝓞 K))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (t : FractionRing (𝓞 K)) ∧
        FractionalIdeal.mk0 (FractionRing (𝓞 K))
            ⟨conjInvariantIntegralRep K F.1,
              conjInvariantIntegralRep_mem_nonZeroDivisors K F.ne_zero⟩ *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K)) t =
        F := by
  let R := 𝓞 K
  let a : R := F.1.den
  let b : R := conjAutRingOfIntegers K a
  let c : R := a * b
  let z : FractionRing R := algebraMap R (FractionRing R) c
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.1.den.prop
  have hb0 : b ≠ 0 :=
    fun hb => ha0 ((conjAutRingOfIntegers K).injective (by simpa [b] using hb))
  have hc0 : c ≠ 0 := mul_ne_zero ha0 hb0
  have hz0 : z ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr hc0)
  let t : (FractionRing R)ˣ := Units.mk0 (z⁻¹ ^ 2) (pow_ne_zero 2 (inv_ne_zero hz0))
  refine ⟨t, ?_, ?_⟩
  · exact NarrowClassGroup.isTotallyPositive_sq_of_ne_zero z⁻¹ (inv_ne_zero hz0)
  · apply Units.ext
    change
      ((conjInvariantIntegralRep K F.1 : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) *
          (toPrincipalIdeal R (FractionRing R) t :
            FractionalIdeal R⁰ (FractionRing R)) =
        F.1
    rw [coe_conjInvariantIntegralRep, coe_toPrincipalIdeal]
    have hzsq :
        algebraMap R (FractionRing R)
            (((F.1.den : R) *
              conjAutRingOfIntegers K (F.1.den : R)) ^ 2) =
          z ^ 2 := by
      simp [z, c, a, b, map_pow]
    have ht : (t : FractionRing R) = z⁻¹ ^ 2 := rfl
    rw [hzsq, ht]
    calc
      (FractionalIdeal.spanSingleton R⁰ (z ^ 2) * F.1) *
          FractionalIdeal.spanSingleton R⁰ (z⁻¹ ^ 2) =
          F.1 *
            (FractionalIdeal.spanSingleton R⁰ (z ^ 2) *
              FractionalIdeal.spanSingleton R⁰ (z⁻¹ ^ 2)) := by
        ac_rfl
      _ = F.1 * FractionalIdeal.spanSingleton R⁰ 1 := by
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton,
          show z ^ 2 * (z⁻¹ ^ 2) = 1 by rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]]
      _ = F.1 := by
        rw [FractionalIdeal.spanSingleton_one, mul_one]

/-- Integral clearing boundary for a conjugation-stable fractional representative.
If the fractional representative `I * (y)` matches its conjugate factorization,
then an ambiguous integral ideal represents the same narrow class, up to a
totally positive principal multiplier. -/
private theorem exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (𝓞 K))⁰)
    (y : (FractionRing (𝓞 K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K)) y =
        FractionalIdeal.mk0 (FractionRing (𝓞 K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (𝓞 K)
            (FractionRing (𝓞 K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    ∃ J : (Ideal (𝓞 K))⁰,
      IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (𝓞 K)) ∧
        ∃ t : (FractionRing (𝓞 K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (t : FractionRing (𝓞 K)) ∧
            FractionalIdeal.mk0 (FractionRing (𝓞 K)) J *
                toPrincipalIdeal (𝓞 K)
                  (FractionRing (𝓞 K)) t =
              FractionalIdeal.mk0 (FractionRing (𝓞 K)) I *
                toPrincipalIdeal (𝓞 K)
                  (FractionRing (𝓞 K)) y := by
  let R := 𝓞 K
  let F : (FractionalIdeal R⁰ (FractionRing R))ˣ :=
    FractionalIdeal.mk0 (FractionRing R) I *
      toPrincipalIdeal R (FractionRing R) y
  have hFfixed :
      FractionalIdeal.ringEquivMap
          (K := FractionRing R) (L := FractionRing R)
          (conjAutRingOfIntegers K) F.1 = F.1 := by
    simpa [F, R] using
      ringEquivMap_conjAut_fractionalRep_eq_self_of_eq_conjAutFractionalRep
        K I y hfixed
  let J : (Ideal R)⁰ :=
    ⟨conjInvariantIntegralRep K F.1,
      conjInvariantIntegralRep_mem_nonZeroDivisors K F.ne_zero⟩
  obtain ⟨t, htpos, ht⟩ := exists_tp_multiplier_conjInvariantIntegralRep K F
  refine ⟨J, ?_, t, htpos, ?_⟩
  · simpa [J, R] using conjInvariantIntegralRep_isAmbiguous K F hFfixed
  · simpa [J, F, R] using ht

/-- Every strict two-torsion class is represented by a full ramified-prime
parity vector. -/
theorem twoTorsion_le_fullRamifiedParityNarrowClassHom_range :
    NarrowClassGroup.twoTorsion OK ≤
      (fullRamifiedParityNarrowClassHom d).range := by
  intro C hC
  let C₂ : NarrowClassGroup.twoTorsion OK := ⟨C, hC⟩
  obtain ⟨I, hI, x, hxpos, hconj⟩ :=
    exists_integralIdeal_tp_multiplier_to_conjAut_of_twoTorsion C₂
  obtain ⟨y, hypos, hy⟩ :=
    exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
      d hxpos hconj
  obtain ⟨J, hJamb, t, htpos, ht⟩ :=
    exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq
      (Qsqrtd (d : ℚ)) I y
      (fractionalRep_eq_conjAutFractionalRep_of_coboundary
        (Qsqrtd (d : ℚ)) I hy hconj)
  have hJmk :
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing OK) I *
            toPrincipalIdeal OK (FractionRing OK) y) := by
    rw [← NarrowClassGroup.mk_mk0]
    exact NarrowClassGroup.mk_eq_mk.mpr ⟨⟨t, htpos⟩, ht⟩
  have hmk :
      NarrowClassGroup.mk (FractionalIdeal.mk0 (FractionRing OK) I) =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing OK) I *
            toPrincipalIdeal OK (FractionRing OK) y) :=
    NarrowClassGroup.mk_eq_mk.mpr ⟨⟨y, hypos⟩, rfl⟩
  have hJmk0 : NarrowClassGroup.mk0 J = NarrowClassGroup.mk0 I :=
    hJmk.trans hmk.symm
  refine ⟨Multiplicative.ofAdd (fullRamifiedParityVector d J), ?_⟩
  rw [← ambiguousIdeal_mk0_eq_fullRamifiedParityNarrowClassHom d J hJamb]
  exact hJmk0.trans (by simpa [C₂] using hI)

end Hilbert90

end Ambiguous
end ClassGroup
end QuadraticNumberFields
