/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Norm
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Representatives

/-!
# Descent Of Genus Characters

This file proves that each raw genus character is constant on the fibers of
the restricted narrow class map, then descends it to the narrow class group.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

private theorem exists_totallyPositive_generator_of_mk0_eq_one
    (I : (Ideal OK)⁰) (hI : NarrowClassGroup.mk0 I = 1) :
    ∃ a : OK, NarrowClassGroup.IsTotallyPositive (algebraMap OK (FractionRing OK) a) ∧
      Ideal.span ({a} : Set OK) = (I : Ideal OK) := by
  obtain ⟨x, hxpos, hx⟩ :=
    (NarrowClassGroup.mk0_eq_one_iff_exists_fraction_ring (I := I)).mp hI
  have hI_frac :
      ((I : Ideal OK) : FractionalIdeal OK⁰ (FractionRing OK)) =
        FractionalIdeal.spanSingleton OK⁰ (x⁻¹ : FractionRing OK) := by
    simpa [coe_toPrincipalIdeal] using
      congrArg Units.val (eq_inv_of_mul_eq_one_left hx)
  have hxinv_mem : (x⁻¹ : FractionRing OK) ∈
      ((I : Ideal OK) : FractionalIdeal OK⁰ (FractionRing OK)) := by
    rw [hI_frac]
    exact (FractionalIdeal.mem_spanSingleton OK⁰).mpr ⟨1, by simp⟩
  obtain ⟨a, _haI, ha⟩ := (FractionalIdeal.mem_coeIdeal OK⁰).mp hxinv_mem
  have hainvpos : NarrowClassGroup.IsTotallyPositive (x⁻¹ : FractionRing OK) := by
    intro σ
    simpa using inv_pos.mpr (hxpos σ)
  refine ⟨a, by simpa [ha] using hainvpos, ?_⟩
  apply FractionalIdeal.coeIdeal_injective (K := FractionRing OK)
  change
    ((Ideal.span ({a} : Set OK) : Ideal OK) : FractionalIdeal OK⁰ (FractionRing OK)) =
      ((I : Ideal OK) : FractionalIdeal OK⁰ (FractionRing OK))
  rw [FractionalIdeal.coeIdeal_span_singleton, ha]
  exact hI_frac.symm

private theorem rawGenusCharacter_eq_one_of_narrowMk0_eq_one
    (p : RamifiedPrimeIndex d) (I : GenusCoprimeIdeal d)
    (hI : narrowMk0OnGenusCoprimeIdeals d I = 1) :
    rawGenusCharacter d p I = 1 := by
  have hI_mk0 : NarrowClassGroup.mk0 I.1 = 1 := by
    simpa [narrowMk0OnGenusCoprimeIdeals] using hI
  obtain ⟨a, hapos, ha⟩ :=
    exists_totallyPositive_generator_of_mk0_eq_one d I.1 hI_mk0
  apply Units.ext
  change kroneckerSymNat (primeDiscriminantFactor d p)
      (Ideal.absNorm (I.1.1 : Ideal OK)) = 1
  rw [← ha]
  exact kroneckerSymNat_primeDiscriminantFactor_absNorm_span_eq_one d p
    (algebraNorm_nonneg_of_isTotallyPositive d hapos)
    (by simpa [ha] using genusCoprimeIdeal_coprime_factor d I p)

/-- A raw genus character depends only on the narrow class of its
discriminant-coprime ideal. -/
theorem rawGenusCharacter_eq_of_narrowMk0_eq
    (p : RamifiedPrimeIndex d) (I J : GenusCoprimeIdeal d)
    (hIJ : narrowMk0OnGenusCoprimeIdeals d I =
      narrowMk0OnGenusCoprimeIdeals d J) :
    rawGenusCharacter d p I = rawGenusCharacter d p J := by
  obtain ⟨K, hK⟩ := exists_genusCoprimeIdeal_mk0_eq d
    ((narrowMk0OnGenusCoprimeIdeals d I)⁻¹)
  have hIK : narrowMk0OnGenusCoprimeIdeals d (I * K) = 1 := by
    rw [map_mul, hK, mul_inv_cancel]
  have hJK : narrowMk0OnGenusCoprimeIdeals d (J * K) = 1 := by
    rw [map_mul, ← hIJ, hK, mul_inv_cancel]
  apply mul_right_cancel (b := rawGenusCharacter d p K)
  calc
    rawGenusCharacter d p I * rawGenusCharacter d p K =
        rawGenusCharacter d p (I * K) := (map_mul (rawGenusCharacter d p) I K).symm
    _ = 1 := rawGenusCharacter_eq_one_of_narrowMk0_eq_one d p (I * K) hIK
    _ = rawGenusCharacter d p (J * K) :=
      (rawGenusCharacter_eq_one_of_narrowMk0_eq_one d p (J * K) hJK).symm
    _ = rawGenusCharacter d p J * rawGenusCharacter d p K :=
      map_mul (rawGenusCharacter d p) J K

/-- The genus character associated to a ramified rational prime. -/
noncomputable def genusCharacter (p : RamifiedPrimeIndex d) :
    Cl⁺(d) →* ℤˣ where
  toFun C := rawGenusCharacter d p
    (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d C))
  map_one' := by
    calc
      rawGenusCharacter d p
          (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d 1)) =
          rawGenusCharacter d p 1 :=
        rawGenusCharacter_eq_of_narrowMk0_eq d p _ _ (by
          rw [Classical.choose_spec (narrowMk0OnGenusCoprimeIdeals_surjective d 1)]
          exact (map_one (narrowMk0OnGenusCoprimeIdeals d)).symm)
      _ = 1 := map_one (rawGenusCharacter d p)
  map_mul' C D := by
    calc
      rawGenusCharacter d p
          (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d (C * D))) =
          rawGenusCharacter d p
            (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d C) *
              Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d D)) :=
        rawGenusCharacter_eq_of_narrowMk0_eq d p _ _ (by
          rw [Classical.choose_spec
            (narrowMk0OnGenusCoprimeIdeals_surjective d (C * D)), map_mul,
            Classical.choose_spec (narrowMk0OnGenusCoprimeIdeals_surjective d C),
            Classical.choose_spec (narrowMk0OnGenusCoprimeIdeals_surjective d D)])
      _ = rawGenusCharacter d p
            (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d C)) *
          rawGenusCharacter d p
            (Classical.choose (narrowMk0OnGenusCoprimeIdeals_surjective d D)) :=
        map_mul (rawGenusCharacter d p) _ _

/-- A descended genus character is computed by the raw Kronecker character on
any discriminant-coprime representative. -/
@[simp]
theorem genusCharacter_apply_mk0
    (p : RamifiedPrimeIndex d) (I : GenusCoprimeIdeal d) :
    genusCharacter d p (narrowMk0OnGenusCoprimeIdeals d I) =
      rawGenusCharacter d p I :=
  rawGenusCharacter_eq_of_narrowMk0_eq d p _ I
    (Classical.choose_spec
      (narrowMk0OnGenusCoprimeIdeals_surjective d
        (narrowMk0OnGenusCoprimeIdeals d I)))

end GenusTheory
end ClassGroup
end QuadraticNumberFields
