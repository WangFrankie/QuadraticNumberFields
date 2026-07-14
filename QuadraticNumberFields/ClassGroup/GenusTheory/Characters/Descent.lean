/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Norm
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Representatives
import QuadraticNumberFields.ClassGroup.Narrow.Principal

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

private theorem exists_generator_of_narrowToClassGroup_eq_one
    (I : GenusCoprimeIdeal d)
    (hI : Qsqrtd.narrowToClassGroup d
      (narrowMk0OnGenusCoprimeIdeals d I) = 1) :
    ∃ α : OK, Ideal.span ({α} : Set OK) = (I.1.1 : Ideal OK) := by
  have hwide : ClassGroup.mk0 I.1 = 1 := by
    rw [← NarrowClassGroup.toClassGroup_mk0]
    simpa [narrowMk0OnGenusCoprimeIdeals] using hI
  obtain ⟨α, hα⟩ :=
    (Submodule.isPrincipal_iff (I.1.1 : Ideal OK)).mp
      ((ClassGroup.mk0_eq_one_iff I.1.2).mp hwide)
  exact ⟨α, hα.symm⟩

private theorem narrowMk0_eq_one_of_generator_algebraNorm_pos
    (hd : 0 < d) (I : GenusCoprimeIdeal d) {α : OK}
    (hα : Ideal.span ({α} : Set OK) = (I.1.1 : Ideal OK))
    (hN : 0 < Algebra.norm ℤ α) :
    narrowMk0OnGenusCoprimeIdeals d I = 1 := by
  have hα0 : α ≠ 0 := (Algebra.norm_ne_zero_iff.mp hN.ne')
  rcases Qsqrtd.Real.isTotallyPositive_algebraMap_or_neg_of_algebraNorm_pos
    d hd hN with hαpos | hnegαpos
  · have hmk :=
      NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive hα0 hαpos
    have hsubtype :
        I.1 = ⟨Ideal.span ({α} : Set OK), by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          exact Ideal.span_singleton_eq_bot.not.mpr hα0⟩ :=
      Subtype.ext hα.symm
    simpa [narrowMk0OnGenusCoprimeIdeals, hsubtype] using hmk
  · have hmk :=
      NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive
        (neg_ne_zero.mpr hα0) hnegαpos
    have hspan : Ideal.span ({-α} : Set OK) = (I.1.1 : Ideal OK) := by
      simpa using hα
    have hsubtype :
        I.1 = ⟨Ideal.span ({-α} : Set OK), by
          rw [mem_nonZeroDivisors_iff_ne_zero]
          exact Ideal.span_singleton_eq_bot.not.mpr (neg_ne_zero.mpr hα0)⟩ :=
      Subtype.ext hspan.symm
    simpa [narrowMk0OnGenusCoprimeIdeals, hsubtype] using hmk

/-- An ordinary-principal narrow class has trivial local genus character at a
ramified prime congruent to `1` modulo `4`. -/
theorem genusCharacter_eq_one_of_narrowToClassGroup_eq_one_of_mod_four_one
    (p : RamifiedPrimeIndex d) (hp4 : p.1 % 4 = 1) (C : Cl⁺(d))
    (hC : Qsqrtd.narrowToClassGroup d C = 1) :
    genusCharacter d p C = 1 := by
  obtain ⟨I, hI⟩ := exists_genusCoprimeIdeal_mk0_eq d C
  obtain ⟨α, hα⟩ := exists_generator_of_narrowToClassGroup_eq_one d I (by rwa [hI])
  rw [← hI, genusCharacter_apply_mk0]
  apply Units.ext
  change kroneckerSymNat (primeDiscriminantFactor d p)
      (Ideal.absNorm (I.1.1 : Ideal OK)) = 1
  rw [← hα]
  exact kroneckerSymNat_primeDiscriminantFactor_absNorm_span_eq_one_of_mod_four_one
    d p hp4 (by simpa [hα] using genusCoprimeIdeal_coprime_factor d I p)

/-- A nontrivial ordinary-principal narrow class has local genus character
`-1` at a ramified prime congruent to `3` modulo `4`. -/
theorem genusCharacter_eq_neg_one_of_narrowToClassGroup_eq_one_of_mod_four_three
    (hd : 0 < d) (p : RamifiedPrimeIndex d) (hp4 : p.1 % 4 = 3)
    (C : Cl⁺(d)) (hC : Qsqrtd.narrowToClassGroup d C = 1) (hC1 : C ≠ 1) :
    genusCharacter d p C = -1 := by
  obtain ⟨I, hI⟩ := exists_genusCoprimeIdeal_mk0_eq d C
  obtain ⟨α, hα⟩ := exists_generator_of_narrowToClassGroup_eq_one d I (by rwa [hI])
  have hα0 : α ≠ 0 := by
    intro hα0
    have hIbot : (I.1.1 : Ideal OK) = ⊥ := by
      rw [← hα, Ideal.span_singleton_eq_bot.mpr hα0]
    exact (mem_nonZeroDivisors_iff_ne_zero.mp I.1.2) (by
      simpa [Ideal.zero_eq_bot] using hIbot)
  have hNne : Algebra.norm ℤ α ≠ 0 := Algebra.norm_ne_zero_iff.mpr hα0
  have hNneg : Algebra.norm ℤ α < 0 := by
    by_contra hN
    have hNpos : 0 < Algebra.norm ℤ α :=
      lt_of_le_of_ne (not_lt.mp hN) (Ne.symm hNne)
    exact hC1 (hI.symm.trans
      (narrowMk0_eq_one_of_generator_algebraNorm_pos d hd I hα hNpos))
  rw [← hI, genusCharacter_apply_mk0]
  apply Units.ext
  change kroneckerSymNat (primeDiscriminantFactor d p)
      (Ideal.absNorm (I.1.1 : Ideal OK)) = -1
  rw [← hα]
  exact
    kroneckerSymNat_primeDiscriminantFactor_absNorm_span_eq_neg_one_of_mod_four_three
      d p hp4 hNneg (by
        simpa [hα] using genusCoprimeIdeal_coprime_factor d I p)

end GenusTheory
end ClassGroup
end QuadraticNumberFields
