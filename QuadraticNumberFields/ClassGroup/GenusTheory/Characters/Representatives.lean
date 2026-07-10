/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import QuadraticNumberFields.ClassGroup.GenusTheory.Characters.Raw
import QuadraticNumberFields.ClassGroup.Narrow.Basic
import QuadraticNumberFields.Qsqrtd.TotallyRealComplex

/-!
# Discriminant-Coprime Narrow Representatives

This file proves that every narrow ideal class has a nonzero integral
representative whose absolute norm is coprime to the field discriminant.
-/

open scoped NumberField nonZeroDivisors QuadraticNumberFields.ClassGroup

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

attribute [-instance] DivisionRing.toRatAlgebra

variable (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "OK" => NumberField.RingOfIntegers (Qsqrtd (d : ℚ))

/-- The narrow class map restricted to discriminant-coprime integral ideals. -/
noncomputable def narrowMk0OnGenusCoprimeIdeals :
    GenusCoprimeIdeal d →* Cl⁺(d) :=
  NarrowClassGroup.mk0.comp (genusCoprimeIdeals d).subtype

private theorem exists_nat_forall_pos_add_nat_mul {ι : Type*} [Finite ι]
    (x : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ k : ℕ, ∀ i : ι, 0 < x i + (k : ℝ) * c := by
  classical
  letI := Fintype.ofFinite ι
  let B : ℝ := ∑ i : ι, max 0 ((-x i) / c)
  obtain ⟨k, hk⟩ := exists_nat_gt B
  refine ⟨k + 1, ?_⟩
  intro i
  have hnonneg : ∀ j : ι, 0 ≤ max 0 ((-x j) / c) := fun j ↦ le_max_left _ _
  have hi_le_B : (-x i) / c ≤ B :=
    (le_max_right _ _).trans
      (Finset.single_le_sum (fun j _ ↦ hnonneg j) (Finset.mem_univ i))
  have hlt : (-x i) / c < (k + 1 : ℕ) :=
    lt_of_le_of_lt hi_le_B (lt_trans hk (by norm_num))
  have hlt_real : (-x i) / c < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hlt
  have hmul : -x i < ((k + 1 : ℕ) : ℝ) * c :=
    (div_lt_iff₀ hc).mp hlt_real
  linarith

/-- Every narrow ideal class has a discriminant-coprime integral
representative. -/
theorem exists_genusCoprimeIdeal_mk0_eq (C : Cl⁺(d)) :
    ∃ I : GenusCoprimeIdeal d, narrowMk0OnGenusCoprimeIdeals d I = C := by
  classical
  let M : ℕ := primeDiscriminantModulus d
  let Mideal : Ideal OK := Ideal.span ({(M : OK)} : Set OK)
  have hM_ne : M ≠ 0 := by
    simpa [M] using primeDiscriminantModulus_ne_zero d
  have hM_cast_ne : (M : OK) ≠ 0 := Nat.cast_ne_zero.mpr hM_ne
  by_cases hMtop : Mideal = ⊤
  · obtain ⟨I, hI⟩ := NarrowClassGroup.mk0_surjective C
    have hI_ne : (I : Ideal OK) ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using mem_nonZeroDivisors_iff_ne_zero.mp I.2
    have hcop : Nat.Coprime (Ideal.absNorm (I : Ideal OK)) M :=
      Ideal.absNorm_coprime_of_sup_span_natCast_eq_top (I : Ideal OK) M hI_ne (by
        change (I : Ideal OK) ⊔ Mideal = ⊤
        rw [hMtop, sup_top_eq])
    refine ⟨⟨I, by simpa [genusCoprimeIdeals, M] using hcop⟩, ?_⟩
    simpa [narrowMk0OnGenusCoprimeIdeals] using hI
  · obtain ⟨A, hA⟩ := NarrowClassGroup.mk0_surjective (C⁻¹)
    have hA0 : (A : Ideal OK) ≠ 0 := by
      simpa using mem_nonZeroDivisors_iff_ne_zero.mp A.2
    have hM0 : Mideal ≠ 0 := by
      dsimp [Mideal]
      simpa [Ideal.zero_eq_bot] using hM_cast_ne
    have hle : (A : Ideal OK) * Mideal ≤ (A : Ideal OK) :=
      Ideal.mul_le_inf.trans inf_le_left
    have hAM0 : (A : Ideal OK) * Mideal ≠ 0 := mul_ne_zero hA0 hM0
    obtain ⟨a₀, hsup₀⟩ := IsDedekindDomain.exists_sup_span_eq hle hAM0
    have hspan₀_le : Ideal.span ({a₀} : Set OK) ≤ (A : Ideal OK) :=
      le_sup_right.trans hsup₀.le
    let n : ℕ := Ideal.absNorm ((A : Ideal OK) * Mideal)
    have hn_mem : (n : OK) ∈ (A : Ideal OK) * Mideal := by
      change (Ideal.absNorm ((A : Ideal OK) * Mideal) : OK) ∈
        (A : Ideal OK) * Mideal
      exact Ideal.absNorm_mem ((A : Ideal OK) * Mideal)
    have hn_ne : n ≠ 0 := by
      dsimp [n]
      exact Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hAM0)
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn_ne
    rcases exists_nat_forall_pos_add_nat_mul
      (fun σ : FractionRing OK →+* ℝ ↦ σ (algebraMap OK (FractionRing OK) a₀))
      hn_pos with ⟨k, hk⟩
    let a : OK := a₀ + (k : OK) * (n : OK)
    have ha_sub_mem : a - a₀ ∈ (A : Ideal OK) * Mideal := by
      simpa [a] using Ideal.mul_mem_left ((A : Ideal OK) * Mideal) (k : OK) hn_mem
    have ha_pos : NarrowClassGroup.IsTotallyPositive
        (algebraMap OK (FractionRing OK) a) := by
      intro σ
      simpa [a] using hk σ
    have ha_mem_A : a ∈ (A : Ideal OK) := by
      dsimp [a]
      exact add_mem (hspan₀_le (Ideal.mem_span_singleton_self a₀))
        (hle (Ideal.mul_mem_left _ (k : OK) hn_mem))
    have hspan_a_le : Ideal.span ({a} : Set OK) ≤ (A : Ideal OK) :=
      (Ideal.span_singleton_le_iff_mem (I := (A : Ideal OK))).mpr ha_mem_A
    have hsup_a :
        (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) = (A : Ideal OK) := by
      apply le_antisymm
      · exact sup_le hle hspan_a_le
      · calc
          (A : Ideal OK) = (A : Ideal OK) * Mideal ⊔ Ideal.span ({a₀} : Set OK) :=
            hsup₀.symm
          _ ≤ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) := by
            apply sup_le le_sup_left
            have ha_mem_sup :
                a ∈ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) :=
              (show Ideal.span ({a} : Set OK) ≤
                (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) from le_sup_right)
                  (Ideal.mem_span_singleton_self a)
            have hdiff_mem_sup :
                a - a₀ ∈ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) :=
              (show (A : Ideal OK) * Mideal ≤
                (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) from le_sup_left)
                  ha_sub_mem
            have hsub := sub_mem ha_mem_sup hdiff_mem_sup
            have ha₀_mem_sup :
                a₀ ∈ (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK) := by
              convert hsub using 1
              ring
            exact (Ideal.span_singleton_le_iff_mem
              (I := (A : Ideal OK) * Mideal ⊔ Ideal.span ({a} : Set OK))).mpr
                ha₀_mem_sup
    have ha_ne : a ≠ 0 := by
      intro ha
      apply hMtop
      have hspan_zero : Ideal.span ({a} : Set OK) = ⊥ := by
        rw [ha, Ideal.span_singleton_eq_bot]
      rw [hspan_zero, sup_bot_eq] at hsup_a
      have hM1 : Mideal = 1 := mul_left_cancel₀ hA0 (by rw [hsup_a, mul_one])
      rwa [Ideal.one_eq_top] at hM1
    obtain ⟨I, hImul⟩ := Ideal.dvd_iff_le.mpr hspan_a_le
    have hI0 : I ≠ 0 := by
      intro h
      rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hImul
      exact ha_ne hImul
    let I0 : (Ideal OK)⁰ := ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩
    have hC : NarrowClassGroup.mk0 I0 = C := by
      have hprin : NarrowClassGroup.mk0 (A * I0) = 1 := by
        have hAI_eq :
            A * I0 =
              ⟨Ideal.span ({a} : Set OK), by
                rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
                  Ideal.span_singleton_eq_bot]
                exact ha_ne⟩ := by
          ext y
          change y ∈ (A : Ideal OK) * I ↔ y ∈ Ideal.span ({a} : Set OK)
          rw [hImul]
        rw [hAI_eq]
        exact NarrowClassGroup.mk0_span_singleton_eq_one_of_isTotallyPositive ha_ne ha_pos
      rw [map_mul, hA, inv_mul_eq_one] at hprin
      exact hprin.symm
    have hIcop_M : I ⊔ Mideal = ⊤ := by
      have hMI : Mideal ⊔ I = 1 := mul_left_cancel₀ hA0 (by
        rw [Ideal.mul_sup, ← hImul, hsup_a, mul_one])
      rw [sup_comm, hMI, Ideal.one_eq_top]
    have hI_ne : I ≠ ⊥ := by
      simpa [Ideal.zero_eq_bot] using hI0
    have hcop : Nat.Coprime (Ideal.absNorm I) M :=
      Ideal.absNorm_coprime_of_sup_span_natCast_eq_top I M hI_ne (by
        simpa [Mideal] using hIcop_M)
    refine ⟨⟨I0, by simpa [genusCoprimeIdeals, M] using hcop⟩, ?_⟩
    simpa [narrowMk0OnGenusCoprimeIdeals] using hC

/-- The restricted narrow class map is surjective. -/
theorem narrowMk0OnGenusCoprimeIdeals_surjective :
    Function.Surjective (narrowMk0OnGenusCoprimeIdeals d) :=
  exists_genusCoprimeIdeal_mk0_eq d

end GenusTheory
end ClassGroup
end QuadraticNumberFields
