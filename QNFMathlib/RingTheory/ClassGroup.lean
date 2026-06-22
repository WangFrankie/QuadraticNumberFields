/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Coprime integral representatives of ideal classes

Material destined for mathlib.

In a Dedekind domain, every ideal class has an integral ideal representative whose
underlying ideal is coprime to any prescribed nonzero ideal. The proof avoids
valuations: it uses the `1.5`-generator property `IsDedekindDomain.exists_sup_span_eq`
together with cancellation in the monoid of nonzero ideals.
-/

open scoped nonZeroDivisors

namespace ClassGroup

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

/-- **Coprime integral representative.** In a Dedekind domain, every ideal class `C`
admits an integral ideal representative whose underlying ideal is coprime to a
prescribed nonzero ideal `M`. -/
theorem exists_integralRep_isCoprime
    (C : ClassGroup R) (M : Ideal R) (hM : M ≠ ⊥) :
    ∃ I : (Ideal R)⁰, ClassGroup.mk0 I = C ∧ IsCoprime (I : Ideal R) M := by
  by_cases hMtop : M = ⊤
  · obtain ⟨B, hB⟩ := ClassGroup.mk0_surjective C
    exact ⟨B, hB, by rw [Ideal.isCoprime_iff_sup_eq, hMtop, sup_top_eq]⟩
  · obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective C⁻¹
    have hA0 : (A : Ideal R) ≠ 0 := by
      have h := A.2
      rwa [mem_nonZeroDivisors_iff_ne_zero] at h
    have hM0 : M ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hM
    have hle : (A : Ideal R) * M ≤ (A : Ideal R) := Ideal.mul_le_inf.trans inf_le_left
    have hAM0 : (A : Ideal R) * M ≠ 0 := mul_ne_zero hA0 hM0
    obtain ⟨a, hsup⟩ := IsDedekindDomain.exists_sup_span_eq hle hAM0
    have hspan_le : Ideal.span {a} ≤ (A : Ideal R) := le_sup_right.trans hsup.le
    obtain ⟨I, hImul⟩ := Ideal.dvd_iff_le.mpr hspan_le
    have ha0 : a ≠ 0 := by
      intro ha
      subst ha
      apply hMtop
      have hsz : Ideal.span ({0} : Set R) = ⊥ := Ideal.span_singleton_eq_bot.mpr rfl
      rw [hsz, sup_bot_eq] at hsup
      have hAM1 : (A : Ideal R) * M = (A : Ideal R) * 1 := by rw [hsup, mul_one]
      have := mul_left_cancel₀ hA0 hAM1
      rwa [Ideal.one_eq_top] at this
    have hI0 : I ≠ 0 := by
      intro h
      rw [h, mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hImul
      exact ha0 hImul
    refine ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩, ?_, ?_⟩
    · have hprin :
          ClassGroup.mk0 (A * ⟨I, mem_nonZeroDivisors_iff_ne_zero.mpr hI0⟩) = 1 := by
        rw [ClassGroup.mk0_eq_one_iff]
        change ((A : Ideal R) * I).IsPrincipal
        rw [← hImul]
        exact ⟨a, rfl⟩
      rw [map_mul, hA, inv_mul_eq_one] at hprin
      exact hprin.symm
    · change IsCoprime I M
      rw [Ideal.isCoprime_iff_sup_eq]
      have hkey : (A : Ideal R) * (M ⊔ I) = (A : Ideal R) := by
        rw [Ideal.mul_sup, ← hImul, hsup]
      have hkey1 : (A : Ideal R) * (M ⊔ I) = (A : Ideal R) * 1 := by rw [hkey, mul_one]
      have hMI : M ⊔ I = 1 := mul_left_cancel₀ hA0 hkey1
      rw [sup_comm, hMI, Ideal.one_eq_top]

end ClassGroup
