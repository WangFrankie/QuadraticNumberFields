/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Class-group and fractional-ideal helpers

Material destined for mathlib.

This file currently contains three helper families:

* denominator clearing for single principal fractional-ideal multipliers;
* denominator clearing for square principal fractional-ideal multipliers;
* in a Dedekind domain, integral ideal-class representatives coprime to a
  prescribed nonzero ideal. The proof avoids valuations: it uses the `1.5`-generator
  property `IsDedekindDomain.exists_sup_span_eq` together with cancellation in the
  monoid of nonzero ideals.
-/

open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- Clear denominators in a principal fractional-ideal multiplier.

If `z I = J` as fractional ideals, then after writing `z = x / y` one gets
`(x) I = (y) J` as integral ideals. -/
theorem exists_span_mul_eq_span_mul_of_spanSingleton_mul_coeIdeal_eq_coeIdeal
    {I J : Ideal R} {z : FractionRing R}
    (hJ : spanSingleton R⁰ z * (I : FractionalIdeal R⁰ (FractionRing R)) =
      (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ x y : R, y ≠ 0 ∧ Ideal.span ({x} : Set R) * I = Ideal.span ({y} : Set R) * J := by
  refine ⟨(IsLocalization.sec R⁰ z).1, (IsLocalization.sec R⁰ z).2, ?_, ?_⟩
  · exact mem_nonZeroDivisors_iff_ne_zero.mp (IsLocalization.sec R⁰ z).2.prop
  · exact (FractionalIdeal.spanSingleton_mul_coeIdeal_eq_coeIdeal (K := FractionRing R)).mp hJ

/-- Clear denominators in a square principal fractional-ideal multiplier.

If `(z ^ 2) I = J` as fractional ideals, then after writing `z = x / y` one gets
`(x) (x) I = (y) (y) J` as integral ideals. -/
theorem exists_span_mul_span_mul_eq_of_spanSingleton_sq_mul_coeIdeal_eq_coeIdeal
    {I J : Ideal R} {z : FractionRing R} (hz : z ≠ 0)
    (hJ : spanSingleton R⁰ (z ^ 2) * (I : FractionalIdeal R⁰ (FractionRing R)) =
      (J : FractionalIdeal R⁰ (FractionRing R))) :
    ∃ x y : R, x ≠ 0 ∧ y ≠ 0 ∧
      Ideal.span ({x} : Set R) * Ideal.span ({x} : Set R) * I =
        Ideal.span ({y} : Set R) * Ideal.span ({y} : Set R) * J := by
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ z
  have hy_ne : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hz
    rw [hx, IsFractionRing.mk'_eq_div, map_zero, zero_div]
  have hy2 : y ^ 2 ∈ R⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero 2 hy_ne)
  refine ⟨x, y, hx_ne, hy_ne, ?_⟩
  have hsq :
      (IsLocalization.mk' (FractionRing R) x ⟨y, hy⟩) ^ 2 =
        IsLocalization.mk' (FractionRing R) (x ^ 2) ⟨y ^ 2, hy2⟩ := by
    rw [IsFractionRing.mk'_eq_div, IsFractionRing.mk'_eq_div]
    field_simp [IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy]
    rw [map_pow, map_pow]
    ring
  have hclear : Ideal.span ({x ^ 2} : Set R) * I = Ideal.span ({y ^ 2} : Set R) * J := by
    exact (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal (FractionRing R) hy2).mp (by
      rw [← hsq]
      exact hJ)
  rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_mul_span_singleton]
  simpa [pow_two] using hclear

end FractionalIdeal

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
