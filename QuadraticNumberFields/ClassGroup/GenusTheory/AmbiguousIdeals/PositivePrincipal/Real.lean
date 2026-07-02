/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.PositivePrincipal.Internal
import Mathlib.NumberTheory.Pell

/-!
# Real Positive-Principal Ramified Parity Relation

The real quadratic branch: the genuine unit/sign correction. Builds totally
positive norm-one units from Pell solutions and produces a totally positive
generator of the full ramified-parity ideal product.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

private theorem toPrincipalIdeal_neg
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (γ : (FractionRing R)ˣ) :
    toPrincipalIdeal R (FractionRing R) (-γ) = toPrincipalIdeal R (FractionRing R) γ := by
  rw [← Units.val_inj]
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  exact ⟨-1, by simp⟩

private theorem toPrincipalIdeal_algebraMap_unit_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (u : Rˣ) :
    toPrincipalIdeal R (FractionRing R)
        (Units.map (algebraMap R (FractionRing R)).toMonoidHom u) = 1 := by
  rw [← Units.val_inj]
  rw [coe_toPrincipalIdeal]
  change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) (u : R)) =
    (1 : FractionalIdeal R⁰ (FractionRing R))
  rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) (u : R)]
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit]
  rfl

private theorem toPrincipalIdeal_mul_algebraMap_unit
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (γ : (FractionRing R)ˣ) (u : Rˣ) :
    toPrincipalIdeal R (FractionRing R)
        (γ * Units.map (algebraMap R (FractionRing R)).toMonoidHom u) =
      toPrincipalIdeal R (FractionRing R) γ := by
  rw [map_mul]
  rw [toPrincipalIdeal_algebraMap_unit_eq_one]
  simp

private theorem isTotallyPositive_or_neg_isTotallyPositive_of_qsqrt_norm_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (Qsqrtd (d : ℚ))
            (γ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) : ℝ)) :
    NarrowClassGroup.IsTotallyPositive
        (γ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∨
      NarrowClassGroup.IsTotallyPositive
        ((-γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ) :
          FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  let z : Qsqrtd (d : ℚ) := e (γ : FractionRing R)
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  have hprod :
      0 < Qsqrtd.realEmbeddingPos d hd_nonneg_real z *
        Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
    simpa [z, e, R] using
      (by
        rw [← Qsqrtd.norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hd_nonneg_real z]
        exact hNormPos)
  rcases mul_pos_iff.mp hprod with hsign | hsign
  · left
    intro σ
    let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
      (σ.comp e.symm.toRingHom).toRatAlgHom
    have hσγ : σ (γ : FractionRing R) = φ (e (γ : FractionRing R)) :=
      qsqrt_ringHom_eval_eq_algHom_eval d σ (γ : FractionRing R)
    rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
    · rw [hσγ, hφ]
      simpa [z] using hsign.1
    · rw [hσγ, hφ]
      simpa [z] using hsign.2
  · right
    intro σ
    let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
      (σ.comp e.symm.toRingHom).toRatAlgHom
    have hσγ : σ (γ : FractionRing R) = φ (e (γ : FractionRing R)) :=
      qsqrt_ringHom_eval_eq_algHom_eval d σ (γ : FractionRing R)
    rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
    · have hγneg : σ (γ : FractionRing R) < 0 := by
        rw [hσγ, hφ]
        simpa [z] using hsign.1
      simpa using neg_pos.mpr hγneg
    · have hγneg : σ (γ : FractionRing R) < 0 := by
        rw [hσγ, hφ]
        simpa [z] using hsign.2
      simpa using neg_pos.mpr hγneg

private theorem qsqrt_norm_pos_of_isTotallyPositive_fractionRing_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    0 <
      (Qsqrtd.norm
        (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (Qsqrtd (d : ℚ))
          (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) : ℝ) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  let z : Qsqrtd (d : ℚ) := e (x : FractionRing R)
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  apply Qsqrtd.norm_pos_of_realEmbedding_pos d hd_nonneg_real
  · let σpos : FractionRing R →+* ℝ :=
      (Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
    simpa [σpos, z, e, R, RingHom.comp_apply] using hxpos σpos
  · let σneg : FractionRing R →+* ℝ :=
      (Qsqrtd.realEmbeddingNeg d hd_nonneg_real).toRingHom.comp e.toRingHom
    simpa [σneg, z, e, R, RingHom.comp_apply] using hxpos σneg

private theorem exists_tp_generator_of_qsqrt_norm_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    {r : {p // p ∈ ramifiedPrimes d} → Fin 2}
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (fullRamifiedParityIdealProduct d r))
    (hNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (Qsqrtd (d : ℚ))
            (γ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) : ℝ)) :
    ∃ δ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (δ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) δ =
          FractionalIdeal.mk0
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
            (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  rcases isTotallyPositive_or_neg_isTotallyPositive_of_qsqrt_norm_pos d hd hNormPos with
    hpos | hneg
  · exact ⟨γ, hpos, hγ⟩
  · refine ⟨-γ, hneg, ?_⟩
    rw [toPrincipalIdeal_neg, hγ]

private theorem qsqrt_norm_mul_fractionRing_units
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (γ x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    (Qsqrtd.norm
      (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
        ((γ * x : (FractionRing R)ˣ) : FractionRing R)) : ℝ) =
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) *
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (x : FractionRing R)) : ℝ) := by
  intro R
  change
    (Qsqrtd.norm
      (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
        ((γ : FractionRing R) * (x : FractionRing R))) : ℝ) =
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) *
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (x : FractionRing R)) : ℝ)
  rw [map_mul]
  norm_num [Qsqrtd.norm]

private theorem exists_positive_norm_generator_of_principal_ambiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) J)
    (hγNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (Qsqrtd (d : ℚ))
            (γ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) : ℝ)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ δ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) δ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (δ : FractionRing R)) : ℝ) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let r := fullRamifiedParityVector d J
  have hmk :
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk0 (fullRamifiedParityIdealProduct d r) := by
    simpa [r] using ambiguousIdeal_mk0_eq_fullRamifiedParityIdealProduct_of_factorization'
      d J hJamb
  obtain ⟨x, hxpos, hx⟩ :=
    (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp hmk
  refine ⟨r, hJparity, γ * x, ?_, ?_⟩
  · rw [map_mul, hγ]
    exact hx
  · rw [qsqrt_norm_mul_fractionRing_units d γ x]
    exact mul_pos hγNormPos
      (qsqrt_norm_pos_of_isTotallyPositive_fractionRing_unit d hd hxpos)

private theorem exists_tp_generator_of_principal_ambiguousIdeal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0)
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hγ :
      toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) γ =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) J)
    (hγNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (Qsqrtd (d : ℚ))
            (γ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) : ℝ)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ δ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (δ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) δ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨r, hrnonzero, η, hη, hηNormPos⟩ :=
    exists_positive_norm_generator_of_principal_ambiguousIdeal
      d hd J hJamb hJparity hγ hγNormPos
  obtain ⟨δ, hδpos, hδ⟩ := exists_tp_generator_of_qsqrt_norm_pos d hd hη hηNormPos
  exact ⟨r, hrnonzero, δ, hδpos, hδ⟩

private theorem exists_tp_generator_of_ambiguous_span_intCast_add_sqrtdInt
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hda : d < a ^ 2)
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJspan :
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
        Ideal.span
          ({algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
              Splitting.sqrtdInt d} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let α : R := algebraMap ℤ R a + Splitting.sqrtdInt d
  have hα0 : α ≠ 0 := by
    simpa [α, R] using intCast_add_sqrtdInt_ne_zero_of_lt_sq d a hda
  let γ : (FractionRing R)ˣ :=
    Units.mk0 (algebraMap R (FractionRing R) α) (by
      simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne hα0)
  have hγ :
      toPrincipalIdeal R (FractionRing R) γ =
        FractionalIdeal.mk0 (FractionRing R) J := by
    rw [toPrincipalIdeal_eq_iff]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) α) =
      (FractionalIdeal.mk0 (FractionRing R) J : FractionalIdeal R⁰ (FractionRing R))
    rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) α]
    rw [← hJspan]
    rfl
  have hγNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
    simpa [γ, α, R] using qsqrt_norm_fractionRing_intCast_add_sqrtdInt_pos d a hda
  exact exists_tp_generator_of_principal_ambiguousIdeal
    d hd J hJamb hJparity hγ hγNormPos

private theorem exists_tp_generator_of_span_intCast_add_sqrtdInt_eq
    (d a : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    {r : {p // p ∈ ramifiedPrimes d} → Fin 2} (hda : d < a ^ 2)
    (hrnonzero : ∃ p, r p ≠ 0)
    (hspan :
      Ideal.span
          ({algebraMap ℤ (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) a +
              Splitting.sqrtdInt d} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
        (fullRamifiedParityIdealProduct d r :
          Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨r, hrnonzero, γ, hγ, hγNormPos⟩ :=
    exists_positive_norm_generator_of_span_intCast_add_sqrtdInt_eq d a hda hrnonzero hspan
  obtain ⟨δ, hδpos, hδ⟩ := exists_tp_generator_of_qsqrt_norm_pos d hd hγ hγNormPos
  exact ⟨r, hrnonzero, δ, hδpos, hδ⟩

private theorem qsqrt_norm_mul_algebraMap_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {γ : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (ε : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let εK : (FractionRing R)ˣ :=
      Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
    (Qsqrtd.norm
      (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
        ((γ * εK : (FractionRing R)ˣ) : FractionRing R)) : ℝ) =
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) *
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) := by
  intro R εK
  change
    (Qsqrtd.norm
      (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
        ((γ : FractionRing R) * (εK : FractionRing R))) : ℝ) =
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) *
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ)
  rw [map_mul]
  norm_num [Qsqrtd.norm]

private theorem qsqrt_norm_pos_of_no_negative_norm_integral_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0)
    (ε : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let εK : (FractionRing R)ˣ :=
      Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
    0 <
      (Qsqrtd.norm
        (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let εK : (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
  let z : Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)
  let n : ℝ := (Qsqrtd.norm z : ℝ)
  have hz_ne : z ≠ 0 := by
    exact (map_ne_zero (FractionRing.algEquiv R (Qsqrtd (d : ℚ))).toRingHom).mpr
      (Units.ne_zero εK)
  have hn_ne : n ≠ 0 := by
    have hnorm_ne : Qsqrtd.norm z ≠ 0 := by
      intro hnorm
      exact hz_ne (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp hnorm)
    have hnorm_ne_real : ((Qsqrtd.norm z : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hnorm_ne
    simpa [n] using hnorm_ne_real
  have hn_not_neg : ¬ n < 0 := by
    intro hn
    exact hnoNegUnit ⟨ε, by simpa [n, z, εK, R] using hn⟩
  rcases lt_trichotomy n 0 with hn_neg | hn_zero | hn_pos
  · exact False.elim (hn_not_neg hn_neg)
  · exact False.elim (hn_ne hn_zero)
  · simpa [n, z, εK, R] using hn_pos

private theorem exists_isTotallyPositive_conjAut_mul_self_eq_one_unit_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0)
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ)
    (hu :
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ v : Rˣ,
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv v * v = 1 ∧
        let vK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom v
        NarrowClassGroup.IsTotallyPositive (vK : FractionRing R) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let uK : (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom u
  have huNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (uK : FractionRing R)) : ℝ) := by
    simpa [uK, R] using qsqrt_norm_pos_of_no_negative_norm_integral_unit d hnoNegUnit u
  rcases isTotallyPositive_or_neg_isTotallyPositive_of_qsqrt_norm_pos
      d hd (γ := uK) huNormPos with hpos | hneg
  · exact ⟨u, hu, by simpa [uK, R] using hpos⟩
  · refine ⟨-u, ?_, ?_⟩
    · have hmap_neg :
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv (-u) =
            -Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u := by
        apply Units.ext
        change
          conjAutRingOfIntegers (Qsqrtd (d : ℚ)) (-(u : R)) =
            -conjAutRingOfIntegers (Qsqrtd (d : ℚ)) (u : R)
        simp
      calc
        Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv (-u) * (-u)
            = -Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * (-u) := by
              rw [hmap_neg]
        _ = Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u := by
              simp
        _ = 1 := hu
    · simpa [uK, R] using hneg

private theorem exists_nontrivial_tp_unit_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0)
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ)
    (hu_ne_one : u ≠ 1) (hu_ne_neg_one : u ≠ -1)
    (hu :
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ v : Rˣ,
      v ≠ 1 ∧
        v ≠ -1 ∧
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv v * v = 1 ∧
            let vK : (FractionRing R)ˣ :=
              Units.map (algebraMap R (FractionRing R)).toMonoidHom v
            NarrowClassGroup.IsTotallyPositive (vK : FractionRing R) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let uK : (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom u
  have huNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (uK : FractionRing R)) : ℝ) := by
    simpa [uK, R] using qsqrt_norm_pos_of_no_negative_norm_integral_unit d hnoNegUnit u
  rcases isTotallyPositive_or_neg_isTotallyPositive_of_qsqrt_norm_pos
      d hd (γ := uK) huNormPos with hpos | hneg
  · exact ⟨u, hu_ne_one, hu_ne_neg_one, hu, by simpa [uK, R] using hpos⟩
  · refine ⟨-u, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hu_ne_neg_one (by simpa using congrArg Neg.neg h)
    · intro h
      exact hu_ne_one (by simpa using congrArg Neg.neg h)
    · have hmap_neg :
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv (-u) =
            -Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u := by
        apply Units.ext
        change
          conjAutRingOfIntegers (Qsqrtd (d : ℚ)) (-(u : R)) =
            -conjAutRingOfIntegers (Qsqrtd (d : ℚ)) (u : R)
        simp
      calc
        Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv (-u) * (-u)
            = -Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * (-u) := by
              rw [hmap_neg]
        _ = Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u := by
              simp
        _ = 1 := hu
    · simpa [uK, R] using hneg

private theorem one_add_unit_ne_zero_of_ne_neg_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ) (hu_ne_neg_one : u ≠ -1) :
    (1 + (u : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ≠ 0 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  intro hα
  apply hu_ne_neg_one
  apply Units.ext
  change (u : R) = (-1 : R)
  have hα' : (u : R) + 1 = 0 := by
    rw [add_comm]
    simpa [R] using hα
  exact eq_neg_of_add_eq_zero_left hα'

private theorem intCast_add_intCast_mul_sqrtdInt_mul_intCast_sub_intCast_mul_sqrtdInt
    (d x y : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hxy : x ^ 2 - d * y ^ 2 = 1) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    (algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d) *
        (algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d) = 1 := by
  intro R
  let K := Qsqrtd (d : ℚ)
  apply NumberField.RingOfIntegers.ext
  change (((algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) *
      ((algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K)) =
    (1 : K)
  have hleft :
      ((algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) =
        (⟨(x : ℚ), (y : ℚ)⟩ : K) := by
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  have hright :
      ((algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) =
        (⟨(x : ℚ), -(y : ℚ)⟩ : K) := by
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  rw [hleft, hright]
  rw [QuadraticAlgebra.mk_mul_mk]
  ext
  · change (x : ℚ) * (x : ℚ) + (d : ℚ) * (y : ℚ) * (-(y : ℚ)) = 1
    have hxyq : (x : ℚ) ^ 2 - (d : ℚ) * (y : ℚ) ^ 2 = 1 := by
      exact_mod_cast hxy
    ring_nf at hxyq ⊢
    exact hxyq
  · change (x : ℚ) * (-(y : ℚ)) + (y : ℚ) * (x : ℚ) +
        (0 : ℚ) * (y : ℚ) * (-(y : ℚ)) = 0
    ring

private theorem conjAutRingOfIntegers_intCast_add_intCast_mul_sqrtdInt
    (d x y : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    conjAutRingOfIntegers (Qsqrtd (d : ℚ))
        (algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d) =
      algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d := by
  intro R
  let K := Qsqrtd (d : ℚ)
  apply NumberField.RingOfIntegers.ext
  rw [coe_conjAutRingOfIntegers_apply]
  change QuadraticField.conjAut K
      ((algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) =
    ((algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K)
  have hleft :
      ((algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) =
        (⟨(x : ℚ), (y : ℚ)⟩ : K) := by
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  have hright :
      ((algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d : R) : K) =
        (⟨(x : ℚ), -(y : ℚ)⟩ : K) := by
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  rw [hleft, hright]
  change Qsqrtd.starAlgEquiv (d : ℚ) (⟨(x : ℚ), (y : ℚ)⟩ : K) = _
  rw [Qsqrtd.starAlgEquiv_apply]
  ext <;> simp [QuadraticAlgebra.star_mk]

private noncomputable def unitOfPellSolution
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (a : Pell.Solution₁ d) :
    (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let α : R := algebraMap ℤ R a.x + algebraMap ℤ R a.y * Splitting.sqrtdInt d
  let β : R := algebraMap ℤ R a.x - algebraMap ℤ R a.y * Splitting.sqrtdInt d
  have hαβ : α * β = 1 := by
    simpa [α, β, R] using
      intCast_add_intCast_mul_sqrtdInt_mul_intCast_sub_intCast_mul_sqrtdInt d
        a.x a.y a.prop
  exact Units.mkOfMulEqOne α β hαβ

private theorem unitOfPellSolution_val
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (a : Pell.Solution₁ d) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    (unitOfPellSolution d a : R) =
      algebraMap ℤ R a.x + algebraMap ℤ R a.y * Splitting.sqrtdInt d := by
  intro R
  simp [unitOfPellSolution, R]

private theorem unitOfPellSolution_conjAut_mul_self_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (a : Pell.Solution₁ d) :
    Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv
        (unitOfPellSolution d a) *
      unitOfPellSolution d a = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  let α : R := algebraMap ℤ R a.x + algebraMap ℤ R a.y * Splitting.sqrtdInt d
  let β : R := algebraMap ℤ R a.x - algebraMap ℤ R a.y * Splitting.sqrtdInt d
  have hαβ : α * β = 1 := by
    simpa [α, β, R] using
      intCast_add_intCast_mul_sqrtdInt_mul_intCast_sub_intCast_mul_sqrtdInt d
        a.x a.y a.prop
  have hval : (unitOfPellSolution d a : R) = α := by
    simpa [α, R] using unitOfPellSolution_val d a
  have hconj : conjAutRingOfIntegers K (unitOfPellSolution d a : R) = β := by
    rw [hval]
    simpa [α, β, R, K] using
      conjAutRingOfIntegers_intCast_add_intCast_mul_sqrtdInt d a.x a.y
  apply Units.ext
  change conjAutRingOfIntegers K (unitOfPellSolution d a : R) *
      (unitOfPellSolution d a : R) = (1 : R)
  rw [hconj, hval]
  rw [mul_comm]
  exact hαβ

private theorem unitOfPellSolution_ne_one_of_y_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] {a : Pell.Solution₁ d}
    (ha_y : a.y ≠ 0) :
    unitOfPellSolution d a ≠ 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  intro h
  have hval : (unitOfPellSolution d a : R) = (1 : R) := by
    have h' := congrArg
      (fun z : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ =>
        (z : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) h
    simpa [R] using h'
  have hyq : (a.y : ℚ) = 0 := by
    have hcoe := congrArg (fun z : R => ((z : K))) hval
    have him := congrArg QuadraticAlgebra.im hcoe
    simpa [unitOfPellSolution_val, R, K, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
      QuadraticAlgebra.im_one] using him
  exact ha_y (Int.cast_eq_zero.mp hyq)

private theorem unitOfPellSolution_ne_neg_one_of_y_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] {a : Pell.Solution₁ d}
    (ha_y : a.y ≠ 0) :
    unitOfPellSolution d a ≠ -1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  intro h
  have hval : (unitOfPellSolution d a : R) = (-1 : R) := by
    have h' := congrArg
      (fun z : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ =>
        (z : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) h
    simpa [R] using h'
  have hyq : (a.y : ℚ) = 0 := by
    have hcoe := congrArg (fun z : R => ((z : K))) hval
    have him := congrArg QuadraticAlgebra.im hcoe
    simpa [unitOfPellSolution_val, R, K, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
      QuadraticAlgebra.im_one] using him
  exact ha_y (Int.cast_eq_zero.mp hyq)

private theorem exists_fundamental_pell_unit_of_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    ∃ a : Pell.Solution₁ d,
      Pell.IsFundamental a ∧
        let u := unitOfPellSolution d a
        u ≠ 1 ∧
          u ≠ -1 ∧
            Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 := by
  have hsq : ¬ IsSquare d :=
    not_isSquare_int_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hd hsq
  refine ⟨a, ha, ?_, ?_, ?_⟩
  · exact unitOfPellSolution_ne_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  · exact unitOfPellSolution_ne_neg_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  · exact unitOfPellSolution_conjAut_mul_self_eq_one d a

private theorem unitOfPellSolution_isTotallyPositive_of_pos
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    {a : Pell.Solution₁ d} (hax : 0 < a.x) (hay : 0 < a.y) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let uK : (FractionRing R)ˣ :=
      Units.map (algebraMap R (FractionRing R)).toMonoidHom (unitOfPellSolution d a)
    NarrowClassGroup.IsTotallyPositive (uK : FractionRing R) := by
  intro R uK σ
  let K := Qsqrtd (d : ℚ)
  let e : FractionRing R ≃ₐ[R] K := FractionRing.algEquiv R K
  let z : K := e (uK : FractionRing R)
  have hz : z = (⟨(a.x : ℚ), (a.y : ℚ)⟩ : K) := by
    have hmap :
        e (uK : FractionRing R) =
          ((unitOfPellSolution d a : R) : K) := by
      simp [e, uK, R, K]
    have hval :
        (unitOfPellSolution d a : R) =
          algebraMap ℤ R a.x + algebraMap ℤ R a.y * Splitting.sqrtdInt d := by
      simpa [R] using unitOfPellSolution_val d a
    change e (uK : FractionRing R) = (⟨(a.x : ℚ), (a.y : ℚ)⟩ : K)
    rw [hmap, hval]
    ext <;> simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega]
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hd
  have hpos :
      0 < Qsqrtd.realEmbeddingPos d hd_nonneg_real z := by
    rw [hz, Qsqrtd.realEmbeddingPos_apply]
    have hxR : 0 < (a.x : ℝ) := by exact_mod_cast hax
    have hyR : 0 ≤ (a.y : ℝ) := by exact_mod_cast le_of_lt hay
    exact add_pos_of_pos_of_nonneg hxR (mul_nonneg hyR (Real.sqrt_nonneg _))
  have hnorm :
      (Qsqrtd.norm z : ℝ) = 1 := by
    rw [hz]
    simp only [Qsqrtd.norm, QuadraticAlgebra.norm_def]
    norm_num
    have hprop : a.x * a.x - d * a.y * a.y = 1 := by
      nlinarith [a.prop]
    exact_mod_cast hprop
  have hneg :
      0 < Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
    have hmul :
        Qsqrtd.realEmbeddingPos d hd_nonneg_real z *
            Qsqrtd.realEmbeddingNeg d hd_nonneg_real z = 1 := by
      rw [← Qsqrtd.norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hd_nonneg_real z,
        hnorm]
    exact pos_of_mul_pos_right (by rw [hmul]; exact zero_lt_one) hpos.le
  let φ : K →ₐ[ℚ] ℝ := (σ.comp e.symm.toRingHom).toRatAlgHom
  have hσu : σ (uK : FractionRing R) = φ (e (uK : FractionRing R)) :=
    qsqrt_ringHom_eval_eq_algHom_eval d σ (uK : FractionRing R)
  rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
  · rw [hσu, hφ]
    simpa [z] using hpos
  · rw [hσu, hφ]
    simpa [z] using hneg

private theorem algebraNorm_one_add_unitOfPellSolution
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (a : Pell.Solution₁ d) :
    Algebra.norm ℤ
        (1 + (unitOfPellSolution d a :
          NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
      2 * (a.x + 1) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int (K := K),
    Qsqrtd.algebraNorm_ratAlgebra_eq_qsqrtdNorm]
  have hval :
      (unitOfPellSolution d a : R) =
        algebraMap ℤ R a.x + algebraMap ℤ R a.y * Splitting.sqrtdInt d := by
    simpa [R] using unitOfPellSolution_val d a
  have hcoord :
      ((1 + (unitOfPellSolution d a : R) : R) : K) =
        (⟨((a.x + 1 : ℤ) : ℚ), (a.y : ℚ)⟩ : K) := by
    rw [hval]
    ext
    · simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
        QuadraticAlgebra.re_one]
      ring
    · simp [R, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
        QuadraticAlgebra.im_one]
  rw [hcoord]
  simp only [Qsqrtd.norm, QuadraticAlgebra.norm_def, Int.cast_add, Int.cast_one,
    Int.cast_mul, Int.cast_ofNat]
  have hprop : ((a.x : ℚ) ^ 2 - (d : ℚ) * (a.y : ℚ) ^ 2 : ℚ) = 1 := by
    exact_mod_cast a.prop
  ring_nf at hprop ⊢
  nlinarith

private theorem absNorm_span_one_add_unitOfPellSolution
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (a : Pell.Solution₁ d) :
    Ideal.absNorm
        (Ideal.span
          ({1 + (unitOfPellSolution d a :
            NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      (2 * (a.x + 1)).natAbs := by
  rw [Ideal.absNorm_span_singleton, algebraNorm_one_add_unitOfPellSolution]

private theorem two_mul_x_add_one_pos_of_isFundamental
    {d : ℤ} {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    0 < 2 * (a.x + 1) := by
  nlinarith [ha.1]

private theorem absNorm_span_one_add_unitOfPellSolution_of_isFundamental
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    Ideal.absNorm
        (Ideal.span
          ({1 + (unitOfPellSolution d a :
            NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) =
      Int.toNat (2 * (a.x + 1)) := by
  rw [absNorm_span_one_add_unitOfPellSolution]
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (le_of_lt (two_mul_x_add_one_pos_of_isFundamental ha)),
    Int.toNat_of_nonneg (le_of_lt (two_mul_x_add_one_pos_of_isFundamental ha))]

private theorem exists_nontrivial_conjAut_mul_self_eq_one_unit_of_pell_solution
    (d x y : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hxy : x ^ 2 - d * y ^ 2 = 1) (hy : y ≠ 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ u : Rˣ,
      u ≠ 1 ∧
        u ≠ -1 ∧
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 := by
  intro R
  let K := Qsqrtd (d : ℚ)
  let α : R := algebraMap ℤ R x + algebraMap ℤ R y * Splitting.sqrtdInt d
  let β : R := algebraMap ℤ R x - algebraMap ℤ R y * Splitting.sqrtdInt d
  have hαβ : α * β = 1 := by
    simpa [α, β, R] using
      intCast_add_intCast_mul_sqrtdInt_mul_intCast_sub_intCast_mul_sqrtdInt d x y hxy
  let u : Rˣ := Units.mkOfMulEqOne α β hαβ
  have hconj : conjAutRingOfIntegers K (u : R) = β := by
    simpa [u, α, β, R, K] using
      conjAutRingOfIntegers_intCast_add_intCast_mul_sqrtdInt d x y
  have hu :
      Units.mapEquiv (conjAutRingOfIntegers K).toMulEquiv u * u = 1 := by
    apply Units.ext
    change conjAutRingOfIntegers K (u : R) * (u : R) = (1 : R)
    rw [hconj]
    rw [show β * (u : R) = α * β by simp [u, α, β, mul_comm]]
    exact hαβ
  have hu_ne_one : u ≠ 1 := by
    intro h
    have hval : α = (1 : R) := by
      simpa [u] using congrArg (fun z : Rˣ => (z : R)) h
    have hyq : (y : ℚ) = 0 := by
      have hcoe := congrArg (fun z : R => ((z : K))) hval
      have him := congrArg QuadraticAlgebra.im hcoe
      simpa [α, R, K, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
        QuadraticAlgebra.im_one] using him
    exact hy (Int.cast_eq_zero.mp hyq)
  have hu_ne_neg_one : u ≠ -1 := by
    intro h
    have hval : α = (-1 : R) := by
      simpa [u] using congrArg (fun z : Rˣ => (z : R)) h
    have hyq : (y : ℚ) = 0 := by
      have hcoe := congrArg (fun z : R => ((z : K))) hval
      have him := congrArg QuadraticAlgebra.im hcoe
      simpa [α, R, K, Splitting.coe_sqrtdInt, QuadraticAlgebra.omega,
        QuadraticAlgebra.im_one] using him
    exact hy (Int.cast_eq_zero.mp hyq)
  exact ⟨u, hu_ne_one, hu_ne_neg_one, hu⟩

private theorem exists_nontrivial_conjAut_mul_self_eq_one_unit_of_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ u : Rˣ,
      u ≠ 1 ∧
        u ≠ -1 ∧
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 := by
  have hsq : ¬ IsSquare d :=
    not_isSquare_int_of_squarefree_ne_one (Fact.out : Squarefree d) (Fact.out : d ≠ 1)
  obtain ⟨x, y, hxy, hy⟩ := Pell.exists_of_not_isSquare hd hsq
  exact exists_nontrivial_conjAut_mul_self_eq_one_unit_of_pell_solution d x y hxy hy

private theorem pell_isFundamental_not_sq {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) :
    ¬ ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  rintro ⟨b, hb⟩
  rcases ha.eq_zpow_or_neg_zpow b with ⟨n, hbna | hbna⟩
  · have hpow : a ^ (2 * n : ℤ) = a := by
      calc
        a ^ (2 * n : ℤ) = (a ^ n) ^ (2 : ℤ) := by
          rw [zpow_mul']
        _ = b ^ 2 := by
          rw [← hbna]
          rfl
        _ = a := hb
    have hone : a ^ (2 * n - 1 : ℤ) = 1 := by
      calc
        a ^ (2 * n - 1 : ℤ) = a ^ (2 * n : ℤ) * a ^ (-1 : ℤ) := by
          rw [sub_eq_add_neg, zpow_add]
        _ = a * a ^ (-1 : ℤ) := by rw [hpow]
        _ = 1 := by simp
    have hzero := (ha.zpow_eq_one_iff (2 * n - 1)).mp hone
    omega
  · have hpow : a ^ (2 * n : ℤ) = a := by
      calc
        a ^ (2 * n : ℤ) = (a ^ n) ^ (2 : ℤ) := by
          rw [zpow_mul']
        _ = (-b) ^ 2 := by
          rw [hbna]
          simp
          rfl
        _ = b ^ 2 := by simp
        _ = a := hb
    have hone : a ^ (2 * n - 1 : ℤ) = 1 := by
      calc
        a ^ (2 * n - 1 : ℤ) = a ^ (2 * n : ℤ) * a ^ (-1 : ℤ) := by
          rw [sub_eq_add_neg, zpow_add]
        _ = a * a ^ (-1 : ℤ) := by rw [hpow]
        _ = 1 := by simp
    have hzero := (ha.zpow_eq_one_iff (2 * n - 1)).mp hone
    omega

private theorem pell_isFundamental_not_neg_sq {d : ℤ} {a : Pell.Solution₁ d}
    (ha : Pell.IsFundamental a) :
    ¬ ∃ b : Pell.Solution₁ d, b ^ 2 = -a := by
  rintro ⟨b, hb⟩
  rcases ha.eq_zpow_or_neg_zpow b with ⟨n, hbna | hbna⟩
  · have hpow : a ^ (2 * n : ℤ) = -a := by
      calc
        a ^ (2 * n : ℤ) = (a ^ n) ^ (2 : ℤ) := by
          rw [zpow_mul']
        _ = b ^ 2 := by
          rw [← hbna]
          rfl
        _ = -a := hb
    exact ha.zpow_ne_neg_zpow (n := 2 * n) (n' := 1) (by simpa using hpow)
  · have hpow : a ^ (2 * n : ℤ) = -a := by
      calc
        a ^ (2 * n : ℤ) = (a ^ n) ^ (2 : ℤ) := by
          rw [zpow_mul']
        _ = (-b) ^ 2 := by
          rw [hbna]
          simp
          rfl
        _ = b ^ 2 := by simp
        _ = -a := hb
    exact ha.zpow_ne_neg_zpow (n := 2 * n) (n' := 1) (by simpa using hpow)

private theorem exists_int_sq_eq_of_isSquare_toNat_of_pos {n : ℤ} (hn : 0 < n)
    (hsq : IsSquare n.toNat) :
    ∃ m : ℤ, 0 ≤ m ∧ m ^ 2 = n := by
  rcases hsq with ⟨m, hm⟩
  refine ⟨m, by positivity, ?_⟩
  have hncast : ((n.toNat : ℕ) : ℤ) = n :=
    Int.toNat_of_nonneg (le_of_lt hn)
  calc
    (m : ℤ) ^ 2 = ((m * m : ℕ) : ℤ) := by norm_num [pow_two]
    _ = n := by
      rw [← hm, hncast]

private theorem exists_half_of_nonneg_sq_eq_two_mul {x m : ℤ} (hm0 : 0 ≤ m)
    (hm : m ^ 2 = 2 * (x + 1)) :
    ∃ r : ℤ, 0 ≤ r ∧ m = 2 * r ∧ x + 1 = 2 * r ^ 2 := by
  have h2dvd_m_sq : (2 : ℤ) ∣ m ^ 2 := by
    rw [hm]
    exact dvd_mul_right 2 (x + 1)
  have h2prime : Prime (2 : ℤ) := by norm_num
  have h2dvd_m : (2 : ℤ) ∣ m :=
    h2prime.dvd_of_dvd_pow h2dvd_m_sq
  rcases h2dvd_m with ⟨r, hr⟩
  have hr0 : 0 ≤ r := by nlinarith
  refine ⟨r, hr0, hr, ?_⟩
  have hcalc : 4 * r ^ 2 = 2 * (x + 1) := by
    calc
      4 * r ^ 2 = (2 * r) ^ 2 := by ring
      _ = m ^ 2 := by rw [← hr]
      _ = 2 * (x + 1) := hm
  nlinarith

private theorem nat_factorization_four_of_prime {p : ℕ} (hp : p.Prime) :
    (4 : ℕ).factorization p = if p = 2 then 2 else 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    rw [Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_two]
  · rw [if_neg hp2]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hp4
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num] at hp4
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hp4 with ⟨k, hk, hpk⟩
    interval_cases k <;> norm_num at hpk
    · exact hp.ne_one hpk
    · exact hp2 hpk
    · subst hpk
      norm_num at hp

private theorem nat_factorization_two_of_prime {p : ℕ} (hp : p.Prime) :
    (2 : ℕ).factorization p = if p = 2 then 1 else 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    simp [Nat.Prime.factorization_self Nat.prime_two]
  · rw [if_neg hp2]
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpdiv
    rw [show (2 : ℕ) = 2 ^ 1 by norm_num] at hpdiv
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hpdiv with ⟨k, hk, hpk⟩
    interval_cases k <;> norm_num at hpk
    · exact hp.ne_one hpk
    · exact hp2 hpk

private theorem nat_factorization_two_mul_of_prime
    {R p : ℕ} (hR0 : R ≠ 0) (hp : p.Prime) :
    (2 * R).factorization p = (if p = 2 then 1 else 0) + R.factorization p := by
  have h2 : (2 : ℕ) ≠ 0 := by norm_num
  rw [Nat.factorization_mul h2 hR0]
  simp [nat_factorization_two_of_prime hp]

private theorem nat_factorization_eq_of_pell_half
    {D R Y : ℕ} (hD0 : D ≠ 0) (hY0 : Y ≠ 0) (hR0 : R ≠ 0)
    (hRm1 : R ^ 2 - 1 ≠ 0)
    (hEq : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1)) {p : ℕ} (hp : p.Prime) :
    D.factorization p + 2 * Y.factorization p =
      (if p = 2 then 2 else 0) + 2 * R.factorization p +
        (R ^ 2 - 1).factorization p := by
  have h4 : (4 : ℕ) ≠ 0 := by norm_num
  have hR2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hR0
  have hfac := congrArg (fun n : ℕ => n.factorization p) hEq
  change (D * Y ^ 2).factorization p =
    (4 * R ^ 2 * (R ^ 2 - 1)).factorization p at hfac
  rw [Nat.factorization_mul hD0 (pow_ne_zero 2 hY0), Nat.factorization_pow,
    Nat.factorization_mul (mul_ne_zero h4 hR2) hRm1,
    Nat.factorization_mul h4 hR2, Nat.factorization_pow] at hfac
  simpa [nat_factorization_four_of_prime hp, two_nsmul, two_mul, add_assoc] using hfac

private theorem factorization_sq_sub_one_eq_zero_of_prime_dvd
    {p R : ℕ} (hR0 : R ≠ 0) (hp : p.Prime) (hpR : p ∣ R) :
    (R ^ 2 - 1).factorization p = 0 := by
  apply Nat.factorization_eq_zero_of_not_dvd
  intro hpRm1
  have hpR2 : p ∣ R ^ 2 := dvd_pow hpR (by norm_num : 2 ≠ 0)
  have hp1 : p ∣ 1 := by
    have hsub : R ^ 2 - (R ^ 2 - 1) = 1 := by
      have hRpos : 0 < R := Nat.pos_of_ne_zero hR0
      have hle : 1 ≤ R ^ 2 := by nlinarith
      omega
    rw [← hsub]
    exact Nat.dvd_sub hpR2 hpRm1
  exact hp.not_dvd_one hp1

private theorem two_dvd_y_of_squarefree_mul_square
    {D Y : ℕ} (hDsq : Squarefree D) (h4 : (4 : ℕ) ∣ D * Y ^ 2) :
    2 ∣ Y := by
  have h2sq : (2 : ℕ) * 2 ∣ D * Y ^ 2 := by simpa using h4
  have h2Ysq : (2 : ℕ) ∣ Y ^ 2 :=
    Squarefree.dvd_of_squarefree_of_mul_dvd_mul_right hDsq h2sq
  exact Nat.prime_two.dvd_of_dvd_pow h2Ysq

private theorem nat_two_mul_dvd_y_of_squarefree_pell_half
    {D R Y : ℕ} (hDsq : Squarefree D) (hD0 : D ≠ 0) (hY0 : Y ≠ 0)
    (hR0 : R ≠ 0) (hRm1 : R ^ 2 - 1 ≠ 0)
    (hEq : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1)) :
    2 * R ∣ Y := by
  have htwoY : 2 ∣ Y := by
    apply two_dvd_y_of_squarefree_mul_square hDsq
    rw [hEq]
    simp [mul_assoc, dvd_mul_right]
  rw [← (Nat.factorization_le_iff_dvd (mul_ne_zero (by norm_num) hR0) hY0)]
  intro p
  by_cases hp : p.Prime
  · rw [nat_factorization_two_mul_of_prime hR0 hp]
    by_cases hpR : p ∣ R
    · have hRm1fac := factorization_sq_sub_one_eq_zero_of_prime_dvd hR0 hp hpR
      have hfac := nat_factorization_eq_of_pell_half hD0 hY0 hR0 hRm1 hEq hp
      rw [hRm1fac] at hfac
      have hDle : D.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one hD0).mp hDsq p
      by_cases hp2 : p = 2
      · subst p
        simp at hfac ⊢
        omega
      · simp [hp2] at hfac ⊢
        omega
    · by_cases hp2 : p = 2
      · subst p
        simp [Nat.factorization_eq_zero_of_not_dvd hpR]
        have hle :=
          (Nat.factorization_le_iff_dvd (by norm_num : (2 : ℕ) ≠ 0) hY0).mpr htwoY
        simpa [Nat.Prime.factorization_self Nat.prime_two] using hle 2
      · simp [hp2, Nat.factorization_eq_zero_of_not_dvd hpR]
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem two_mul_dvd_y_of_pell_half
    {d : ℤ} (hdSq : Squarefree d) {a : Pell.Solution₁ d} {r : ℤ}
    (ha : Pell.IsFundamental a) (hr0 : 0 ≤ r) (hx : a.x + 1 = 2 * r ^ 2) :
    2 * r ∣ a.y := by
  let D : ℕ := d.toNat
  let R : ℕ := r.toNat
  let Y : ℕ := a.y.toNat
  have hdpos : 0 < d := ha.d_pos
  have hypos : 0 < a.y := ha.2.1
  have hrpos : 0 < r := by
    have hrne : r ≠ 0 := by
      intro hr
      nlinarith [ha.1, hx]
    exact lt_of_le_of_ne' hr0 hrne
  have hDcast : (D : ℤ) = d := Int.toNat_of_nonneg (le_of_lt hdpos)
  have hYcast : (Y : ℤ) = a.y := Int.toNat_of_nonneg (le_of_lt hypos)
  have hRcast : (R : ℤ) = r := Int.toNat_of_nonneg hr0
  have hDsq : Squarefree D := by
    have hD_eq : D = d.natAbs := by
      apply Nat.cast_injective (R := ℤ)
      rw [hDcast, Int.natAbs_of_nonneg (le_of_lt hdpos)]
    simpa [hD_eq] using Int.squarefree_natAbs.mpr hdSq
  have hD0 : D ≠ 0 :=
    Nat.ne_of_gt (Int.ofNat_lt.mp (by simpa [hDcast] using hdpos))
  have hY0 : Y ≠ 0 :=
    Nat.ne_of_gt (Int.ofNat_lt.mp (by simpa [hYcast] using hypos))
  have hR0 : R ≠ 0 :=
    Nat.ne_of_gt (Int.ofNat_lt.mp (by simpa [hRcast] using hrpos))
  have hr2gt1 : 1 < r ^ 2 := by
    have h2 : 2 < 2 * r ^ 2 := by nlinarith [ha.1, hx]
    nlinarith
  have hR2cast : ((R ^ 2 : ℕ) : ℤ) = r ^ 2 := by
    calc
      ((R ^ 2 : ℕ) : ℤ) = (R : ℤ) ^ 2 := by norm_num
      _ = r ^ 2 := by rw [hRcast]
  have hRgt1 : 1 < R ^ 2 := by
    apply Int.ofNat_lt.mp
    rw [hR2cast]
    exact hr2gt1
  have hRm1 : R ^ 2 - 1 ≠ 0 := by omega
  have hEqInt : d * a.y ^ 2 = 4 * r ^ 2 * (r ^ 2 - 1) := by
    have hx' : a.x = 2 * r ^ 2 - 1 := by omega
    rw [a.prop_y, hx']
    ring
  have hRm1cast : ((R ^ 2 - 1 : ℕ) : ℤ) = r ^ 2 - 1 := by
    omega
  have hEqNat : D * Y ^ 2 = 4 * R ^ 2 * (R ^ 2 - 1) := by
    apply Nat.cast_injective (R := ℤ)
    change (D : ℤ) * (Y : ℤ) ^ 2 =
      (4 : ℤ) * (R : ℤ) ^ 2 * ((R ^ 2 - 1 : ℕ) : ℤ)
    rw [hDcast, hYcast, hRcast, hRm1cast]
    exact hEqInt
  have hNatDvd : 2 * R ∣ Y :=
    nat_two_mul_dvd_y_of_squarefree_pell_half hDsq hD0 hY0 hR0 hRm1 hEqNat
  have hIntDvd : ((2 * R : ℕ) : ℤ) ∣ a.y := by
    rcases hNatDvd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hYcast]
    exact_mod_cast hk
  simpa [R, hRcast] using hIntDvd

private theorem exists_pell_sq_of_half_and_dvd {d : ℤ} {a : Pell.Solution₁ d} {r : ℤ}
    (ha1 : 1 < a.x) (hx : a.x + 1 = 2 * r ^ 2) (hydiv : 2 * r ∣ a.y) :
    ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  rcases hydiv with ⟨s, hs⟩
  have hr0 : r ≠ 0 := by
    intro hr
    nlinarith [ha1, hx]
  have hx' : a.x = 2 * r ^ 2 - 1 := by omega
  have hy' : a.y = 2 * r * s := hs
  have hbprop : r ^ 2 - d * s ^ 2 = 1 := by
    have hprop := a.prop
    rw [hx', hy'] at hprop
    have hr2pos : 0 < r ^ 2 := sq_pos_of_ne_zero hr0
    nlinarith
  let b : Pell.Solution₁ d := Pell.Solution₁.mk r s hbprop
  refine ⟨b, ?_⟩
  apply Pell.Solution₁.ext
  · simp [b, pow_two]
    nlinarith [hbprop, hx']
  · simp [b, pow_two, hy']
    ring_nf

private theorem exists_pellSolution_sq_of_isSquare_two_mul_x_add_one
    {d : ℤ} [Fact (Squarefree d)] {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a)
    (hsq : IsSquare (Int.toNat (2 * (a.x + 1)))) :
    ∃ b : Pell.Solution₁ d, b ^ 2 = a := by
  obtain ⟨m, hm0, hm⟩ :=
    exists_int_sq_eq_of_isSquare_toNat_of_pos
      (two_mul_x_add_one_pos_of_isFundamental ha) hsq
  obtain ⟨r, hr0, _hmr, hx⟩ := exists_half_of_nonneg_sq_eq_two_mul hm0 hm
  exact exists_pell_sq_of_half_and_dvd ha.1 hx
    (two_mul_dvd_y_of_pell_half (Fact.out : Squarefree d) ha hr0 hx)

private theorem exists_isTotallyPositive_conjAut_mul_self_eq_one_unit_of_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ u : Rˣ,
      u ≠ 1 ∧
        u ≠ -1 ∧
          Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 ∧
            let uK : (FractionRing R)ˣ :=
              Units.map (algebraMap R (FractionRing R)).toMonoidHom u
            NarrowClassGroup.IsTotallyPositive (uK : FractionRing R) := by
  obtain ⟨u, hu_ne_one, hu_ne_neg_one, hu⟩ :=
    exists_nontrivial_conjAut_mul_self_eq_one_unit_of_real d hd
  exact
    exists_nontrivial_tp_unit_of_no_negative_norm_unit
      d hd hnoNegUnit u hu_ne_one hu_ne_neg_one hu

private theorem isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ)
    (hu :
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1) :
    IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
      (Ideal.span
        ({1 + (u : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
          Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let K := Qsqrtd (d : ℚ)
  have hunit :
      conjAutRingOfIntegers K (u : R) * (u : R) = 1 := by
    simpa [R, K] using Units.ext_iff.mp hu
  have hmul :
      conjAutRingOfIntegers K (1 + (u : R)) * (u : R) = 1 + (u : R) := by
    rw [map_add, map_one, add_mul, one_mul, hunit, add_comm]
  change Ideal.map (conjAutRingOfIntegers K : R →+* R)
      (Ideal.span ({1 + (u : R)} : Set R)) =
    Ideal.span ({1 + (u : R)} : Set R)
  calc
    Ideal.map (conjAutRingOfIntegers K : R →+* R)
        (Ideal.span ({1 + (u : R)} : Set R)) =
        Ideal.span ({conjAutRingOfIntegers K (1 + (u : R))} : Set R) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = Ideal.span ({conjAutRingOfIntegers K (1 + (u : R)) * (u : R)} : Set R) := by
      rw [Ideal.span_singleton_mul_right_unit u.isUnit]
    _ = Ideal.span ({1 + (u : R)} : Set R) := by
      rw [hmul]

private theorem exists_tp_generator_of_ambiguous_span_one_add_unit_of_isTotallyPositive
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ)
    (hu :
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1)
    (hupos :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      let uK : (FractionRing R)ˣ :=
        Units.map (algebraMap R (FractionRing R)).toMonoidHom u
      NarrowClassGroup.IsTotallyPositive (uK : FractionRing R))
    (J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    (hJspan :
      (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) =
        Ideal.span
          ({1 + (u : NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))} :
            Set (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hJparity : ∃ p, fullRamifiedParityVector d J p ≠ 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let α : R := 1 + (u : R)
  let uK : (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom u
  have hαpos : NarrowClassGroup.IsTotallyPositive (algebraMap R (FractionRing R) α) := by
    intro σ
    have huσ : 0 < σ (uK : FractionRing R) := by
      simpa [uK, R] using hupos σ
    have hsum : 0 < (1 : ℝ) + σ (uK : FractionRing R) := add_pos zero_lt_one huσ
    simpa [α, uK, map_add, RingHom.comp_apply] using hsum
  have hα0 : α ≠ 0 := by
    intro hα
    have hJ0 : (J : Ideal R) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp J.2
    apply hJ0
    rw [hJspan, show 1 + (u : R) = α from rfl, hα, Ideal.span_singleton_eq_bot]
  let γ : (FractionRing R)ˣ :=
    Units.mk0 (algebraMap R (FractionRing R) α) (by
      simpa using (FaithfulSMul.algebraMap_injective R (FractionRing R)).ne hα0)
  have hγ :
      toPrincipalIdeal R (FractionRing R) γ =
        FractionalIdeal.mk0 (FractionRing R) J := by
    rw [toPrincipalIdeal_eq_iff]
    change FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) α) =
      (FractionalIdeal.mk0 (FractionRing R) J : FractionalIdeal R⁰ (FractionRing R))
    rw [← FractionalIdeal.coeIdeal_span_singleton (P := FractionRing R) α]
    rw [← hJspan]
    rfl
  have hγpos : NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) := by
    simpa [γ, α] using hαpos
  have hγNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
    simpa [R] using qsqrt_norm_pos_of_isTotallyPositive_fractionRing_unit
      d hd (x := γ) hγpos
  have hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal R) := by
    rw [hJspan]
    simpa [R] using isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one d u hu
  exact exists_tp_generator_of_principal_ambiguousIdeal
    d hd J hJamb hJparity hγ hγNormPos

private theorem exists_nonzero_ramifiedParity_positive_norm_generator_of_real_of_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (_hd : 0 < d)
    (hprincipal :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing R)ˣ,
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r))
    (hnegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨ε, hεNormNeg⟩ := hnegUnit
  obtain ⟨r, hrnonzero, γ, hγ⟩ := hprincipal
  let z : Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)
  let n : ℝ := (Qsqrtd.norm z : ℝ)
  have hz_ne : z ≠ 0 := by
    exact (map_ne_zero (FractionRing.algEquiv R (Qsqrtd (d : ℚ))).toRingHom).mpr
      (Units.ne_zero γ)
  have hn_ne : n ≠ 0 := by
    have hnorm_ne : Qsqrtd.norm z ≠ 0 := by
      intro hnorm
      exact hz_ne (QuadraticAlgebra.norm_eq_zero_iff_eq_zero.mp hnorm)
    have hnorm_ne_real : ((Qsqrtd.norm z : ℚ) : ℝ) ≠ 0 := by
      exact_mod_cast hnorm_ne
    simpa [n] using hnorm_ne_real
  rcases lt_trichotomy n 0 with hn_neg | hn_zero | hn_pos
  · let εK : (FractionRing R)ˣ :=
      Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
    have hγε :
        toPrincipalIdeal R (FractionRing R) (γ * εK) =
          FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
      rw [toPrincipalIdeal_mul_algebraMap_unit, hγ]
    have hNormPos :
        0 <
          (Qsqrtd.norm
            (FractionRing.algEquiv R (Qsqrtd (d : ℚ))
              ((γ * εK : (FractionRing R)ˣ) : FractionRing R)) : ℝ) := by
      rw [qsqrt_norm_mul_algebraMap_unit d ε]
      exact mul_pos_of_neg_of_neg (by simpa [n, z, R] using hn_neg) hεNormNeg
    exact ⟨r, hrnonzero, γ * εK, hγε, hNormPos⟩
  · exact False.elim (hn_ne hn_zero)
  · exact ⟨r, hrnonzero, γ, hγ, by simpa [n, z, R] using hn_pos⟩

private theorem exists_nonzero_ramifiedParity_tp_generator_of_real_of_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hprincipal :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing R)ˣ,
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r))
    (hnegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨r, hrnonzero, γ, hγ, hγNormPos⟩ :=
    exists_nonzero_ramifiedParity_positive_norm_generator_of_real_of_negative_norm_unit
      d hd hprincipal hnegUnit
  obtain ⟨δ, hδpos, hδ⟩ := exists_tp_generator_of_qsqrt_norm_pos d hd hγ hγNormPos
  exact ⟨r, hrnonzero, δ, hδpos, hδ⟩

private theorem span_one_add_totallyPositive_normOne_unit_is_ambiguous_and_narrow_principal
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (u : (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))ˣ)
    (hu_ne_neg_one : u ≠ -1)
    (hu :
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1)
    (hupos :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      let uK : (FractionRing R)ˣ :=
        Units.map (algebraMap R (FractionRing R)).toMonoidHom u
      NarrowClassGroup.IsTotallyPositive (uK : FractionRing R)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ J : (Ideal R)⁰,
      (J : Ideal R) = Ideal.span ({1 + (u : R)} : Set R) ∧
        NarrowClassGroup.mk0 J = (1 : NarrowClassGroup R) ∧
          IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal R) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let J : (Ideal R)⁰ :=
    ⟨Ideal.span ({1 + (u : R)} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact one_add_unit_ne_zero_of_ne_neg_one d u hu_ne_neg_one⟩
  have hJspan : (J : Ideal R) = Ideal.span ({1 + (u : R)} : Set R) := rfl
  let α : R := 1 + (u : R)
  let uK : (FractionRing R)ˣ :=
    Units.map (algebraMap R (FractionRing R)).toMonoidHom u
  have hα0 : α ≠ 0 := by
    exact one_add_unit_ne_zero_of_ne_neg_one d u hu_ne_neg_one
  have hαpos : NarrowClassGroup.IsTotallyPositive (algebraMap R (FractionRing R) α) := by
    intro σ
    have huσ : 0 < σ (uK : FractionRing R) := by
      simpa [uK, R] using hupos σ
    have hsum : 0 < (1 : ℝ) + σ (uK : FractionRing R) := add_pos zero_lt_one huσ
    simpa [α, uK, map_add, RingHom.comp_apply] using hsum
  let Jα : (Ideal R)⁰ :=
    ⟨Ideal.span ({α} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      exact hα0⟩
  have hJ_eq_Jα : J = Jα := by
    apply Subtype.ext
    rfl
  have hJnarrow : NarrowClassGroup.mk0 J = (1 : NarrowClassGroup R) := by
    rw [hJ_eq_Jα]
    exact narrowClassGroup_mk0_span_singleton_eq_one_of_isTotallyPositive hα0 hαpos
  have hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal R) := by
    rw [hJspan]
    simpa [R] using isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one d u hu
  exact ⟨J, hJspan, hJnarrow, hJamb⟩

private theorem exists_nonzero_fullRamifiedParityVector_span_one_add_unitOfFundamentalPell
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (_hd : 0 < d)
    {a : Pell.Solution₁ d} (ha : Pell.IsFundamental a) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let u := unitOfPellSolution d a
    ∃ J : (Ideal R)⁰,
      (J : Ideal R) = Ideal.span ({1 + (u : R)} : Set R) ∧
        ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  intro R u
  have hu_ne_neg_one : u ≠ -1 := by
    simpa [u] using unitOfPellSolution_ne_neg_one_of_y_ne_zero d (ne_of_gt ha.2.1)
  let J : (Ideal R)⁰ :=
    ⟨Ideal.span ({1 + (u : R)} : Set R), by
      rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot, ne_eq,
        Ideal.span_singleton_eq_bot]
      simpa [u] using one_add_unit_ne_zero_of_ne_neg_one d u hu_ne_neg_one⟩
  refine ⟨J, rfl, ?_⟩
  by_contra hnone
  have hparity : ∀ p, fullRamifiedParityVector d J p = 0 := by
    intro p
    by_contra hp
    exact hnone ⟨p, hp⟩
  have hJamb : IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (J : Ideal R) := by
    simpa [J, u, R] using
      isAmbiguousIdeal_span_one_add_unit_of_conjAut_mul_self_eq_one d u
        (unitOfPellSolution_conjAut_mul_self_eq_one d a)
  have hsqNorm :
      IsSquare (Ideal.absNorm (J : Ideal R)) :=
    isSquare_absNorm_of_isAmbiguousIdeal_of_forall_fullRamifiedParityVector_eq_zero
      d J hJamb hparity
  have hnorm :
      Ideal.absNorm (J : Ideal R) = Int.toNat (2 * (a.x + 1)) := by
    simpa [J, u, R] using absNorm_span_one_add_unitOfPellSolution_of_isFundamental d ha
  have hsqTwo : IsSquare (Int.toNat (2 * (a.x + 1))) := by
    rw [← hnorm]
    exact hsqNorm
  exact (pell_isFundamental_not_sq ha)
    (exists_pellSolution_sq_of_isSquare_two_mul_x_add_one ha hsqTwo)

/-- Unit construction in the real quadratic no-negative-unit branch.

This constructs a totally positive norm-one unit `u` such that the ambiguous
principal ideal `(1 + u)` has nonzero ramified parity. This is the signed
unit/ramified-prime calculation, not an exact-count genus formula. -/
theorem exists_ambiguous_span_one_add_totallyPositive_normOne_unit_with_nonzero_ramifiedParity
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (_hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ u : Rˣ,
      Units.mapEquiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))).toMulEquiv u * u = 1 ∧
        (let uK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom u
        NarrowClassGroup.IsTotallyPositive (uK : FractionRing R)) ∧
        ∃ J : (Ideal R)⁰,
          (J : Ideal R) =
              Ideal.span ({1 + (u : R)} : Set R) ∧
            ∃ p, fullRamifiedParityVector d J p ≠ 0 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨a, ha, hu_ne_one, hu_ne_neg_one, hu⟩ :=
    exists_fundamental_pell_unit_of_real d hd
  let u := unitOfPellSolution d a
  have hupos :
      let uK : (FractionRing R)ˣ :=
        Units.map (algebraMap R (FractionRing R)).toMonoidHom u
      NarrowClassGroup.IsTotallyPositive (uK : FractionRing R) := by
    simpa [u, R] using
      unitOfPellSolution_isTotallyPositive_of_pos d hd
        (show 0 < a.x from zero_lt_one.trans ha.1) ha.2.1
  obtain ⟨J, hJspan, hJparity⟩ :=
    exists_nonzero_fullRamifiedParityVector_span_one_add_unitOfFundamentalPell
      d hd ha
  exact ⟨u, hu, hupos, J, hJspan, hJparity⟩

/-- In the real quadratic case with no negative-norm integral unit, genus theory
must produce a nonzero ramified parity relation with a positive-norm generator.

This is the genuine real quadratic signed-prime-discriminant/unit branch left
after the negative-norm unit case has been separated out. It belongs to the
uniform genus-theory input itself. -/
theorem exists_nonzero_ramifiedParity_positive_norm_generator_of_real_of_no_negative_norm_unit
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hnoNegUnit :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ¬ ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  obtain ⟨u, hu, hupos, J, hJspan, hJparity⟩ :=
    exists_ambiguous_span_one_add_totallyPositive_normOne_unit_with_nonzero_ramifiedParity
      d hd hnoNegUnit
  obtain ⟨r, hrnonzero, γ, hγpos, hγ⟩ :=
    exists_tp_generator_of_ambiguous_span_one_add_unit_of_isTotallyPositive
      d hd u hu hupos J hJspan hJparity
  have hγNormPos :
      0 <
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
    exact qsqrt_norm_pos_of_isTotallyPositive_fractionRing_unit d hd hγpos
  exact ⟨r, hrnonzero, γ, hγ, hγNormPos⟩

/-- Real quadratic positive-norm ramified parity relation.

The negative-norm unit case is an elementary sign correction. The no-negative-unit
case is supplied by the signed-prime-discriminant ramified-product construction. -/
theorem exists_nonzero_ramifiedParity_positive_norm_generator_of_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hprincipal :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing R)ˣ,
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) ∧
            0 <
              (Qsqrtd.norm
                (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (γ : FractionRing R)) : ℝ) := by
  classical
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  by_cases hnegUnit :
      ∃ ε : Rˣ,
        let εK : (FractionRing R)ˣ :=
          Units.map (algebraMap R (FractionRing R)).toMonoidHom ε
        (Qsqrtd.norm
          (FractionRing.algEquiv R (Qsqrtd (d : ℚ)) (εK : FractionRing R)) : ℝ) < 0
  · exact exists_nonzero_ramifiedParity_positive_norm_generator_of_real_of_negative_norm_unit
      d hd hprincipal hnegUnit
  · exact exists_nonzero_ramifiedParity_positive_norm_generator_of_real_of_no_negative_norm_unit
      d hd hnegUnit

/-- Real quadratic sign-unit branch for the narrow positive-principal relation.

This is where the genuine unit/sign correction belongs. The imaginary branch
does not use this theorem: there are no real embeddings there, so total
positivity is vacuous. -/
theorem exists_nonzero_ramifiedParity_tp_generator_of_real
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 < d)
    (hprincipal :
      let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
      ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
        (∃ p, r p ≠ 0) ∧
          ∃ γ : (FractionRing R)ˣ,
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r)) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    ∃ r : ({p // p ∈ ramifiedPrimes d} → Fin 2),
      (∃ p, r p ≠ 0) ∧
        ∃ γ : (FractionRing R)ˣ,
          NarrowClassGroup.IsTotallyPositive (γ : FractionRing R) ∧
            toPrincipalIdeal R (FractionRing R) γ =
              FractionalIdeal.mk0 (FractionRing R) (fullRamifiedParityIdealProduct d r) := by
  obtain ⟨r, hrnonzero, γ, hγ, hγNormPos⟩ :=
    exists_nonzero_ramifiedParity_positive_norm_generator_of_real d hd hprincipal
  obtain ⟨δ, hδpos, hδ⟩ := exists_tp_generator_of_qsqrt_norm_pos d hd hγ hγNormPos
  exact ⟨r, hrnonzero, δ, hδpos, hδ⟩

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
