/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.GenusTheory.AmbiguousIdeals.RamifiedParity

/-!
# Ambiguous Representatives

This file turns inversion-fixed narrow classes into genuinely ambiguous integral
ideal representatives using the quadratic Hilbert-90 adjustment.
-/

namespace QuadraticNumberFields
namespace ClassGroup
namespace GenusTheory

open scoped nonZeroDivisors NumberField Pointwise QuadraticNumberFields.ClassGroup
open scoped QuadraticNumberFields.Splitting

attribute [-instance] DivisionRing.toRatAlgebra
attribute [local instance] FractionRing.liftAlgebra

namespace Internal

/-- If a nonzero integral ideal represents an inversion-fixed narrow class, then
its square represents the trivial narrow class. -/
theorem narrowClassGroup_mk0_mul_self_eq_one_of_inversionFixed
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    {C : NarrowInversionFixedClass R} {I : (Ideal R)⁰}
    (hI : NarrowClassGroup.mk0 I = C.1) :
    NarrowClassGroup.mk0 (I * I) = 1 := by
  have hmul : (C.1 : NarrowClassGroup R) * C.1 = 1 := by
    nth_rewrite 1 [C.2]
    rw [inv_mul_cancel]
  rw [map_mul, hI]
  exact hmul

/-- An inversion-fixed narrow class has a nonzero integral ideal representative
whose square is cancelled by a totally positive principal fractional ideal. This
is the parity relation used before reducing the representative to ramified
prime exponents. -/
theorem exists_integralIdeal_square_principal_relation_of_narrowInversionFixedClass
    {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]
    (C : NarrowInversionFixedClass R) :
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
conjugate differs from it by a totally positive principal fractional ideal. This
is the class-level input for the Hilbert-90 adjustment to an ambiguous
representative. -/
theorem exists_integralIdeal_tp_multiplier_to_conjAut_of_narrowInversionFixedClass
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (C : NarrowInversionFixedClass (NumberField.RingOfIntegers K)) :
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
  exact (NarrowClassGroup.mk0_eq_mk0_iff_exists_fraction_ring).mp (hI.trans hconj.symm)

/-- A totally positive fraction-field unit in `Q(√d)` has nonnegative field norm
after transport to the standard field model. -/
theorem algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) :
    0 ≤ Algebra.norm ℚ
      (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (Qsqrtd (d : ℚ))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
    FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  let z : Qsqrtd (d : ℚ) := e (x : FractionRing R)
  change 0 ≤ Algebra.norm ℚ z
  rw [Qsqrtd.algebraNorm_eq_qsqrtdNorm]
  by_cases hdneg : d < 0
  · exact Qsqrtd.norm_nonneg_of_neg hdneg z
  have hd_ne_zero : d ≠ 0 := Squarefree.ne_zero (Fact.out : Squarefree d)
  have hdpos : 0 < d := by omega
  have hd_nonneg_real : 0 ≤ (d : ℝ) := by exact_mod_cast le_of_lt hdpos
  let σpos : FractionRing R →+* ℝ :=
    (Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
  let σneg : FractionRing R →+* ℝ :=
    (Qsqrtd.realEmbeddingNeg d hd_nonneg_real).toRingHom.comp e.toRingHom
  have hpos_pos : 0 < Qsqrtd.realEmbeddingPos d hd_nonneg_real z := by
    simpa [σpos, z, e, R] using hxpos σpos
  have hpos_neg : 0 < Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
    simpa [σneg, z, e, R] using hxpos σneg
  have hnorm_pos_real : 0 < (Qsqrtd.norm z : ℝ) :=
    Qsqrtd.norm_pos_of_realEmbedding_pos d hd_nonneg_real hpos_pos hpos_neg
  have hnorm_pos_rat : 0 < Qsqrtd.norm z := by
    exact_mod_cast hnorm_pos_real
  exact le_of_lt hnorm_pos_rat

/-- Norm-one extraction boundary. A totally positive principal multiplier
relating an ideal to its conjugate has field norm `1`. -/
theorem norm_eq_one_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    Algebra.norm ℚ
      (FractionRing.algEquiv (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
        (Qsqrtd (d : ℚ))
        (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))) = 1 := by
  let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
  let e := FractionRing.algEquiv R (Qsqrtd (d : ℚ))
  have habs_map :
      Ideal.absNorm
          (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R)
            (I : Ideal R)) =
        Ideal.absNorm (I : Ideal R) := by
    exact Ideal.absNorm_map_equiv (conjAutRingOfIntegers (Qsqrtd (d : ℚ))) (I : Ideal R)
  have habs_map_rat :
      (Ideal.absNorm
          (Ideal.map (conjAutRingOfIntegers (Qsqrtd (d : ℚ)) : R →+* R)
            (I : Ideal R)) : ℚ) =
        Ideal.absNorm (I : Ideal R) := by
    exact_mod_cast habs_map
  have hnorm_abs : |Algebra.norm ℚ (e (x : FractionRing R))| = 1 := by
    let E := FractionalIdeal.canonicalEquiv R⁰ (FractionRing R) (Qsqrtd (d : ℚ))
    have h :=
      congrArg
        (fun J : (FractionalIdeal R⁰ (FractionRing R))ˣ =>
          FractionalIdeal.absNorm (E (J : FractionalIdeal R⁰ (FractionRing R))))
        hconj
    have hIpos :
        (0 : ℚ) < Ideal.absNorm (I : Ideal R) := by
      exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
    have hIne : (Ideal.absNorm (I : Ideal R) : ℚ) ≠ 0 := ne_of_gt hIpos
    have h' :
        (Ideal.absNorm (I : Ideal R) : ℚ) *
            |Algebra.norm ℚ (e (x : FractionRing R))| =
          (Ideal.absNorm (I : Ideal R) : ℚ) := by
      change
        FractionalIdeal.absNorm
            (E (((FractionalIdeal.mk0 (FractionRing R) I) *
              toPrincipalIdeal R (FractionRing R) x :
                (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) =
          FractionalIdeal.absNorm
            (E ((FractionalIdeal.mk0 (FractionRing R)
                (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I) :
                  (FractionalIdeal R⁰ (FractionRing R))ˣ) :
              FractionalIdeal R⁰ (FractionRing R))) at h
      rw [Units.val_mul, map_mul, FractionalIdeal.absNorm.map_mul] at h
      simpa [R, e, E, FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm,
        coe_toPrincipalIdeal, FractionalIdeal.canonicalEquiv_spanSingleton,
        FractionalIdeal.absNorm_span_singleton, coe_conjAutNonzeroIdealMulEquiv_apply,
        habs_map_rat] using h
    exact mul_left_cancel₀ hIne (by simpa using h')
  have hnorm_nonneg : 0 ≤ Algebra.norm ℚ (e (x : FractionRing R)) := by
    exact algebra_norm_nonneg_of_isTotallyPositive_fractionRing_algEquiv_qsqrtd d hxpos
  have hnorm_abs_self :
      |Algebra.norm ℚ (e (x : FractionRing R))| = Algebra.norm ℚ (e (x : FractionRing R)) :=
    abs_of_nonneg hnorm_nonneg
  rw [hnorm_abs_self] at hnorm_abs
  exact hnorm_abs

/-- Fraction-field Hilbert 90 for the localized conjugation action. A norm-one
fraction-field unit is an ordinary conjugation coboundary.

This private helper is universe-zero because the available mathlib Hilbert 90
theorem is universe-zero; this is enough for the `Qsqrtd` application below. -/
theorem exists_conjAut_coboundary_of_norm_eq_one
    (K : Type) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {x : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hxnorm :
      Algebra.norm ℚ
        (FractionRing.algEquiv (NumberField.RingOfIntegers K) K
          (x : FractionRing (NumberField.RingOfIntegers K))) = 1) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers K))ˣ,
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹ := by
  let R := NumberField.RingOfIntegers K
  let e := FractionRing.algEquiv R K
  haveI : IsGalois ℚ K := Algebra.IsQuadraticExtension.isGalois ℚ K
  have hcard : Nat.card Gal(K / ℚ) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  haveI : IsCyclic Gal(K / ℚ) := isCyclic_of_prime_card hcard
  have hconj_ne_one : (QuadraticField.conjAut K : Gal(K / ℚ)) ≠ 1 := by
    simpa using (QuadraticField.Conj.conj_ne_refl (K := K))
  have hg : ∀ σ : Gal(K / ℚ), σ ∈ Subgroup.zpowers (QuadraticField.conjAut K) := by
    intro σ
    exact mem_zpowers_of_prime_card (p := 2) hcard hconj_ne_one
  obtain ⟨yK, hyK⟩ :=
    groupCohomology.exists_div_of_norm_eq_one
      (K := ℚ) (L := K) (g := QuadraticField.conjAut K) hg hxnorm
  let y : (FractionRing R)ˣ := Units.mapEquiv e.symm.toRingEquiv yK
  refine ⟨y, ?_⟩
  apply Units.ext
  apply e.injective
  have hy_map : e (y : FractionRing R) = (yK : K) := by
    change e (e.symm (yK : K)) = (yK : K)
    exact e.apply_symm_apply (yK : K)
  have hσ_map :
      e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          (FractionRing R)ˣ) : FractionRing R) =
        QuadraticField.conjAut K (yK : K) := by
    calc
      e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          (FractionRing R)ˣ) : FractionRing R) =
          e ((conjAutFractionRingAlgEquiv K) (y : FractionRing R)) := rfl
      _ = QuadraticField.conjAut K (e (y : FractionRing R)) := by
        change FractionRing.algEquiv (NumberField.RingOfIntegers K) K
            ((conjAutFractionRingAlgEquiv K) (y : FractionRing R)) =
          QuadraticField.conjAut K
            (FractionRing.algEquiv (NumberField.RingOfIntegers K) K (y : FractionRing R))
        exact fractionRing_algEquiv_conjAutFractionRingAlgEquiv K (y : FractionRing R)
      _ = QuadraticField.conjAut K (yK : K) := by
        rw [hy_map]
  calc
    e (x : FractionRing R) = (yK : K) / QuadraticField.conjAut K (yK : K) := hyK.symm
    _ =
        e (y : FractionRing R) *
          (e (((Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
            (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      rw [hy_map, hσ_map]
      exact div_eq_mul_inv (yK : K) (QuadraticField.conjAut K (yK : K))
    _ = e ((y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹ :
          (FractionRing R)ˣ) : FractionRing R) := by
      dsimp
      simp

/-- Hilbert-90 extraction boundary. A principal multiplier relating an ideal to
its conjugate should be an ordinary conjugation coboundary in the fraction
field. -/
theorem exists_conjAut_coboundary_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      x =
        y *
          (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv
            y)⁻¹ := by
  exact exists_conjAut_coboundary_of_norm_eq_one (Qsqrtd (d : ℚ))
    (norm_eq_one_of_tp_multiplier_to_conjAut d I hxpos hconj)

/-- A real embedding of `Q(√d)` sends the standard square root to one of the
two real roots. -/
theorem qsqrt_algHom_omega_eq_sqrt_or_neg
    (d : ℤ) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
    φ QuadraticAlgebra.omega = Real.sqrt (d : ℝ) ∨
      φ QuadraticAlgebra.omega = -Real.sqrt (d : ℝ) := by
  have hsq :
      φ QuadraticAlgebra.omega * φ QuadraticAlgebra.omega = (d : ℝ) := by
    have h :=
      congrArg φ
        (QuadraticAlgebra.omega_mul_omega_eq_add (R := ℚ) (a := (d : ℚ)) (b := 0))
    simpa [Algebra.smul_def] using h
  have hsq' : φ QuadraticAlgebra.omega ^ 2 = (d : ℝ) := by
    simpa [sq] using hsq
  have habs : |φ QuadraticAlgebra.omega| = Real.sqrt (d : ℝ) := by
    rw [← Real.sqrt_sq_eq_abs (φ QuadraticAlgebra.omega), hsq']
  rcases abs_cases (φ QuadraticAlgebra.omega) with h | h
  · left
    linarith
  · right
    linarith

/-- The two explicit real embeddings exhaust the real embeddings of `Q(√d)`. -/
theorem qsqrt_algHom_eq_realEmbeddingPos_or_neg
    (d : ℤ) (hd : 0 ≤ (d : ℝ)) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
    φ = Qsqrtd.realEmbeddingPos d hd ∨ φ = Qsqrtd.realEmbeddingNeg d hd := by
  rcases qsqrt_algHom_omega_eq_sqrt_or_neg d φ with hω | hω
  · left
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = Qsqrtd.realEmbeddingPos d hd QuadraticAlgebra.omega
    rw [hω, Qsqrtd.realEmbeddingPos_apply]
    simp
  · right
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = Qsqrtd.realEmbeddingNeg d hd QuadraticAlgebra.omega
    rw [hω, Qsqrtd.realEmbeddingNeg_apply]
    simp

/-- Positive real embedding after quadratic conjugation agrees with the negative
real embedding. -/
theorem qsqrt_realEmbeddingPos_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (hd : 0 ≤ (d : ℝ)) (z : Qsqrtd (d : ℚ)) :
    Qsqrtd.realEmbeddingPos d hd (QuadraticField.conjAut (Qsqrtd (d : ℚ)) z) =
      Qsqrtd.realEmbeddingNeg d hd z := by
  change Qsqrtd.realEmbeddingPos d hd (star z) = Qsqrtd.realEmbeddingNeg d hd z
  rw [Qsqrtd.realEmbeddingPos_apply, Qsqrtd.realEmbeddingNeg_apply]
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

/-- Evaluating a fraction-field element by a ring hom to `ℝ` agrees with first
transporting it to `Q(√d)` and then evaluating by the induced `ℚ`-algebra hom. -/
theorem qsqrt_ringHom_eval_eq_algHom_eval
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (σ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ)
    (w : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
    let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ := (σ.comp e.symm.toRingHom).toRatAlgHom
    σ w = φ (e w) := by
  intro R e φ
  dsimp [φ]
  have hw : e.toRingEquiv.symm (e w) = w := by
    exact e.toRingEquiv.symm_apply_apply w
  rw [hw]

/-- Sign choice for the quadratic Hilbert-90 representative in the standard
model. If a totally positive element is written as `y / σ(y)`, then either `y`
or `-y` is totally positive. -/
theorem qsqrt_isTotallyPositive_or_neg_isTotallyPositive_of_totallyPositive_coboundary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hy :
      x =
        y * (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹) :
    NarrowClassGroup.IsTotallyPositive
        (y : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∨
      NarrowClassGroup.IsTotallyPositive
        ((-y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ) :
          FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  by_cases hreal :
      Nonempty (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ)
  · let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
    let z : Qsqrtd (d : ℚ) := e (y : FractionRing R)
    let τy : (FractionRing R)ˣ :=
      Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y
    have hd_nonneg_real : 0 ≤ (d : ℝ) := by
      by_contra hdn
      have hdneg : d < 0 := by
        have : (d : ℝ) < 0 := lt_of_not_ge hdn
        exact_mod_cast this
      haveI : IsEmpty (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ) :=
        Qsqrtd.Imaginary.isEmpty_fractionRing_realEmbeddings d hdneg
      rcases hreal with ⟨σ⟩
      exact isEmptyElim σ
    let σpos : FractionRing R →+* ℝ :=
      (Qsqrtd.realEmbeddingPos d hd_nonneg_real).toRingHom.comp e.toRingHom
    have hσpos_y :
        σpos (y : FractionRing R) = Qsqrtd.realEmbeddingPos d hd_nonneg_real z := rfl
    have hσpos_τy :
        σpos (τy : FractionRing R) = Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
      calc
        σpos (τy : FractionRing R) =
            Qsqrtd.realEmbeddingPos d hd_nonneg_real
              (e ((conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ)))
                (y : FractionRing R))) := rfl
        _ =
            Qsqrtd.realEmbeddingPos d hd_nonneg_real
              (QuadraticField.conjAut (Qsqrtd (d : ℚ)) (e (y : FractionRing R))) := by
          rw [fractionRing_algEquiv_conjAutFractionRingAlgEquiv]
        _ = Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
          simpa [z] using qsqrt_realEmbeddingPos_conjAut d hd_nonneg_real z
    have hratio :
        0 <
          Qsqrtd.realEmbeddingPos d hd_nonneg_real z /
            Qsqrtd.realEmbeddingNeg d hd_nonneg_real z := by
      have hxσ := hxpos σpos
      rw [hy] at hxσ
      change 0 < σpos ((y * τy⁻¹ : (FractionRing R)ˣ) : FractionRing R) at hxσ
      simpa [div_eq_mul_inv, hσpos_y, hσpos_τy] using hxσ
    rcases div_pos_iff.mp hratio with hsign | hsign
    · left
      intro σ
      let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
        (σ.comp e.symm.toRingHom).toRatAlgHom
      have hσy :
          σ (y : FractionRing R) = φ (e (y : FractionRing R)) :=
        qsqrt_ringHom_eval_eq_algHom_eval d σ (y : FractionRing R)
      rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
      · rw [hσy, hφ]
        simpa [z] using hsign.1
      · rw [hσy, hφ]
        simpa [z] using hsign.2
    · right
      intro σ
      let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
        (σ.comp e.symm.toRingHom).toRatAlgHom
      have hσy :
          σ (y : FractionRing R) = φ (e (y : FractionRing R)) :=
        qsqrt_ringHom_eval_eq_algHom_eval d σ (y : FractionRing R)
      rcases qsqrt_algHom_eq_realEmbeddingPos_or_neg d hd_nonneg_real φ with hφ | hφ
      · have hyneg : σ (y : FractionRing R) < 0 := by
          rw [hσy, hφ]
          simpa [z] using hsign.1
        simpa using neg_pos.mpr hyneg
      · have hyneg : σ (y : FractionRing R) < 0 := by
          rw [hσy, hφ]
          simpa [z] using hsign.2
        simpa using neg_pos.mpr hyneg
  · left
    intro σ
    exact False.elim (hreal ⟨σ⟩)

/-- Positivity adjustment boundary for the quadratic Hilbert-90 coboundary. If a
totally positive multiplier is an ordinary conjugation coboundary, the
coboundary representative can be chosen totally positive. -/
theorem exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    {x y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hy :
      x =
        y * (Units.mapEquiv (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹) :
    ∃ z : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (z : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        x =
          z *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv z)⁻¹ := by
  obtain hypos | hyneg :=
    qsqrt_isTotallyPositive_or_neg_isTotallyPositive_of_totallyPositive_coboundary d hxpos hy
  · exact ⟨y, hypos, hy⟩
  · refine ⟨-y, hyneg, ?_⟩
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let σy :=
      Units.mapEquiv
        ((conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv :
          FractionRing R ≃* FractionRing R) y
    have hmap_neg :
        Units.mapEquiv
            (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv (-y) =
          -σy := by
      ext
      simp [σy]
    calc
      x =
          y *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹ := hy
      _ =
          (-y) *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv (-y))⁻¹ := by
        rw [hmap_neg]
        simp [σy]

/-- Narrow Hilbert-90 boundary. A totally positive principal multiplier relating
an ideal to its conjugate should be a totally positive conjugation coboundary. -/
theorem exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
          toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
            (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
        FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
          (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ y : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (y : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) ∧
        x =
          y *
            (Units.mapEquiv
              (conjAutFractionRingAlgEquiv (Qsqrtd (d : ℚ))).toRingEquiv y)⁻¹ := by
  obtain ⟨y, hy⟩ :=
    exists_conjAut_coboundary_of_tp_multiplier_to_conjAut d I hxpos hconj
  exact exists_totallyPositive_conjAut_coboundary_of_conjAut_coboundary d hxpos hy

/-- A coboundary multiplier turns the relation `I * (x) = σ(I)` into the
fractional-ideal equality `I * (y) = σ(I) * (σ y)`. -/
theorem fractionalRep_eq_conjAutFractionalRep_of_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I) *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K))
          (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) := by
  let R := NumberField.RingOfIntegers K
  let σy : (FractionRing R)ˣ :=
    Units.mapEquiv
      ((conjAutFractionRingAlgEquiv K).toRingEquiv : FractionRing R ≃* FractionRing R) y
  have hxy : x * σy = y := by
    calc
      x * σy = (y * σy⁻¹) * σy := by
        rw [hy]
      _ = y * (σy⁻¹ * σy) := by
        rw [mul_assoc]
      _ = y := by
        rw [inv_mul_cancel, mul_one]
  calc
    FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) y =
        FractionalIdeal.mk0 (FractionRing R) I *
          toPrincipalIdeal R (FractionRing R) (x * σy) := by
      rw [hxy]
    _ =
        FractionalIdeal.mk0 (FractionRing R) I *
          (toPrincipalIdeal R (FractionRing R) x * toPrincipalIdeal R (FractionRing R) σy) := by
      rw [map_mul]
    _ =
        (FractionalIdeal.mk0 (FractionRing R) I * toPrincipalIdeal R (FractionRing R) x) *
          toPrincipalIdeal R (FractionRing R) σy := by
      rw [mul_assoc]
    _ =
        FractionalIdeal.mk0 (FractionRing R) (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal R (FractionRing R) σy := by
      rw [hconj]

/-- The base-ring-equivalence image of an integral fractional representative is
the fractional representative of the conjugate integral ideal. -/
theorem ringEquivMap_conjAut_mk0
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I) =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
        (conjAutNonzeroIdealMulEquiv K I) := by
  let R := NumberField.RingOfIntegers K
  change
    FractionalIdeal.ringEquivMap
        (K := FractionRing R) (L := FractionRing R)
        (conjAutRingOfIntegers K)
        ((I : Ideal R) : FractionalIdeal R⁰ (FractionRing R)) =
      (((conjAutNonzeroIdealMulEquiv K I : (Ideal R)⁰) : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R))
  rw [FractionalIdeal.ringEquivMap_coeIdeal]
  simp [coe_conjAutNonzeroIdealMulEquiv_apply]

/-- The base-ring-equivalence image of a principal fractional ideal generated by
`y` is the principal fractional ideal generated by the conjugate of `y`. -/
theorem ringEquivMap_conjAut_toPrincipalIdeal
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y :
            FractionalIdeal (NumberField.RingOfIntegers K)⁰
              (FractionRing (NumberField.RingOfIntegers K))) =
      (toPrincipalIdeal (NumberField.RingOfIntegers K)
        (FractionRing (NumberField.RingOfIntegers K))
        (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y) :
          FractionalIdeal (NumberField.RingOfIntegers K)⁰
            (FractionRing (NumberField.RingOfIntegers K))) := by
  let R := NumberField.RingOfIntegers K
  rw [coe_toPrincipalIdeal, coe_toPrincipalIdeal, FractionalIdeal.ringEquivMap_spanSingleton]
  rfl

/-- Rephrase the explicit conjugate-factorization equality as fixedness under
the fractional-ideal map induced by ring-of-integers conjugation. -/
theorem ringEquivMap_conjAut_fractionalRep_eq_self_of_eq_conjAutFractionalRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    FractionalIdeal.ringEquivMap
        (K := FractionRing (NumberField.RingOfIntegers K))
        (L := FractionRing (NumberField.RingOfIntegers K))
        (conjAutRingOfIntegers K)
        (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y) =
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
        toPrincipalIdeal (NumberField.RingOfIntegers K)
          (FractionRing (NumberField.RingOfIntegers K)) y := by
  let R := NumberField.RingOfIntegers K
  rw [FractionalIdeal.ringEquivMap_mul, ringEquivMap_conjAut_mk0,
    ringEquivMap_conjAut_toPrincipalIdeal]
  exact (congrArg Units.val hfixed).symm

/-- A denominator-cleared integral representative using a conjugation-invariant
square denominator. If `a` is a denominator for `F`, this is
`(a * σ a ^ 2) * F.num`, whose associated fractional ideal is
`(a * σ a)^2 * F`. -/
noncomputable def conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))) :
    Ideal (NumberField.RingOfIntegers K) :=
  let a : NumberField.RingOfIntegers K := F.den
  let b : NumberField.RingOfIntegers K := conjAutRingOfIntegers K a
  Ideal.span ({a * b ^ 2} : Set (NumberField.RingOfIntegers K)) * F.num

/-- The conjugation-invariant integral representative is nonzero when the
fractional ideal is nonzero. -/
theorem conjInvariantIntegralRep_mem_nonZeroDivisors
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    {F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))}
    (hF : F ≠ 0) :
    conjInvariantIntegralRep K F ∈ (Ideal (NumberField.RingOfIntegers K))⁰ := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.den.prop
  have hb0 : b ≠ 0 := by
    dsimp [b]
    intro hb
    exact ha0 ((conjAutRingOfIntegers K).injective (by simpa using hb))
  rw [mem_nonZeroDivisors_iff_ne_zero, conjInvariantIntegralRep]
  dsimp [a, b]
  apply mul_ne_zero
  · rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 (pow_ne_zero 2 hb0)
  · rwa [ne_eq, FractionalIdeal.num_eq_zero_iff]

/-- As a fractional ideal, the conjugation-invariant integral representative is
the original fractional ideal multiplied by a square denominator. -/
theorem coe_conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K))) :
    ((conjInvariantIntegralRep K F : Ideal (NumberField.RingOfIntegers K)) :
        FractionalIdeal (NumberField.RingOfIntegers K)⁰
          (FractionRing (NumberField.RingOfIntegers K))) =
      FractionalIdeal.spanSingleton (NumberField.RingOfIntegers K)⁰
          (algebraMap (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (((F.den : NumberField.RingOfIntegers K) *
              conjAutRingOfIntegers K (F.den : NumberField.RingOfIntegers K)) ^ 2)) *
        F := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.den
  let b : R := conjAutRingOfIntegers K a
  change ((Ideal.span ({a * b ^ 2} : Set R) * F.num : Ideal R) :
      FractionalIdeal R⁰ (FractionRing R)) =
    FractionalIdeal.spanSingleton R⁰
        (algebraMap R (FractionRing R) ((a * b) ^ 2)) * F
  calc
    ((Ideal.span ({a * b ^ 2} : Set R) * F.num : Ideal R) :
        FractionalIdeal R⁰ (FractionRing R)) =
        (Ideal.span ({a * b ^ 2} : Set R) : FractionalIdeal R⁰ (FractionRing R)) *
          (F.num : FractionalIdeal R⁰ (FractionRing R)) := by
      rw [FractionalIdeal.coeIdeal_mul]
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) (a * b ^ 2)) *
          (F.num : FractionalIdeal R⁰ (FractionRing R)) := by
      rw [FractionalIdeal.coeIdeal_span_singleton]
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) (a * b ^ 2)) *
          (FractionalIdeal.spanSingleton R⁰ (algebraMap R (FractionRing R) a) * F) := by
      rw [FractionalIdeal.den_mul_self_eq_num']
    _ =
        FractionalIdeal.spanSingleton R⁰
            (algebraMap R (FractionRing R) ((a * b) ^ 2)) * F := by
      rw [← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton]
      congr 1
      simp [pow_two, mul_left_comm, mul_comm]

/-- The product of an algebraic integer and its conjugate is fixed by
ring-of-integers conjugation. -/
theorem conjAutRingOfIntegers_mul_conj_fixed
    (K : Type*) [Field K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (a : NumberField.RingOfIntegers K) :
    conjAutRingOfIntegers K (a * conjAutRingOfIntegers K a) =
      a * conjAutRingOfIntegers K a := by
  rw [map_mul, conjAutRingOfIntegers_apply_apply, mul_comm]

/-- The conjugation-invariant integral representative is an ambiguous ideal when
the original fractional ideal is fixed by fractional-ideal conjugation. -/
theorem conjInvariantIntegralRep_isAmbiguous
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ)
    (hFfixed :
      FractionalIdeal.ringEquivMap
          (K := FractionRing (NumberField.RingOfIntegers K))
          (L := FractionRing (NumberField.RingOfIntegers K))
          (conjAutRingOfIntegers K) F.1 = F.1) :
    IsAmbiguousIdeal (conjAutRingOfIntegers K)
      (conjInvariantIntegralRep K F.1) := by
  let R := NumberField.RingOfIntegers K
  let σ := conjAutRingOfIntegers K
  let c : R := (F.1.den : R) * σ (F.1.den : R)
  have hc : σ c = c := by
    dsimp [c, σ]
    exact conjAutRingOfIntegers_mul_conj_fixed K (F.1.den : R)
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
theorem exists_tp_multiplier_conjInvariantIntegralRep
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (F : (FractionalIdeal (NumberField.RingOfIntegers K)⁰
      (FractionRing (NumberField.RingOfIntegers K)))ˣ) :
    ∃ t : (FractionRing (NumberField.RingOfIntegers K))ˣ,
      NarrowClassGroup.IsTotallyPositive
        (t : FractionRing (NumberField.RingOfIntegers K)) ∧
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            ⟨conjInvariantIntegralRep K F.1,
              conjInvariantIntegralRep_mem_nonZeroDivisors K F.ne_zero⟩ *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) t =
        F := by
  let R := NumberField.RingOfIntegers K
  let a : R := F.1.den
  let b : R := conjAutRingOfIntegers K a
  let c : R := a * b
  let z : FractionRing R := algebraMap R (FractionRing R) c
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp F.1.den.prop
  have hb0 : b ≠ 0 := by
    dsimp [b]
    intro hb
    exact ha0 ((conjAutRingOfIntegers K).injective (by simpa using hb))
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
        have hzinv : z ^ 2 * (z⁻¹ ^ 2) = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hz0, one_pow]
        rw [FractionalIdeal.spanSingleton_mul_spanSingleton, hzinv]
      _ = F.1 := by
        rw [FractionalIdeal.spanSingleton_one, mul_one]

/-- Integral clearing boundary for a conjugation-stable fractional representative.
If the fractional representative `I * (y)` matches its conjugate factorization,
then an ambiguous integral ideal represents the same narrow class, up to a
totally positive principal multiplier. -/
theorem exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) ∧
        ∃ t : (FractionRing (NumberField.RingOfIntegers K))ˣ,
          NarrowClassGroup.IsTotallyPositive
            (t : FractionRing (NumberField.RingOfIntegers K)) ∧
            FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) J *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) t =
              FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
                toPrincipalIdeal (NumberField.RingOfIntegers K)
                  (FractionRing (NumberField.RingOfIntegers K)) y := by
  let R := NumberField.RingOfIntegers K
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

/-- Integral clearing boundary for a conjugation-stable fractional representative.
If the fractional representative `I * (y)` matches its conjugate factorization,
then it has an ambiguous integral ideal representative in the same narrow
class. -/
theorem exists_integralIdeal_ambiguous_fractionalRep_of_conjAutFractionalRep_eq
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    (y : (FractionRing (NumberField.RingOfIntegers K))ˣ)
    (hfixed :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) y =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
            (conjAutNonzeroIdealMulEquiv K I) *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K))
            (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  obtain ⟨J, hJamb, t, htpos, ht⟩ :=
    exists_ambiguousIntegralClearing_of_conjAutFractionalRep_eq K I y hfixed
  refine ⟨J, ?_, hJamb⟩
  rw [← NarrowClassGroup.mk_mk0]
  exact NarrowClassGroup.mk_eq_mk.mpr ⟨⟨t, htpos⟩, ht⟩

/-- Integral clearing boundary for a coboundary-adjusted fractional ideal. Under
the coboundary relation, the fractional ideal `I * (y)` should have an ambiguous
integral representative in the same narrow class. -/
theorem exists_integralIdeal_ambiguous_fractionalRep_of_conjAut_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  exact
    exists_integralIdeal_ambiguous_fractionalRep_of_conjAutFractionalRep_eq
      K I y (fractionalRep_eq_conjAutFractionalRep_of_coboundary K I hy hconj)

/-- Coboundary-to-ideal boundary. If the conjugation multiplier is a totally
positive coboundary, multiplying by the coboundary gives an ambiguous integral
ideal representative in the same narrow class. -/
theorem exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_conjAut_coboundary
    (K : Type*) [Field K] [NumberField K] [Algebra ℚ K]
    [QuadraticField K] [QuadraticField.Conj K]
    (I : (Ideal (NumberField.RingOfIntegers K))⁰)
    {x y : (FractionRing (NumberField.RingOfIntegers K))ˣ}
    (hypos : NarrowClassGroup.IsTotallyPositive
      (y : FractionRing (NumberField.RingOfIntegers K)))
    (hy :
      x = y * (Units.mapEquiv (conjAutFractionRingAlgEquiv K).toRingEquiv y)⁻¹)
    (hconj :
      FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
          toPrincipalIdeal (NumberField.RingOfIntegers K)
            (FractionRing (NumberField.RingOfIntegers K)) x =
        FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K))
          (conjAutNonzeroIdealMulEquiv K I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers K))⁰,
      NarrowClassGroup.mk0 J = NarrowClassGroup.mk0 I ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers K)
          (J : Ideal (NumberField.RingOfIntegers K)) := by
  obtain ⟨J, hJmk, hJamb⟩ :=
    exists_integralIdeal_ambiguous_fractionalRep_of_conjAut_coboundary
      K I hy hconj
  refine ⟨J, ?_, hJamb⟩
  have hmk :
      NarrowClassGroup.mk (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I) =
        NarrowClassGroup.mk
          (FractionalIdeal.mk0 (FractionRing (NumberField.RingOfIntegers K)) I *
            toPrincipalIdeal (NumberField.RingOfIntegers K)
              (FractionRing (NumberField.RingOfIntegers K)) y) := by
    refine NarrowClassGroup.mk_eq_mk.mpr ?_
    exact ⟨⟨y, hypos⟩, rfl⟩
  exact hJmk.trans hmk.symm

/-- Hilbert-90 adjustment boundary. A representative whose conjugate differs by
a totally positive principal fractional ideal can be changed within the same
narrow class to a genuinely ambiguous integral ideal. -/
theorem exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_tp_multiplier_to_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)]
    (I : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰)
    {x : (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))ˣ}
    (hxpos : NarrowClassGroup.IsTotallyPositive
      (x : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))))
    (hconj :
      FractionalIdeal.mk0
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) I *
        toPrincipalIdeal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))
          (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) x =
      FractionalIdeal.mk0
        (FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))
        (conjAutNonzeroIdealMulEquiv (Qsqrtd (d : ℚ)) I)) :
    ∃ J : (Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))))⁰,
      NarrowClassGroup.mk0 J = NarrowClassGroup.mk0 I ∧
        IsAmbiguousIdeal (conjAutRingOfIntegers (Qsqrtd (d : ℚ)))
          (J : Ideal (NumberField.RingOfIntegers (Qsqrtd (d : ℚ)))) := by
  obtain ⟨y, hypos, hy⟩ :=
    exists_totallyPositive_conjAut_coboundary_of_tp_multiplier_to_conjAut
      d I hxpos hconj
  exact exists_integralIdeal_isAmbiguousIdeal_mk0_eq_of_conjAut_coboundary
    (Qsqrtd (d : ℚ)) I hypos hy hconj

end Internal
end GenusTheory
end ClassGroup
end QuadraticNumberFields
