/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Conj
import QuadraticNumberFields.QuadraticField.Transport
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Totally real and totally complex quadratic fields

This file proves the sign test for the quadratic field `Q(√d)`.

If `d > 0`, every embedding into `ℂ` has real image. If `d < 0`, none of the
embeddings into `ℂ` has real image, and `Q(√d)` is a CM field over `ℚ`.

The main declarations are:

* `Qsqrtd.isTotallyReal`: `Q(√d)` is totally real when `0 < d`.
* `Qsqrtd.isTotallyComplex`: `Q(√d)` is totally complex when `d < 0`.
* `Qsqrtd.isCMField`: `Q(√d)` is a CM field when `d < 0`.
* `QuadraticField.exists_totallyReal_or_totallyComplex`: every abstract
  quadratic field is either real or imaginary after choosing a squarefree
  `Qsqrtd` parameter.

The proof computes with `φ(ω)^2 = d`. If `φ(ω) = a + bi`, then
`a^2 - b^2 = d` and `2ab = 0`. For `d > 0`, the second equation forces
`b = 0`. For `d < 0`, the assumption `b = 0` would give `a^2 = d < 0`.
-/

-- Disable the rational algebra instance that conflicts with `QuadraticAlgebra.instAlgebra`.
attribute [-instance] DivisionRing.toRatAlgebra

namespace Qsqrtd

section RealEmbeddings

/-- The `ℚ`-algebra homomorphism `ℚ(√d) → ℝ` sending `ω` to a real root `r` of
`X^2 - d`. -/
noncomputable def realEmbedding (d : ℤ) (r : ℝ) (hr : r * r = (d : ℝ)) :
    Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift (R := ℚ) (a := (d : ℚ)) (b := (0 : ℚ))
    ⟨r, hr.trans (by simp [Algebra.smul_def])⟩

/-- The embedding `realEmbedding d r hr` sends `x + y√d` to `x + y r`. -/
theorem realEmbedding_apply (d : ℤ) (r : ℝ) (hr : r * r = (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbedding d r hr z = (z.re : ℝ) + (z.im : ℝ) * r := by
  change (QuadraticAlgebra.lift (R := ℚ) (a := (d : ℚ)) (b := (0 : ℚ))
      ⟨r, hr.trans (by simp [Algebra.smul_def])⟩ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) z =
    (z.re : ℝ) + (z.im : ℝ) * r
  simp [QuadraticAlgebra.lift, Algebra.smul_def]

/-- The real embedding `ℚ(√d) → ℝ` sending `√d` to `sqrt d`. -/
noncomputable def realEmbeddingPos (d : ℤ) (hd : 0 ≤ (d : ℝ)) :
    Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
  realEmbedding d (Real.sqrt (d : ℝ)) (by simpa [sq] using Real.sq_sqrt hd)

/-- The real embedding `ℚ(√d) → ℝ` sending `√d` to `-sqrt d`. -/
noncomputable def realEmbeddingNeg (d : ℤ) (hd : 0 ≤ (d : ℝ)) :
    Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ :=
  realEmbedding d (-Real.sqrt (d : ℝ)) (by
    rw [neg_mul_neg]
    simpa [sq] using Real.sq_sqrt hd)

/-- The positive real embedding sends `x + y√d` to `x + y * sqrt d`. -/
theorem realEmbeddingPos_apply (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbeddingPos d hd z = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ) :=
  realEmbedding_apply d (Real.sqrt (d : ℝ)) (by simpa [sq] using Real.sq_sqrt hd) z

/-- The negative real embedding sends `x + y√d` to `x - y * sqrt d`. -/
theorem realEmbeddingNeg_apply (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbeddingNeg d hd z = (z.re : ℝ) - (z.im : ℝ) * Real.sqrt (d : ℝ) := by
  rw [realEmbeddingNeg, realEmbedding_apply]
  ring

/-- A real embedding of `ℚ(√d)` sends `ω` to `sqrt d` or to its negative. -/
theorem algHom_omega_eq_sqrt_or_neg (d : ℤ) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
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

/-- The real embeddings of `ℚ(√d)` are `realEmbeddingPos` and `realEmbeddingNeg`. -/
theorem algHom_eq_realEmbeddingPos_or_neg
    (d : ℤ) (hd : 0 ≤ (d : ℝ)) (φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ) :
    φ = realEmbeddingPos d hd ∨ φ = realEmbeddingNeg d hd := by
  rcases algHom_omega_eq_sqrt_or_neg d φ with hω | hω
  · left
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = realEmbeddingPos d hd QuadraticAlgebra.omega
    rw [hω, realEmbeddingPos_apply]
    simp
  · right
    apply QuadraticAlgebra.algHom_ext
    change φ QuadraticAlgebra.omega = realEmbeddingNeg d hd QuadraticAlgebra.omega
    rw [hω, realEmbeddingNeg_apply]
    simp

/-- Applying `star` turns the positive real embedding into the negative one. -/
theorem realEmbeddingPos_star (d : ℤ) (hd : 0 ≤ (d : ℝ)) (z : Qsqrtd (d : ℚ)) :
    realEmbeddingPos d hd (star z) = realEmbeddingNeg d hd z := by
  rw [realEmbeddingPos_apply, realEmbeddingNeg_apply]
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
  ring

/-- Quadratic conjugation turns the positive real embedding into the negative one. -/
theorem realEmbeddingPos_conjAut
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbeddingPos d hd (QuadraticField.conjAut (Qsqrtd (d : ℚ)) z) =
      realEmbeddingNeg d hd z := by
  change realEmbeddingPos d hd (star z) = realEmbeddingNeg d hd z
  exact realEmbeddingPos_star d hd z

/-- Positivity under all real embeddings is equivalent to positivity under
`realEmbeddingPos` and `realEmbeddingNeg`. -/
theorem forall_algHom_pos_iff_realEmbeddingPos_and_realEmbeddingNeg_pos
    (d : ℤ) (hd : 0 ≤ (d : ℝ)) (z : Qsqrtd (d : ℚ)) :
    (∀ σ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ, 0 < σ z) ↔
      0 < realEmbeddingPos d hd z ∧ 0 < realEmbeddingNeg d hd z := by
  constructor
  · intro hz
    exact ⟨hz (realEmbeddingPos d hd), hz (realEmbeddingNeg d hd)⟩
  · intro hz σ
    rcases algHom_eq_realEmbeddingPos_or_neg d hd σ with hσ | hσ
    · rw [hσ]
      exact hz.1
    · rw [hσ]
      exact hz.2

/-- A conjugation-fixed element that is positive under every real embedding has
positive rational coordinate. -/
theorem re_pos_of_forall_algHom_pos_of_star_self
    (d : ℤ) (hd : 0 ≤ (d : ℝ)) {z : Qsqrtd (d : ℚ)}
    (hzpos : ∀ σ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ, 0 < σ z)
    (hfix : star z = z) :
    0 < z.re := by
  have hsign := (forall_algHom_pos_iff_realEmbeddingPos_and_realEmbeddingNeg_pos d hd z).mp hzpos
  have hpos : 0 < realEmbeddingPos d hd z := hsign.1
  rw [_root_.eq_algebraMap_re_of_star_self hfix] at hpos
  have hposR : (0 : ℝ) < z.re := by
    simpa using hpos
  exact_mod_cast hposR

/-- For `d ≥ 0`, the quadratic norm is the product of the two real
embeddings. -/
theorem norm_eq_realEmbeddingPos_mul_realEmbeddingNeg (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    (Qsqrtd.norm z : ℝ) = realEmbeddingPos d hd z * realEmbeddingNeg d hd z := by
  rw [realEmbeddingPos_apply, realEmbeddingNeg_apply]
  simp [Qsqrtd.norm, QuadraticAlgebra.norm_def]
  ring_nf
  rw [Real.sq_sqrt hd]
  ring

/-- An element positive under both real embeddings has positive quadratic norm. -/
theorem norm_pos_of_realEmbedding_pos (d : ℤ) (hd : 0 ≤ (d : ℝ))
    {z : Qsqrtd (d : ℚ)}
    (hpos : 0 < realEmbeddingPos d hd z)
    (hneg : 0 < realEmbeddingNeg d hd z) :
    0 < (Qsqrtd.norm z : ℝ) := by
  rw [norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hd z]
  exact mul_pos hpos hneg

end RealEmbeddings

section FractionRingEvaluation

/-- Evaluating `w` by `σ` is the same as evaluating its image in `Q(√d)` by the
`ℚ`-algebra hom obtained from `σ.comp e.symm.toRingHom`. -/
theorem ringHom_eval_eq_algHom_eval
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
  have hw : e.toRingEquiv.symm (e w) = w := e.toRingEquiv.symm_apply_apply w
  rw [hw]

/-- The real embeddings of the fraction field of `𝓞(ℚ(√d))` are induced by
`realEmbeddingPos` and `realEmbeddingNeg` through the canonical fraction-field
equivalence. -/
theorem fractionRing_ringHom_eq_realEmbeddingPos_or_neg
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd : 0 ≤ (d : ℝ))
    (σ : FractionRing (NumberField.RingOfIntegers (Qsqrtd (d : ℚ))) →+* ℝ) :
    let R := NumberField.RingOfIntegers (Qsqrtd (d : ℚ))
    let e : FractionRing R ≃ₐ[R] Qsqrtd (d : ℚ) :=
      FractionRing.algEquiv R (Qsqrtd (d : ℚ))
    σ = (realEmbeddingPos d hd).toRingHom.comp e.toRingHom ∨
      σ = (realEmbeddingNeg d hd).toRingHom.comp e.toRingHom := by
  intro R e
  let φ : Qsqrtd (d : ℚ) →ₐ[ℚ] ℝ := (σ.comp e.symm.toRingHom).toRatAlgHom
  rcases algHom_eq_realEmbeddingPos_or_neg d hd φ with hφ | hφ
  · left
    ext w
    have heval := ringHom_eval_eq_algHom_eval d σ w
    change σ w = φ (e w) at heval
    rw [hφ] at heval
    simpa [RingHom.comp_apply] using heval
  · right
    ext w
    have heval := ringHom_eval_eq_algHom_eval d σ w
    change σ w = φ (e w) at heval
    rw [hφ] at heval
    simpa [RingHom.comp_apply] using heval

end FractionRingEvaluation

section InternalLemmas

variable {d : ℤ} [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- The quadratic-extension instance coming from `QuadraticAlgebra.finrank_eq_two`. -/
instance : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

/-- For an infinite place `v` of `Q(√d)`, the image of `ω` satisfies
`φ(ω)^2 = d`. -/
theorem embedding_omega_sq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    v.embedding QuadraticAlgebra.omega ^ 2 = ((d : ℚ) : ℂ) := by
  rw [sq, ← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

/-- The real part of `φ(ω)^2` is `re^2 - im^2`. -/
private theorem embedding_omega_sq_re
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    (v.embedding QuadraticAlgebra.omega).re ^ 2 -
    (v.embedding QuadraticAlgebra.omega).im ^ 2 = (d : ℝ) := by
  have := congr_arg Complex.re (embedding_omega_sq v)
  simp [sq, Complex.mul_re] at this; linarith

/-- The imaginary part of `φ(ω)^2` is `2 * re * im = 0`. -/
private theorem embedding_omega_sq_im
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    2 * (v.embedding QuadraticAlgebra.omega).re *
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have := congr_arg Complex.im (embedding_omega_sq v)
  simp [sq, Complex.mul_im] at this; linarith

/-- When `d > 0`, the image of `ω` under any embedding has imaginary part zero. -/
private theorem embedding_omega_im_eq_zero
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hd : 0 < d) :
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have hre := embedding_omega_sq_re v
  have him := embedding_omega_sq_im v
  rcases mul_eq_zero.mp him with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · rw [h] at hre; simp at hre
      nlinarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).im,
                 (show (d : ℝ) > 0 from by exact_mod_cast hd)]
  · exact h

/-- If `φ(ω)` is real, then complex conjugation fixes `φ`. -/
private theorem conjugate_embedding_eq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ)))
    (hω_im : (v.embedding QuadraticAlgebra.omega).im = 0) :
    NumberField.ComplexEmbedding.conjugate v.embedding = v.embedding := by
  rw [← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    (NumberField.ComplexEmbedding.conjugate v.embedding),
    ← @RingHom.toRatAlgHom_toRingHom (Qsqrtd (d : ℚ)) ℂ _ _ _ _
    v.embedding]
  congr 1
  apply QuadraticAlgebra.algHom_ext
  change (NumberField.ComplexEmbedding.conjugate v.embedding).toRatAlgHom
    QuadraticAlgebra.omega = v.embedding.toRatAlgHom QuadraticAlgebra.omega
  simp only [RingHom.toRatAlgHom_apply, NumberField.ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.mpr hω_im

end InternalLemmas

section InfinitePlaceClassification

variable (d : ℤ) [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- A quadratic field `Q(√d)` with `d > 0` is totally real. -/
theorem isTotallyReal (hd : 0 < d) :
    NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := {
    isReal := fun v => by
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      simpa using conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)
  }

/-- A quadratic field `Q(√d)` with `d < 0` is totally complex. -/
theorem isTotallyComplex (hd : d < 0) :
    NumberField.IsTotallyComplex (Qsqrtd (d : ℚ)) := {
    isComplex := fun v => by
      rw [NumberField.InfinitePlace.isComplex_iff, NumberField.ComplexEmbedding.isReal_iff]
      intro hreal
      have hω_real : (v.embedding QuadraticAlgebra.omega).im = 0 := by
        have h := RingHom.congr_fun hreal QuadraticAlgebra.omega
        simp only [NumberField.ComplexEmbedding.conjugate_coe_eq] at h
        exact Complex.conj_eq_iff_im.mp h
      have hre := embedding_omega_sq_re v
      rw [hω_real] at hre; simp at hre
      linarith [sq_nonneg (v.embedding QuadraticAlgebra.omega).re,
                (show (d : ℝ) < 0 from by exact_mod_cast hd)]
  }

/-- A quadratic field `Q(√d)` with `d < 0` is a CM field. -/
theorem isCMField (hd : d < 0) :
    NumberField.IsCMField (Qsqrtd (d : ℚ)) := by
  letI := isTotallyComplex d hd
  exact NumberField.IsCMField.ofCMExtension ℚ (Qsqrtd (d : ℚ))

/-- An imaginary quadratic field `ℚ(√d)` has one complex place. -/
theorem nrComplexPlaces_eq_one_of_neg (hd : d < 0) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 1 := by
  haveI := isTotallyComplex d hd
  have hfin := finrank_ratAlgebra_eq_two (d : ℚ)
  have hc := NumberField.IsTotallyComplex.finrank (Qsqrtd (d : ℚ))
  have h : 2 = 2 * NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) :=
    hfin.symm.trans hc
  omega

/-- A real quadratic field `ℚ(√d)` has no complex places. -/
theorem nrComplexPlaces_eq_zero_of_pos (hd : 0 < d) :
    NumberField.InfinitePlace.nrComplexPlaces (Qsqrtd (d : ℚ)) = 0 := by
  haveI := isTotallyReal d hd
  exact NumberField.IsTotallyReal.nrComplexPlaces_eq_zero (Qsqrtd (d : ℚ))

end InfinitePlaceClassification

end Qsqrtd

namespace QuadraticField

variable {K : Type*} [Field K] [Algebra ℚ K]
variable (d : ℤ) [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- Transport total reality along an algebra equivalence with `Qsqrtd d`. -/
theorem isTotallyReal_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : 0 < d) :
    NumberField.IsTotallyReal K :=
  (NumberField.isTotallyReal_iff_ofAlgEquiv e).mpr (Qsqrtd.isTotallyReal d hd)

/-- Transport total complexity along an algebra equivalence with `Qsqrtd d`. -/
theorem isTotallyComplex_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : d < 0) :
    NumberField.IsTotallyComplex K :=
  (NumberField.isTotallyComplex_iff_ofAlgEquiv e).mpr (Qsqrtd.isTotallyComplex d hd)

/-- Every abstract quadratic field is real or imaginary after choosing a squarefree
integer parameter.

The proof chooses `d` with `exists_algEquiv_qsqrtd`, proves the statement for
`Qsqrtd d`, then transports it back to `K`. -/
theorem exists_totallyReal_or_totallyComplex
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    ∃ d : ℤ, Squarefree d ∧ d ≠ 1 ∧ Nonempty (K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) ∧
      ((0 < d ∧ NumberField.IsTotallyReal K) ∨
      (d < 0 ∧ NumberField.IsTotallyComplex K)) := by
  obtain ⟨d, hd_sf, hd_ne, ⟨e⟩⟩ := exists_algEquiv_qsqrtd K
  letI : Fact (Squarefree d) := ⟨hd_sf⟩
  letI : Fact (d ≠ 1) := ⟨hd_ne⟩
  rcases lt_trichotomy d 0 with hd_neg | hd_zero | hd_pos
  · exact ⟨d, hd_sf, hd_ne, ⟨e⟩,
      Or.inr ⟨hd_neg, isTotallyComplex_of_algEquiv_qsqrtd d e hd_neg⟩⟩
  · exact False.elim (Squarefree.ne_zero hd_sf hd_zero)
  · exact ⟨d, hd_sf, hd_ne, ⟨e⟩,
      Or.inl ⟨hd_pos, isTotallyReal_of_algEquiv_qsqrtd d e hd_pos⟩⟩

end QuadraticField
