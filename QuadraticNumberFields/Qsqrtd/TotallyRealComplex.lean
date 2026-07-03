/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Transport
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Totally Real, Totally Complex, and CM Field Classification

This file classifies the quadratic field `Q(√d)` by the sign of `d`.

If `d > 0`, every complex embedding has real image. If `d < 0`, no complex
embedding has real image, and `Q(√d)` is a CM field over `ℚ`.

The main declarations are:

* `Qsqrtd.isTotallyReal`: `Q(√d)` is totally real when `0 < d`.
* `Qsqrtd.isTotallyComplex`: `Q(√d)` is totally complex when `d < 0`.
* `Qsqrtd.isCMField`: `Q(√d)` is a CM field when `d < 0`.
* `QuadraticField.exists_totallyReal_or_totallyComplex`: every abstract
  quadratic field is classified as real or imaginary after choosing a standard
  squarefree parameter.

The proof uses the equation `φ(ω)^2 = d`. If `φ(ω) = a + bi`, then
`a^2 - b^2 = d` and `2ab = 0`. For `d > 0`, the second equation forces
`b = 0`. For `d < 0`, the assumption `b = 0` would give `a^2 = d < 0`.
-/

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and `QuadraticAlgebra.instAlgebra`.
-- NOTE: This is a file-local workaround.
attribute [-instance] DivisionRing.toRatAlgebra

namespace Qsqrtd

section RealEmbeddings

/-- The `ℚ`-algebra homomorphism `ℚ(√d) → ℝ` that sends `√d` to a chosen real
root `r` of `X^2 - d`. -/
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

theorem realEmbeddingPos_apply (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbeddingPos d hd z = (z.re : ℝ) + (z.im : ℝ) * Real.sqrt (d : ℝ) :=
  realEmbedding_apply d (Real.sqrt (d : ℝ)) (by simpa [sq] using Real.sq_sqrt hd) z

theorem realEmbeddingNeg_apply (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    realEmbeddingNeg d hd z = (z.re : ℝ) - (z.im : ℝ) * Real.sqrt (d : ℝ) := by
  rw [realEmbeddingNeg, realEmbedding_apply]
  ring

/-- For nonnegative `d`, the quadratic norm is the product of the two real
embeddings. -/
theorem norm_eq_realEmbeddingPos_mul_realEmbeddingNeg (d : ℤ) (hd : 0 ≤ (d : ℝ))
    (z : Qsqrtd (d : ℚ)) :
    (Qsqrtd.norm z : ℝ) = realEmbeddingPos d hd z * realEmbeddingNeg d hd z := by
  rw [realEmbeddingPos_apply, realEmbeddingNeg_apply]
  simp [Qsqrtd.norm, QuadraticAlgebra.norm_def]
  ring_nf
  rw [Real.sq_sqrt hd]
  ring

/-- If an element is positive under both real embeddings, then its quadratic norm
is positive. -/
theorem norm_pos_of_realEmbedding_pos (d : ℤ) (hd : 0 ≤ (d : ℝ))
    {z : Qsqrtd (d : ℚ)}
    (hpos : 0 < realEmbeddingPos d hd z)
    (hneg : 0 < realEmbeddingNeg d hd z) :
    0 < (Qsqrtd.norm z : ℝ) := by
  rw [norm_eq_realEmbeddingPos_mul_realEmbeddingNeg d hd z]
  exact mul_pos hpos hneg

end RealEmbeddings

section InternalLemmas

variable {d : ℤ} [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- With the `ℚ`-algebra diamond resolved, `IsQuadraticExtension` follows from
`QuadraticAlgebra.finrank_eq_two`. This is the instance needed after disabling
`DivisionRing.toRatAlgebra`. -/
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

/-- The imaginary part of `φ(ω)^2` gives `2 * re * im = 0`. -/
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
    NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := by
  exact {
    isReal := fun v => by
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      simpa using conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)
  }

/-- A quadratic field `Q(√d)` with `d < 0` is totally complex. -/
theorem isTotallyComplex (hd : d < 0) :
    NumberField.IsTotallyComplex (Qsqrtd (d : ℚ)) := by
  exact {
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
instance isCMField (hd : d < 0) :
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

/-- Transport total reality from `Qsqrtd d` to an abstract field isomorphic to
it. -/
theorem isTotallyReal_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : 0 < d) :
    NumberField.IsTotallyReal K := by
  exact (NumberField.isTotallyReal_iff_ofAlgEquiv e).mpr (Qsqrtd.isTotallyReal d hd)

/-- Transport total complexity from `Qsqrtd d` to an abstract field isomorphic
to it. -/
theorem isTotallyComplex_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : d < 0) :
    NumberField.IsTotallyComplex K := by
  exact (NumberField.isTotallyComplex_iff_ofAlgEquiv e).mpr (Qsqrtd.isTotallyComplex d hd)

/-- Every abstract quadratic field is real or imaginary after choosing a
standard squarefree integer parameter.

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
