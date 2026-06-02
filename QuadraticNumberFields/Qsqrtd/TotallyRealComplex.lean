/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import QuadraticNumberFields.Instances
import QuadraticNumberFields.Qsqrtd.Basic
import QuadraticNumberFields.QuadraticField.Classification
import QuadraticNumberFields.QuadraticField.Transport
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.CMField

/-!
# Totally Real, Totally Complex, and CM Field Classification

This file classifies quadratic number fields `Q(√d)` according to the sign of `d`:

* `d > 0`: `Q(√d)` is **totally real** — all embeddings into `ℂ` have real image.
* `d < 0`: `Q(√d)` is **totally complex** and a **CM field** — no embedding has real image,
  and `Q(√d)` is a quadratic extension of its totally real subfield `ℚ`.

## Main Theorems

* `Qsqrtd.isTotallyReal`: `Q(√d)` is totally real when `0 < d`.
* `Qsqrtd.isTotallyComplex`: `Q(√d)` is totally complex when `d < 0`.
* `Qsqrtd.isCMField`: `Q(√d)` is a CM field when `d < 0`.
* `QuadraticField.exists_totallyReal_or_totallyComplex`: every abstract
  quadratic field is classified as real or imaginary after choosing a standard
  squarefree parameter.

## Proof Strategy

For any embedding `φ : Q(√d) →+* ℂ`, we have `φ(ω)² = d` in `ℂ`.
Writing `φ(ω) = a + bi` gives `a² - b² = d` and `2ab = 0`.

* When `d > 0`: the case `a = 0` gives `-b² = d > 0`, a contradiction. So `b = 0`,
  meaning `φ(ω) ∈ ℝ`, hence the embedding is real.
* When `d < 0`: if the embedding were real, then `b = 0`, giving `a² = d < 0`,
  contradicting `a² ≥ 0`.
-/

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and `QuadraticAlgebra.instAlgebra`.
-- NOTE: This is a file-local workaround.
attribute [-instance] DivisionRing.toRatAlgebra

namespace Qsqrtd

section InternalLemmas

variable {d : ℤ} [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- With the `ℚ`-algebra diamond resolved, `IsQuadraticExtension` follows directly from
`QuadraticAlgebra.finrank_eq_two`. This re-derives the instance in the context where
`DivisionRing.toRatAlgebra` is disabled. -/
instance : Algebra.IsQuadraticExtension ℚ (Qsqrtd (d : ℚ)) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two (d : ℚ) 0

/-- For any infinite place `v` of `Q(√d)`, the image of `ω` satisfies `φ(ω)² = d`. -/
theorem embedding_omega_sq
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    v.embedding QuadraticAlgebra.omega ^ 2 = ((d : ℚ) : ℂ) := by
  rw [sq, ← map_mul, QuadraticAlgebra.omega_mul_omega_eq_add]
  simp [Algebra.smul_def]

/-- The real part of `φ(ω)²` decomposes as `re² - im²`. -/
private theorem embedding_omega_sq_re
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    (v.embedding QuadraticAlgebra.omega).re ^ 2 -
    (v.embedding QuadraticAlgebra.omega).im ^ 2 = (d : ℝ) := by
  have := congr_arg Complex.re (embedding_omega_sq v)
  simp [sq, Complex.mul_re] at this; linarith

/-- The imaginary part of `φ(ω)²` gives `2 · re · im = 0`. -/
private theorem embedding_omega_sq_im
    (v : NumberField.InfinitePlace (Qsqrtd (d : ℚ))) :
    2 * (v.embedding QuadraticAlgebra.omega).re *
    (v.embedding QuadraticAlgebra.omega).im = 0 := by
  have := congr_arg Complex.im (embedding_omega_sq v)
  simp [sq, Complex.mul_im] at this; linarith

/-- When `d > 0`, the image of `ω` under any embedding is real (imaginary part is zero). -/
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

/-- If `im(φ(ω)) = 0`, then `conj ∘ φ = φ`. -/
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

/-- A real quadratic field `Q(√d)` with `d > 0` is totally real:
all embeddings into `ℂ` have image contained in `ℝ`. -/
theorem isTotallyReal (hd : 0 < d) :
    NumberField.IsTotallyReal (Qsqrtd (d : ℚ)) := by
  exact {
    isReal := fun v => by
      rw [NumberField.InfinitePlace.isReal_iff, NumberField.ComplexEmbedding.isReal_iff]
      simpa using conjugate_embedding_eq v (embedding_omega_im_eq_zero v hd)
  }

/-- An imaginary quadratic field `Q(√d)` with `d < 0` is totally complex:
no embedding into `ℂ` has image contained in `ℝ`. -/
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

/-- An imaginary quadratic field `Q(√d)` with `d < 0` is a CM field. -/
theorem isCMField (hd : d < 0) :
    NumberField.IsCMField (Qsqrtd (d : ℚ)) := by
  letI := isTotallyComplex d hd
  exact NumberField.IsCMField.ofCMExtension ℚ (Qsqrtd (d : ℚ))

end InfinitePlaceClassification

end Qsqrtd

namespace QuadraticField

variable {K : Type*} [Field K] [Algebra ℚ K]
variable (d : ℤ) [Fact (¬ IsSquare ((d : ℤ) : ℚ))]

/-- Transport total reality from the standard model `Qsqrtd d` back to an
abstract field identified with it. -/
theorem isTotallyReal_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : 0 < d) :
    NumberField.IsTotallyReal K := by
  exact (isTotallyReal_iff_of_algEquiv e).mpr (Qsqrtd.isTotallyReal d hd)

/-- Transport total complexity from the standard model `Qsqrtd d` back to an
abstract field identified with it. -/
theorem isTotallyComplex_of_algEquiv_qsqrtd
    (e : K ≃ₐ[ℚ] Qsqrtd (d : ℚ)) (hd : d < 0) :
    NumberField.IsTotallyComplex K := by
  exact (isTotallyComplex_iff_of_algEquiv e).mpr (Qsqrtd.isTotallyComplex d hd)

/-- Every abstract quadratic field is either real or imaginary after choosing
a standard squarefree integer parameter.

This packages the intended workflow for infinite-place classification:
`exists_algEquiv_qsqrtd` chooses `d`, `Qsqrtd.isTotallyReal` or
`Qsqrtd.isTotallyComplex` computes on the standard model, and the transport API
moves the result back to `K`. -/
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
