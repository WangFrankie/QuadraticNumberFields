/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import QuadraticNumberFields.Forms.InverseCox
import QuadraticNumberFields.Forms.NormFormBasisChange
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic

/-!
# Cox 7.7 Right Inverse: ideal-class round-trip

Proves the right-inverse law
`formClassToClassGroup (classGroupToFormClass C) = C` at the level of ideal
representatives, for both the `d % 4 ≠ 1` and `d % 4 = 1` branches, via the
principal Cox ideal-generator relations.  The final equivalence is assembled
in `Forms.CoxEquivalence`.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxAssembly

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 ≠ 1`
branch for any chosen oriented basis.  This isolates the remaining Cox
arithmetic to constructing the two nonzero principal generators and the displayed
ideal equality. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_basis_ideal_relation hdneg b
    (idealOfForm_of_mod_four_ne_one d hd4) (idealClassOfForm_of_mod_four_ne_one d hd4)
    (idealOfForm_of_mod_four_ne_one_ne_zero d hd4) (fun Q => rfl) hx hy hrel

/-- A principal-ideal relation proves the right-inverse law for the `d % 4 = 1`
branch for any chosen oriented basis.  This is the half-integral analogue of
`idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_basis_ideal_relation hdneg b
    (idealOfForm_of_mod_four_eq_one d hd4) (idealClassOfForm_of_mod_four_eq_one d hd4)
    (idealOfForm_of_mod_four_eq_one_ne_zero d hd4) (fun Q => rfl) hx hy hrel

/-- In the `d % 4 ≠ 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_ne_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_properEquivalent hdneg b
    (idealClassOfForm_of_mod_four_ne_one d hd4)
    (idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4) R hQR hR

/-- In the `d % 4 = 1` branch, it is enough to prove the right-inverse law after
replacing the norm form attached to an oriented ideal basis by a properly
equivalent representative. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_properEquivalent
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR :
      PrimitivePositiveDefiniteForm.ProperEquivalent
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) R)
    (hR : idealClassOfForm_of_mod_four_eq_one d hd4 R = ClassGroup.mk0 I) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_properEquivalent hdneg b
    (idealClassOfForm_of_mod_four_eq_one d hd4)
    (idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4) R hQR hR

/-- In the `d % 4 ≠ 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  simpa using basis_first_mul_cox_scalar_mem_span_a_mul_ideal b Q e

/-- In the `d % 4 = 1` branch, the scalar generator of the Cox ideal of the norm
form gives one generator of the principal-relation inclusion
`(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_scalar_mem_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    (b.basis 0 : 𝓞K) * e.symm (((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  simpa using basis_first_mul_cox_scalar_mem_span_a_mul_ideal b Q e

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator of the norm form
satisfies the signed classical relation
`α · β_Q = -a_Q · β`, where `(α, β)` is the oriented ideal basis.  The sign is
forced by the orientation convention `N(I) = αᵢβᵣ - αᵣβᵢ`. -/
theorem basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg hI b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) =
      -(((Q.1.a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K)) := by
  intro hI Q e
  have hβQ :
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).re =
        (-(Q.1.b : ℚ)) / 2 ∧
      ((e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) : 𝓞K) : K).im = 1 := by
    have hb_even : Even Q.1.b :=
      even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
    obtain ⟨k, hk⟩ := hb_even
    have hdiv : (-Q.1.b) / 2 = -k := by
      rw [hk]
      omega
    have hk_rat : (Q.1.b : ℚ) / 2 = k := by
      rw [hk]
      norm_num
    have h_embed (x : 𝓞K) : ((x : 𝓞K) : K) = Zsqrtd.toQsqrtdHom d (e x) := by
      simpa [e] using
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one_apply d hd4 x).symm
    rw [h_embed]
    constructor
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
      linarith
    · simp [e, Zsqrtd.toQsqrtdHom, RingEquiv.apply_symm_apply, hdiv]
  -- Orientation determinant: `N(I) = αᵢβᵣ - αᵣβᵢ` (im_val = 1).
  have hNim : ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
      ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im =
      (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) * 1 := by
    have hdet := OrientedBasis.detCoord_eq_neg_absNorm_of_mod_four_ne_one hI hd4 b
    unfold OrientedBasis.detCoord at hdet
    linarith
  have hmain := basis_first_mul_eq_neg_a_mul_basis_second hI b
    (e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d))) 1 hβQ.1 hβQ.2 hNim
  rw [neg_mul] at hmain
  exact hmain

/-- In the `d % 4 = 1` branch, the second Cox ideal generator of the norm form
satisfies the signed classical relation
`α · β_Q = -a_Q · β`, where the Cox generator has `K`-coordinates
`(-b_Q / 2, 1 / 2)`. -/
theorem basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg hI b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      d hd4
    (b.basis 0 : 𝓞K) *
        e.symm ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))) =
      -(((Q.1.a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K)) := by
  intro hI Q e
  have hβQ :
      ((e.symm (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)) :
          𝓞K) : K).re = (-(Q.1.b : ℚ)) / 2 ∧
      ((e.symm (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)) :
          𝓞K) : K).im = (1 : ℚ) / 2 := by
    let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
    let x : 𝓞K := e.symm betaZ
    have hre := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x
    have him := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x
    dsimp [x, e] at hre him
    rw [RingEquiv.apply_symm_apply] at hre him
    have hodd : Odd Q.1.b :=
      odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
    obtain ⟨k, hk⟩ := hodd
    have hdiv : (-(Q.1.b + 1) / 2 : ℤ) = -(k + 1) := by
      rw [hk]
      omega
    have hdiv' : ((-1 + -Q.1.b) / 2 : ℤ) = -1 - k := by
      rw [hk]
      omega
    constructor
    · rw [← hre]
      calc
        ((betaZ.re : ℚ) + (betaZ.im : ℚ) / 2) = ((-1 - k : ℤ) : ℚ) + 1 / 2 := by
          simp [betaZ, hdiv']
        _ = -(Q.1.b : ℚ) / 2 := by
          rw [hk]
          norm_num
          ring
    · simpa [betaZ] using him.symm
  -- Orientation determinant: `N(I) = 2(αᵢβᵣ - αᵣβᵢ)` (im_val = 1/2).
  have hNim : ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
      ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im =
      (Ideal.absNorm (I : Ideal 𝓞K) : ℚ) * (1 / 2) := by
    have hdet := OrientedBasis.detCoord_eq_neg_half_absNorm_of_mod_four_eq_one hI hd4 b
    unfold OrientedBasis.detCoord at hdet
    linarith
  have hmain := basis_first_mul_eq_neg_a_mul_basis_second hI b
    (e.symm ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)))) (1 / 2)
    hβQ.1 hβQ.2 hNim
  rw [neg_mul] at hmain
  exact hmain

/-- In the `d % 4 ≠ 1` branch, the second Cox ideal generator also satisfies
the principal-relation inclusion `(b₀) · β_Q ∈ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    (b.basis 0 : 𝓞K) * e.symm ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
      hdneg hd4 I b
  dsimp only at hrel
  exact basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal b Q e
    ((⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)) (by simpa [Q, e] using hrel)

/-- In the `d % 4 = 1` branch, the second Cox ideal generator also satisfies
the principal-relation inclusion `(b₀) · β_Q ∈ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
      d hd4
    (b.basis 0 : 𝓞K) *
        e.symm ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))) ∈
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q e
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
      hdneg hd4 I b
  dsimp only at hrel
  exact basis_first_mul_cox_ideal_generator_mem_span_a_mul_ideal b Q e
    ((⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)))
    (by simpa [Q, e] using hrel)

/-- In the `d % 4 ≠ 1` branch, the two Cox generator membership lemmas assemble
to the inclusion `(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q ≤
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let betaZ : Zsqrtd d := (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_ne_one, e, betaZ] using
    basis_first_mul_cox_ideal_le_span_a_mul_ideal b Q e betaZ (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 = 1` branch, the two Cox generator membership lemmas assemble
to the inclusion `(b₀) · J(Q_b) ≤ (a_Q) · I`. -/
theorem basis_first_mul_cox_ideal_le_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q ≤
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    d hd4
  let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_eq_one, e, betaZ] using
    basis_first_mul_cox_ideal_le_span_a_mul_ideal b Q e betaZ (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 ≠ 1` branch, the oriented basis decomposition of `I` gives
the reverse inclusion `(a_Q) · I ≤ (b₀) · J(Q_b)`. -/
theorem span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) ≤
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let betaZ : Zsqrtd d := (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_ne_one, e, betaZ] using
    span_a_mul_ideal_le_basis_first_mul_cox_ideal b Q e betaZ
      (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 = 1` branch, the oriented basis decomposition of `I` gives
the reverse inclusion `(a_Q) · I ≤ (b₀) · J(Q_b)`. -/
theorem span_a_mul_ideal_le_basis_first_mul_cox_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) ≤
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    d hd4
  let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_eq_one, e, betaZ] using
    span_a_mul_ideal_le_basis_first_mul_cox_ideal b Q e betaZ
      (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 ≠ 1` branch, the oriented basis first vector gives the
principal ideal relation `(b₀) · J(Q_b) = (a_Q) · I` for the norm form. -/
theorem basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_ne_one d hd4 Q =
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let betaZ : Zsqrtd d := (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_ne_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_ne_one, e, betaZ] using
    basis_first_mul_cox_ideal_eq_span_a_mul_ideal b Q e betaZ
      (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 = 1` branch, the oriented basis first vector gives the
principal ideal relation `(b₀) · J(Q_b) = (a_Q) · I` for the norm form. -/
theorem basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    let Q := primitivePositiveDefiniteNormFormOfBasis hdneg
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b
    Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
        idealOfForm_of_mod_four_eq_one d hd4 Q =
      Ideal.span ({((Q.1.a : ℤ) : 𝓞K)} : Set 𝓞K) * (I : Ideal 𝓞K) := by
  intro Q
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one
    d hd4
  let betaZ : ZOnePlusSqrtdOverTwo (d / 4) := ⟨-(Q.1.b + 1) / 2, 1⟩
  have hrel :=
    basis_first_mul_cox_ideal_generator_eq_neg_normForm_a_mul_basis_second_of_mod_four_eq_one
      hdneg hd4 I b
  dsimp only at hrel
  simpa [idealOfForm_of_mod_four_eq_one, e, betaZ] using
    basis_first_mul_cox_ideal_eq_span_a_mul_ideal b Q e betaZ
      (by simpa [Q, e, betaZ] using hrel)

/-- In the `d % 4 ≠ 1` branch, the right-inverse law follows from the classical
Cox relation `(α) · J(Q_b) = (a_Q) · I`, where `α` is the first vector of the
oriented ideal basis and `Q_b` is its norm form. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_basis_first_vector_relation hdneg b
    (idealOfForm_of_mod_four_ne_one d hd4) (idealClassOfForm_of_mod_four_ne_one d hd4)
    (fun hx hy hrel =>
      idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
        hdneg hd4 I b hx hy hrel)
    hrel

/-- In the `d % 4 ≠ 1` branch, the Cox ideal class of the norm form attached
to any oriented basis of `I` is the original ideal class. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_ne_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I :=
  idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_first_vector_relation
    hdneg hd4 I b
    (basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_ne_one hdneg hd4 I b)

/-- Right-inverse branch law for the `d % 4 ≠ 1` Cox map, using the canonical
oriented basis chosen by `classGroupToFormClass`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_ne_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis hdneg hd4 I
    (orientedBasisOfNeZero (I : Ideal 𝓞K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))

/-- In the `d % 4 = 1` branch, the right-inverse law follows from the same
principal relation between the basis first vector, the Cox ideal of the norm
form, and the original ideal. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_first_vector_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K))
    (hrel :
      Ideal.span ({(b.basis 0 : 𝓞K)} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
        Ideal.span
            ({(((primitivePositiveDefiniteNormFormOfBasis hdneg
              (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b).1.a : ℤ) : 𝓞K)} :
              Set 𝓞K) *
          (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_basis_first_vector_relation hdneg b
    (idealOfForm_of_mod_four_eq_one d hd4) (idealClassOfForm_of_mod_four_eq_one d hd4)
    (fun hx hy hrel =>
      idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
        hdneg hd4 I b hx hy hrel)
    hrel

/-- In the `d % 4 = 1` branch, the Cox ideal class of the norm form attached to
any oriented basis of `I` is the original ideal class. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    idealClassOfForm_of_mod_four_eq_one d hd4
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) =
      ClassGroup.mk0 I :=
  idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_first_vector_relation
    hdneg hd4 I b
    (basis_first_mul_cox_ideal_eq_span_a_mul_ideal_of_mod_four_eq_one hdneg hd4 I b)

/-- Right-inverse branch law for the `d % 4 = 1` Cox map, using the canonical
oriented basis chosen by `classGroupToFormClass`. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_eq_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis hdneg hd4 I
    (orientedBasisOfNeZero (I : Ideal 𝓞K) (mem_nonZeroDivisors_iff_ne_zero.mp I.2))

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 ≠ 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 ≠ 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_ne_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_ne_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_ne_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

/-- A principal-ideal relation proves the right-inverse law for the canonical
oriented basis in the `d % 4 = 1` branch. -/
theorem idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_ideal_relation
    (hdneg : d < 0) (hd4 : d % 4 = 1) (I : (Ideal 𝓞K)⁰)
    {x y : 𝓞K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hrel :
      (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
       let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
       Ideal.span ({x} : Set 𝓞K) *
          idealOfForm_of_mod_four_eq_one d hd4
            (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) =
        Ideal.span ({y} : Set 𝓞K) * (I : Ideal 𝓞K)) :
    (let hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
     let b : OrientedBasis (I : Ideal 𝓞K) := orientedBasisOfNeZero (I : Ideal 𝓞K) hI
     idealClassOfForm_of_mod_four_eq_one d hd4
       (primitivePositiveDefiniteNormFormOfBasis hdneg hI b)) = ClassGroup.mk0 I := by
  exact idealClassOfNormForm_eq_mk0_of_mod_four_eq_one_of_basis_ideal_relation
    hdneg hd4 I (orientedBasisOfNeZero (I : Ideal 𝓞K)
      (mem_nonZeroDivisors_iff_ne_zero.mp I.2)) hx hy hrel

end CoxAssembly

end BinaryQuadraticForm
end QuadraticNumberFields
