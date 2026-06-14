/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.InverseCox

/-!
# Basis-change invariance of the Cox norm form

This file proves the *descent core* of the inverse Cox 7.7 map: the norm form
attached to an oriented ideal basis depends only on the ideal class, not on the
chosen basis.  Concretely:

* two oriented bases of one ideal differ by an element of `SL₂(ℤ)`, so their norm
  forms are properly equivalent (`normFormOfBasis_properEquivalent`);
* scaling an ideal by a nonzero principal factor (and the basis by the same
  factor) leaves the norm form unchanged (`normFormOfBasis_smul`);

These combine to show `formClassOfNonzeroIdeal` is a genuine class function
(`formClassOfNonzeroIdeal_eq_of_mk0_eq`), which is the well-definedness fact the
left and right Cox round-trip laws both rely on.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Form-level helpers -/

/-- A binary quadratic form is determined by its evaluation function. -/
theorem eq_of_eval_eq {Q R : BinaryQuadraticForm}
    (h : ∀ x y : ℤ, Q.eval x y = R.eval x y) : Q = R := by
  have ha := h 1 0
  have hc := h 0 1
  have hbc := h 1 1
  simp only [eval] at ha hc hbc
  ext
  · linarith [ha]
  · nlinarith [ha, hc, hbc]
  · linarith [hc]

/-- Evaluating `transform Q g` at `(x, y)` is evaluating `Q` at the column action
`g • (x, y)`. -/
theorem eval_transform (Q : BinaryQuadraticForm) (g : SL2Z) (x y : ℤ) :
    (transform Q g).eval x y =
      Q.eval ((g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * x + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * y)
        ((g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * x + (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * y) := by
  simp only [transform, eval]
  ring

section BasisChange

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K
local notation "√dK" => (⟨0, 1⟩ : K)

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
/-- The oriented-basis wedge `imPartRatio (α β̄ − β ᾱ)` in coordinates: it is
`2 (α.im β.re − α.re β.im)`, a bilinear alternating form of the `re`/`im`
coordinates. -/
theorem imPartRatio_wedge (u v : K) :
    imPartRatio (u * star v - v * star u) =
      2 * ((u.im : ℚ) * v.re - u.re * v.im) := by
  rw [imPartRatio_eq_im]
  simp only [QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star]
  ring

/-- The image in `K` of any element of a nonzero ideal `I` expands over a
`ℤ`-basis `b` of `I` via the representation coordinates. -/
theorem coe_eq_sum_repr_smul (I : Ideal 𝓞K) (b : Basis (Fin 2) ℤ I) (w : I) :
    ((w : 𝓞K) : K) = ∑ i, (b.repr w i : ℤ) • ((b i : 𝓞K) : K) := by
  set f : I →ₗ[ℤ] K :=
    (Algebra.linearMap 𝓞K K).restrictScalars ℤ ∘ₗ (Submodule.restrictScalars ℤ I).subtype
    with hf
  have h := congrArg f (b.sum_repr w)
  rw [map_sum] at h
  simp only [map_zsmul] at h
  simpa only [hf, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
    Submodule.subtype_apply, Submodule.coe_subtype, Algebra.linearMap_apply] using h.symm

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
theorem re_zsmul (n : ℤ) (z : K) : (n • z : K).re = (n : ℚ) * z.re := by
  rw [zsmul_eq_mul]
  simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

omit [Fact (Squarefree d)] [Fact (d ≠ 1)] in
theorem im_zsmul (n : ℤ) (z : K) : (n • z : K).im = (n : ℚ) * z.im := by
  rw [zsmul_eq_mul]
  simp [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast, QuadraticAlgebra.im_intCast]

/-- The `re` coordinate of an ideal element expands over a `ℤ`-basis. -/
theorem coe_re_eq (I : Ideal 𝓞K) (b : Basis (Fin 2) ℤ I) (w : I) :
    ((w : 𝓞K) : K).re =
      (b.repr w 0 : ℚ) * ((b 0 : 𝓞K) : K).re + (b.repr w 1 : ℚ) * ((b 1 : 𝓞K) : K).re := by
  rw [coe_eq_sum_repr_smul I b w, Fin.sum_univ_two]
  simp only [QuadraticAlgebra.re_add, re_zsmul]

/-- The `im` coordinate of an ideal element expands over a `ℤ`-basis. -/
theorem coe_im_eq (I : Ideal 𝓞K) (b : Basis (Fin 2) ℤ I) (w : I) :
    ((w : 𝓞K) : K).im =
      (b.repr w 0 : ℚ) * ((b 0 : 𝓞K) : K).im + (b.repr w 1 : ℚ) * ((b 1 : 𝓞K) : K).im := by
  rw [coe_eq_sum_repr_smul I b w, Fin.sum_univ_two]
  simp only [QuadraticAlgebra.im_add, im_zsmul]

/-- Changing oriented basis scales the wedge by the determinant of the change of
basis matrix. -/
theorem imPartRatio_wedge_basis_change (I : Ideal 𝓞K) (b b' : OrientedBasis I) :
    imPartRatio (((b'.basis 0 : 𝓞K) : K) * star ((b'.basis 1 : 𝓞K) : K) -
        ((b'.basis 1 : 𝓞K) : K) * star ((b'.basis 0 : 𝓞K) : K)) =
      ((b.basis.repr (b'.basis 0) 0 * b.basis.repr (b'.basis 1) 1 -
          b.basis.repr (b'.basis 0) 1 * b.basis.repr (b'.basis 1) 0 : ℤ) : ℚ) *
        imPartRatio (((b.basis 0 : 𝓞K) : K) * star ((b.basis 1 : 𝓞K) : K) -
          ((b.basis 1 : 𝓞K) : K) * star ((b.basis 0 : 𝓞K) : K)) := by
  rw [imPartRatio_wedge, imPartRatio_wedge,
    coe_re_eq I b.basis (b'.basis 0), coe_im_eq I b.basis (b'.basis 0),
    coe_re_eq I b.basis (b'.basis 1), coe_im_eq I b.basis (b'.basis 1)]
  push_cast
  ring

/-- The image in `𝓞K` of an ideal element expands over a `ℤ`-basis of the ideal. -/
theorem coe_OK_eq_sum_repr_smul (I : Ideal 𝓞K) (b : Basis (Fin 2) ℤ I) (w : I) :
    (w : 𝓞K) = ∑ i, (b.repr w i : ℤ) • (b i : 𝓞K) := by
  set f : I →ₗ[ℤ] 𝓞K := (Submodule.restrictScalars ℤ I).subtype with hf
  have h := congrArg f (b.sum_repr w)
  rw [map_sum] at h
  simp only [map_zsmul] at h
  simpa only [hf, Submodule.subtype_apply, Submodule.coe_subtype] using h.symm

/-- The change-of-basis matrix between two oriented bases of one ideal has
determinant `1`: it is a unit (so `±1`), and orientation rules out `-1`. -/
theorem toMatrix_det_eq_one_of_oriented (I : Ideal 𝓞K) (b b' : OrientedBasis I) :
    (b.basis.toMatrix b'.basis).det = 1 := by
  have hmul : (b.basis.toMatrix b'.basis).det * (b'.basis.toMatrix b.basis).det = 1 := by
    rw [← Matrix.det_mul, Basis.toMatrix_mul_toMatrix_flip, Matrix.det_one]
  have hfactor :
      (b.basis.toMatrix b'.basis).det =
        b.basis.repr (b'.basis 0) 0 * b.basis.repr (b'.basis 1) 1 -
          b.basis.repr (b'.basis 0) 1 * b.basis.repr (b'.basis 1) 0 := by
    rw [Matrix.det_fin_two]
    simp only [Basis.toMatrix_apply]
    ring
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmul with ⟨h1, -⟩ | ⟨hm1, -⟩
  · exact h1
  · exfalso
    have hscale := imPartRatio_wedge_basis_change I b b'
    rw [← hfactor, hm1] at hscale
    have hb := b.oriented
    have hb' := b'.oriented
    rw [hscale] at hb'
    push_cast at hb'
    nlinarith [hb, hb']

/-- **Basis independence of the Cox norm form.** Two oriented bases of one ideal
differ by an element of `SL₂(ℤ)`, so their norm forms are properly equivalent.
This is the descent core: it shows `formClassOfNonzeroIdeal` does not depend on
the chosen oriented basis. -/
theorem normFormOfBasis_properEquivalent {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b b' : OrientedBasis I) :
    ProperEquivalent (normFormOfBasis hI b) (normFormOfBasis hI b') := by
  set g : SL2Z :=
    ⟨b.basis.toMatrix b'.basis, toMatrix_det_eq_one_of_oriented I b b'⟩ with hg
  refine ⟨g, ?_⟩
  apply eq_of_eval_eq
  intro x y
  have hgcoe : ∀ i j : Fin 2,
      (g : Matrix (Fin 2) (Fin 2) ℤ) i j = b.basis.repr (b'.basis j) i := by
    intro i j
    change b.basis.toMatrix b'.basis i j = b.basis.repr (b'.basis j) i
    rw [Basis.toMatrix_apply]
  rw [eval_transform, normFormOfBasis_eval_eq_norm_ediv_absNorm hI b,
    normFormOfBasis_eval_eq_norm_ediv_absNorm hI b']
  simp only [hgcoe]
  have helt :
      (b.basis.repr (b'.basis 0) 0 * x + b.basis.repr (b'.basis 1) 0 * y) • (b.basis 0 : 𝓞K) +
          (b.basis.repr (b'.basis 0) 1 * x + b.basis.repr (b'.basis 1) 1 * y) •
            (b.basis 1 : 𝓞K) =
        x • (b'.basis 0 : 𝓞K) + y • (b'.basis 1 : 𝓞K) := by
    rw [coe_OK_eq_sum_repr_smul I b.basis (b'.basis 0),
      coe_OK_eq_sum_repr_smul I b.basis (b'.basis 1), Fin.sum_univ_two, Fin.sum_univ_two]
    module
  rw [helt]

/-- The inverse-map form class of a nonzero ideal can be computed from *any*
oriented basis, not only the canonical `orientedBasisOfNeZero` choice. -/
theorem formClassOfNonzeroIdeal_eq_mk (hdneg : d < 0) (I : (Ideal 𝓞K)⁰)
    (b : OrientedBasis (I : Ideal 𝓞K)) :
    formClassOfNonzeroIdeal hdneg I =
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d))
        (primitivePositiveDefiniteNormFormOfBasis hdneg
          (mem_nonZeroDivisors_iff_ne_zero.mp I.2) b) :=
  Quotient.sound
    (normFormOfBasis_properEquivalent (mem_nonZeroDivisors_iff_ne_zero.mp I.2) _ b)

end BasisChange

end BinaryQuadraticForm
end QuadraticNumberFields
