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

/-! ## Principal scaling invariance -/

/-- The ideal norm of a principal scaling `span{x} · I` factors through the field
norm of `x`. -/
theorem absNorm_span_singleton_mul (x : 𝓞K) (I : Ideal 𝓞K) :
    Ideal.absNorm (Ideal.span {x} * I) = (Algebra.norm ℤ x).natAbs * Ideal.absNorm I := by
  rw [map_mul, Ideal.absNorm_span_singleton]

/-- As `ℤ`-submodules, the image of `I` under multiplication by `x` is the
principal scaling `span{x} * I`. -/
theorem map_mulLeft_restrictScalars (x : 𝓞K) (I : Ideal 𝓞K) :
    (Submodule.restrictScalars ℤ I).map (LinearMap.mulLeft ℤ x) =
      Submodule.restrictScalars ℤ (Ideal.span {x} * I) := by
  ext m
  simp only [Submodule.mem_map, Submodule.restrictScalars_mem, LinearMap.mulLeft_apply,
    Ideal.mem_span_singleton_mul]

/-- A `ℤ`-basis of `I`, scaled by a nonzero `x`, as a `ℤ`-basis of `span{x} * I`
(via the multiplication-by-`x` isomorphism). -/
noncomputable def scaledBasis (x : 𝓞K) (hx : x ≠ 0) {I : Ideal 𝓞K}
    (b : Basis (Fin 2) ℤ I) : Basis (Fin 2) ℤ (Ideal.span {x} * I : Ideal 𝓞K) :=
  b.map ((Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ x)
      (mul_right_injective₀ hx) (Submodule.restrictScalars ℤ I)).trans
    (LinearEquiv.ofEq _ _ (map_mulLeft_restrictScalars x I)))

@[simp] theorem scaledBasis_coe (x : 𝓞K) (hx : x ≠ 0) {I : Ideal 𝓞K}
    (b : Basis (Fin 2) ℤ I) (i : Fin 2) :
    (scaledBasis x hx b i : 𝓞K) = x * (b i : 𝓞K) := by
  simp only [scaledBasis, Basis.map_apply]
  rfl

/-- An oriented basis of `I`, scaled by a nonzero `x`, as an oriented basis of
`span{x} * I` (orientation is preserved because the field norm of `x` is positive
for `d < 0`). -/
noncomputable def scaledOrientedBasis (hdneg : d < 0) {x : 𝓞K} (hx : x ≠ 0)
    {I : Ideal 𝓞K} (b : OrientedBasis I) : OrientedBasis (Ideal.span {x} * I) where
  basis := scaledBasis x hx b.basis
  oriented := by
    have hcoe : ∀ i : Fin 2,
        ((scaledBasis x hx b.basis i : 𝓞K) : K) = (x : K) * ((b.basis i : 𝓞K) : K) := by
      intro i
      rw [scaledBasis_coe]
      push_cast
      ring
    rw [hcoe, hcoe, imPartRatio_wedge_mul_left, ← fieldNorm_int_eq]
    exact mul_pos (by exact_mod_cast norm_int_pos hdneg hx) b.oriented

/-- Scaling an ideal by a nonzero principal factor (and the basis by the same
factor) leaves the Cox norm form unchanged: the `N(x)` factor cancels between the
basis-vector norms and the ideal norm. -/
theorem normFormOfBasis_scaledOrientedBasis (hdneg : d < 0) {x : 𝓞K} (hx : x ≠ 0)
    {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I)
    (hM : Ideal.span {x} * I ≠ 0) :
    normFormOfBasis hM (scaledOrientedBasis hdneg hx b) = normFormOfBasis hI b := by
  apply eq_of_eval_eq
  intro p q
  rw [normFormOfBasis_eval_eq_norm_ediv_absNorm hM, normFormOfBasis_eval_eq_norm_ediv_absNorm hI]
  have helt : p • ((scaledOrientedBasis hdneg hx b).basis 0 : 𝓞K) +
        q • ((scaledOrientedBasis hdneg hx b).basis 1 : 𝓞K) =
      x * (p • (b.basis 0 : 𝓞K) + q • (b.basis 1 : 𝓞K)) := by
    change p • (scaledBasis x hx b.basis 0 : 𝓞K) + q • (scaledBasis x hx b.basis 1 : 𝓞K) = _
    simp only [scaledBasis_coe, mul_add, mul_smul_comm]
  rw [helt, map_mul]
  have hMnorm : (Ideal.absNorm (Ideal.span {x} * I) : ℤ) =
      Algebra.norm ℤ x * (Ideal.absNorm I : ℤ) := by
    rw [absNorm_span_singleton_mul]
    push_cast
    rw [abs_of_nonneg (le_of_lt (norm_int_pos hdneg hx))]
  rw [hMnorm, Int.mul_ediv_mul_of_pos _ _ (norm_int_pos hdneg hx)]

/-- A principal scaling of a nonzero ideal is again a non-zero-divisor ideal. -/
theorem span_singleton_mul_mem_nonZeroDivisors {x : 𝓞K} (hx : x ≠ 0) (I : (Ideal 𝓞K)⁰) :
    Ideal.span {x} * (I : Ideal 𝓞K) ∈ nonZeroDivisors (Ideal 𝓞K) := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact mul_ne_zero (fun hc => hx (Ideal.span_singleton_eq_bot.mp hc))
    (mem_nonZeroDivisors_iff_ne_zero.mp I.2)

/-- Multiplying an ideal by a nonzero principal factor does not change its Cox
form class. -/
theorem formClassOfNonzeroIdeal_span_singleton_mul (hdneg : d < 0) {x : 𝓞K} (hx : x ≠ 0)
    (I : (Ideal 𝓞K)⁰)
    (hM : Ideal.span {x} * (I : Ideal 𝓞K) ∈ nonZeroDivisors (Ideal 𝓞K)) :
    formClassOfNonzeroIdeal hdneg ⟨Ideal.span {x} * (I : Ideal 𝓞K), hM⟩ =
      formClassOfNonzeroIdeal hdneg I := by
  have hI : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hM' : Ideal.span {x} * (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hM
  rw [formClassOfNonzeroIdeal_eq_mk hdneg ⟨Ideal.span {x} * (I : Ideal 𝓞K), hM⟩
        (scaledOrientedBasis hdneg hx (orientedBasisOfNeZero (I : Ideal 𝓞K) hI)),
      formClassOfNonzeroIdeal_eq_mk hdneg I (orientedBasisOfNeZero (I : Ideal 𝓞K) hI)]
  exact congrArg (Quotient.mk _)
    (Subtype.ext (normFormOfBasis_scaledOrientedBasis hdneg hx hI
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI) hM'))

/-- **The descent core.** `formClassOfNonzeroIdeal` is a genuine ideal-class
function: properly equivalent (same-class) ideals yield the same Cox form class.
This is the well-definedness fact both Cox round-trip laws rely on. -/
theorem formClassOfNonzeroIdeal_eq_of_mk0_eq (hdneg : d < 0) (I J : (Ideal 𝓞K)⁰)
    (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    formClassOfNonzeroIdeal hdneg I = formClassOfNonzeroIdeal hdneg J := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  rw [← formClassOfNonzeroIdeal_span_singleton_mul hdneg hx I
        (span_singleton_mul_mem_nonZeroDivisors hx I),
      ← formClassOfNonzeroIdeal_span_singleton_mul hdneg hy J
        (span_singleton_mul_mem_nonZeroDivisors hy J)]
  exact congrArg (formClassOfNonzeroIdeal hdneg) (Subtype.ext hxy)

/-! ## Branch-agnostic left-inverse core

The two Cox left-inverse branches (`d % 4 ≠ 1` and `d % 4 = 1`) differ only in the
concrete order (`Zsqrtd d` versus `ZOnePlusSqrtdOverTwo (d / 4)`), the ring
equivalence to `𝓞K`, and the imaginary `K`-coordinate `im_val` of the second Cox
basis vector (`-1` versus `-1/2`).  The form-level computation that turns those
coordinates into the equality of form classes is identical, so it is proved once
here. -/

/-- The forward Cox map on the class of a nonzero ideal `I` computes to
`formClassOfNonzeroIdeal hdneg I`, regardless of the surjectivity representative
chosen by `classGroupToFormClass`. -/
theorem classGroupToFormClass_mk0_eq_formClassOfNonzeroIdeal (hdneg : d < 0)
    (I : (Ideal 𝓞K)⁰) :
    classGroupToFormClass hdneg (ClassGroup.mk0 I) = formClassOfNonzeroIdeal hdneg I := by
  dsimp [classGroupToFormClass]
  let J := Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
  have hJ_mk0 : ClassGroup.mk0 J = ClassGroup.mk0 I :=
    Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
  exact formClassOfNonzeroIdeal_eq_of_mk0_eq hdneg J I hJ_mk0

/-- **Branch-agnostic Cox left-inverse core.** Given an oriented basis `b` of a
nonzero ideal `I` whose `K`-coordinates are `(a, 0)` and `(b/2, im_val)`, ideal
norm `N(I) = a`, and the norm relation `(b/2)² − d·im_val² = a·c`, the Cox form
class of `I` is the class of `Q`.  Both `d % 4` branches instantiate this with
their `im_val` (`-1` and `-1/2`); only the construction of `b` and the proof of
`hN_eq` are branch-specific. -/
theorem formClassOfNonzeroIdeal_eq_mk_of_oriented (hdneg : d < 0) (I : (Ideal 𝓞K)⁰)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (b : OrientedBasis (I : Ideal 𝓞K)) (im_val : ℚ)
    (h0_re : ((b.basis 0 : 𝓞K) : K).re = (Q.1.a : ℚ))
    (h0_im : ((b.basis 0 : 𝓞K) : K).im = 0)
    (h1_re : ((b.basis 1 : 𝓞K) : K).re = (Q.1.b / 2 : ℚ))
    (h1_im : ((b.basis 1 : 𝓞K) : K).im = im_val)
    (hac : (Q.1.b / 2 : ℚ) ^ 2 - (d : ℚ) * im_val ^ 2 = (Q.1.a : ℚ) * Q.1.c)
    (hN_eq : (Ideal.absNorm (I : Ideal 𝓞K) : ℤ) = Q.1.a) :
    formClassOfNonzeroIdeal hdneg I =
      Quotient.mk (primitivePositiveDefiniteFormSetoid (fieldDiscriminant d)) Q := by
  have hI_ne_zero : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have hane : Q.1.a ≠ 0 := ne_of_gt Q.2.2.2.1
  have hnorm0 : Algebra.norm ℤ (b.basis 0 : 𝓞K) = Q.1.a ^ 2 := by
    have h : (Algebra.norm ℤ (b.basis 0 : 𝓞K) : ℚ) = (Q.1.a : ℚ) ^ 2 := by
      rw [fieldNorm_int_eq, h0_re, h0_im]; ring
    exact_mod_cast h
  have hnorm1 : Algebra.norm ℤ (b.basis 1 : 𝓞K) = Q.1.a * Q.1.c := by
    have h : (Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℚ) = (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
      rw [fieldNorm_int_eq, h1_re, h1_im]; exact hac
    exact_mod_cast h
  have hnormsum : Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) =
      Q.1.a ^ 2 + Q.1.a * Q.1.b + Q.1.a * Q.1.c := by
    have hsum_coe : (((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K) : 𝓞K) : K) =
        ((b.basis 0 : 𝓞K) : K) + ((b.basis 1 : 𝓞K) : K) := by push_cast; ring
    have h : (Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) : ℚ) =
        (Q.1.a : ℚ) ^ 2 + (Q.1.a : ℚ) * (Q.1.b : ℚ) + (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
      rw [fieldNorm_int_eq, hsum_coe]
      simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, h0_re, h0_im, h1_re, h1_im]
      linear_combination hac
    exact_mod_cast h
  have h_normform_eq : normFormOfBasis hI_ne_zero b = Q.1 :=
    normFormOfBasis_eq_of_norms hI_ne_zero b hane hN_eq hnorm0 hnorm1 hnormsum
  have h_target : (normFormOfBasis hI_ne_zero b).ProperEquivalent Q.1 := by
    rw [h_normform_eq]; exact BinaryQuadraticForm.ProperEquivalent.refl Q.1
  rw [formClassOfNonzeroIdeal_eq_mk hdneg I (b := b)]
  dsimp [primitivePositiveDefiniteNormFormOfBasis]
  apply Quotient.sound
  simpa using h_target

/-! ## Branch-agnostic right-inverse core

The Cox right-inverse computation also factors through the `K`-coordinates of the
oriented basis.  The leading and middle coefficients of the norm form are rational
functions of those coordinates (`normFormOfBasis_a_coord`, `normFormOfBasis_b_coord`),
and the signed Cox generator relation `α · β_gen = -a · β` holds for *any* generator
whose coordinates are `(-b/2, im_val)`, where the orientation determinant satisfies
`αᵢβᵣ − αᵣβᵢ = N(I)·im_val`.  Both `d % 4` branches instantiate this with their
`im_val` (`1` and `1/2`). -/

/-- The leading coefficient of the Cox norm form in basis `K`-coordinates. -/
theorem normFormOfBasis_a_coord {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    ((normFormOfBasis hI b).a : ℚ) =
      (((b.basis 0 : 𝓞K) : K).re ^ 2 - (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im ^ 2) /
        (Ideal.absNorm I : ℚ) := by
  have hN : (Ideal.absNorm I : ℚ) ≠ 0 := by exact_mod_cast (absNorm_pos hI).ne'
  rw [eq_div_iff hN]
  have h : ((normFormOfBasis hI b).a : ℚ) * (Ideal.absNorm I : ℚ) =
      (Algebra.norm ℤ (b.basis 0 : 𝓞K) : ℚ) := by
    exact_mod_cast normFormOfBasis_a_mul_absNorm hI b
  rw [fieldNorm_int_eq] at h
  exact h

/-- The middle coefficient of the Cox norm form in basis `K`-coordinates. -/
theorem normFormOfBasis_b_coord {I : Ideal 𝓞K} (hI : I ≠ 0) (b : OrientedBasis I) :
    ((normFormOfBasis hI b).b : ℚ) =
      (2 * (((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).re -
          (d : ℚ) * ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).im)) /
        (Ideal.absNorm I : ℚ) := by
  have hN : (Ideal.absNorm I : ℚ) ≠ 0 := by exact_mod_cast (absNorm_pos hI).ne'
  rw [eq_div_iff hN]
  have h' : ((normFormOfBasis hI b).b : ℚ) * (Ideal.absNorm I : ℚ) =
      ((Algebra.norm ℤ ((b.basis 0 : 𝓞K) + (b.basis 1 : 𝓞K)) -
        Algebra.norm ℤ (b.basis 0 : 𝓞K) - Algebra.norm ℤ (b.basis 1 : 𝓞K) : ℤ) : ℚ) := by
    exact_mod_cast normFormOfBasis_b_mul_absNorm hI b
  rw [h']
  push_cast
  rw [fieldNorm_int_eq, fieldNorm_int_eq, fieldNorm_int_eq]
  push_cast
  simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]
  ring

/-- Real-coordinate identity behind the signed Cox generator relation
`α · β_gen = -A · β`, where `β_gen` has coordinates `(-B/2, im)`. -/
theorem cox_generator_relation_re {αr αi βr βi D N A B im : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N) (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : αi * βr - αr * βi = N * im) (hN0 : N ≠ 0) :
    αr * (-B / 2) + D * αi * im = -A * βr := by
  rw [hA, hB]
  field_simp
  linear_combination (-(D * αi)) * hN

/-- Imaginary-coordinate identity behind the signed Cox generator relation
`α · β_gen = -A · β`, where `β_gen` has coordinates `(-B/2, im)`. -/
theorem cox_generator_relation_im {αr αi βr βi D N A B im : ℚ}
    (hA : A = (αr ^ 2 - D * αi ^ 2) / N) (hB : B = 2 * (αr * βr - D * αi * βi) / N)
    (hN : αi * βr - αr * βi = N * im) (hN0 : N ≠ 0) :
    αr * im + αi * (-B / 2) = -A * βi := by
  rw [hA, hB]
  field_simp
  linear_combination (-αr) * hN

/-- **Branch-agnostic signed Cox generator relation.** For any `β_gen ∈ 𝓞K` whose
`K`-coordinates are `(-b/2, im_val)` (where `b` is the middle coefficient of the
norm form), and whose orientation determinant satisfies `αᵢβᵣ − αᵣβᵢ = N(I)·im_val`,
the first basis vector `α` satisfies `α · β_gen = -a · β`.  The sign is forced by
the orientation convention.  The `d % 4 ≠ 1` branch uses `im_val = 1`, the
`d % 4 = 1` branch uses `im_val = 1/2`. -/
theorem basis_first_mul_eq_neg_a_mul_basis_second {I : Ideal 𝓞K} (hI : I ≠ 0)
    (b : OrientedBasis I) (βgen : 𝓞K) (im_val : ℚ)
    (hβre : ((βgen : 𝓞K) : K).re = -((normFormOfBasis hI b).b : ℚ) / 2)
    (hβim : ((βgen : 𝓞K) : K).im = im_val)
    (hNim : ((b.basis 0 : 𝓞K) : K).im * ((b.basis 1 : 𝓞K) : K).re -
        ((b.basis 0 : 𝓞K) : K).re * ((b.basis 1 : 𝓞K) : K).im =
      (Ideal.absNorm I : ℚ) * im_val) :
    (b.basis 0 : 𝓞K) * βgen =
      -(((normFormOfBasis hI b).a : ℤ) : 𝓞K) * (b.basis 1 : 𝓞K) := by
  have ha := normFormOfBasis_a_coord hI b
  have hb := normFormOfBasis_b_coord hI b
  have hN0 : (Ideal.absNorm I : ℚ) ≠ 0 := by exact_mod_cast (absNorm_pos hI).ne'
  apply IsFractionRing.injective 𝓞K K
  ext <;>
    simp only [map_mul, map_neg, map_intCast, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
      QuadraticAlgebra.re_neg, QuadraticAlgebra.im_neg, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_intCast, zero_mul, add_zero, hβre, hβim]
  · simpa using cox_generator_relation_re ha hb hNim hN0
  · simpa using cox_generator_relation_im ha hb hNim hN0

end BasisChange

end BinaryQuadraticForm
end QuadraticNumberFields
