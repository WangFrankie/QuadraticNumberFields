/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import QuadraticNumberFields.Forms.Cox.Inverse
import QuadraticNumberFields.Forms.Cox.NormFormBasisChange
import QuadraticNumberFields.RingOfIntegers.Norm
import QuadraticNumberFields.Zsqrtd.Basic
import QuadraticNumberFields.ZOnePlusSqrtdOverTwo.Basic

/-!
# Cox 7.7 Left Inverse: `d % 4 = 1` Branch

Round-trip proof
`classGroupToFormClass (idealClassOfForm_of_mod_four_eq_one Q) = ⟦Q⟧`
for the half-integral branch, instantiating the generic `CoxIdealRelation`
core at `bb = 1` (`ZOnePlusSqrtdOverTwo`).  Assembled in `Forms.Cox.Equivalence`.
-/

open scoped NumberField nonZeroDivisors
open Module

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

section CoxLeftInverseEqOne

/-! ## Left Inverse Round-Trip: `d % 4 = 1` Branch

Goal: `classGroupToFormClass hdneg (idealClassOfForm_of_mod_four_eq_one d hd4 Q) = ⟦Q⟧`.

The strategy mirrors the `d % 4 ≠ 1` branch (§CoxLeftInverse) but the
generic `CoxIdealRelation` core is instantiated at `bb = 1` (`ZOnePlusSqrtdOverTwo`).
Each of the four inputs to `normFormOfBasis_eq_of_norms` (ideal norm = a,
N(α) = a², N(β) = a·c, N(α+β) = a²+ab+ac) collapses to the same shape because
the K-coordinates of the second Cox basis vector are `(b/2, -1/2)` instead of
`(b/2, -1)`. -/

variable {d : ℤ} [Fact (Squarefree d)] [Fact (d ≠ 1)]

local notation "K" => Qsqrtd (d : ℚ)
local notation "𝓞K" => 𝓞 K

/-- The ℤ-algebra equivalence `ZOnePlusSqrtdOverTwo (d/4) ≃ₐ[ℤ] 𝓞K` for `d % 4 = 1`. -/
noncomputable def toRingOfIntegersAlgEquivEqOne (hd4 : d % 4 = 1) :
    ZOnePlusSqrtdOverTwo (d / 4) ≃ₐ[ℤ] 𝓞K :=
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  AlgEquiv.ofRingEquiv (f := e.symm) fun _ => by simp

/-- The Cox basis transported to `𝓞K` via the `d % 4 = 1` ring equivalence. -/
noncomputable def coxIdealBasisOKEqOne (hd4 : d % 4 = 1) (_hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Basis (Fin 2) ℤ (idealOfForm_of_mod_four_eq_one d hd4 Q) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let DD : ℤ := d/4
  let bb : ℤ := 1
  let A : ℤ := Q.1.a
  let B : ℤ := Q.1.b
  let C : ℤ := Q.1.c
  let u : ℤ := -(B + 1) / 2
  have h_odd : Odd B := by
    dsimp [B]
    exact odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  let k := h_odd.choose
  have hk : B = 2 * k + 1 := h_odd.choose_spec
  have hu : 2 * u = -(B + bb) := by
    dsimp [u, bb]; rw [hk]; omega
  have hdisc : B ^ 2 - 4 * A * C = bb ^ 2 + 4 * DD := by
    have hdisc_val : Q.1.disc = d := by
      have hfield : fieldDiscriminant d = d := fieldDiscriminant_of_mod_four_eq_one hd4
      simpa [hfield] using Q.2.1
    unfold BinaryQuadraticForm.disc at hdisc_val
    dsimp [B] at *
    rw [hk] at hdisc_val
    have hd_eq : d = 4 * (d / 4) + 1 := by
      have := Int.mul_ediv_add_emod d 4
      rw [hd4] at this
      omega
    dsimp [A, B, C, DD, bb]
    rw [hk]
    rw [hdisc_val, hd_eq]
    omega
  let b_generic : Basis (Fin 2) ℤ (CoxIdealRelation.coxIdeal DD bb A u) :=
    CoxIdealRelation.coxIdealBasis (ne_of_gt Q.2.2.2.1) hu hdisc
  let e_symm_alg : ZOnePlusSqrtdOverTwo (d / 4) ≃ₐ[ℤ] 𝓞K :=
    toRingOfIntegersAlgEquivEqOne hd4
  let e_symm_lin : ZOnePlusSqrtdOverTwo (d / 4) →ₗ[ℤ] 𝓞K := e_symm_alg.toLinearMap
  have h_inj : Function.Injective e_symm_lin := e_symm_alg.injective
  let J := CoxIdealRelation.coxIdeal DD bb A u
  let J_ℤ : Submodule ℤ (ZOnePlusSqrtdOverTwo (d / 4)) :=
    Submodule.restrictScalars ℤ (J : Submodule (ZOnePlusSqrtdOverTwo (d / 4))
      (ZOnePlusSqrtdOverTwo (d / 4)))
  let I_ℤ : Submodule ℤ 𝓞K := Submodule.restrictScalars ℤ
    (idealOfForm_of_mod_four_eq_one d hd4 Q)
  have h_map_sets : (Submodule.map e_symm_lin J_ℤ : Set 𝓞K) = (I_ℤ : Set 𝓞K) := by
    ext x; constructor
    · intro hx
      rcases Submodule.mem_map.mp hx with ⟨y, hy, hy_eq⟩
      rw [← hy_eq]
      have hy_J : (y : ZOnePlusSqrtdOverTwo (d / 4)) ∈ J := hy
      have hmem : e_symm_lin y ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
        rw [idealOfForm_of_mod_four_eq_one, Ideal.mem_comap]
        dsimp [e_symm_lin, e_symm_alg, toRingOfIntegersAlgEquivEqOne]
        simpa [J, CoxIdealRelation.coxIdeal, DD, bb, A, u] using hy_J
      simpa [I_ℤ] using hmem
    · intro hx
      have hx_ideal : (x : 𝓞K) ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := hx
      rw [idealOfForm_of_mod_four_eq_one, Ideal.mem_comap] at hx_ideal
      apply Submodule.mem_map.mpr
      let y_val : ZOnePlusSqrtdOverTwo (d / 4) := e x
      have hy_J : y_val ∈ J := by
        dsimp [J, y_val, CoxIdealRelation.coxIdeal, DD, bb, A, u]
        simpa using hx_ideal
      have hy_ℤ : y_val ∈ J_ℤ := hy_J
      use y_val
      constructor
      · exact hy_ℤ
      · dsimp [e_symm_lin, y_val, e_symm_alg, toRingOfIntegersAlgEquivEqOne]
        exact e.symm_apply_apply x
  have h_map : Submodule.map e_symm_lin J_ℤ = I_ℤ :=
    Submodule.ext fun x => by
      rw [Set.ext_iff] at h_map_sets
      simpa using h_map_sets x
  let f_final : J_ℤ ≃ₗ[ℤ] I_ℤ :=
    (Submodule.equivMapOfInjective e_symm_lin h_inj J_ℤ).trans
      (LinearEquiv.ofEq _ _ h_map)
  let id_src : J ≃ₗ[ℤ] J_ℤ :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let id_tgt : I_ℤ ≃ₗ[ℤ] idealOfForm_of_mod_four_eq_one d hd4 Q :=
    { toFun := fun x => ⟨x.1, x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let b_J_ℤ : Basis (Fin 2) ℤ J_ℤ := b_generic.map id_src
  let b_I_ℤ : Basis (Fin 2) ℤ I_ℤ := b_J_ℤ.map f_final
  exact b_I_ℤ.map id_tgt

/-- The first Cox basis element in the `d % 4 = 1` branch is the transported scalar `a`. -/
theorem coxIdealBasisOKEqOne_val_0 (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).symm
      (Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)) := by
  dsimp [coxIdealBasisOKEqOne]
  simp [CoxIdealRelation.coxIdealBasis, Basis.coe_mk, toRingOfIntegersAlgEquivEqOne]

/-- The second Cox basis element in the `d % 4 = 1` branch is the transported
generic Cox beta. -/
theorem coxIdealBasisOKEqOne_val_1 (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) =
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).symm
      (CoxIdealRelation.coxBeta (d / 4) 1 ((-1 + -Q.1.b) / 2)) := by
  dsimp [coxIdealBasisOKEqOne]
  simp [CoxIdealRelation.coxIdealBasis, Basis.coe_mk, toRingOfIntegersAlgEquivEqOne]

/-- The K-coordinates of the transported Cox basis elements (`d % 4 = 1` branch). -/
theorem coxIdealBasisOKEqOne_K_re_im (hd4 : d % 4 = 1) (hdneg : d < 0)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) : K).re = (Q.1.a : ℚ) ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 0 : 𝓞K) : K).im = 0 ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) : K).re = (Q.1.b / 2 : ℚ) ∧
    (((coxIdealBasisOKEqOne hd4 hdneg Q) 1 : 𝓞K) : K).im = (-(1 : ℚ) / 2) := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let x0 : 𝓞K := (coxIdealBasisOKEqOne hd4 hdneg Q) 0
  let x1 : 𝓞K := (coxIdealBasisOKEqOne hd4 hdneg Q) 1
  have hx0 := coxIdealBasisOKEqOne_val_0 hd4 hdneg Q
  have hx1 := coxIdealBasisOKEqOne_val_1 hd4 hdneg Q
  have hex0 : e x0 = (Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)) := by
    dsimp [x0] at hx0 ⊢
    rw [hx0, RingEquiv.apply_symm_apply]
  have hex1 : e x1 = CoxIdealRelation.coxBeta (d / 4) 1 ((-1 + -Q.1.b) / 2) := by
    dsimp [x1] at hx1 ⊢
    rw [hx1, RingEquiv.apply_symm_apply]
  have h0_re_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x0
  have h0_im_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x0
  have h1_re_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_re
      d hd4 x1
  have h1_im_eq :=
    RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one_im
      d hd4 x1
  dsimp at h0_re_eq h0_im_eq h1_re_eq h1_im_eq
  rw [hex0] at h0_re_eq h0_im_eq
  rw [hex1] at h1_re_eq h1_im_eq
  have h0_re : (x0 : K).re = (Q.1.a : ℚ) := by
    simpa [x0] using h0_re_eq.symm
  have h0_im : (x0 : K).im = 0 := by
    simpa [x0] using h0_im_eq.symm
  have h1_im : (x1 : K).im = (-(1 : ℚ) / 2) := by
    simpa [x1, CoxIdealRelation.coxBeta] using h1_im_eq.symm
  have hodd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  obtain ⟨k, hk⟩ := hodd
  have hdiv : ((-1 + -Q.1.b) / 2 : ℤ) = -1 - k := by
    rw [hk]
    omega
  have h1_re : (x1 : K).re = (Q.1.b / 2 : ℚ) := by
    rw [← h1_re_eq]
    simp only [CoxIdealRelation.coxBeta_re, CoxIdealRelation.coxBeta_im,
      Int.cast_neg, Int.cast_one]
    rw [hdiv, hk]
    norm_num
    ring
  exact ⟨by simpa [x0] using h0_re, by simpa [x0] using h0_im,
    by simpa [x1] using h1_re, by simpa [x1] using h1_im⟩

/-- Left-inverse law for the `d % 4 = 1` branch. -/
theorem classGroupToFormClass_idealClassOfForm_leftInverse_of_mod_four_eq_one
    (hdneg : d < 0) (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    classGroupToFormClass hdneg
      (idealClassOfForm_of_mod_four_eq_one d hd4 Q) =
      Quotient.mk (primitivePositiveDefiniteFormSetoid _) Q := by
  let I : (Ideal 𝓞K)⁰ := ⟨idealOfForm_of_mod_four_eq_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr (idealOfForm_of_mod_four_eq_one_ne_zero d hd4 Q)⟩
  have hI_ne_zero : (I : Ideal 𝓞K) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  have h_idealClass : idealClassOfForm_of_mod_four_eq_one d hd4 Q = ClassGroup.mk0 I := rfl
  rw [h_idealClass]
  have h_class_eq : classGroupToFormClass hdneg (ClassGroup.mk0 I) =
      formClassOfNonzeroIdeal hdneg I := by
    dsimp [classGroupToFormClass]
    let J := Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    have hJ_mk0 : ClassGroup.mk0 J = ClassGroup.mk0 I :=
      Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I))
    exact formClassOfNonzeroIdeal_eq_of_mk0_eq hdneg J I hJ_mk0
  rw [h_class_eq]
  rw [formClassOfNonzeroIdeal_eq_mk hdneg I
    (b := orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)]
  rcases coxIdealBasisOKEqOne_K_re_im hd4 hdneg Q with ⟨h0_re, h0_im, h1_re, h1_im⟩
  let b_cox := coxIdealBasisOKEqOne hd4 hdneg Q
  set α := ((b_cox 0 : 𝓞K) : K) with hα
  set β := ((b_cox 1 : 𝓞K) : K) with hβ
  have h_wedge_im : (α * star β - β * star α).im = (Q.1.a : ℚ) := by
    simp [α, β, QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul,
      h0_re, h0_im, h1_re, h1_im, QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]
    ring
  have ha_pos : 0 < (Q.1.a : ℚ) := by exact_mod_cast Q.2.2.2.1
  have hpos : imPartRatio (d := d) (α * star β - β * star α) > 0 := by
    rw [imPartRatio_eq_im, h_wedge_im]
    exact ha_pos
  let b_oriented : OrientedBasis (I : Ideal 𝓞K) :=
    { basis := b_cox, oriented := hpos }
  have h_normform_eq : normFormOfBasis hI_ne_zero b_oriented = Q.1 := by
    have hb0 : ((b_oriented.basis 0 : 𝓞K) : K) = α := hα.symm
    have hb1 : ((b_oriented.basis 1 : 𝓞K) : K) = β := hβ.symm
    have ha_pos_int : 0 < Q.1.a := Q.2.2.2.1
    have hane : Q.1.a ≠ 0 := ne_of_gt ha_pos_int
    have hdetCoord : b_oriented.detCoord = -(Q.1.a : ℚ) / 2 := by
      unfold OrientedBasis.detCoord
      rw [hb0, hb1, h0_re, h0_im, h1_re, h1_im]
      ring
    have hz_eq : ((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det
        ((↑) ∘ b_oriented.basis) : ℤ) = -Q.1.a := by
      have hz_cast : (((RingOfIntegers.ringOfIntegersBasisOfModFourEqOne hd4).det
          ((↑) ∘ b_oriented.basis) : ℤ) : ℚ) = -(Q.1.a : ℚ) := by
        rw [b_oriented.det_eq_one_cast_eq_two_detCoord hd4, hdetCoord]
        ring
      exact_mod_cast hz_cast
    have hN_eq : (Ideal.absNorm (I : Ideal 𝓞K) : ℤ) = Q.1.a := by
      have hz_abs := b_oriented.det_eq_one_natAbs_eq_absNorm hd4
      rw [hz_eq] at hz_abs
      simp only [Int.natAbs_neg] at hz_abs
      omega
    have hdiscQ : (Q.1.b : ℚ) ^ 2 - 4 * (Q.1.a : ℚ) * (Q.1.c : ℚ) = (d : ℚ) := by
      have hz : Q.1.disc = d :=
        calc Q.1.disc = fieldDiscriminant d := Q.2.1
          _ = d := fieldDiscriminant_of_mod_four_eq_one hd4
      unfold BinaryQuadraticForm.disc at hz
      exact_mod_cast hz
    have hnorm0 : Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) = Q.1.a ^ 2 := by
      have h : (Algebra.norm ℤ (b_oriented.basis 0 : 𝓞K) : ℚ) = (Q.1.a : ℚ) ^ 2 := by
        rw [fieldNorm_int_eq, hb0, h0_re, h0_im]
        ring
      exact_mod_cast h
    have hnorm1 : Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) = Q.1.a * Q.1.c := by
      have h : (Algebra.norm ℤ (b_oriented.basis 1 : 𝓞K) : ℚ) =
          (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hb1, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    have hnormsum :
        Algebra.norm ℤ ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) =
          Q.1.a ^ 2 + Q.1.a * Q.1.b + Q.1.a * Q.1.c := by
      have hsum_coe :
          (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
            α + β := by
        have hpc :
            (((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K) : 𝓞K) : K) =
              ((b_oriented.basis 0 : 𝓞K) : K) + ((b_oriented.basis 1 : 𝓞K) : K) := by
          push_cast
          ring
        rw [hpc, hb0, hb1]
      have h :
          (Algebra.norm ℤ
            ((b_oriented.basis 0 : 𝓞K) + (b_oriented.basis 1 : 𝓞K)) : ℚ) =
            (Q.1.a : ℚ) ^ 2 +
              (Q.1.a : ℚ) * (Q.1.b : ℚ) + (Q.1.a : ℚ) * (Q.1.c : ℚ) := by
        rw [fieldNorm_int_eq, hsum_coe]
        simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
          h0_re, h0_im, h1_re, h1_im]
        linear_combination (1 / 4 : ℚ) * hdiscQ
      exact_mod_cast h
    exact normFormOfBasis_eq_of_norms hI_ne_zero b_oriented hane hN_eq hnorm0 hnorm1 hnormsum
  have h_equiv : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent
      (normFormOfBasis hI_ne_zero b_oriented) :=
    (normFormOfBasis_properEquivalent hI_ne_zero _ _).symm
  have h_target : (normFormOfBasis hI_ne_zero
      (orientedBasisOfNeZero (I : Ideal 𝓞K) hI_ne_zero)).ProperEquivalent Q.1 :=
    h_equiv.trans (by rw [h_normform_eq]; exact BinaryQuadraticForm.ProperEquivalent.refl Q.1)
  dsimp [primitivePositiveDefiniteNormFormOfBasis]
  apply Quotient.sound
  simpa using h_target

end CoxLeftInverseEqOne

end BinaryQuadraticForm
end QuadraticNumberFields
