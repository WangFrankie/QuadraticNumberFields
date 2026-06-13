/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.ClassNumber
import QuadraticNumberFields.Forms.CoxIdealRelation
import QuadraticNumberFields.Forms.UpperHalfPlane
import QuadraticNumberFields.RingOfIntegers.Classification
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Cox 7.7 Bridge from Forms to Ideal Classes

This WIP module records the intended imaginary-side Cox 7.7 bridge. It is
imported only by `Sketch.lean` until the full Gauss reduction and ideal-class
proofs close.
-/

open scoped NumberField

attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## WIP Gauss reduction interface -/

/-- WIP Gauss reduction existence statement for positive definite forms. -/
theorem exists_isReduced_properEquivalent (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) : ∃ R, R.IsReduced ∧ ProperEquivalent Q R := by
  obtain ⟨g, hgfd⟩ := ModularGroup.exists_smul_mem_fd (tauOfForm Q hQ)
  let P := transform Q g⁻¹
  have hPpos : P.IsPositiveDefinite := isPositiveDefinite_transform Q hQ g⁻¹
  have hτP : tauOfForm P hPpos = g • tauOfForm Q hQ := by
    simpa [P] using tauOfForm_transform Q hQ g⁻¹ hPpos
  have hPfd : tauOfForm P hPpos ∈ ModularGroup.fd := by
    simpa [hτP] using hgfd
  obtain ⟨n, hnred⟩ := exists_isReduced_transform_of_mem_fd P hPpos hPfd
  refine ⟨transform P n, hnred, ?_⟩
  refine ⟨g⁻¹ * n, ?_⟩
  simpa [P] using (transform_mul Q g⁻¹ n).symm

private theorem transform_neg (Q : BinaryQuadraticForm) (g : SL2Z) :
    transform Q (-g) = transform Q g := by
  ext <;> simp only [transform_a, transform_b, transform_c,
    Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply] <;> ring

private theorem transform_neg_one (Q : BinaryQuadraticForm) :
    transform Q (-1 : SL2Z) = Q := by
  simpa using transform_neg Q (1 : SL2Z)

private theorem transform_T_inv_mk (a b c : ℤ) :
    transform (BinaryQuadraticForm.mk a b c) (ModularGroup.T⁻¹ : SL2Z) =
      BinaryQuadraticForm.mk a (b - 2 * a) (a - b + c) := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    norm_num [ModularGroup.T, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two] <;>
    ring

private theorem transform_S_mk (a b c : ℤ) :
    transform (BinaryQuadraticForm.mk a b c) ModularGroup.S =
      BinaryQuadraticForm.mk c (-b) a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    simp [ModularGroup.coe_S]

private theorem transform_ST_self_of_mk_eq (a : ℤ) :
    transform (BinaryQuadraticForm.mk a a a) (ModularGroup.S * ModularGroup.T : SL2Z) =
      BinaryQuadraticForm.mk a a a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem transform_T_inv_S_self_of_mk_eq (a : ℤ) :
    transform (BinaryQuadraticForm.mk a a a) (ModularGroup.T⁻¹ * ModularGroup.S : SL2Z) =
      BinaryQuadraticForm.mk a a a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    norm_num [ModularGroup.S, ModularGroup.T, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem transform_ST_inv_self_of_mk_eq (a : ℤ) :
    transform (BinaryQuadraticForm.mk a a a) ((ModularGroup.S * ModularGroup.T : SL2Z)⁻¹) =
      BinaryQuadraticForm.mk a a a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    norm_num [ModularGroup.S, ModularGroup.T, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem transform_T_inv_S_inv_self_of_mk_eq (a : ℤ) :
    transform (BinaryQuadraticForm.mk a a a) ((ModularGroup.T⁻¹ * ModularGroup.S : SL2Z)⁻¹) =
      BinaryQuadraticForm.mk a a a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    norm_num [ModularGroup.S, ModularGroup.T, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem transform_TST_inv_mk_eq (a : ℤ) :
    transform (BinaryQuadraticForm.mk a a a)
        ((ModularGroup.T * ModularGroup.S * ModularGroup.T : SL2Z)⁻¹) =
      BinaryQuadraticForm.mk a (-a) a := by
  ext <;> simp only [transform_a, transform_b, transform_c] <;>
    simp [ModularGroup.coe_S, ModularGroup.coe_T, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals ring

private theorem b_eq_a_of_tauOfForm_re_eq_neg_half (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : (tauOfForm Q hQ).re = -(1 : ℝ) / 2) :
    Q.b = Q.a := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hreal : -(Q.b : ℝ) / (2 * (Q.a : ℝ)) = -(1 : ℝ) / 2 := by
    simpa [tauOfForm_re] using h
  field_simp [ha] at hreal
  have hba : (Q.b : ℝ) = Q.a := by nlinarith
  exact_mod_cast hba

private theorem b_eq_neg_a_of_tauOfForm_re_eq_half (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : (tauOfForm Q hQ).re = (1 : ℝ) / 2) :
    Q.b = -Q.a := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hreal : -(Q.b : ℝ) / (2 * (Q.a : ℝ)) = (1 : ℝ) / 2 := by
    simpa [tauOfForm_re] using h
  field_simp [ha] at hreal
  have hba : (Q.b : ℝ) = -Q.a := by nlinarith
  exact_mod_cast hba

private theorem a_eq_c_of_tauOfForm_norm_eq_one (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : ‖(tauOfForm Q hQ : ℂ)‖ = 1) :
    Q.a = Q.c := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hnormSq : Complex.normSq (tauOfForm Q hQ : ℂ) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h]
    norm_num
  rw [normSq_tauOfForm] at hnormSq
  field_simp [ha] at hnormSq
  have hac : (Q.c : ℝ) = Q.a := by linarith
  exact_mod_cast hac.symm

private theorem b_eq_a_of_tauOfForm_eq_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : tauOfForm Q hQ = UpperHalfPlane.ρ) :
    Q.b = Q.a := by
  apply b_eq_a_of_tauOfForm_re_eq_neg_half Q hQ
  rw [h]
  norm_num [UpperHalfPlane.ρ]

private theorem b_eq_neg_a_of_tauOfForm_eq_one_vadd_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : tauOfForm Q hQ = (1 : ℝ) +ᵥ UpperHalfPlane.ρ) :
    Q.b = -Q.a := by
  apply b_eq_neg_a_of_tauOfForm_re_eq_half Q hQ
  rw [h]
  norm_num [UpperHalfPlane.ρ]

private theorem a_eq_c_of_tauOfForm_eq_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (h : tauOfForm Q hQ = UpperHalfPlane.ρ) :
    Q.a = Q.c := by
  have ha : (Q.a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hQ.1)
  have hnormSq : Complex.normSq (tauOfForm Q hQ : ℂ) = 1 := by
    rw [h]
    have hsqrt : Real.sqrt 3 * Real.sqrt 3 = (3 : ℝ) :=
      Real.mul_self_sqrt (by norm_num)
    norm_num [UpperHalfPlane.ρ, Complex.normSq_apply]
    nlinarith
  rw [normSq_tauOfForm] at hnormSq
  field_simp [ha] at hnormSq
  have hac : (Q.c : ℝ) = Q.a := by linarith
  exact_mod_cast hac.symm

private theorem false_of_isReduced_of_b_eq_neg_a (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hred : Q.IsReduced) (hb : Q.b = -Q.a) : False := by
  rcases Q with ⟨a, b, c⟩
  change 0 < a ∧ _ at hQ
  change b = -a at hb
  subst b
  have hboundary : |-a| = a := by rw [abs_neg, abs_of_pos hQ.1]
  have hnonneg := hred.2.2.1 hboundary
  nlinarith

private theorem false_of_isReduced_transform_T_inv_of_b_eq_a (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hb : Q.b = Q.a)
    (hred : (transform Q (ModularGroup.T⁻¹ : SL2Z)).IsReduced) : False := by
  rcases Q with ⟨a, b, c⟩
  change 0 < a ∧ _ at hQ
  change b = a at hb
  subst b
  rw [transform_T_inv_mk, isReduced_mk_iff] at hred
  have hboundary : |a - 2 * a| = a := by
    rw [show a - 2 * a = -a by ring, abs_neg, abs_of_pos hQ.1]
  have hnonneg := hred.2.2.1 hboundary
  nlinarith

private theorem transform_S_eq_self_of_reduced_of_norm_eq_one (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hQred : Q.IsReduced)
    (hSred : (transform Q ModularGroup.S).IsReduced)
    (hnorm : ‖(tauOfForm Q hQ : ℂ)‖ = 1) :
    transform Q ModularGroup.S = Q := by
  have hac := a_eq_c_of_tauOfForm_norm_eq_one Q hQ hnorm
  rcases Q with ⟨a, b, c⟩
  change a = c at hac
  subst c
  have hb_nonneg : 0 ≤ b := hQred.2.2.2 rfl
  rw [transform_S_mk, isReduced_mk_iff] at hSred
  have hneg_nonneg : 0 ≤ -b := hSred.2.2.2 rfl
  have hb_zero : b = 0 := by nlinarith
  rw [transform_S_mk, hb_zero, neg_zero]

private theorem false_of_isReduced_transform_TST_inv_of_tau_eq_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hrho : tauOfForm Q hQ = UpperHalfPlane.ρ)
    (hred :
      (transform Q ((ModularGroup.T * ModularGroup.S * ModularGroup.T : SL2Z)⁻¹)).IsReduced) :
    False := by
  have hb := b_eq_a_of_tauOfForm_eq_rho Q hQ hrho
  have hac := a_eq_c_of_tauOfForm_eq_rho Q hQ hrho
  rcases Q with ⟨a, b, c⟩
  change 0 < a ∧ _ at hQ
  change b = a at hb
  change a = c at hac
  subst b
  subst c
  rw [transform_TST_inv_mk_eq, isReduced_mk_iff] at hred
  have hboundary : |-a| = a := by rw [abs_neg, abs_of_pos hQ.1]
  have hnonneg := hred.2.2.1 hboundary
  nlinarith

private theorem transform_ST_inv_eq_self_of_tau_eq_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hrho : tauOfForm Q hQ = UpperHalfPlane.ρ) :
    transform Q ((ModularGroup.S * ModularGroup.T : SL2Z)⁻¹) = Q := by
  have hb := b_eq_a_of_tauOfForm_eq_rho Q hQ hrho
  have hac := a_eq_c_of_tauOfForm_eq_rho Q hQ hrho
  rcases Q with ⟨a, b, c⟩
  change b = a at hb
  change a = c at hac
  subst b
  subst c
  exact transform_ST_inv_self_of_mk_eq a

private theorem transform_T_inv_S_inv_eq_self_of_tau_eq_rho (Q : BinaryQuadraticForm)
    (hQ : Q.IsPositiveDefinite) (hrho : tauOfForm Q hQ = UpperHalfPlane.ρ) :
    transform Q ((ModularGroup.T⁻¹ * ModularGroup.S : SL2Z)⁻¹) = Q := by
  have hb := b_eq_a_of_tauOfForm_eq_rho Q hQ hrho
  have hac := a_eq_c_of_tauOfForm_eq_rho Q hQ hrho
  rcases Q with ⟨a, b, c⟩
  change b = a at hb
  change a = c at hac
  subst b
  subst c
  exact transform_T_inv_S_inv_self_of_mk_eq a

/-- WIP uniqueness statement for boundary-normalized reduced representatives. -/
theorem eq_of_isReduced_of_properEquivalent {Q R : BinaryQuadraticForm}
    (hQpos : Q.IsPositiveDefinite) (hQred : Q.IsReduced) (hRred : R.IsReduced)
    (h : ProperEquivalent Q R) : Q = R := by
  rcases h with ⟨g, rfl⟩
  let z := tauOfForm Q hQpos
  have hRpos : (transform Q g).IsPositiveDefinite := isPositiveDefinite_transform Q hQpos g
  have hzfd : z ∈ ModularGroup.fd := by
    simpa [z] using tauOfForm_mem_fd_of_isReduced Q hQpos hQred
  have hτ : tauOfForm (transform Q g) hRpos = g⁻¹ • z := by
    simpa [z] using tauOfForm_transform Q hQpos g hRpos
  have hgfd : g⁻¹ • z ∈ ModularGroup.fd := by
    simpa [hτ] using tauOfForm_mem_fd_of_isReduced (transform Q g) hRpos hRred
  have hcases := ModularGroup.cases_of_mem_fd_smul_mem_fd (g := g⁻¹) (z := z) hzfd hgfd
  rcases hcases with hunit | hcases
  · rcases hunit with hginv | hginv
    · have hg : g = 1 := by simpa using congrArg Inv.inv hginv
      simp [hg]
    · have hg : g = -1 := by simpa using congrArg Inv.inv hginv
      simp [hg, transform_neg_one]
  rcases hcases with hT | hcases
  · rcases hT with ⟨hginv, hzre⟩
    have hb : Q.b = Q.a := b_eq_a_of_tauOfForm_re_eq_neg_half Q hQpos (by
      simpa [z] using hzre)
    have hTred : (transform Q (ModularGroup.T⁻¹ : SL2Z)).IsReduced := by
      rcases hginv with hginv | hginv
      · have hg : g = ModularGroup.T⁻¹ := by simpa using congrArg Inv.inv hginv
        simpa [hg] using hRred
      · have hg : g = -ModularGroup.T⁻¹ := by simpa using congrArg Inv.inv hginv
        simpa [hg, transform_neg] using hRred
    exact (false_of_isReduced_transform_T_inv_of_b_eq_a Q hQpos hb hTred).elim
  rcases hcases with hTinv | hcases
  · rcases hTinv with ⟨_, hzre⟩
    have hb : Q.b = -Q.a := b_eq_neg_a_of_tauOfForm_re_eq_half Q hQpos (by
      simpa [z] using hzre)
    exact (false_of_isReduced_of_b_eq_neg_a Q hQpos hQred hb).elim
  rcases hcases with hS | hcases
  · rcases hS with ⟨hginv, hnorm⟩
    have hSred : (transform Q ModularGroup.S).IsReduced := by
      rcases hginv with hginv | hginv
      · have hg : g = -ModularGroup.S := by
          simpa [ModularGroup.S_inv] using congrArg Inv.inv hginv
        simpa [hg, transform_neg] using hRred
      · have hg : g = ModularGroup.S := by
          simpa [ModularGroup.S_inv] using congrArg Inv.inv hginv
        simpa [hg] using hRred
    have hself := transform_S_eq_self_of_reduced_of_norm_eq_one Q hQpos hQred hSred (by
      simpa [z] using hnorm)
    rcases hginv with hginv | hginv
    · have hg : g = -ModularGroup.S := by
        simpa [ModularGroup.S_inv] using congrArg Inv.inv hginv
      simp [hg, transform_neg, hself]
    · have hg : g = ModularGroup.S := by
        simpa [ModularGroup.S_inv] using congrArg Inv.inv hginv
      simp [hg, hself]
  rcases hcases with hTS | hcases
  · rcases hTS with ⟨_, hzrho⟩
    have hb : Q.b = -Q.a := b_eq_neg_a_of_tauOfForm_eq_one_vadd_rho Q hQpos (by
      simpa [z] using hzrho)
    exact (false_of_isReduced_of_b_eq_neg_a Q hQpos hQred hb).elim
  rcases hcases with hTinSTin | hcases
  · rcases hTinSTin with ⟨_, hzrho⟩
    have hb : Q.b = -Q.a := b_eq_neg_a_of_tauOfForm_eq_one_vadd_rho Q hQpos (by
      simpa [z] using hzrho)
    exact (false_of_isReduced_of_b_eq_neg_a Q hQpos hQred hb).elim
  rcases hcases with hSTin | hcases
  · rcases hSTin with ⟨_, hzrho⟩
    have hb : Q.b = -Q.a := b_eq_neg_a_of_tauOfForm_eq_one_vadd_rho Q hQpos (by
      simpa [z] using hzrho)
    exact (false_of_isReduced_of_b_eq_neg_a Q hQpos hQred hb).elim
  rcases hcases with hST | hcases
  · rcases hST with ⟨hginv, hzrho⟩
    have hrho : tauOfForm Q hQpos = UpperHalfPlane.ρ := by simpa [z] using hzrho
    have hself := transform_ST_inv_eq_self_of_tau_eq_rho Q hQpos hrho
    rcases hginv with hginv | hginv
    · have hg : g = (ModularGroup.S * ModularGroup.T : SL2Z)⁻¹ := by
        simpa using congrArg Inv.inv hginv
      simpa [hg] using hself.symm
    · have hg : g = -((ModularGroup.S * ModularGroup.T : SL2Z)⁻¹) := by
        simpa using congrArg Inv.inv hginv
      simpa [hg, transform_neg] using hself.symm
  rcases hcases with hTST | hcases
  · rcases hTST with ⟨hginv, hzrho⟩
    have hrho : tauOfForm Q hQpos = UpperHalfPlane.ρ := by simpa [z] using hzrho
    have hTSTred :
        (transform Q
          ((ModularGroup.T * ModularGroup.S * ModularGroup.T : SL2Z)⁻¹)).IsReduced := by
      rcases hginv with hginv | hginv
      · have hg : g = (ModularGroup.T * ModularGroup.S * ModularGroup.T : SL2Z)⁻¹ := by
          simpa using congrArg Inv.inv hginv
        simpa [hg] using hRred
      · have hg : g = -((ModularGroup.T * ModularGroup.S * ModularGroup.T : SL2Z)⁻¹) := by
          simpa using congrArg Inv.inv hginv
        simpa [hg, transform_neg] using hRred
    exact (false_of_isReduced_transform_TST_inv_of_tau_eq_rho Q hQpos hrho hTSTred).elim
  rcases hcases with ⟨hginv, hzrho⟩
  have hrho : tauOfForm Q hQpos = UpperHalfPlane.ρ := by simpa [z] using hzrho
  have hself := transform_T_inv_S_inv_eq_self_of_tau_eq_rho Q hQpos hrho
  rcases hginv with hginv | hginv
  · have hg : g = (ModularGroup.T⁻¹ * ModularGroup.S : SL2Z)⁻¹ := by
      simpa using congrArg Inv.inv hginv
    simpa [hg] using hself.symm
  · have hg : g = -((ModularGroup.T⁻¹ * ModularGroup.S : SL2Z)⁻¹) := by
      simpa using congrArg Inv.inv hginv
    simpa [hg, transform_neg] using hself.symm

/-! ## WIP Cox 7.7 class-group bridge -/

/-- Primitive positive definite forms of discriminant `D`. This is the
imaginary-side carrier used by Cox 7.7; negative definite forms of the same
negative discriminant are not part of this class-number bridge. -/
def PrimitivePositiveDefiniteForm (D : ℤ) : Type :=
  { Q : BinaryQuadraticForm //
    Q.HasDiscriminant D ∧ Q.IsPrimitive ∧ Q.IsPositiveDefinite }

namespace PrimitivePositiveDefiniteForm

/-- Proper equivalence restricted to primitive positive definite forms. -/
def ProperEquivalent {D : ℤ}
    (Q R : PrimitivePositiveDefiniteForm D) : Prop :=
  BinaryQuadraticForm.ProperEquivalent Q.1 R.1

end PrimitivePositiveDefiniteForm

/-! ## Restricted Gauss reduction interface -/

/-- Every primitive positive definite form has a properly equivalent reduced
representative inside the same restricted carrier. -/
theorem exists_isReduced_primitivePositiveDefiniteForm_properEquivalent
    {D : ℤ} (Q : PrimitivePositiveDefiniteForm D) :
    ∃ R : PrimitivePositiveDefiniteForm D, R.1.IsReduced ∧
      PrimitivePositiveDefiniteForm.ProperEquivalent Q R := by
  obtain ⟨R, hRred, hQR⟩ := exists_isReduced_properEquivalent Q.1 Q.2.2.2
  rcases hQR with ⟨g, rfl⟩
  refine ⟨⟨transform Q.1 g, ?_⟩, hRred, ⟨g, rfl⟩⟩
  constructor
  · exact (disc_transform Q.1 g).trans Q.2.1
  · constructor
    · exact isPrimitive_transform Q.1 Q.2.2.1 g
    · exact isPositiveDefinite_transform Q.1 Q.2.2.2 g

/-- Boundary-normalized reduced representatives are unique within the
restricted primitive positive definite carrier. -/
theorem eq_of_isReduced_primitivePositiveDefiniteForm_of_properEquivalent
    {D : ℤ} {Q R : PrimitivePositiveDefiniteForm D}
    (hQred : Q.1.IsReduced) (hRred : R.1.IsReduced)
    (h : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) : Q = R := by
  apply Subtype.ext
  exact eq_of_isReduced_of_properEquivalent Q.2.2.2 hQred hRred h

/-- Setoid on primitive positive definite forms given by proper equivalence. -/
instance primitivePositiveDefiniteFormSetoid (D : ℤ) :
    Setoid (PrimitivePositiveDefiniteForm D) where
  r := PrimitivePositiveDefiniteForm.ProperEquivalent
  iseqv := ⟨
    fun Q => BinaryQuadraticForm.ProperEquivalent.refl Q.1,
    fun h => BinaryQuadraticForm.ProperEquivalent.symm h,
    fun hQR hRS => BinaryQuadraticForm.ProperEquivalent.trans hQR hRS⟩

/-- Proper equivalence classes of primitive positive definite binary quadratic
forms of discriminant `D`. -/
def FormClass (D : ℤ) : Type :=
  Quotient (primitivePositiveDefiniteFormSetoid D)

/-- Every form class has a reduced primitive positive definite representative. -/
theorem exists_isReduced_mk_eq_formClass {D : ℤ} (C : FormClass D) :
    ∃ R : PrimitivePositiveDefiniteForm D, R.1.IsReduced ∧
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) R = C := by
  induction C using Quotient.inductionOn with
  | h Q =>
      obtain ⟨R, hRred, hQR⟩ :=
        exists_isReduced_primitivePositiveDefiniteForm_properEquivalent Q
      exact ⟨R, hRred, (Quotient.sound hQR).symm⟩

/-- Reduced representatives of the same form class are equal. -/
theorem eq_of_isReduced_of_mk_eq_mk {D : ℤ} {Q R : PrimitivePositiveDefiniteForm D}
    (hQred : Q.1.IsReduced) (hRred : R.1.IsReduced)
    (hclass : Quotient.mk (primitivePositiveDefiniteFormSetoid D) Q =
      Quotient.mk (primitivePositiveDefiniteFormSetoid D) R) :
    Q = R :=
  eq_of_isReduced_primitivePositiveDefiniteForm_of_properEquivalent hQred hRred
    (Quotient.exact hclass)

/-- The field discriminant attached to a squarefree `Qsqrtd d` parameter. -/
def fieldDiscriminant (d : ℤ) : ℤ :=
  if d % 4 = 1 then d else 4 * d

/-- In the `d % 4 ≠ 1` Cox branch, a form of field discriminant has even
middle coefficient. This justifies the `-b / 2` coordinate in the `Zsqrtd`
ideal generator. -/
theorem even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one
    {d : ℤ} (hd4 : d % 4 ≠ 1) {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d)) : Even Q.b := by
  have hdisc' : Q.b ^ 2 - 4 * Q.a * Q.c = 4 * d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using hdisc
  by_contra hb_even
  have hb_not_dvd : ¬ (2 : ℤ) ∣ Q.b := by simpa [Int.even_iff] using hb_even
  have hb2dvd : (4 : ℤ) ∣ Q.b ^ 2 := by
    refine ⟨Q.a * Q.c + d, ?_⟩
    nlinarith
  have hb2mod0 : Q.b ^ 2 % 4 = 0 := (Int.dvd_iff_emod_eq_zero).mp hb2dvd
  have hb2mod1 : Q.b ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd Q.b hb_not_dvd
  omega

/-- In the `d % 4 = 1` Cox branch, a form of field discriminant has odd
middle coefficient. This justifies the `-(b + 1) / 2` coordinate in the
`ZOnePlusSqrtdOverTwo` ideal generator. -/
theorem odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one
    {d : ℤ} (hd4 : d % 4 = 1) {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d)) : Odd Q.b := by
  rw [← Int.not_even_iff_odd]
  intro hb_even
  have hdisc' : Q.b ^ 2 - 4 * Q.a * Q.c = d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using hdisc
  have hb_dvd : (2 : ℤ) ∣ Q.b := by simpa [Int.even_iff] using hb_even
  have hb2mod0 : Q.b ^ 2 % 4 = 0 := Int.sq_emod_four_of_even Q.b hb_dvd
  have hb2mod1 : Q.b ^ 2 % 4 = 1 := by
    have hmod : Q.b ^ 2 % 4 = d % 4 := by
      have hb2_eq : Q.b ^ 2 = 4 * Q.a * Q.c + d := by nlinarith
      rw [hb2_eq, show 4 * Q.a * Q.c + d = d + 4 * (Q.a * Q.c) by ring,
        Int.add_mul_emod_self_left]
    simpa [hd4] using hmod
  omega

private theorem comap_span_singleton_mul_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (x : S) (I : Ideal S) :
    Ideal.comap (e : R →+* S) (Ideal.span ({x} : Set S) * I) =
      Ideal.span ({e.symm x} : Set R) * Ideal.comap (e : R →+* S) I := by
  have hmap_inj : Function.Injective (fun J : Ideal R => Ideal.map (e : R →+* S) J) := by
    intro J K hJK
    have h := congrArg (fun L : Ideal S => Ideal.map (e.symm : S →+* R) L) hJK
    simpa using h
  apply hmap_inj
  change Ideal.map (e : R →+* S)
      (Ideal.comap (e : R →+* S) (Ideal.span ({x} : Set S) * I)) =
    Ideal.map (e : R →+* S)
      (Ideal.span ({e.symm x} : Set R) * Ideal.comap (e : R →+* S) I)
  rw [Ideal.map_comap_of_surjective (f := (e : R →+* S)) e.surjective]
  rw [Ideal.map_mul]
  rw [Ideal.map_comap_of_surjective (f := (e : R →+* S)) e.surjective]
  rw [Ideal.map_span]
  simp

private theorem two_mul_neg_div_two_of_even {b : ℤ} (hb : Even b) : 2 * ((-b) / 2) = -b := by
  rcases hb with ⟨k, hk⟩
  omega

private theorem two_mul_neg_succ_div_two_of_odd {b : ℤ} (hb : Odd b) :
    2 * (-(b + 1) / 2) = -(b + 1) := by
  rcases hb with ⟨k, hk⟩
  omega

private theorem cox_zsqrtd_lam_ne_zero {D A p q r s u : ℤ}
    (hA : A ≠ 0) (hdet : p * s - q * r = 1) :
    (((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D)) ≠ 0 :=
  CoxIdealRelation.lam_ne_zero (DD := D) (bb := 0) hA hdet

private theorem cox_zsqrtd_ideal_relation {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D)} :
          Set (Zsqrtd D)) *
      Ideal.span ({(A : Zsqrtd D), (⟨u, 1⟩ : Zsqrtd D)} : Set (Zsqrtd D)) =
    Ideal.span
        ({(((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D))} :
          Set (Zsqrtd D)) *
      Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D),
          (⟨v, 1⟩ : Zsqrtd D)} : Set (Zsqrtd D)) :=
  CoxIdealRelation.ideal_relation (DD := D) (bb := 0) hdet (by simpa using hdisc)
    (by simpa using hu) (by simpa using hv)

private theorem cox_zsqrtd_ideal_relation_transform_of_mod_four_ne_one
    {d : ℤ} (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z) :
    Ideal.span ({(((transform Q.1 g).a : ℤ) : Zsqrtd d)} : Set (Zsqrtd d)) *
      Ideal.span
        ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)) =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
          (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d))} :
          Set (Zsqrtd d)) *
      Ideal.span
        ({(((transform Q.1 g).a : ℤ) : Zsqrtd d),
          (⟨(-(transform Q.1 g).b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa using h
  have hdisc : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 4 * d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using Q.2.1
  have hb_even : Even Q.1.b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 Q.2.1
  have hdisc_transform : (transform Q.1 g).HasDiscriminant (fieldDiscriminant d) := by
    simpa [HasDiscriminant, disc_transform] using Q.2.1
  have hb_transform_even : Even (transform Q.1 g).b :=
    even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one hd4 hdisc_transform
  have hu : 2 * ((-Q.1.b) / 2) = -Q.1.b :=
    two_mul_neg_div_two_of_even hb_even
  have hv : 2 * ((-(transform Q.1 g).b) / 2) =
      -(2 * Q.1.a * g 0 0 * g 0 1 +
        Q.1.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.1.c * g 1 0 * g 1 1) := by
    simpa [transform_b] using two_mul_neg_div_two_of_even hb_transform_even
  simpa [transform_a] using
    cox_zsqrtd_ideal_relation (D := d) (A := Q.1.a) (B := Q.1.b) (C := Q.1.c)
      (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1)
      (u := (-Q.1.b) / 2) (v := (-(transform Q.1 g).b) / 2)
      hdet hdisc hu hv

private theorem cox_zomega_ideal_relation {k A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 1 + 4 * k)
    (hu : 2 * u = -(B + 1))
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s + 1)) :
    Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : ZOnePlusSqrtdOverTwo k)} :
          Set (ZOnePlusSqrtdOverTwo k)) *
      Ideal.span
        ({(A : ZOnePlusSqrtdOverTwo k), (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k)} :
          Set (ZOnePlusSqrtdOverTwo k)) =
    Ideal.span
        ({(((p * A : ℤ) : ZOnePlusSqrtdOverTwo k) -
          (r : ZOnePlusSqrtdOverTwo k) * (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k))} :
          Set (ZOnePlusSqrtdOverTwo k)) *
      Ideal.span
        ({((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : ZOnePlusSqrtdOverTwo k),
          (⟨v, 1⟩ : ZOnePlusSqrtdOverTwo k)} : Set (ZOnePlusSqrtdOverTwo k)) :=
  CoxIdealRelation.ideal_relation (DD := k) (bb := 1) hdet (by simpa using hdisc)
    (by simpa using hu) (by simpa [add_comm] using hv)

private theorem cox_zomega_ideal_relation_transform_of_mod_four_eq_one
    {d : ℤ} (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z) :
    Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) *
      Ideal.span
        ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) =
    Ideal.span
        ({(((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
          (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
            (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4)))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) *
      Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-((transform Q.1 g).b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))) := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa using h
  have hdisc_d : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using Q.2.1
  have hd_eq : d = 1 + 4 * (d / 4) := by omega
  have hdisc : Q.1.b ^ 2 - 4 * Q.1.a * Q.1.c = 1 + 4 * (d / 4) :=
    hdisc_d.trans hd_eq
  have hb_odd : Odd Q.1.b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 Q.2.1
  have hdisc_transform : (transform Q.1 g).HasDiscriminant (fieldDiscriminant d) := by
    simpa [HasDiscriminant, disc_transform] using Q.2.1
  have hb_transform_odd : Odd (transform Q.1 g).b :=
    odd_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_eq_one hd4 hdisc_transform
  have hu : 2 * (-(Q.1.b + 1) / 2) = -(Q.1.b + 1) :=
    two_mul_neg_succ_div_two_of_odd hb_odd
  have hv : 2 * (-((transform Q.1 g).b + 1) / 2) =
      -(2 * Q.1.a * g 0 0 * g 0 1 +
        Q.1.b * (g 0 0 * g 1 1 + g 0 1 * g 1 0) + 2 * Q.1.c * g 1 0 * g 1 1 +
          1) := by
    simpa [transform_b] using two_mul_neg_succ_div_two_of_odd hb_transform_odd
  simpa [transform_a] using
    cox_zomega_ideal_relation (k := d / 4) (A := Q.1.a) (B := Q.1.b) (C := Q.1.c)
      (p := g 0 0) (q := g 0 1) (r := g 1 0) (s := g 1 1)
      (u := -(Q.1.b + 1) / 2) (v := -((transform Q.1 g).b + 1) / 2)
      hdet hdisc hu hv

private theorem cox_zomega_lam_ne_zero {k A p q r s u : ℤ}
    (hA : A ≠ 0) (hdet : p * s - q * r = 1) :
    (((p * A : ℤ) : ZOnePlusSqrtdOverTwo k) -
      (r : ZOnePlusSqrtdOverTwo k) * (⟨u, 1⟩ : ZOnePlusSqrtdOverTwo k)) ≠ 0 :=
  CoxIdealRelation.lam_ne_zero (DD := k) (bb := 1) hA hdet

/-- The Cox ideal `(a, (-b + √D) / 2)` in the `d % 4 ≠ 1` branch, transported
from the `Zsqrtd d` model back to the ring of integers of `Qsqrtd d`.

For forms of discriminant `fieldDiscriminant d = 4 * d`, the second generator is
represented in `Zsqrtd d` by `(-b / 2) + √d`. The divisibility-by-two fact is a
property of the discriminant hypotheses and is intentionally left to later Cox
bridge lemmas rather than baked into this definition. -/
noncomputable def idealOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Ideal (𝓞 (Qsqrtd (d : ℚ))) :=
  Ideal.comap
    (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4).toRingHom
    (Ideal.span
      ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
        Set (Zsqrtd d)))

private theorem cox_ringOfIntegers_ideal_relation_transform_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
    let lam : Zsqrtd d :=
      ((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
        (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
    Ideal.span ({e.symm (((R.1.a : ℤ) : Zsqrtd d))} :
        Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_ne_one d hd4 Q =
    Ideal.span ({e.symm lam} : Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_ne_one d hd4 R := by
  intro e lam
  have hcoord := cox_zsqrtd_ideal_relation_transform_of_mod_four_ne_one hd4 Q g
  have hcomap := congrArg (Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* Zsqrtd d)) hcoord
  rw [comap_span_singleton_mul_of_ringEquiv e (((transform Q.1 g).a : ℤ) : Zsqrtd d)
      (Ideal.span
        ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)))] at hcomap
  rw [comap_span_singleton_mul_of_ringEquiv e lam
      (Ideal.span
        ({(((transform Q.1 g).a : ℤ) : Zsqrtd d),
          (⟨(-(transform Q.1 g).b) / 2, 1⟩ : Zsqrtd d)} :
          Set (Zsqrtd d)))] at hcomap
  simpa [idealOfForm_of_mod_four_ne_one, hR] using hcomap

/-- The Cox ideal `(a, (-b + √d) / 2)` in the `d % 4 = 1` branch, transported
from the `ZOnePlusSqrtdOverTwo (d / 4)` model back to the ring of integers of
`Qsqrtd d`.

In the basis `1, ω` with `ω = (1 + √d) / 2`, the second generator has coordinates
`(-(b + 1) / 2, 1)`. The oddness of `b` follows from the discriminant hypotheses
and is left as a later Cox bridge lemma. -/
noncomputable def idealOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    Ideal (𝓞 (Qsqrtd (d : ℚ))) :=
  Ideal.comap
    (RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4).toRingHom
    (Ideal.span
      ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
        Set (ZOnePlusSqrtdOverTwo (d / 4))))

private theorem cox_ringOfIntegers_ideal_relation_transform_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
    let lam : ZOnePlusSqrtdOverTwo (d / 4) :=
      ((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
        (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))
    Ideal.span ({e.symm (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)))} :
        Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_eq_one d hd4 Q =
    Ideal.span ({e.symm lam} : Set (𝓞 (Qsqrtd (d : ℚ)))) *
      idealOfForm_of_mod_four_eq_one d hd4 R := by
  intro e lam
  have hcoord := cox_zomega_ideal_relation_transform_of_mod_four_eq_one hd4 Q g
  have hcomap := congrArg
    (Ideal.comap (e : 𝓞 (Qsqrtd (d : ℚ)) →+* ZOnePlusSqrtdOverTwo (d / 4))) hcoord
  rw [comap_span_singleton_mul_of_ringEquiv e
      (((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))
      (Ideal.span
        ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
          Set (ZOnePlusSqrtdOverTwo (d / 4))))] at hcomap
  rw [comap_span_singleton_mul_of_ringEquiv e lam
      (Ideal.span
        ({(((transform Q.1 g).a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
          (⟨-((transform Q.1 g).b + 1) / 2, 1⟩ :
            ZOnePlusSqrtdOverTwo (d / 4))} : Set (ZOnePlusSqrtdOverTwo (d / 4))))] at hcomap
  simpa [idealOfForm_of_mod_four_eq_one, hR] using hcomap

/-- The Cox ideal in the `d % 4 ≠ 1` branch is nonzero, because it contains the
nonzero positive integer coefficient `a`. -/
theorem idealOfForm_of_mod_four_ne_one_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    idealOfForm_of_mod_four_ne_one d hd4 Q ≠ 0 := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let x : 𝓞 (Qsqrtd (d : ℚ)) := e.symm ((Q.1.a : Zsqrtd d))
  have hxmem : x ∈ idealOfForm_of_mod_four_ne_one d hd4 Q := by
    change e x ∈ Ideal.span
      ({((Q.1.a : ℤ) : Zsqrtd d), (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)} :
        Set (Zsqrtd d))
    rw [show e x = ((Q.1.a : ℤ) : Zsqrtd d) by simp [x, e]]
    exact Ideal.subset_span (by simp)
  intro hI
  have hxzero : x = 0 := by
    have hxmem0 : x ∈ (0 : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
      simpa [hI] using hxmem
    simpa using hxmem0
  have haZ : ((Q.1.a : ℤ) : Zsqrtd d) = 0 := by
    have := congrArg e hxzero
    simpa [x, e] using this
  have ha0 : Q.1.a = 0 := by
    exact_mod_cast congrArg QuadraticAlgebra.re haZ
  exact (ne_of_gt Q.2.2.2.1) ha0

/-- The Cox ideal in the `d % 4 = 1` branch is nonzero, because it contains the
nonzero positive integer coefficient `a`. -/
theorem idealOfForm_of_mod_four_eq_one_ne_zero
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    idealOfForm_of_mod_four_eq_one d hd4 Q ≠ 0 := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let x : 𝓞 (Qsqrtd (d : ℚ)) :=
    e.symm ((Q.1.a : ZOnePlusSqrtdOverTwo (d / 4)))
  have hxmem : x ∈ idealOfForm_of_mod_four_eq_one d hd4 Q := by
    change e x ∈ Ideal.span
      ({((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)),
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))} :
        Set (ZOnePlusSqrtdOverTwo (d / 4)))
    rw [show e x = ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) by simp [x, e]]
    exact Ideal.subset_span (by simp)
  intro hI
  have hxzero : x = 0 := by
    have hxmem0 : x ∈ (0 : Ideal (𝓞 (Qsqrtd (d : ℚ)))) := by
      simpa [hI] using hxmem
    simpa using hxmem0
  have haZ : ((Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) = 0 := by
    have := congrArg e hxzero
    simpa [x, e] using this
  have ha0 : Q.1.a = 0 := by
    exact_mod_cast congrArg QuadraticAlgebra.re haZ
  exact (ne_of_gt Q.2.2.2.1) ha0

/-- The Cox ideal in the `d % 4 ≠ 1` branch as a nonzero ideal. -/
noncomputable def nonzeroIdealOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
  ⟨idealOfForm_of_mod_four_ne_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (idealOfForm_of_mod_four_ne_one_ne_zero d hd4 Q)⟩

/-- The Cox ideal in the `d % 4 = 1` branch as a nonzero ideal. -/
noncomputable def nonzeroIdealOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    nonZeroDivisors (Ideal (𝓞 (Qsqrtd (d : ℚ)))) :=
  ⟨idealOfForm_of_mod_four_eq_one d hd4 Q,
    mem_nonZeroDivisors_iff_ne_zero.mpr
      (idealOfForm_of_mod_four_eq_one_ne_zero d hd4 Q)⟩

/-- The ideal class attached to a single primitive positive definite form in the
`d % 4 ≠ 1` branch. This has not yet been descended to `FormClass`. -/
noncomputable def idealClassOfForm_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0 (nonzeroIdealOfForm_of_mod_four_ne_one d hd4 Q)

/-- The ideal class attached to a single primitive positive definite form in the
`d % 4 = 1` branch. This has not yet been descended to `FormClass`. -/
noncomputable def idealClassOfForm_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) :
    ClassGroup (𝓞 (Qsqrtd (d : ℚ))) :=
  ClassGroup.mk0 (nonzeroIdealOfForm_of_mod_four_eq_one d hd4 Q)

private theorem idealClassOfForm_of_mod_four_ne_one_eq_of_transform
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    idealClassOfForm_of_mod_four_ne_one d hd4 Q =
      idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4
  let lam : Zsqrtd d :=
    ((g 0 0 * Q.1.a : ℤ) : Zsqrtd d) -
      (g 1 0 : Zsqrtd d) * (⟨(-Q.1.b) / 2, 1⟩ : Zsqrtd d)
  let x : 𝓞 (Qsqrtd (d : ℚ)) := e.symm (((R.1.a : ℤ) : Zsqrtd d))
  let y : 𝓞 (Qsqrtd (d : ℚ)) := e.symm lam
  have hx : x ≠ 0 := by
    intro hx0
    have hxZ : (((R.1.a : ℤ) : Zsqrtd d)) = 0 := by
      have := congrArg e hx0
      simpa [x, e] using this
    have ha0 : R.1.a = 0 := by
      exact_mod_cast congrArg QuadraticAlgebra.re hxZ
    exact (ne_of_gt R.2.2.2.1) ha0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa using h
  have hlam : lam ≠ 0 :=
    cox_zsqrtd_lam_ne_zero (D := d) (A := Q.1.a) (p := g 0 0)
      (q := g 0 1) (r := g 1 0) (s := g 1 1) (u := (-Q.1.b) / 2)
      (ne_of_gt Q.2.2.2.1) hdet
  have hy : y ≠ 0 := by
    intro hy0
    apply hlam
    have := congrArg e hy0
    simpa [y, e] using this
  have hideal :=
    cox_ringOfIntegers_ideal_relation_transform_of_mod_four_ne_one d hd4 Q R g hR
  unfold idealClassOfForm_of_mod_four_ne_one
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [x, y, lam, nonzeroIdealOfForm_of_mod_four_ne_one] using hideal

private theorem idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) :
    idealClassOfForm_of_mod_four_ne_one d hd4 Q =
      idealClassOfForm_of_mod_four_ne_one d hd4 R := by
  rcases hQR with ⟨g, hg⟩
  exact idealClassOfForm_of_mod_four_ne_one_eq_of_transform d hd4 Q R g hg.symm

private theorem idealClassOfForm_of_mod_four_eq_one_eq_of_transform
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d)) (g : SL2Z)
    (hR : R.1 = transform Q.1 g) :
    idealClassOfForm_of_mod_four_eq_one d hd4 Q =
      idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  let e := RingOfIntegers.ringOfIntegers_equiv_zOnePlusSqrtOverTwo_of_mod_four_eq_one d hd4
  let lam : ZOnePlusSqrtdOverTwo (d / 4) :=
    ((g 0 0 * Q.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)) -
      (g 1 0 : ZOnePlusSqrtdOverTwo (d / 4)) *
        (⟨-(Q.1.b + 1) / 2, 1⟩ : ZOnePlusSqrtdOverTwo (d / 4))
  let x : 𝓞 (Qsqrtd (d : ℚ)) :=
    e.symm (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4)))
  let y : 𝓞 (Qsqrtd (d : ℚ)) := e.symm lam
  have hx : x ≠ 0 := by
    intro hx0
    have hxZ : (((R.1.a : ℤ) : ZOnePlusSqrtdOverTwo (d / 4))) = 0 := by
      have := congrArg e hx0
      simpa [x, e] using this
    have ha0 : R.1.a = 0 := by
      exact_mod_cast congrArg QuadraticAlgebra.re hxZ
    exact (ne_of_gt R.2.2.2.1) ha0
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := g.2
    rw [Matrix.det_fin_two] at h
    simpa using h
  have hlam : lam ≠ 0 :=
    cox_zomega_lam_ne_zero (k := d / 4) (A := Q.1.a) (p := g 0 0)
      (q := g 0 1) (r := g 1 0) (s := g 1 1) (u := -(Q.1.b + 1) / 2)
      (ne_of_gt Q.2.2.2.1) hdet
  have hy : y ≠ 0 := by
    intro hy0
    apply hlam
    have := congrArg e hy0
    simpa [y, e] using this
  have hideal :=
    cox_ringOfIntegers_ideal_relation_transform_of_mod_four_eq_one d hd4 Q R g hR
  unfold idealClassOfForm_of_mod_four_eq_one
  rw [ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa [x, y, lam, nonzeroIdealOfForm_of_mod_four_eq_one] using hideal

private theorem idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1)
    (Q R : PrimitivePositiveDefiniteForm (fieldDiscriminant d))
    (hQR : PrimitivePositiveDefiniteForm.ProperEquivalent Q R) :
    idealClassOfForm_of_mod_four_eq_one d hd4 Q =
      idealClassOfForm_of_mod_four_eq_one d hd4 R := by
  rcases hQR with ⟨g, hg⟩
  exact idealClassOfForm_of_mod_four_eq_one_eq_of_transform d hd4 Q R g hg.symm

/-- WIP map from form classes to ideal classes in the `d % 4 ≠ 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  exact Quotient.lift (idealClassOfForm_of_mod_four_ne_one d hd4)
    (idealClassOfForm_of_mod_four_ne_one_eq_of_properEquivalent d hd4)

/-- WIP map from form classes to ideal classes in the `d % 4 = 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  exact Quotient.lift (idealClassOfForm_of_mod_four_eq_one d hd4)
    (idealClassOfForm_of_mod_four_eq_one_eq_of_properEquivalent d hd4)

/-- WIP Cox map from primitive positive definite form classes to ideal classes,
dispatching between the two integer-ring models by the field discriminant
congruence. -/
noncomputable def formClassToClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  by_cases hd4 : d % 4 = 1
  · exact formClassToClassGroup_of_mod_four_eq_one d hd4
  · exact formClassToClassGroup_of_mod_four_ne_one d hd4

theorem formClassToClassGroup_eq_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    formClassToClassGroup d = formClassToClassGroup_of_mod_four_eq_one d hd4 := by
  simp [formClassToClassGroup, hd4]

theorem formClassToClassGroup_eq_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    formClassToClassGroup d = formClassToClassGroup_of_mod_four_ne_one d hd4 := by
  simp [formClassToClassGroup, hd4]

/-- WIP Cox 7.7 bijection for imaginary quadratic fields. -/
noncomputable def formClassEquivClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  sorry

end BinaryQuadraticForm
end QuadraticNumberFields
