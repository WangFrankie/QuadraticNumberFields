/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.ClassNumber
import QuadraticNumberFields.ClassGroup.Forms.UpperHalfPlane
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

private theorem cox_zsqrtd_linear_relation {A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    p * A - r * u = s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v := by
  have hB : B = -2 * u := by omega
  have hv' := hv
  rw [hB] at hv'
  rw [hB]
  have hvr2 : 2 * (v * r) =
      2 * (-A * p * q * r + p * u * s * r + q * u * r * r - C * s * r * r) := by
    linear_combination r * hv'
  have hvr : v * r =
      -A * p * q * r + p * u * s * r + q * u * r * r - C * s * r * r := by
    omega
  calc
    p * A - r * u = A * p * (p * s - q * r) - u * r * (p * s - q * r) := by
      rw [hdet]
      ring
    _ = s * (A * p ^ 2 + (-2 * u) * p * r + C * r ^ 2) + r * v := by
      rw [show r * v = v * r by ring, hvr]
      ring

private theorem cox_zsqrtd_root_relation_re {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    (p * A - r * u) * v - D * r =
      (A * p ^ 2 + B * p * r + C * r ^ 2) * (s * u - q * A) := by
  have hB : B = -2 * u := by omega
  have hv_def : v = -A * p * q + u * (p * s + q * r) - C * r * s := by
    have hv' := hv
    rw [hB] at hv'
    ring_nf at hv' ⊢
    omega
  have hD : D = u ^ 2 - A * C := by
    have hdisc' := hdisc
    rw [hB] at hdisc'
    nlinarith
  rw [hB, hv_def, hD]
  have hzero :
      ((p * A - r * u) * (-A * p * q + u * (p * s + q * r) - C * r * s) -
          (u ^ 2 - A * C) * r) -
        ((A * p ^ 2 + (-2 * u) * p * r + C * r ^ 2) * (s * u - q * A)) = 0 := by
    calc
      ((p * A - r * u) * (-A * p * q + u * (p * s + q * r) - C * r * s) -
          (u ^ 2 - A * C) * r) -
        ((A * p ^ 2 + (-2 * u) * p * r + C * r ^ 2) * (s * u - q * A))
          = r * (u ^ 2 - A * C) * (p * s - q * r - 1) := by
            ring
      _ = 0 := by
        rw [hdet]
        ring
  nlinarith

private theorem cox_zsqrtd_norm_relation {D A B C p r u : ℤ}
    (hdisc : B ^ 2 - 4 * A * C = 4 * D) (hu : 2 * u = -B) :
    (p * A - r * u) ^ 2 - D * r ^ 2 =
      A * (A * p ^ 2 + B * p * r + C * r ^ 2) := by
  have hB : B = -2 * u := by omega
  have hD : D = u ^ 2 - A * C := by
    have hdisc' := hdisc
    rw [hB] at hdisc'
    nlinarith
  rw [hB, hD]
  ring

private theorem cox_zsqrtd_root_relation {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    (((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D)) *
        (⟨v, 1⟩ : Zsqrtd D) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D) *
        ((s : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D) -
          (q : Zsqrtd D) * (A : Zsqrtd D)) := by
  have hlin1 : p * A - r * u =
      s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v :=
    cox_zsqrtd_linear_relation hdet hu hv
  ext <;>
    simp only [QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast, zero_mul,
      mul_zero, add_zero]
  · simpa [mul_comm, mul_assoc, mul_left_comm] using
      cox_zsqrtd_root_relation_re hdet hdisc hu hv
  · have htarget : p * A - r * u - r * v =
        s * (A * p ^ 2 + B * p * r + C * r ^ 2) := by
      calc
        p * A - r * u - r * v =
            (s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v) - r * v := by
          rw [hlin1]
        _ = s * (A * p ^ 2 + B * p * r + C * r ^ 2) := by
          ring
    simpa [mul_comm, mul_assoc, mul_left_comm, sub_eq_add_neg] using htarget

private theorem cox_zsqrtd_conj_relation {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    (((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D)) *
        (((s * (A * p ^ 2 + B * p * r + C * r ^ 2) : ℤ) : Zsqrtd D) +
          (r : Zsqrtd D) * (⟨v, 1⟩ : Zsqrtd D)) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D) *
        (A : Zsqrtd D) := by
  have hlin1 : p * A - r * u =
      s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v :=
    cox_zsqrtd_linear_relation hdet hu hv
  have hnorm :=
    cox_zsqrtd_norm_relation (D := D) (A := A) (B := B) (C := C) (p := p)
      (r := r) (u := u) hdisc hu
  ext <;>
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast, zero_mul,
      mul_zero, add_zero, zero_add]
  · norm_num
    rw [← hlin1]
    nlinarith [hnorm]
  · norm_num
    rw [← hlin1]
    ring

private theorem cox_zsqrtd_beta_relation {D A B C p q r s u v : ℤ}
    (hdet : p * s - q * r = 1) (hdisc : B ^ 2 - 4 * A * C = 4 * D)
    (hu : 2 * u = -B)
    (hv : 2 * v = -(2 * A * p * q + B * (p * s + q * r) + 2 * C * r * s)) :
    (((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * (⟨u, 1⟩ : Zsqrtd D)) *
        ((p : Zsqrtd D) * (⟨v, 1⟩ : Zsqrtd D) +
          (q : Zsqrtd D) *
            ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D)) =
      ((A * p ^ 2 + B * p * r + C * r ^ 2 : ℤ) : Zsqrtd D) *
        (⟨u, 1⟩ : Zsqrtd D) := by
  have hlin1 : p * A - r * u =
      s * (A * p ^ 2 + B * p * r + C * r ^ 2) + r * v :=
    cox_zsqrtd_linear_relation hdet hu hv
  have hroot_re :=
    cox_zsqrtd_root_relation_re (D := D) (A := A) (B := B) (C := C)
      (p := p) (q := q) (r := r) (s := s) (u := u) (v := v)
      hdet hdisc hu hv
  ext <;>
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add,
      QuadraticAlgebra.re_sub, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_sub, QuadraticAlgebra.im_mul, QuadraticAlgebra.im_intCast, zero_mul,
      mul_zero, add_zero]
  · norm_num
    calc
      (p * A - r * u) * (p * v + q * (A * p ^ 2 + B * p * r + C * r ^ 2)) +
          -(D * r * p) =
          p * ((p * A - r * u) * v - D * r) +
            q * (A * p ^ 2 + B * p * r + C * r ^ 2) * (p * A - r * u) := by
        ring
      _ = p * ((A * p ^ 2 + B * p * r + C * r ^ 2) * (s * u - q * A)) +
            q * (A * p ^ 2 + B * p * r + C * r ^ 2) * (p * A - r * u) := by
        rw [hroot_re]
      _ = (A * p ^ 2 + B * p * r + C * r ^ 2) * u := by
        calc
          p * ((A * p ^ 2 + B * p * r + C * r ^ 2) * (s * u - q * A)) +
              q * (A * p ^ 2 + B * p * r + C * r ^ 2) * (p * A - r * u)
              =
            (A * p ^ 2 + B * p * r + C * r ^ 2) * (u * (p * s - q * r)) := by
            ring
          _ = (A * p ^ 2 + B * p * r + C * r ^ 2) * u := by
            rw [hdet]
            ring
  · norm_num
    calc
      (p * A - r * u) * p +
          -(r * (p * v + q * (A * p ^ 2 + B * p * r + C * r ^ 2))) =
          (p * s - q * r) * (A * p ^ 2 + B * p * r + C * r ^ 2) := by
        rw [hlin1]
        ring
      _ = A * p ^ 2 + B * p * r + C * r ^ 2 := by
        rw [hdet]
        ring

private theorem span_singleton_mul_span_pair_le {R : Type*} [CommRing R]
    {x a b : R} {K : Ideal R} (ha : x * a ∈ K) (hb : x * b ∈ K) :
    Ideal.span ({x} : Set R) * Ideal.span ({a, b} : Set R) ≤ K := by
  rw [Ideal.span_singleton_mul_le_iff]
  intro z hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
      rcases hy with rfl | rfl
      · exact ha
      · exact hb
  | zero => simp
  | add y z _ _ hy hz => simpa [mul_add] using K.add_mem hy hz
  | smul r y _ hy =>
      simpa [mul_assoc, mul_comm, mul_left_comm] using K.mul_mem_left r hy

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
          (⟨v, 1⟩ : Zsqrtd D)} : Set (Zsqrtd D)) := by
  let A' : ℤ := A * p ^ 2 + B * p * r + C * r ^ 2
  let α : Zsqrtd D := (A' : Zsqrtd D)
  let β : Zsqrtd D := ⟨u, 1⟩
  let β' : Zsqrtd D := ⟨v, 1⟩
  let lam : Zsqrtd D := ((p * A : ℤ) : Zsqrtd D) - (r : Zsqrtd D) * β
  let I : Ideal (Zsqrtd D) := Ideal.span ({(A : Zsqrtd D), β} : Set (Zsqrtd D))
  let J : Ideal (Zsqrtd D) := Ideal.span ({α, β'} : Set (Zsqrtd D))
  change Ideal.span ({α} : Set (Zsqrtd D)) * I =
    Ideal.span ({lam} : Set (Zsqrtd D)) * J
  have hroot : lam * β' = α * ((s : Zsqrtd D) * β - (q : Zsqrtd D) * (A : Zsqrtd D)) := by
    simpa [A', α, β, β', lam] using
      cox_zsqrtd_root_relation (D := D) (A := A) (B := B) (C := C)
        (p := p) (q := q) (r := r) (s := s) (u := u) (v := v)
        hdet hdisc hu hv
  have hconj :
      lam * (((s * A' : ℤ) : Zsqrtd D) + (r : Zsqrtd D) * β') =
        α * (A : Zsqrtd D) := by
    simpa [A', α, β, β', lam] using
      cox_zsqrtd_conj_relation (D := D) (A := A) (B := B) (C := C)
        (p := p) (q := q) (r := r) (s := s) (u := u) (v := v)
        hdet hdisc hu hv
  have hbeta : lam * ((p : Zsqrtd D) * β' + (q : Zsqrtd D) * α) = α * β := by
    simpa [A', α, β, β', lam] using
      cox_zsqrtd_beta_relation (D := D) (A := A) (B := B) (C := C)
        (p := p) (q := q) (r := r) (s := s) (u := u) (v := v)
        hdet hdisc hu hv
  have hA_mem_I : (A : Zsqrtd D) ∈ I := Ideal.subset_span (by simp)
  have hβ_mem_I : β ∈ I := Ideal.subset_span (by simp)
  have hα_mem_J : α ∈ J := Ideal.subset_span (by simp)
  have hβ'_mem_J : β' ∈ J := Ideal.subset_span (by simp)
  have hlam_mem_I : lam ∈ I := by
    have hpA_mem_I : ((p * A : ℤ) : Zsqrtd D) ∈ I := by
      simpa using I.mul_mem_left (p : Zsqrtd D) hA_mem_I
    exact I.sub_mem hpA_mem_I (I.mul_mem_left (r : Zsqrtd D) hβ_mem_I)
  have hsα_add_rβ'_mem_J :
      ((s * A' : ℤ) : Zsqrtd D) + (r : Zsqrtd D) * β' ∈ J := by
    have hsα_mem_J : ((s * A' : ℤ) : Zsqrtd D) ∈ J := by
      simpa [A', α] using J.mul_mem_left (s : Zsqrtd D) hα_mem_J
    exact J.add_mem hsα_mem_J (J.mul_mem_left (r : Zsqrtd D) hβ'_mem_J)
  have hpβ'_add_qα_mem_J : (p : Zsqrtd D) * β' + (q : Zsqrtd D) * α ∈ J :=
    J.add_mem (J.mul_mem_left (p : Zsqrtd D) hβ'_mem_J)
      (J.mul_mem_left (q : Zsqrtd D) hα_mem_J)
  have hsβ_sub_qA_mem_I : (s : Zsqrtd D) * β - (q : Zsqrtd D) * (A : Zsqrtd D) ∈ I :=
    I.sub_mem (I.mul_mem_left (s : Zsqrtd D) hβ_mem_I)
      (I.mul_mem_left (q : Zsqrtd D) hA_mem_I)
  apply le_antisymm
  · apply span_singleton_mul_span_pair_le
    · rw [← hconj]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [lam])) hsα_add_rβ'_mem_J
    · rw [← hbeta]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [lam])) hpβ'_add_qα_mem_J
  · apply span_singleton_mul_span_pair_le
    · have hα_mem_left : α * lam ∈ Ideal.span ({α} : Set (Zsqrtd D)) * I :=
        Ideal.mul_mem_mul (Ideal.subset_span (by simp [α])) hlam_mem_I
      simpa [mul_comm] using hα_mem_left
    · rw [hroot]
      exact Ideal.mul_mem_mul (Ideal.subset_span (by simp [α])) hsβ_sub_qA_mem_I

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

/-- WIP map from form classes to ideal classes in the `d % 4 ≠ 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_ne_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 ≠ 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  intro Q
  classical
  sorry

/-- WIP map from form classes to ideal classes in the `d % 4 = 1` branch. -/
noncomputable def formClassToClassGroup_of_mod_four_eq_one
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hd4 : d % 4 = 1) :
    FormClass (fieldDiscriminant d) → ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  intro Q
  classical
  sorry

/-- WIP Cox 7.7 bijection for imaginary quadratic fields. -/
noncomputable def formClassEquivClassGroup
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) :
    FormClass (fieldDiscriminant d) ≃ ClassGroup (𝓞 (Qsqrtd (d : ℚ))) := by
  classical
  sorry

end BinaryQuadraticForm
end QuadraticNumberFields
