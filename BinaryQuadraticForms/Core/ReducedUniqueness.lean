/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.UpperHalfPlane

/-!
# Uniqueness of Reduced Representatives

This module proves the Gauss-reduction half of the Cox 7.7 bridge: every
positive definite binary quadratic form is properly equivalent to a reduced
form (`exists_isReduced_properEquivalent`), and the boundary-normalized reduced
representative of a proper-equivalence class is unique
(`eq_of_isReduced_of_properEquivalent`).

The argument runs through the upper-half-plane root `tauOfForm`: reduction is the
statement that the root lies in the modular fundamental domain `ModularGroup.fd`,
and uniqueness is a case analysis on the `SL₂(ℤ)` elements that fix the
fundamental domain (the identity, `S`, `T`, and the stabilizers of `ρ`).

These results are consumed by `Forms.Core.ClassReduced` and the Cox bridge to
choose reduced representatives of `FormClass`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-- Gauss reduction existence statement for positive definite forms. -/
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

/-- Uniqueness statement for boundary-normalized reduced representatives. -/
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

end BinaryQuadraticForm
end QuadraticNumberFields
