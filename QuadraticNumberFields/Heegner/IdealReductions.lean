/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Mathlib.NumberTheory.Multiplicity
import QuadraticNumberFields.QuadraticField.Basic
import QuadraticNumberFields.RingOfIntegers.Norm

/-!
# Ideal-Theoretic Reductions for the Heegner Class-Number-One Problem

This file collects small ideal-first reductions used in the class-number-one
direction of the Baker--Heegner--Stark theorem.  The first reduction isolates
the elementary norm obstruction in the even-discriminant branch: in the
`d % 4 ≠ 1` integer-ring model, an algebraic integer of norm absolute value `2`
can occur only for `d = -1` or `d = -2`.
-/

open scoped NumberField

namespace QuadraticNumberFields
namespace Heegner

attribute [-instance] DivisionRing.toRatAlgebra

private theorem int_sq_ne_two (a : ℤ) : a ^ 2 ≠ 2 := by
  intro h
  rcases Int.even_or_odd a with ⟨k, hk⟩ | hodd
  · have hmod := congrArg (fun n : ℤ => n % 4) h
    have ha4 : a ^ 2 % 4 = 0 := by
      rw [hk]
      have hsq : (k + k) ^ 2 = 4 * k ^ 2 := by ring
      rw [hsq]
      simp
    omega
  · have hmod := congrArg (fun n : ℤ => n % 4) h
    have ha4 : a ^ 2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hodd
    omega

private theorem eq_neg_one_or_eq_neg_two_of_zsqrtd_norm_eq_two
    {d : ℤ} (hdneg : d < 0) {z : Zsqrtd d} (hnorm : Zsqrtd.norm z = 2) :
    d = -1 ∨ d = -2 := by
  have hcoord : z.re ^ 2 - d * z.im ^ 2 = 2 := by
    simpa [RingOfIntegers.norm_zsqrtd] using hnorm
  by_cases him : z.im = 0
  · have hre_sq : z.re ^ 2 = 2 := by
      simpa [him] using hcoord
    exact False.elim (int_sq_ne_two z.re hre_sq)
  · have him_sq_pos : 0 < z.im ^ 2 := sq_pos_of_ne_zero him
    have hnegd_le : -d ≤ 2 := by nlinarith [sq_nonneg z.re, him_sq_pos]
    omega

/-- In the `d % 4 ≠ 1` branch of an imaginary quadratic field, an algebraic integer
of norm absolute value `2` can exist only for `d = -1` or `d = -2`. -/
theorem eq_neg_one_or_eq_neg_two_of_exists_absNorm_eq_two
    (d : ℤ) [Fact (Squarefree d)] [Fact (d ≠ 1)] (hdneg : d < 0) (hd4 : d % 4 ≠ 1)
    (h : ∃ α : 𝓞 (Qsqrtd (d : ℚ)), (Algebra.norm ℤ α).natAbs = 2) :
    d = -1 ∨ d = -2 := by
  rcases h with ⟨α, hα⟩
  have hnorm_nonneg : 0 ≤ Algebra.norm ℤ α :=
    RingOfIntegers.algebraNorm_nonneg_of_neg d hdneg α
  have hnorm_eq_two : Algebra.norm ℤ α = 2 := by
    have hnat := Int.natAbs_of_nonneg hnorm_nonneg
    omega
  have hz_norm :
      Zsqrtd.norm
        (RingOfIntegers.ringOfIntegers_equiv_zsqrtd_of_mod_four_ne_one d hd4 α) = 2 := by
    rw [← RingOfIntegers.algebraNorm_eq_zsqrtd_norm_of_mod_four_ne_one d hd4 α]
    exact hnorm_eq_two
  exact eq_neg_one_or_eq_neg_two_of_zsqrtd_norm_eq_two hdneg hz_norm

end Heegner
end QuadraticNumberFields
