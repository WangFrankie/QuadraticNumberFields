/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Action
import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.NormNum

/-!
# Reduced Binary Quadratic Forms

This file defines the reduced predicate for positive definite binary quadratic
forms in triple coordinates.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-- Boundary-normalized Gauss reduction predicate for positive definite forms. -/
def IsReduced (Q : BinaryQuadraticForm) : Prop :=
  |Q.b| ≤ Q.a ∧ Q.a ≤ Q.c ∧
    (|Q.b| = Q.a → 0 ≤ Q.b) ∧
    (Q.a = Q.c → 0 ≤ Q.b)

theorem isReduced_mk_iff (a b c : ℤ) :
    IsReduced (BinaryQuadraticForm.mk a b c) ↔
      |b| ≤ a ∧ a ≤ c ∧ (|b| = a → 0 ≤ b) ∧ (a = c → 0 ≤ b) :=
  Iff.rfl

/-- A reduced positive definite form satisfies the standard discriminant bound
`3a² ≤ -D`. This is the arithmetic core of the finite reduced-form search. -/
theorem three_mul_a_sq_le_neg_disc_of_isReduced (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    3 * Q.a ^ 2 ≤ -Q.disc := by
  rcases Q with ⟨a, b, c⟩
  rcases hpos with ⟨ha, hdisc⟩
  rcases hred with ⟨hb_le_a, ha_le_c, _, _⟩
  change |b| ≤ a at hb_le_a
  change a ≤ c at ha_le_c
  simp only [disc_mk] at hdisc ⊢
  have hb_sq_le : b ^ 2 ≤ a ^ 2 := by
    have hb_abs_le_abs_a : |b| ≤ |a| := by
      simpa [abs_of_pos ha] using hb_le_a
    exact sq_le_sq.mpr hb_abs_le_abs_a
  have ha_mul_le : a * a ≤ a * c :=
    mul_le_mul_of_nonneg_left ha_le_c (le_of_lt ha)
  nlinarith

/-- Nat-valued version of `three_mul_a_sq_le_neg_disc_of_isReduced`, phrased
for the eventual `Nat.sqrt D.natAbs + 1` search bound. -/
theorem three_mul_a_natAbs_sq_le_disc_natAbs (Q : BinaryQuadraticForm)
    (hpos : Q.IsPositiveDefinite) (hred : Q.IsReduced) :
    3 * Q.a.natAbs ^ 2 ≤ Q.disc.natAbs := by
  have hbound := three_mul_a_sq_le_neg_disc_of_isReduced Q hpos hred
  have hdisc_nonpos : Q.disc ≤ 0 := le_of_lt hpos.2
  have ha_nonneg : 0 ≤ Q.a := le_of_lt hpos.1
  have hcast : ((3 * Q.a.natAbs ^ 2 : ℕ) : ℤ) ≤ (Q.disc.natAbs : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
    rw [Int.natAbs_of_nonneg ha_nonneg]
    rw [Int.ofNat_natAbs_of_nonpos hdisc_nonpos]
    exact hbound
  exact_mod_cast hcast

example : (BinaryQuadraticForm.mk 1 0 1).IsReduced := by
  norm_num [IsReduced]

example : (BinaryQuadraticForm.mk 1 1 1).IsReduced := by
  norm_num [IsReduced]

example : ¬ (BinaryQuadraticForm.mk 1 (-1) 1).IsReduced := by
  norm_num [IsReduced]

end BinaryQuadraticForm
end QuadraticNumberFields
