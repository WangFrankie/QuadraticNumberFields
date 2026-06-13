/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.ClassGroup.Forms.Action
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

example : (BinaryQuadraticForm.mk 1 0 1).IsReduced := by
  norm_num [IsReduced]

example : (BinaryQuadraticForm.mk 1 1 1).IsReduced := by
  norm_num [IsReduced]

example : ¬ (BinaryQuadraticForm.mk 1 (-1) 1).IsReduced := by
  intro h
  rcases h with ⟨_, _, hb, _⟩
  have : (|-1| : ℤ) = 1 := by norm_num
  have hnonneg := hb this
  norm_num at hnonneg

end BinaryQuadraticForm
end QuadraticNumberFields
