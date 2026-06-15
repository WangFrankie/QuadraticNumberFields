/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gauss Composition of Binary Quadratic Forms

This file starts the explicit Gauss composition API for the project-owned
integer-triple model of binary quadratic forms.

The first layer is the classical concordant-form composition formula.  Full
composition on proper equivalence classes will additionally need the reduction
of arbitrary same-discriminant representatives to concordant representatives
and a proof that the resulting class is independent of choices.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Elementary composition data -/

/-- The absolute gcd of three integer coefficients. -/
def coeffGCD3 (x y z : ℤ) : ℕ :=
  Nat.gcd x.natAbs (Nat.gcd y.natAbs z.natAbs)

/-- The half-sum of the two middle coefficients used in Gauss's united-form
condition.  The value is meaningful for composition once the two middle
coefficients have the same parity. -/
def sigma (Q R : BinaryQuadraticForm) : ℤ :=
  (Q.b + R.b) / 2

/-- Gauss's united condition for two same-discriminant forms, expressed in the
integer-triple model. -/
def IsUnited (Q R : BinaryQuadraticForm) : Prop :=
  Q.disc = R.disc ∧ coeffGCD3 Q.a R.a (sigma Q R) = 1

/-- Concordant forms are the already-aligned representatives on which the
elementary Gauss composition formula is direct. -/
def IsConcordant (Q R : BinaryQuadraticForm) : Prop :=
  Q.disc = R.disc ∧ Q.b = R.b ∧ Int.gcd Q.a R.a = 1

/-- The direct Gauss composition formula for concordant representatives.

For concordant primitive forms the denominator divides the numerator; the
definition is total by integer division so that divisibility hypotheses can be
carried by theorems rather than by the data structure. -/
def composeConcordant (Q R : BinaryQuadraticForm) : BinaryQuadraticForm where
  a := Q.a * R.a
  b := Q.b
  c := (Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a)

@[simp] theorem composeConcordant_a (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).a = Q.a * R.a :=
  rfl

@[simp] theorem composeConcordant_b (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).b = Q.b :=
  rfl

@[simp] theorem composeConcordant_c (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).c = (Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a) :=
  rfl

/-- If the integer division in the concordant formula is exact, the composed
form has the same discriminant as the left factor. -/
theorem disc_composeConcordant_of_eq_mul (Q R : BinaryQuadraticForm) {c : ℤ}
    (hden : 4 * Q.a * R.a ≠ 0)
    (hc : Q.b ^ 2 - Q.disc = (4 * Q.a * R.a) * c) :
    (composeConcordant Q R).disc = Q.disc := by
  have hcdiv :
      (Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a) = c := by
    rw [hc]
    exact Int.mul_ediv_cancel_left c hden
  rw [show (composeConcordant Q R).disc =
      Q.b ^ 2 - 4 * (Q.a * R.a) *
        ((Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a)) by rfl]
  rw [hcdiv]
  nlinarith [hc]

/-! ## Sanity checks -/

example :
    (BinaryQuadraticForm.mk 1 0 1).IsUnited (BinaryQuadraticForm.mk 1 0 1) := by
  norm_num [IsUnited, sigma, coeffGCD3]

example :
    composeConcordant (BinaryQuadraticForm.mk 1 0 1) (BinaryQuadraticForm.mk 1 0 1) =
      BinaryQuadraticForm.mk 1 0 1 := by
  norm_num [composeConcordant, disc]

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).disc = -4 := by
  exact disc_composeConcordant_of_eq_mul
    (BinaryQuadraticForm.mk 1 0 1) (BinaryQuadraticForm.mk 1 0 1) (c := 1)
    (by norm_num) (by norm_num [disc])

end BinaryQuadraticForm
end QuadraticNumberFields
