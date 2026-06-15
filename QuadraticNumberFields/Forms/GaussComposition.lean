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

/-- Concordant forms with equal discriminants and equal middle coefficient
satisfy `a c = a' c'`. -/
theorem mul_c_eq_mul_c_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : Q.a * Q.c = R.a * R.c := by
  rcases h with ⟨hdisc, hb, _⟩
  simp [disc, hb] at hdisc
  nlinarith

/-- For concordant forms, the right leading coefficient divides the left
trailing coefficient. -/
theorem right_a_dvd_left_c_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : R.a ∣ Q.c := by
  have hprod := mul_c_eq_mul_c_of_isConcordant h
  have hdiv : R.a ∣ Q.a * Q.c := by
    rw [hprod]
    exact dvd_mul_right R.a R.c
  have hgcd : Int.gcd R.a Q.a = 1 := by
    simpa [Int.gcd, Nat.gcd_comm] using h.2.2
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv hgcd

/-- For concordant forms, the left leading coefficient divides the right
trailing coefficient. -/
theorem left_a_dvd_right_c_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : Q.a ∣ R.c := by
  have hprod := mul_c_eq_mul_c_of_isConcordant h
  have hdiv : Q.a ∣ R.a * R.c := by
    rw [← hprod]
    exact dvd_mul_right Q.a Q.c
  exact Int.dvd_of_dvd_mul_right_of_gcd_one hdiv h.2.2

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

/-- Concordant forms with nonzero leading coefficients compose to a form with
the same discriminant. -/
theorem disc_composeConcordant_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) (hQa : Q.a ≠ 0) (hRa : R.a ≠ 0) :
    (composeConcordant Q R).disc = Q.disc := by
  apply disc_composeConcordant_of_eq_mul Q R (c := Q.c / R.a)
  · exact mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hQa) hRa
  · have hRdvd : R.a ∣ Q.c := right_a_dvd_left_c_of_isConcordant h
    have hQcediv : Q.c / R.a * R.a = Q.c := Int.ediv_mul_cancel hRdvd
    have hdiscQ : Q.b ^ 2 - Q.disc = 4 * Q.a * Q.c := by
      simp [disc]
    calc
      Q.b ^ 2 - Q.disc = 4 * Q.a * Q.c := hdiscQ
      _ = 4 * Q.a * (Q.c / R.a * R.a) := by rw [hQcediv]
      _ = (4 * Q.a * R.a) * (Q.c / R.a) := by ring

/-- Concordant composition preserves a prescribed discriminant when both
leading coefficients are nonzero. -/
theorem hasDiscriminant_composeConcordant_of_isConcordant
    {Q R : BinaryQuadraticForm} {D : ℤ}
    (hQD : Q.HasDiscriminant D) (h : Q.IsConcordant R)
    (hQa : Q.a ≠ 0) (hRa : R.a ≠ 0) :
    (composeConcordant Q R).HasDiscriminant D := by
  unfold HasDiscriminant at hQD ⊢
  rw [disc_composeConcordant_of_isConcordant h hQa hRa, hQD]

/-- Concordant composition preserves positive definiteness. -/
theorem isPositiveDefinite_composeConcordant_of_isConcordant
    {Q R : BinaryQuadraticForm} (h : Q.IsConcordant R)
    (hQ : Q.IsPositiveDefinite) (hR : R.IsPositiveDefinite) :
    (composeConcordant Q R).IsPositiveDefinite := by
  constructor
  · exact mul_pos hQ.1 hR.1
  · rw [disc_composeConcordant_of_isConcordant h (ne_of_gt hQ.1) (ne_of_gt hR.1)]
    exact hQ.2

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

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).disc = -4 := by
  exact disc_composeConcordant_of_isConcordant
    (Q := BinaryQuadraticForm.mk 1 0 1) (R := BinaryQuadraticForm.mk 1 0 1)
    (by norm_num [IsConcordant, disc]) (by norm_num) (by norm_num)

example :
    (composeConcordant (BinaryQuadraticForm.mk 1 0 1)
      (BinaryQuadraticForm.mk 1 0 1)).IsPositiveDefinite := by
  exact isPositiveDefinite_composeConcordant_of_isConcordant
    (Q := BinaryQuadraticForm.mk 1 0 1) (R := BinaryQuadraticForm.mk 1 0 1)
    (by norm_num [IsConcordant, disc])
    (by norm_num [IsPositiveDefinite, disc])
    (by norm_num [IsPositiveDefinite, disc])

end BinaryQuadraticForm
end QuadraticNumberFields
