/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Core.Action
import QuadraticNumberFields.Forms.Core.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.PrimeFin
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

/-- Bézout data attached to a united pair of binary quadratic forms. -/
structure UnitedBezout (Q R : BinaryQuadraticForm) where
  /-- Coefficient of the left leading coefficient. -/
  u : ℤ
  /-- Coefficient of the right leading coefficient. -/
  v : ℤ
  /-- Coefficient of the half-sum `sigma Q R`. -/
  w : ℤ
  /-- The Bézout identity certifying the united condition. -/
  linear_combination : u * Q.a + v * R.a + w * sigma Q R = 1

/-- A united pair admits three-term Bézout coefficients
`u * a + v * a' + w * sigma = 1`. -/
theorem exists_unitedBezout_of_isUnited {Q R : BinaryQuadraticForm}
    (h : Q.IsUnited R) : Nonempty (UnitedBezout Q R) := by
  let g : ℕ := Int.gcd R.a (sigma Q R)
  have hgcd : Int.gcd Q.a g = 1 := by
    simpa [IsUnited, coeffGCD3, g, Int.gcd] using h.2
  have hbezout_left : (1 : ℤ) = Q.a * Int.gcdA Q.a g + (g : ℤ) * Int.gcdB Q.a g := by
    rw [← Int.gcd_eq_gcd_ab Q.a g, hgcd]
    norm_num
  have hbezout_right :
      (g : ℤ) = R.a * Int.gcdA R.a (sigma Q R) +
        sigma Q R * Int.gcdB R.a (sigma Q R) := by
    exact Int.gcd_eq_gcd_ab R.a (sigma Q R)
  refine ⟨⟨Int.gcdA Q.a g,
    Int.gcdB Q.a g * Int.gcdA R.a (sigma Q R),
    Int.gcdB Q.a g * Int.gcdB R.a (sigma Q R), ?_⟩⟩
  calc
    Int.gcdA Q.a g * Q.a +
        (Int.gcdB Q.a g * Int.gcdA R.a (sigma Q R)) * R.a +
        (Int.gcdB Q.a g * Int.gcdB R.a (sigma Q R)) * sigma Q R
        = Q.a * Int.gcdA Q.a g + (g : ℤ) * Int.gcdB Q.a g := by
          rw [hbezout_right]
          ring
    _ = 1 := hbezout_left.symm

namespace UnitedBezout

/-- A noncomputable choice of Bézout data attached to a proof that two forms are
united. -/
noncomputable def ofIsUnited {Q R : BinaryQuadraticForm} (h : Q.IsUnited R) :
    UnitedBezout Q R :=
  Classical.choice (exists_unitedBezout_of_isUnited h)

end UnitedBezout

/-- Concordant forms are the already-aligned representatives on which the
elementary Gauss composition formula is direct. -/
def IsConcordant (Q R : BinaryQuadraticForm) : Prop :=
  Q.disc = R.disc ∧ Q.b = R.b ∧ Int.gcd Q.a R.a = 1

/-- If two forms have the same middle coefficient, their Gauss `sigma` is that
middle coefficient. -/
theorem sigma_eq_left_b_of_b_eq {Q R : BinaryQuadraticForm} (h : Q.b = R.b) :
    sigma Q R = Q.b := by
  unfold sigma
  rw [← h]
  rw [show Q.b + Q.b = 2 * Q.b by ring]
  exact Int.mul_ediv_cancel_left Q.b (by norm_num : (2 : ℤ) ≠ 0)

/-- Concordance is symmetric. -/
theorem IsConcordant.symm {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : R.IsConcordant Q := by
  rcases h with ⟨hdisc, hb, hgcd⟩
  refine ⟨hdisc.symm, hb.symm, ?_⟩
  simpa [Int.gcd, Nat.gcd_comm] using hgcd

/-- Concordant forms are united. -/
theorem IsConcordant.isUnited {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : Q.IsUnited R := by
  refine ⟨h.1, ?_⟩
  have hsigma : sigma Q R = Q.b := sigma_eq_left_b_of_b_eq h.2.1
  have hgcd : Nat.gcd Q.a.natAbs R.a.natAbs = 1 := by
    simpa [Int.gcd] using h.2.2
  unfold coeffGCD3
  rw [hsigma]
  apply Nat.dvd_one.mp
  rw [← hgcd]
  exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
    (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))

/-- Concordant forms have united Bézout data with zero coefficient on
`sigma`. -/
theorem exists_unitedBezout_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) : Nonempty (UnitedBezout Q R) := by
  have hbezout : (1 : ℤ) = Q.a * Int.gcdA Q.a R.a + R.a * Int.gcdB Q.a R.a := by
    rw [← Int.gcd_eq_gcd_ab Q.a R.a, h.2.2]
    norm_num
  refine ⟨⟨Int.gcdA Q.a R.a, Int.gcdB Q.a R.a, 0, ?_⟩⟩
  calc
    Int.gcdA Q.a R.a * Q.a + Int.gcdB Q.a R.a * R.a + 0 * sigma Q R
        = Q.a * Int.gcdA Q.a R.a + R.a * Int.gcdB Q.a R.a := by ring
    _ = 1 := hbezout.symm

/-- The direct Gauss composition formula for concordant representatives.

For concordant primitive forms the denominator divides the numerator; the
definition is total by integer division so that divisibility hypotheses can be
carried by theorems rather than by the data structure. -/
def composeConcordant (Q R : BinaryQuadraticForm) : BinaryQuadraticForm where
  a := Q.a * R.a
  b := Q.b
  c := (Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a)

/-- The direct Gauss composition formula for united representatives equipped
with explicit Bézout data.  The middle coefficient is the classical
`B = b + 2a(v(sigma-b) - w c)` choice before reduction modulo `2aa'`; the final
coefficient is again made total by integer division. -/
def composeUnited (Q R : BinaryQuadraticForm) (bezout : UnitedBezout Q R) :
    BinaryQuadraticForm where
  a := Q.a * R.a
  b := Q.b + 2 * Q.a * (bezout.v * (sigma Q R - Q.b) - bezout.w * Q.c)
  c := ((Q.b + 2 * Q.a * (bezout.v * (sigma Q R - Q.b) - bezout.w * Q.c)) ^ 2 -
    Q.disc) / (4 * (Q.a * R.a))

/-- The direct united-composition formula, choosing Bézout data from an
`IsUnited` proof. -/
noncomputable def composeUnitedOfIsUnited
    (Q R : BinaryQuadraticForm) (h : Q.IsUnited R) : BinaryQuadraticForm :=
  composeUnited Q R (UnitedBezout.ofIsUnited h)

@[simp] theorem composeConcordant_a (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).a = Q.a * R.a :=
  rfl

@[simp] theorem composeConcordant_b (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).b = Q.b :=
  rfl

@[simp] theorem composeConcordant_c (Q R : BinaryQuadraticForm) :
    (composeConcordant Q R).c = (Q.b ^ 2 - Q.disc) / (4 * Q.a * R.a) :=
  rfl

@[simp] theorem composeUnited_a (Q R : BinaryQuadraticForm)
    (bezout : UnitedBezout Q R) :
    (composeUnited Q R bezout).a = Q.a * R.a :=
  rfl

@[simp] theorem composeUnited_b (Q R : BinaryQuadraticForm)
    (bezout : UnitedBezout Q R) :
    (composeUnited Q R bezout).b =
      Q.b + 2 * Q.a * (bezout.v * (sigma Q R - Q.b) - bezout.w * Q.c) :=
  rfl

@[simp] theorem composeUnited_c (Q R : BinaryQuadraticForm)
    (bezout : UnitedBezout Q R) :
    (composeUnited Q R bezout).c =
      ((Q.b + 2 * Q.a * (bezout.v * (sigma Q R - Q.b) - bezout.w * Q.c)) ^ 2 -
        Q.disc) / (4 * (Q.a * R.a)) :=
  rfl

@[simp] theorem composeUnitedOfIsUnited_a (Q R : BinaryQuadraticForm)
    (h : Q.IsUnited R) :
    (composeUnitedOfIsUnited Q R h).a = Q.a * R.a :=
  rfl

/-- The united formula recovers the concordant formula when the middle
coefficients are aligned and the chosen Bézout data has zero `sigma`
coefficient. -/
theorem composeUnited_eq_composeConcordant_of_sigma_eq_b_of_w_eq_zero
    {Q R : BinaryQuadraticForm} {bezout : UnitedBezout Q R}
    (hsigma : sigma Q R = Q.b) (hw : bezout.w = 0) :
    composeUnited Q R bezout = composeConcordant Q R := by
  ext
  · rfl
  · simp only [composeUnited_b, composeConcordant_b, hsigma, hw, sub_self, mul_zero,
      zero_mul, add_zero]
  · simp only [composeUnited_c, composeConcordant_c, hsigma, hw, sub_self, mul_zero,
      zero_mul, add_zero]
    exact congrArg (fun n => (Q.b ^ 2 - Q.disc) / n)
      (show 4 * (Q.a * R.a) = 4 * Q.a * R.a by ring)

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

/-- For concordant forms with nonzero leading coefficients, the final
coefficient in the direct composition formula is `c / a'`. -/
theorem composeConcordant_c_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) (hQa : Q.a ≠ 0) (hRa : R.a ≠ 0) :
    (composeConcordant Q R).c = Q.c / R.a := by
  have hden : 4 * Q.a * R.a ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hQa) hRa
  have hRdvd : R.a ∣ Q.c := right_a_dvd_left_c_of_isConcordant h
  have hQcediv : Q.c / R.a * R.a = Q.c := Int.ediv_mul_cancel hRdvd
  have hdiscQ : Q.b ^ 2 - Q.disc = 4 * Q.a * Q.c := by
    simp [disc]
  have hnum : Q.b ^ 2 - Q.disc = (4 * Q.a * R.a) * (Q.c / R.a) := by
    calc
      Q.b ^ 2 - Q.disc = 4 * Q.a * Q.c := hdiscQ
      _ = 4 * Q.a * (Q.c / R.a * R.a) := by rw [hQcediv]
      _ = (4 * Q.a * R.a) * (Q.c / R.a) := by ring
  rw [composeConcordant_c, hnum]
  exact Int.mul_ediv_cancel_left (Q.c / R.a) hden

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

/-- Concordant composition is symmetric at the representative-formula level. -/
theorem composeConcordant_comm_of_isConcordant {Q R : BinaryQuadraticForm}
    (h : Q.IsConcordant R) :
    composeConcordant Q R = composeConcordant R Q := by
  ext <;> simp [composeConcordant, h.1, h.2.1, mul_comm, mul_left_comm]

/-- A representative with leading coefficient `1` and the same middle
coefficient as `Q`, concordant to `Q`.  This is the representative-level unit
for the direct concordant composition formula attached to `Q`; identifying it
with the canonical principal form is a separate proper-equivalence statement. -/
def concordantUnitRepresentative (Q : BinaryQuadraticForm) : BinaryQuadraticForm where
  a := 1
  b := Q.b
  c := Q.a * Q.c

/-- The attached unit representative is concordant to the original form. -/
theorem concordantUnitRepresentative_isConcordant (Q : BinaryQuadraticForm) :
    (concordantUnitRepresentative Q).IsConcordant Q := by
  refine ⟨?_, rfl, ?_⟩
  · simp [concordantUnitRepresentative, disc]
    ring
  · simp [concordantUnitRepresentative, Int.gcd]

/-- The attached unit representative is a left identity for direct concordant
composition. -/
theorem composeConcordant_concordantUnitRepresentative (Q : BinaryQuadraticForm)
    (hQa : Q.a ≠ 0) :
    composeConcordant (concordantUnitRepresentative Q) Q = Q := by
  ext
  · change 1 * Q.a = Q.a
    ring
  · change Q.b = Q.b
    rfl
  · simp only [composeConcordant_c, concordantUnitRepresentative, disc]
    rw [show Q.b ^ 2 - (Q.b ^ 2 - 4 * 1 * (Q.a * Q.c)) =
        (4 * Q.a) * Q.c by ring]
    rw [show 4 * 1 * Q.a = 4 * Q.a by ring]
    exact Int.mul_ediv_cancel_left Q.c
      (mul_ne_zero (by norm_num : (4 : ℤ) ≠ 0) hQa)

/-- The attached unit representative is a right identity for direct concordant
composition. -/
theorem composeConcordant_concordantUnitRepresentative_right (Q : BinaryQuadraticForm)
    (hQa : Q.a ≠ 0) :
    composeConcordant Q (concordantUnitRepresentative Q) = Q := by
  rw [composeConcordant_comm_of_isConcordant
    (concordantUnitRepresentative_isConcordant Q).symm]
  exact composeConcordant_concordantUnitRepresentative Q hQa

/-- Primitive forms have no prime common divisor of all three coefficients. -/
theorem not_prime_dvd_coefficients_of_isPrimitive {Q : BinaryQuadraticForm}
    (hQ : Q.IsPrimitive) {p : ℕ} (hp : Nat.Prime p)
    (ha : (p : ℤ) ∣ Q.a) (hb : (p : ℤ) ∣ Q.b) (hc : (p : ℤ) ∣ Q.c) :
    False := by
  unfold IsPrimitive at hQ
  have hbc : p ∣ Int.gcd Q.b Q.c := Int.dvd_gcd hb hc
  have hgcd : p ∣ Int.gcd Q.a (Int.gcd Q.b Q.c) :=
    Int.dvd_gcd ha (by exact_mod_cast hbc)
  rw [hQ] at hgcd
  exact hp.not_dvd_one hgcd

/-- Concordant composition preserves primitivity. -/
theorem isPrimitive_composeConcordant_of_isConcordant
    {Q R : BinaryQuadraticForm} (h : Q.IsConcordant R)
    (hQ : Q.IsPrimitive) (hR : R.IsPrimitive) (hQa : Q.a ≠ 0) (hRa : R.a ≠ 0) :
    (composeConcordant Q R).IsPrimitive := by
  unfold IsPrimitive
  let S := composeConcordant Q R
  let n : ℕ := Int.gcd S.a (Int.gcd S.b S.c)
  change n = 1
  by_contra hn
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
  have hpz_dvd_n : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
  have hn_a : (n : ℤ) ∣ S.a := Int.gcd_dvd_left _ _
  have hn_bc : (n : ℤ) ∣ Int.gcd S.b S.c := Int.gcd_dvd_right _ _
  have hn_b : (n : ℤ) ∣ S.b := dvd_trans hn_bc (Int.gcd_dvd_left _ _)
  have hn_c : (n : ℤ) ∣ S.c := dvd_trans hn_bc (Int.gcd_dvd_right _ _)
  have hpS_a : (p : ℤ) ∣ S.a := dvd_trans hpz_dvd_n hn_a
  have hpS_b : (p : ℤ) ∣ S.b := dvd_trans hpz_dvd_n hn_b
  have hpS_c : (p : ℤ) ∣ S.c := dvd_trans hpz_dvd_n hn_c
  have hpQaRa : (p : ℤ) ∣ Q.a * R.a := by
    simpa [S, composeConcordant] using hpS_a
  have hpQb : (p : ℤ) ∣ Q.b := by
    simpa [S, composeConcordant] using hpS_b
  have hpC : (p : ℤ) ∣ Q.c / R.a := by
    have hSc : S.c = Q.c / R.a := composeConcordant_c_of_isConcordant h hQa hRa
    rwa [hSc] at hpS_c
  have hRdvd : R.a ∣ Q.c := right_a_dvd_left_c_of_isConcordant h
  have hQcediv : Q.c / R.a * R.a = Q.c := Int.ediv_mul_cancel hRdvd
  have hpQc : (p : ℤ) ∣ Q.c := by
    rw [← hQcediv]
    exact dvd_mul_of_dvd_left hpC R.a
  have hprod := mul_c_eq_mul_c_of_isConcordant h
  have hRceq : Q.a * (Q.c / R.a) = R.c := by
    have hcancel :
        R.a * (Q.a * (Q.c / R.a)) = R.a * R.c := by
      calc
        R.a * (Q.a * (Q.c / R.a)) = Q.a * (Q.c / R.a * R.a) := by ring
        _ = Q.a * Q.c := by rw [hQcediv]
        _ = R.a * R.c := hprod
    exact mul_left_cancel₀ hRa hcancel
  have hpRc : (p : ℤ) ∣ R.c := by
    rw [← hRceq]
    exact dvd_mul_of_dvd_right hpC Q.a
  have hpQaRa_nat : p ∣ (Q.a * R.a).natAbs := (Int.natCast_dvd).mp hpQaRa
  rw [Int.natAbs_mul] at hpQaRa_nat
  rcases (Nat.Prime.dvd_mul hp).mp hpQaRa_nat with hpQa_nat | hpRa_nat
  · have hpQa : (p : ℤ) ∣ Q.a := (Int.natCast_dvd).mpr hpQa_nat
    exact not_prime_dvd_coefficients_of_isPrimitive hQ hp hpQa hpQb hpQc
  · have hpRa : (p : ℤ) ∣ R.a := (Int.natCast_dvd).mpr hpRa_nat
    have hpRb : (p : ℤ) ∣ R.b := by
      simpa [h.2.1] using hpQb
    exact not_prime_dvd_coefficients_of_isPrimitive hR hp hpRa hpRb hpRc

/-! ## Cox Lemma 2.25: primitive forms represent numbers coprime to any given M

The key number-theoretic lemma: a primitive binary quadratic form represents
infinitely many integers coprime to any prescribed nonzero integer.  This is
the form-level engine behind concordant-representative replacement and
ultimately behind the fact that every ideal class contains an ideal with norm
coprime to any given modulus (Cox Corollary 7.17). -/

section Lemma_2_25

open scoped Function

/-- For a primitive form and a prime `p`, one of the three canonical vectors
`(1,0)`, `(0,1)`, `(1,1)` evaluates to an integer not divisible by `p`. -/
theorem exists_eval_not_dvd_of_isPrimitive_of_prime {Q : BinaryQuadraticForm}
    (hQ : Q.IsPrimitive) {p : ℕ} (hp : Nat.Prime p) :
    (¬ (p : ℤ) ∣ Q.eval 1 0) ∨ (¬ (p : ℤ) ∣ Q.eval 0 1)
      ∨ (¬ (p : ℤ) ∣ Q.eval 1 1) := by
  have ha : Q.eval 1 0 = Q.a := by simp [eval]
  have hc : Q.eval 0 1 = Q.c := by simp [eval]
  have hsum : Q.eval 1 1 = Q.a + Q.b + Q.c := by simp [eval]
  by_cases hpa : (p : ℤ) ∣ Q.a
  · by_cases hpc : (p : ℤ) ∣ Q.c
    · right; right
      rw [hsum]
      intro hpsum
      -- Since p divides a, c, and a+b+c, it also divides b
      have hpb : (p : ℤ) ∣ Q.b := by
        have htemp : (p : ℤ) ∣ (Q.a + Q.b + Q.c) - Q.a - Q.c := by
          exact (dvd_sub (dvd_sub hpsum hpa) hpc)
        -- (a+b+c) - a - c = b
        simpa [add_sub_add_right_eq_sub, add_sub_cancel_left, add_comm, add_left_comm] using htemp
      -- Convert ℤ divisibility to ℕ divisibility
      have hpb_nat : p ∣ Int.gcd Q.b Q.c :=
        Int.dvd_gcd (by exact_mod_cast hpb) (by exact_mod_cast hpc)
      have hpa_nat : p ∣ Int.gcd Q.a (Int.gcd Q.b Q.c) :=
        Int.dvd_gcd (by exact_mod_cast hpa) (by exact_mod_cast hpb_nat)
      rw [hQ] at hpa_nat
      have hp_dvd_one : p ∣ (1 : ℕ) := hpa_nat
      exact Nat.Prime.not_dvd_one hp hp_dvd_one
    · right; left
      rw [hc]
      exact hpc
  · left
    rw [ha]
    exact hpa

/-- If no prime divisor of `M` divides `n`, then `n` is coprime to `M`. -/
theorem gcd_eq_one_of_forall_prime_not_dvd {n M : ℤ}
    (h : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ M → ¬ (p : ℤ) ∣ n) :
    Int.gcd n M = 1 := by
  by_contra hg
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hg
  have hpz_dvd_gcd : (p : ℤ) ∣ (Int.gcd n M : ℤ) := by exact_mod_cast hpdvd
  have hpz_dvd_n : (p : ℤ) ∣ n := dvd_trans hpz_dvd_gcd (Int.gcd_dvd_left n M)
  have hpz_dvd_M : (p : ℤ) ∣ M := dvd_trans hpz_dvd_gcd (Int.gcd_dvd_right n M)
  exact (h p hp hpz_dvd_M) hpz_dvd_n

/-- Evaluation of an integral binary quadratic form respects congruent input
vectors. -/
theorem eval_modEq {Q : BinaryQuadraticForm} {m x x' y y' : ℤ}
    (hx : x ≡ x' [ZMOD m]) (hy : y ≡ y' [ZMOD m]) :
    Q.eval x y ≡ Q.eval x' y' [ZMOD m] := by
  unfold eval
  simpa [mul_assoc] using
    (Int.ModEq.add (Int.ModEq.add (Int.ModEq.mul_left Q.a (Int.ModEq.pow 2 hx))
      (Int.ModEq.mul_left Q.b (Int.ModEq.mul hx hy)))
      (Int.ModEq.mul_left Q.c (Int.ModEq.pow 2 hy)))

/-- Binary quadratic form evaluation is homogeneous of degree two. -/
theorem eval_mul_right (Q : BinaryQuadraticForm) (x y k : ℤ) :
    Q.eval (x * k) (y * k) = k ^ 2 * Q.eval x y := by
  unfold eval
  ring

/-- A small residue vector modulo a prime on which a primitive form is nonzero. -/
private structure PrimeAvoidingVector (Q : BinaryQuadraticForm) (p : ℕ) where
  x : ℕ
  y : ℕ
  x_le_one : x ≤ 1
  y_le_one : y ≤ 1
  coprime : Int.gcd (x : ℤ) (y : ℤ) = 1
  not_dvd_eval : ¬ (p : ℤ) ∣ Q.eval x y

/-- Primitive forms have a nonzero value modulo every prime at one of
`(1, 0)`, `(0, 1)`, or `(1, 1)`. -/
private theorem exists_primeAvoidingVector {Q : BinaryQuadraticForm}
    (hQ : Q.IsPrimitive) {p : ℕ} (hp : Nat.Prime p) :
    Nonempty (PrimeAvoidingVector Q p) := by
  rcases exists_eval_not_dvd_of_isPrimitive_of_prime hQ hp with h10 | h01 | h11
  · exact ⟨⟨1, 0, by norm_num, by norm_num, by norm_num, by simpa using h10⟩⟩
  · exact ⟨⟨0, 1, by norm_num, by norm_num, by norm_num, by simpa using h01⟩⟩
  · exact ⟨⟨1, 1, by norm_num, by norm_num, by norm_num, by simpa using h11⟩⟩

/-- Distinct prime divisors of a natural number are pairwise coprime. -/
private theorem primeFactors_pairwise_coprime (N : ℕ) :
    Set.Pairwise N.primeFactors (Nat.Coprime on id) := by
  intro p hp q hq hpq
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  exact hpp.coprime_iff_not_dvd.mpr fun hpdq =>
    hpq ((hqp.dvd_iff_eq hpp.ne_one).mp hpdq).symm

/-- The first coordinate chosen for a prime factor of `M`, defaulting to `0`
away from the prime-factor set. -/
private noncomputable def primeAvoidingX
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ) (p : ℕ) : ℕ :=
  if hp : p ∈ M.natAbs.primeFactors then
    (Classical.choice
      (exists_primeAvoidingVector (Q := Q) hQ (Nat.prime_of_mem_primeFactors hp))).x
  else
    0

/-- The second coordinate chosen for a prime factor of `M`, defaulting to `0`
away from the prime-factor set. -/
private noncomputable def primeAvoidingY
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ) (p : ℕ) : ℕ :=
  if hp : p ∈ M.natAbs.primeFactors then
    (Classical.choice
      (exists_primeAvoidingVector (Q := Q) hQ (Nat.prime_of_mem_primeFactors hp))).y
  else
    0

/-- The chosen local residue vector avoids zero modulo each prime factor of
`M`. -/
private theorem primeAvoiding_not_dvd_eval
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ)
    {p : ℕ} (hp : p ∈ M.natAbs.primeFactors) :
    ¬ (p : ℤ) ∣ Q.eval (primeAvoidingX Q hQ M p) (primeAvoidingY Q hQ M p) := by
  simpa [primeAvoidingX, primeAvoidingY, hp] using
    (Classical.choice
      (exists_primeAvoidingVector (Q := Q) hQ (Nat.prime_of_mem_primeFactors hp))).not_dvd_eval

/-- CRT choice of first coordinates avoiding all prime factors of `M`. -/
private noncomputable def crtAvoidingX
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ) : ℕ :=
  Nat.chineseRemainderOfFinset
    (primeAvoidingX Q hQ M)
    id M.natAbs.primeFactors
    (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (primeFactors_pairwise_coprime M.natAbs)

/-- CRT choice of second coordinates avoiding all prime factors of `M`. -/
private noncomputable def crtAvoidingY
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ) : ℕ :=
  Nat.chineseRemainderOfFinset
    (primeAvoidingY Q hQ M)
    id M.natAbs.primeFactors
    (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (primeFactors_pairwise_coprime M.natAbs)

/-- The CRT first coordinate has the prescribed residue modulo every prime
factor of `M`. -/
private theorem crtAvoidingX_modEq
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ)
    {p : ℕ} (hp : p ∈ M.natAbs.primeFactors) :
    crtAvoidingX Q hQ M ≡ primeAvoidingX Q hQ M p [MOD p] := by
  unfold crtAvoidingX
  simpa using (Nat.chineseRemainderOfFinset
    (primeAvoidingX Q hQ M)
    id M.natAbs.primeFactors
    (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (primeFactors_pairwise_coprime M.natAbs)).prop p hp

/-- The CRT second coordinate has the prescribed residue modulo every prime
factor of `M`. -/
private theorem crtAvoidingY_modEq
    (Q : BinaryQuadraticForm) (hQ : Q.IsPrimitive) (M : ℤ)
    {p : ℕ} (hp : p ∈ M.natAbs.primeFactors) :
    crtAvoidingY Q hQ M ≡ primeAvoidingY Q hQ M p [MOD p] := by
  unfold crtAvoidingY
  simpa using (Nat.chineseRemainderOfFinset
    (primeAvoidingY Q hQ M)
    id M.natAbs.primeFactors
    (by intro p hp; exact (Nat.prime_of_mem_primeFactors hp).ne_zero)
    (primeFactors_pairwise_coprime M.natAbs)).prop p hp

/-- **Cox Lemma 2.25.** A primitive binary quadratic form represents an integer
coprime to any prescribed nonzero integer `M`.  Moreover, the representing
vector `(x, y)` can be chosen with `gcd x y = 1`.

The proof uses the Chinese Remainder Theorem: for each prime `p | |M|`, pick
`(u_p, v_p) ∈ {(1,0),(0,1),(1,1)}` with `p ∤ Q(u_p, v_p)` (by
`exists_eval_not_dvd_of_isPrimitive_of_prime`), then combine via CRT to get
`(x, y)` satisfying all congruences simultaneously. After dividing by `d =
gcd(x, y)`, the resulting coprime pair still works. -/
theorem exists_coprime_eval_of_isPrimitive {Q : BinaryQuadraticForm}
    (hQ : Q.IsPrimitive) {M : ℤ} (hM : M ≠ 0) :
    ∃ x y : ℤ, Int.gcd x y = 1 ∧ Int.gcd (Q.eval x y) M = 1 := by
  by_cases hMone : M.natAbs = 1
  · exact ⟨1, 0, by norm_num, by simp [Int.gcd, hMone]⟩
  let X : ℤ := crtAvoidingX Q hQ M
  let Y : ℤ := crtAvoidingY Q hQ M
  have hMnat : M.natAbs ≠ 0 := by
    contrapose! hM
    exact Int.natAbs_eq_zero.mp hM
  have havoid : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ M → ¬ (p : ℤ) ∣ Q.eval X Y := by
    intro p hp hpdM hpEval
    have hpdMnat : p ∣ M.natAbs := (Int.natCast_dvd).mp hpdM
    have hp_mem : p ∈ M.natAbs.primeFactors := hp.mem_primeFactors hpdMnat hMnat
    have hxnat := crtAvoidingX_modEq Q hQ M hp_mem
    have hynat := crtAvoidingY_modEq Q hQ M hp_mem
    have hx : X ≡ (primeAvoidingX Q hQ M p : ℤ) [ZMOD p] := by
      simpa [X] using (by exact_mod_cast hxnat)
    have hy : Y ≡ (primeAvoidingY Q hQ M p : ℤ) [ZMOD p] := by
      simpa [Y] using (by exact_mod_cast hynat)
    have heval : Q.eval X Y ≡
        Q.eval (primeAvoidingX Q hQ M p) (primeAvoidingY Q hQ M p) [ZMOD p] :=
      eval_modEq hx hy
    have hlocal_dvd : (p : ℤ) ∣
        Q.eval (primeAvoidingX Q hQ M p) (primeAvoidingY Q hQ M p) := by
      have hzero : Q.eval X Y ≡ 0 [ZMOD p] := Int.modEq_zero_iff_dvd.mpr hpEval
      exact Int.modEq_zero_iff_dvd.mp (heval.symm.trans hzero)
    exact primeAvoiding_not_dvd_eval Q hQ M hp_mem hlocal_dvd
  have hXYcoprimeM : Int.gcd (Q.eval X Y) M = 1 :=
    gcd_eq_one_of_forall_prime_not_dvd havoid
  have hgpos : 0 < Int.gcd X Y := by
    exact Nat.pos_of_ne_zero fun hg => by
      have hX0Y0 : X = 0 ∧ Y = 0 := by
        simpa using (Int.gcd_eq_zero_iff.mp hg)
      have hQE0 : Q.eval X Y = 0 := by
        rw [hX0Y0.1, hX0Y0.2]
        simp [eval]
      have hbad : Int.gcd (Q.eval X Y) M = M.natAbs := by
        simp [hQE0]
      rw [hXYcoprimeM] at hbad
      exact hMone hbad.symm
  obtain ⟨x, y, hxy, hX, hY⟩ := Int.exists_gcd_one hgpos
  refine ⟨x, y, hxy, ?_⟩
  apply gcd_eq_one_of_forall_prime_not_dvd
  intro p hp hpdM hpdEval
  have hpdEvalXY : (p : ℤ) ∣ Q.eval X Y := by
    let g : ℤ := Int.gcd X Y
    have hXg : X = x * g := by simpa [g] using hX
    have hYg : Y = y * g := by simpa [g] using hY
    have hQeval : Q.eval X Y = g ^ 2 * Q.eval x y := by
      rw [hXg, hYg, eval_mul_right]
    rw [hQeval]
    exact dvd_mul_of_dvd_right hpdEval ((Int.gcd X Y : ℤ) ^ 2)
  exact (havoid p hp hpdM) hpdEvalXY

end Lemma_2_25

/-! ## Concordant representative replacement

The main lemma that makes Gauss composition work on arbitrary form classes:
given two primitive positive definite forms of the same discriminant, there
exist properly equivalent forms that are concordant (same middle coefficient,
coprime leading coefficients). -/

section ConcordantReplacement

/-- From coprime `x y : ℤ`, construct an `SL₂(ℤ)` matrix whose first column is
`(x, y)`.  The second column is produced by Bézout's identity. -/
def sl2z_of_coprime (x y : ℤ) (h : Int.gcd x y = 1) : SL2Z := by
  have hbezout : (Int.gcd x y : ℤ) = x * Int.gcdA x y + y * Int.gcdB x y :=
    Int.gcd_eq_gcd_ab x y
  rw [h] at hbezout
  have hone : x * Int.gcdA x y + y * Int.gcdB x y = (1 : ℤ) :=
    hbezout.symm
  -- Build matrix [[x, -gcdB], [y, gcdA]] with determinant 1
  refine ⟨![![x, -Int.gcdB x y], ![y, Int.gcdA x y]], ?_⟩
  rw [Matrix.det_fin_two]
  calc
    x * Int.gcdA x y - (-Int.gcdB x y) * y = x * Int.gcdA x y + y * Int.gcdB x y := by ring
    _ = (1 : ℤ) := hone

/-- The transform of a form by `sl2z_of_coprime x y h` has leading coefficient
equal to `Q.eval x y`. -/
theorem transform_sl2z_of_coprime_a (Q : BinaryQuadraticForm) (x y : ℤ)
    (h : Int.gcd x y = 1) :
    (transform Q (sl2z_of_coprime x y h)).a = Q.eval x y := by
  -- Compute directly: the first column of the matrix is (x, y)
  have h00 : (sl2z_of_coprime x y h : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = x := rfl
  have h10 : (sl2z_of_coprime x y h : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = y := rfl
  -- The leading coefficient after SL₂(ℤ) transform is Q.eval at the first column
  have hcalc : (transform Q (sl2z_of_coprime x y h)).a =
      Q.eval ((sl2z_of_coprime x y h : Matrix (Fin 2) (Fin 2) ℤ) 0 0)
             ((sl2z_of_coprime x y h : Matrix (Fin 2) (Fin 2) ℤ) 1 0) := by
    simp [transform, eval]
  rw [hcalc, h00, h10]

/-- The transform of a form by `sl2z_of_coprime x y h` preserves the discriminant
and primitivity (inherited from `Action.lean`). -/
theorem properEquivalent_sl2z_of_coprime (Q : BinaryQuadraticForm) (x y : ℤ)
    (h : Int.gcd x y = 1) : ProperEquivalent Q (transform Q (sl2z_of_coprime x y h)) :=
  ⟨sl2z_of_coprime x y h, rfl⟩

/-- The translation matrix `T^n = [[1,n],[0,1]]`. -/
def translateSL2Z (n : ℤ) : SL2Z := by
  refine ⟨![![1, n], ![0, 1]], ?_⟩
  rw [Matrix.det_fin_two]
  change 1 * 1 - n * 0 = 1
  ring

@[simp] theorem translateSL2Z_apply_00 (n : ℤ) :
    (translateSL2Z n : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = 1 :=
  rfl

@[simp] theorem translateSL2Z_apply_01 (n : ℤ) :
    (translateSL2Z n : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = n :=
  rfl

@[simp] theorem translateSL2Z_apply_10 (n : ℤ) :
    (translateSL2Z n : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 :=
  rfl

@[simp] theorem translateSL2Z_apply_11 (n : ℤ) :
    (translateSL2Z n : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 :=
  rfl

@[simp] theorem transform_translate_a (Q : BinaryQuadraticForm) (n : ℤ) :
    (transform Q (translateSL2Z n)).a = Q.a := by
  change Q.a * 1 ^ 2 + Q.b * 1 * 0 + Q.c * 0 ^ 2 = Q.a
  ring

@[simp] theorem transform_translate_b (Q : BinaryQuadraticForm) (n : ℤ) :
    (transform Q (translateSL2Z n)).b = Q.b + 2 * Q.a * n := by
  change 2 * Q.a * 1 * n + Q.b * (1 * 1 + n * 0) + 2 * Q.c * 0 * 1 =
    Q.b + 2 * Q.a * n
  ring

@[simp] theorem transform_translate_c (Q : BinaryQuadraticForm) (n : ℤ) :
    (transform Q (translateSL2Z n)).c = Q.a * n ^ 2 + Q.b * n + Q.c := by
  change Q.a * n ^ 2 + Q.b * n * 1 + Q.c * 1 ^ 2 = Q.a * n ^ 2 + Q.b * n + Q.c
  ring

/-- Same-discriminant forms have middle coefficients of the same parity. -/
theorem even_sub_b_of_same_discriminant {Q R : BinaryQuadraticForm}
    (hD : Q.disc = R.disc) : Even (R.b - Q.b) := by
  rcases Q with ⟨a, b, c⟩
  rcases R with ⟨A, B, C⟩
  simp only [disc_mk] at hD
  have hprod : (B - b) * (B + b) = 4 * (A * C - a * c) := by nlinarith
  have hprod_even : Even ((B - b) * (B + b)) := by
    rw [hprod]
    use 2 * (A * C - a * c)
    ring
  rw [Int.even_mul] at hprod_even
  rcases hprod_even with h | h
  · exact h
  · have hsame : Even ((B + b) - (B - b)) := by
      use b
      ring
    rcases h with ⟨k, hk⟩
    rcases hsame with ⟨l, hl⟩
    use k - l
    linarith

/-- If leading coefficients are coprime and middle coefficients have the same
parity, translations can align the middle coefficients. -/
theorem exists_middle_alignment {A C b d : ℤ} (hgcd : Int.gcd A C = 1)
    (heven : Even (d - b)) :
    ∃ n m : ℤ, b + 2 * A * n = d + 2 * C * m := by
  rcases heven with ⟨k, hk⟩
  have hbez : (1 : ℤ) = A * Int.gcdA A C + C * Int.gcdB A C := by
    rw [← Int.gcd_eq_gcd_ab A C, hgcd]
    norm_num
  refine ⟨Int.gcdA A C * k, -Int.gcdB A C * k, ?_⟩
  calc
    b + 2 * A * (Int.gcdA A C * k) = b + 2 * (A * Int.gcdA A C) * k := by ring
    _ = b + 2 * ((1 : ℤ) - C * Int.gcdB A C) * k := by
      have hA : A * Int.gcdA A C = (1 : ℤ) - C * Int.gcdB A C := by linarith
      rw [hA]
    _ = b + 2 * k + 2 * C * (-Int.gcdB A C * k) := by ring
    _ = b + (d - b) + 2 * C * (-Int.gcdB A C * k) := by rw [hk]; ring
    _ = d + 2 * C * (-Int.gcdB A C * k) := by ring

/-- **Concordant replacement lemma.** Given two primitive positive definite forms
of the same discriminant, there exist properly equivalent forms that are
concordant.

The proof first uses `exists_coprime_eval_of_isPrimitive` to find a primitive
vector where `Q` takes a value coprime to `R.a`, then applies the corresponding
`SL₂(ℤ)` change of variables to make that value the leading coefficient.  Since
same-discriminant forms have middle coefficients of the same parity, Bezout
coefficients for the two coprime leading coefficients give translations that
align the middle coefficients, producing concordant representatives. -/
theorem exists_concordant_of_sameDiscriminant
    {Q R : BinaryQuadraticForm} (hQprim : Q.IsPrimitive) (_hRprim : R.IsPrimitive)
    (_hQpos : Q.IsPositiveDefinite) (hRpos : R.IsPositiveDefinite)
    (hD : Q.disc = R.disc) :
    ∃ Q' R' : BinaryQuadraticForm,
      ProperEquivalent Q Q' ∧ ProperEquivalent R R' ∧ IsConcordant Q' R' := by
  obtain ⟨x, y, hxy, hcop⟩ :=
    exists_coprime_eval_of_isPrimitive hQprim (M := R.a) (ne_of_gt hRpos.1)
  let g : SL2Z := sl2z_of_coprime x y hxy
  let Q₁ : BinaryQuadraticForm := transform Q g
  have hQ_Q₁ : ProperEquivalent Q Q₁ := ⟨g, rfl⟩
  have hQ₁a : Q₁.a = Q.eval x y := by
    simpa [Q₁, g] using transform_sl2z_of_coprime_a Q x y hxy
  have hQ₁a_coprime_Ra : Int.gcd Q₁.a R.a = 1 := by
    simpa [hQ₁a] using hcop
  have hQ₁disc_R : Q₁.disc = R.disc := by
    calc
      Q₁.disc = Q.disc := by simpa [Q₁, g] using disc_transform Q g
      _ = R.disc := hD
  have heven : Even (R.b - Q₁.b) := even_sub_b_of_same_discriminant hQ₁disc_R
  obtain ⟨n, m, hbm⟩ :=
    exists_middle_alignment (A := Q₁.a) (C := R.a) (b := Q₁.b) (d := R.b)
      hQ₁a_coprime_Ra heven
  let Q' : BinaryQuadraticForm := transform Q₁ (translateSL2Z n)
  let R' : BinaryQuadraticForm := transform R (translateSL2Z m)
  refine ⟨Q', R', ?_, ?_, ?_⟩
  · exact hQ_Q₁.trans ⟨translateSL2Z n, rfl⟩
  · exact ⟨translateSL2Z m, rfl⟩
  · refine ⟨?_, ?_, ?_⟩
    · calc
        Q'.disc = Q₁.disc := by simpa [Q'] using disc_transform Q₁ (translateSL2Z n)
        _ = R.disc := hQ₁disc_R
        _ = R'.disc := by simpa [R'] using (disc_transform R (translateSL2Z m)).symm
    · simpa [Q', R'] using hbm
    · simpa [Q', R'] using hQ₁a_coprime_Ra

end ConcordantReplacement

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
