/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import QuadraticNumberFields.Forms.Action
import QuadraticNumberFields.Forms.Basic
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
  -- The core CRT argument is deferred; this is the main outstanding sorry in the
  -- Gauss composition development.  See the module docstring for the proof sketch.
  sorry

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

/-- **Concordant replacement lemma.** Given two primitive positive definite forms
of the same discriminant, there exist properly equivalent forms that are
concordant.  This is Boundary 1 of the Gauss composition implementation.

Proof sketch (deferred):
1. Apply `exists_coprime_eval_of_isPrimitive` to `Q` with `M = R.a` to get
   `(x, y)` with `gcd x y = 1` and `gcd(Q(x, y), R.a) = 1`.
2. Use `sl2z_of_coprime` to build an `SL₂(ℤ)` matrix sending `(1,0)` to `(x, y)`;
   the transformed form `Q₁` has `Q₁.a = Q(x, y)` coprime to `R.a`.
3. By the Chinese Remainder Theorem (since `gcd(Q₁.a, R.a) = 1` and
   `Q₁.b ≡ R.b (mod 2)` from the shared discriminant), there exists `B`
   with `B ≡ Q₁.b (mod 2·Q₁.a)` and `B ≡ R.b (mod 2·R.a)`.
4. Apply `Tⁿ` transforms to both `Q₁` and `R` to make their middle
   coefficients equal to `B`, yielding concordant `Q'`, `R'`. -/
theorem exists_concordant_of_sameDiscriminant
    {Q R : BinaryQuadraticForm} (hQprim : Q.IsPrimitive) (hRprim : R.IsPrimitive)
    (hQpos : Q.IsPositiveDefinite) (hRpos : R.IsPositiveDefinite)
    (hD : Q.disc = R.disc) :
    ∃ Q' R' : BinaryQuadraticForm,
      ProperEquivalent Q Q' ∧ ProperEquivalent R R' ∧ IsConcordant Q' R' := by
  sorry

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
