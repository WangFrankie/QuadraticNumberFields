/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Action
import QNFMathlib.Data.Int.ModFour

/-!
# Primitive Positive Definite Form Classes

This file defines the restricted carrier used by the imaginary Cox 7.7 bridge:
primitive positive definite binary quadratic forms of a fixed discriminant,
their proper equivalence classes, and the squarefree field-discriminant
arithmetic used by the bridge and computable layers.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-! ## Primitive positive definite form classes -/

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

/-- In the `d % 4 = 1` branch, the field discriminant is `d`. -/
theorem fieldDiscriminant_of_mod_four_eq_one {d : ℤ} (hd4 : d % 4 = 1) :
    fieldDiscriminant d = d := by
  simp [fieldDiscriminant, hd4]

/-- In the `d % 4 ≠ 1` branch, the field discriminant is `4 * d`. -/
theorem fieldDiscriminant_of_mod_four_ne_one {d : ℤ} (hd4 : d % 4 ≠ 1) :
    fieldDiscriminant d = 4 * d := by
  simp [fieldDiscriminant, hd4]

/-- Imaginary squarefree parameters have negative field discriminant. -/
theorem fieldDiscriminant_neg {d : ℤ} (hdneg : d < 0) :
    fieldDiscriminant d < 0 := by
  by_cases hd4 : d % 4 = 1
  · rw [fieldDiscriminant_of_mod_four_eq_one hd4]
    exact hdneg
  · rw [fieldDiscriminant_of_mod_four_ne_one hd4]
    nlinarith

/-- In the `d % 4 ≠ 1` Cox branch, a form of field discriminant has even
middle coefficient. This justifies the `-b / 2` coordinate in the `Zsqrtd`
ideal generator. -/
theorem even_b_of_hasDiscriminant_fieldDiscriminant_of_mod_four_ne_one
    {d : ℤ} (hd4 : d % 4 ≠ 1) {Q : BinaryQuadraticForm}
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d)) : Even Q.b := by
  have hdisc' : Q.b ^ 2 - 4 * Q.a * Q.c = 4 * d := by
    simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using hdisc
  by_contra hb_even
  have hb_not_dvd : ¬ (2 : ℤ) ∣ Q.b := by simpa [even_iff_two_dvd] using hb_even
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
  have hb_dvd : (2 : ℤ) ∣ Q.b := by simpa [even_iff_two_dvd] using hb_even
  have hb2mod0 : Q.b ^ 2 % 4 = 0 := Int.sq_emod_four_of_even Q.b hb_dvd
  have hb2mod1 : Q.b ^ 2 % 4 = 1 := by
    have hmod : Q.b ^ 2 % 4 = d % 4 := by
      have hb2_eq : Q.b ^ 2 = 4 * Q.a * Q.c + d := by nlinarith
      rw [hb2_eq, show 4 * Q.a * Q.c + d = d + 4 * (Q.a * Q.c) by ring,
        Int.add_mul_emod_self_left]
    simpa [hd4] using hmod
  omega

private theorem dvd_disc_of_dvd_coefficients (Q : BinaryQuadraticForm) {n : ℕ}
    (ha : (n : ℤ) ∣ Q.a) (hb : (n : ℤ) ∣ Q.b) (hc : (n : ℤ) ∣ Q.c) :
    ((n : ℤ) * (n : ℤ)) ∣ Q.disc := by
  rcases Q with ⟨A, B, C⟩
  simp only at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  refine ⟨b ^ 2 - 4 * a * c, ?_⟩
  simp [disc]
  ring

private theorem not_two_dvd_common_coefficients_of_fieldDiscriminant_ne_one
    {d : ℤ} [Fact (Squarefree d)] (hd4 : d % 4 ≠ 1) (Q : BinaryQuadraticForm)
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d))
    (ha : (2 : ℤ) ∣ Q.a) (hb : (2 : ℤ) ∣ Q.b) (hc : (2 : ℤ) ∣ Q.c) :
    False := by
  rcases Q with ⟨A, B, C⟩
  simp only at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  have hd_eq : d = b ^ 2 - 4 * a * c := by
    have hdisc' : (2 * b) ^ 2 - 4 * (2 * a) * (2 * c) = 4 * d := by
      simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using hdisc
    nlinarith
  by_cases hb_even : (2 : ℤ) ∣ b
  · have hb2mod0 : b ^ 2 % 4 = 0 := Int.sq_emod_four_of_even b hb_even
    have hdmod : d % 4 = 0 := by
      rw [hd_eq, show b ^ 2 - 4 * a * c = b ^ 2 + 4 * (-(a * c)) by ring]
      omega
    have hdvd : (4 : ℤ) ∣ d := (Int.dvd_iff_emod_eq_zero).mpr hdmod
    exact squarefree_int_not_dvd_four d (Fact.out : Squarefree d) hdvd
  · have hb2mod1 : b ^ 2 % 4 = 1 := Int.sq_emod_four_of_odd b hb_even
    have hdmod : d % 4 = 1 := by
      rw [hd_eq, show b ^ 2 - 4 * a * c = b ^ 2 + 4 * (-(a * c)) by ring]
      omega
    exact hd4 hdmod

private theorem odd_prime_not_common_coefficients_of_fieldDiscriminant_ne_one
    {d : ℤ} [Fact (Squarefree d)] (hd4 : d % 4 ≠ 1) (Q : BinaryQuadraticForm)
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d)) {p : ℕ} (hp : Nat.Prime p)
    (hp2 : p ≠ 2)
    (ha : (p : ℤ) ∣ Q.a) (hb : (p : ℤ) ∣ Q.b) (hc : (p : ℤ) ∣ Q.c) :
    False := by
  rcases Q with ⟨A, B, C⟩
  simp only at ha hb hc
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨c, rfl⟩ := hc
  have hp2dvd4d : (((p * p : ℕ) : ℤ)) ∣ 4 * d := by
    refine ⟨b ^ 2 - 4 * a * c, ?_⟩
    have hdisc' :
        ((p : ℤ) * b) ^ 2 - 4 * ((p : ℤ) * a) * ((p : ℤ) * c) = 4 * d := by
      simpa [HasDiscriminant, disc, fieldDiscriminant, hd4] using hdisc
    rw [← hdisc']
    norm_num
    ring
  have hgcd : Int.gcd (((p * p : ℕ) : ℤ)) (4 : ℤ) = 1 := by
    have hpnot2dvd : ¬ p ∣ 2 := by
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).mp h with hp1 | hpeq2
      · exact hp.ne_one hp1
      · exact hp2 hpeq2
    have hcop2 : Nat.Coprime p 2 := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpnot2dvd
    have hcoppp2 : Nat.Coprime (p * p) 2 := hcop2.mul_left hcop2
    have hcop4 : Nat.Coprime (p * p) 4 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num]
      exact hcoppp2.mul_right hcoppp2
    unfold Int.gcd
    norm_num [Int.natAbs_mul]
    exact hcop4.gcd_eq_one
  have hp2dvdd : (((p * p : ℕ) : ℤ)) ∣ d := by
    apply Int.dvd_of_dvd_mul_left_of_gcd_one
    · simpa [mul_comm, mul_left_comm, mul_assoc] using hp2dvd4d
    · exact hgcd
  have hpunit : ¬ IsUnit (p : ℤ) := by
    rw [Int.isUnit_iff]
    rintro (hp1 | hpneg)
    · exact hp.ne_one (Int.ofNat.inj hp1)
    · omega
  exact Squarefree.not_mul_self_dvd_of_not_isUnit (Fact.out : Squarefree d) hpunit (by
    simpa using hp2dvdd)

/-- A form with squarefree field discriminant is primitive. -/
theorem isPrimitive_of_hasDiscriminant_fieldDiscriminant
    {d : ℤ} [Fact (Squarefree d)] (Q : BinaryQuadraticForm)
    (hdisc : Q.HasDiscriminant (fieldDiscriminant d)) : Q.IsPrimitive := by
  unfold IsPrimitive
  let n : ℕ := Int.gcd Q.a (Int.gcd Q.b Q.c)
  have ha : (n : ℤ) ∣ Q.a := Int.gcd_dvd_left _ _
  have hbc : (n : ℤ) ∣ Int.gcd Q.b Q.c := Int.gcd_dvd_right _ _
  have hb : (n : ℤ) ∣ Q.b := dvd_trans hbc (Int.gcd_dvd_left _ _)
  have hc : (n : ℤ) ∣ Q.c := dvd_trans hbc (Int.gcd_dvd_right _ _)
  by_cases hd4 : d % 4 = 1
  · have hnsq_dvd_disc : ((n : ℤ) * (n : ℤ)) ∣ Q.disc :=
      dvd_disc_of_dvd_coefficients Q ha hb hc
    have hnsq_dvd_d : ((n : ℤ) * (n : ℤ)) ∣ d := by
      rw [hdisc, fieldDiscriminant_of_mod_four_eq_one hd4] at hnsq_dvd_disc
      exact hnsq_dvd_disc
    by_contra hn
    have hnunit : ¬ IsUnit (n : ℤ) := by
      rw [Int.isUnit_iff]
      omega
    exact Squarefree.not_mul_self_dvd_of_not_isUnit (Fact.out : Squarefree d) hnunit
      hnsq_dvd_d
  · by_contra hn
    obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd hn
    have hpz_dvd_n : (p : ℤ) ∣ (n : ℤ) := by exact_mod_cast hpn
    have hpa : (p : ℤ) ∣ Q.a := dvd_trans hpz_dvd_n ha
    have hpb : (p : ℤ) ∣ Q.b := dvd_trans hpz_dvd_n hb
    have hpc : (p : ℤ) ∣ Q.c := dvd_trans hpz_dvd_n hc
    by_cases hp2 : p = 2
    · subst hp2
      exact not_two_dvd_common_coefficients_of_fieldDiscriminant_ne_one
        hd4 Q hdisc hpa hpb hpc
    · exact
        odd_prime_not_common_coefficients_of_fieldDiscriminant_ne_one
          hd4 Q hdisc hp hp2 hpa hpb hpc

end BinaryQuadraticForm
end QuadraticNumberFields
