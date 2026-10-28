/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import BinaryQuadraticForms.Core.Enumeration
import BinaryQuadraticForms.Core.ReducedUniqueness

/-!
# Reduced Forms of Discriminant `-4p`

For a prime `p ≡ 3 (mod 8)` with `p ≠ 3`, this file shows that class number one
for the fundamental discriminant `-p` leaves exactly three primitive reduced
forms of discriminant `-4p`: the principal form `(1, 0, p)` and the pair
`(4, ±2, (p + 1) / 4)`.  This is the conductor-`2` class-number jump
`h(-4p) = 3 h(-p)` in the special case `h(-p) = 1`, proved by elementary
reduction theory.

## Main results

* `a_eq_one_or_le_four_mul_a_of_card_eq_one`: if `-p` has a single reduced
  form, then the leading coefficient of every positive definite form of
  discriminant `-p` is `1` or at least `p / 4`.
* `enumPrimitiveReducedForms_neg_four_mul_eq`: the explicit reduced forms of
  discriminant `-4p` for `p > 20`.
* `card_enumPrimitiveReducedForms_neg_four_mul_eq_three`: there are exactly
  three of them for every admissible `p`.
-/

namespace QuadraticNumberFields
namespace BinaryQuadraticForm

/-- An odd integer squares to `1` modulo `4`. -/
private theorem sq_emod_four_of_odd {x : ℤ} (hx : Odd x) : x ^ 2 % 4 = 1 := by
  obtain ⟨k, rfl⟩ := hx
  ring_nf
  omega

/-- If `4 ∣ x * y` with `x` odd, then `4 ∣ y`. -/
private theorem four_dvd_of_four_dvd_mul_of_odd {x y : ℤ} (hx : Odd x) (h : 4 ∣ x * y) :
    4 ∣ y := by
  have h2 : IsCoprime (2 : ℤ) x := Int.isCoprime_two_left.mpr hx
  have h4 : IsCoprime (4 : ℤ) x := by
    simpa [show (4 : ℤ) = 2 * 2 by norm_num] using h2.mul_left h2
  exact h4.dvd_of_dvd_mul_left h

variable {p : ℕ}

/-- If the discriminant `-p` has a single reduced form, then every positive
definite form of discriminant `-p` has leading coefficient `1` or at least
`p / 4`: it is equivalent to the principal form `x² + xy + ((p + 1) / 4) y²`,
which represents `1` and otherwise only values at least `p / 4`. -/
theorem a_eq_one_or_le_four_mul_a_of_card_eq_one [Fact (Squarefree (-(p : ℤ)))]
    (hp4 : p % 4 = 3) (hcard : (enumPrimitiveReducedForms (-(p : ℤ))).card = 1)
    {F : BinaryQuadraticForm} (hdisc : F.disc = -(p : ℤ)) (ha : 0 < F.a) :
    F.a = 1 ∨ (p : ℤ) ≤ 4 * F.a := by
  set N : ℤ := ((p : ℤ) + 1) / 4 with hN
  have hN4 : 4 * N = (p : ℤ) + 1 := by omega
  have hp3 : (3 : ℤ) ≤ p := by omega
  have hfd : fieldDiscriminant (-(p : ℤ)) = -(p : ℤ) :=
    fieldDiscriminant_of_mod_four_eq_one (by omega)
  have hPmem : (⟨1, 1, N⟩ : BinaryQuadraticForm) ∈ enumPrimitiveReducedForms (-(p : ℤ)) := by
    rw [mem_enumPrimitiveReducedForms_iff]
    refine ⟨?_, ⟨by norm_num, ?_⟩, ?_, by simp [IsPrimitive]⟩
    · change (1 : ℤ) ^ 2 - 4 * 1 * N = -(p : ℤ)
      linarith
    · change (1 : ℤ) ^ 2 - 4 * 1 * N < 0
      linarith
    · exact ⟨by norm_num, by change (1 : ℤ) ≤ N; omega, fun _ => by norm_num,
        fun _ => by norm_num⟩
  have hFpos : F.IsPositiveDefinite := ⟨ha, by omega⟩
  obtain ⟨R, hRred, hFR⟩ := exists_isReduced_properEquivalent F hFpos
  have hRdisc : R.disc = -(p : ℤ) := (disc_eq_of_properEquivalent hFR).symm.trans hdisc
  have hRmem : R ∈ enumPrimitiveReducedForms (-(p : ℤ)) :=
    mem_enumPrimitiveReducedForms_iff.mpr ⟨hRdisc,
      isPositiveDefinite_of_properEquivalent hFpos hFR, hRred,
      isPrimitive_of_hasDiscriminant_fieldDiscriminant (d := -(p : ℤ)) R
        (by rw [HasDiscriminant, hfd]; exact hRdisc)⟩
  have hRP : R = ⟨1, 1, N⟩ := Finset.card_le_one.mp hcard.le R hRmem _ hPmem
  obtain ⟨g, hg⟩ := hFR
  change transform F g = R at hg
  have hF : F = transform ⟨1, 1, N⟩ g⁻¹ := by
    rw [← hRP, ← hg, transform_mul, mul_inv_cancel, transform_one]
  set s := (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set t := (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  have hFa : F.a = s ^ 2 + s * t + N * t ^ 2 := by
    rw [hF]
    change 1 * s ^ 2 + 1 * s * t + N * t ^ 2 = _
    ring
  have hdet : s * (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * t = 1 := by
    have := (g⁻¹).det_coe
    rwa [Matrix.det_fin_two] at this
  by_cases ht : t = 0
  · left
    rw [ht] at hdet
    have hs : s = 1 ∨ s = -1 := Int.eq_one_or_neg_one_of_mul_eq_one
      (show s * (↑(g⁻¹) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 by linarith)
    rw [hFa, ht]
    rcases hs with hs | hs <;> rw [hs] <;> norm_num
  · right
    have ht2 : 0 < t ^ 2 := by positivity
    rw [hFa]
    nlinarith [sq_nonneg (2 * s + t)]

/-- For `p ≡ 3 (mod 8)` with `p > 20`, class number one for discriminant `-p`
leaves exactly three reduced forms of discriminant `-4p`: the principal form
and the pair `(4, ±2, (p + 1) / 4)`. -/
theorem enumPrimitiveReducedForms_neg_four_mul_eq [Fact (Squarefree (-(p : ℤ)))]
    (hp8 : p % 8 = 3) (hp20 : 20 < p)
    (hcard : (enumPrimitiveReducedForms (-(p : ℤ))).card = 1) :
    enumPrimitiveReducedForms (-(4 * (p : ℤ))) =
      {⟨1, 0, p⟩, ⟨4, 2, ((p : ℤ) + 1) / 4⟩, ⟨4, -2, ((p : ℤ) + 1) / 4⟩} := by
  have hp4 : p % 4 = 3 := by omega
  have key := @a_eq_one_or_le_four_mul_a_of_card_eq_one p _ hp4 hcard
  ext ⟨a, b, c⟩
  rw [mem_enumPrimitiveReducedForms_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton, BinaryQuadraticForm.mk.injEq]
  constructor
  · rintro ⟨hdisc, hpos, hred, hprim⟩
    change b ^ 2 - 4 * a * c = -(4 * (p : ℤ)) at hdisc
    have ha : 0 < a := hpos.1
    have h3 : 3 * a ^ 2 ≤ 4 * (p : ℤ) := by
      have := three_mul_a_sq_le_neg_disc_of_isReduced ⟨a, b, c⟩ hpos hred
      change 3 * a ^ 2 ≤ -(b ^ 2 - 4 * a * c) at this
      linarith
    obtain ⟨hba, hac, -, -⟩ := hred
    change |b| ≤ a at hba
    change a ≤ c at hac
    -- `b` is even
    obtain ⟨β, rfl⟩ : ∃ β, b = 2 * β := by
      rcases Int.even_or_odd' b with ⟨β, hβ | hβ⟩
      · exact ⟨β, hβ⟩
      · subst hβ
        ring_nf at hdisc
        omega
    have hβp : a * c - β ^ 2 = (p : ℤ) := by linarith
    rcases Int.even_or_odd a with ha_even | ha_odd
    · -- `a` even: then `β` and `c` are odd and `4 ∣ a`.
      have hβ_odd : Odd β := by
        rcases Int.even_or_odd β with ⟨k, hk⟩ | hβ
        · obtain ⟨m, hm⟩ := ha_even
          subst hk hm
          ring_nf at hβp
          omega
        · exact hβ
      have hc_odd : Odd c := by
        rcases Int.even_or_odd c with hc | hc
        · exfalso
          have h2 : (2 : ℤ) ∣ (Int.gcd a (Int.gcd (2 * β) c) : ℤ) :=
            Int.dvd_coe_gcd (even_iff_two_dvd.mp ha_even)
              (Int.dvd_coe_gcd (dvd_mul_right 2 β) (even_iff_two_dvd.mp hc))
          rw [show Int.gcd a (Int.gcd (2 * β) c) = 1 from hprim] at h2
          norm_num at h2
        · exact hc
      have h4a : 4 ∣ a := by
        have hsq := sq_emod_four_of_odd hβ_odd
        have : 4 ∣ c * a := by
          rw [mul_comm]
          omega
        exact four_dvd_of_four_dvd_mul_of_odd hc_odd this
      obtain ⟨a', rfl⟩ := h4a
      have hF := key (F := ⟨a', β, c⟩) (by
        change β ^ 2 - 4 * a' * c = -(p : ℤ)
        linarith) (by change 0 < a'; omega)
      change a' = 1 ∨ (p : ℤ) ≤ 4 * a' at hF
      rcases hF with rfl | hF
      · right
        have hβ1 : β = 1 ∨ β = -1 := by
          obtain ⟨k, rfl⟩ := hβ_odd
          rw [abs_le] at hba
          omega
        have hc' : c = ((p : ℤ) + 1) / 4 := by
          rcases hβ1 with rfl | rfl <;> omega
        rcases hβ1 with rfl | rfl
        · left
          exact ⟨rfl, rfl, hc'⟩
        · right
          exact ⟨rfl, by norm_num, hc'⟩
      · exfalso
        nlinarith
    · -- `a` odd: build a form of discriminant `-p` with leading coefficient `a`.
      have hF : ∃ F : BinaryQuadraticForm, F.disc = -(p : ℤ) ∧ F.a = a := by
        rcases Int.even_or_odd β with hβ | hβ
        · -- `β` even: use the middle coefficient `β + a`.
          have hc4 : 4 ∣ c + 2 * β + a := by
            obtain ⟨k, rfl⟩ := hβ
            have hmod := Int.mul_emod a c 4
            have hac4 : a * c % 4 = 3 := by
              have : a * c = 4 * k ^ 2 + (p : ℤ) := by linarith
              omega
            obtain ⟨m, rfl⟩ := ha_odd
            have hc0 : 0 ≤ c % 4 := Int.emod_nonneg _ (by norm_num)
            have hc1 : c % 4 < 4 := Int.emod_lt_of_pos _ (by norm_num)
            have ha4 : (2 * m + 1) % 4 = 1 ∨ (2 * m + 1) % 4 = 3 := by omega
            rcases ha4 with h | h <;> rw [h] at hmod <;> omega
          obtain ⟨C, hC⟩ := hc4
          exact ⟨⟨a, β + a, C⟩, by
            change (β + a) ^ 2 - 4 * a * C = -(p : ℤ)
            linear_combination a * hC - hβp, rfl⟩
        · -- `β` odd: `4 ∣ c`.
          have hc4 : 4 ∣ c := by
            have hsq := sq_emod_four_of_odd hβ
            have : 4 ∣ a * c := by omega
            exact four_dvd_of_four_dvd_mul_of_odd ha_odd this
          obtain ⟨C, rfl⟩ := hc4
          exact ⟨⟨a, β, C⟩, by
            change β ^ 2 - 4 * a * C = -(p : ℤ)
            linarith, rfl⟩
      obtain ⟨F, hFdisc, hFa⟩ := hF
      rcases key hFdisc (hFa ▸ ha) with h1 | h1
      · rw [hFa] at h1
        subst h1
        left
        have hβ0 : β = 0 := by
          rw [abs_le] at hba
          omega
        subst hβ0
        refine ⟨rfl, by norm_num, by linarith⟩
      · exfalso
        rw [hFa] at h1
        have hp20' : (20 : ℤ) < p := by exact_mod_cast hp20
        have ha5 : a ≤ 5 := by
          by_contra! h
          nlinarith
        omega
  · have hN4 : 4 * (((p : ℤ) + 1) / 4) = (p : ℤ) + 1 := by omega
    have hNodd : Odd (((p : ℤ) + 1) / 4) := ⟨((p : ℤ) + 1) / 8, by omega⟩
    have hgcd : Int.gcd 2 (((p : ℤ) + 1) / 4) = 1 :=
      Int.isCoprime_iff_gcd_eq_one.mp (Int.isCoprime_two_left.mpr hNodd)
    rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · refine ⟨?_, ⟨by norm_num, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · change (0 : ℤ) ^ 2 - 4 * 1 * p = -(4 * (p : ℤ))
        ring
      · change (0 : ℤ) ^ 2 - 4 * 1 * p < 0
        omega
      · change |(0 : ℤ)| ≤ 1
        norm_num
      · change (1 : ℤ) ≤ p
        omega
      · intro _
        exact le_rfl
      · intro _
        exact le_rfl
      · simp [IsPrimitive]
    · refine ⟨?_, ⟨by norm_num, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · change (2 : ℤ) ^ 2 - 4 * 4 * (((p : ℤ) + 1) / 4) = -(4 * (p : ℤ))
        linarith
      · change (2 : ℤ) ^ 2 - 4 * 4 * (((p : ℤ) + 1) / 4) < 0
        linarith
      · change |(2 : ℤ)| ≤ 4
        norm_num
      · change (4 : ℤ) ≤ ((p : ℤ) + 1) / 4
        omega
      · intro _
        norm_num
      · intro _
        norm_num
      · change Int.gcd 4 (Int.gcd 2 (((p : ℤ) + 1) / 4)) = 1
        rw [hgcd]
        rfl
    · refine ⟨?_, ⟨by norm_num, ?_⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · change (-2 : ℤ) ^ 2 - 4 * 4 * (((p : ℤ) + 1) / 4) = -(4 * (p : ℤ))
        linarith
      · change (-2 : ℤ) ^ 2 - 4 * 4 * (((p : ℤ) + 1) / 4) < 0
        linarith
      · change |(-2 : ℤ)| ≤ 4
        norm_num
      · change (4 : ℤ) ≤ ((p : ℤ) + 1) / 4
        omega
      · intro h
        norm_num at h
      · intro h
        change (4 : ℤ) = ((p : ℤ) + 1) / 4 at h
        omega
      · change Int.gcd 4 (Int.gcd (-2) (((p : ℤ) + 1) / 4)) = 1
        rw [Int.neg_gcd, hgcd]
        rfl

/-- Class number one for discriminant `-p`, with `p ≡ 3 (mod 8)` and `p ≠ 3`,
gives exactly three reduced forms of discriminant `-4p`. -/
theorem card_enumPrimitiveReducedForms_neg_four_mul_eq_three
    [Fact (Squarefree (-(p : ℤ)))] (hp8 : p % 8 = 3) (hp_ne_three : p ≠ 3)
    (hcard : (enumPrimitiveReducedForms (-(p : ℤ))).card = 1) :
    (enumPrimitiveReducedForms (-(4 * (p : ℤ)))).card = 3 := by
  by_cases hp20 : 20 < p
  · rw [enumPrimitiveReducedForms_neg_four_mul_eq hp8 hp20 hcard]
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩ <;>
      intro h <;> simp only [BinaryQuadraticForm.mk.injEq] at h <;> omega
  · have : p = 11 ∨ p = 19 := by omega
    rcases this with rfl | rfl
    · rw [enumPrimitiveReducedForms_card_eq_length]
      norm_num
      reduce_forms_count
    · rw [enumPrimitiveReducedForms_card_eq_length]
      norm_num
      reduce_forms_count

end BinaryQuadraticForm
end QuadraticNumberFields
